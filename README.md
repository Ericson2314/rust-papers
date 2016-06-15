# A Stateful MIR for Rust

I here propose an enrichment of Rust's core language (the MIR) to support more advanced features.
The list of features I use or enable in the surface language is broad, and should include:

 - "First-class "initializedness" i.e. making the type system aware of initialized locations (or even values!)
   - Typestate
 - [`&move` and friends](https://github.com/rust-lang/rfcs/issues/998)
   - Moving out of `&mut` temporarily [isn't there an issue for this?]
 - Enum variant subtyping
 - Safe `DerefMove`
 - [Placer API](https://github.com/rust-lang/rfcs/pull/809)
 - Partial Moves
   - [Non lexical lifetime](http://smallcultfollowing.com/babysteps/blog/2016/05/04/non-lexical-lifetimes-based-on-liveness/)'s "fragments"
 - Drop
   - [By-value / by `&move` Drop](https://github.com/rust-lang/rfcs/pull/1180)
   - [Cyclic drop](https://github.com/rust-lang/rfcs/pull/1327)
   - Cyclic init
   - [Linear types](https://github.com/rust-lang/rfcs/pull/776)
 - Dynamism
  - Enums with tags in a separate location
  - Desugaring [non-zeroing dynamic drop](https://github.com/rust-lang/rfcs/pull/320)
  - [Non-lexical lifetimes](http://smallcultfollowing.com/babysteps/blog/2016/05/09/non-lexical-lifetimes-adding-the-outlives-relation/)'s "outlives at"

Most previous discussion (what I've linked) focuses on the surface language, backwards compatibility, and the like.
Where the discussion gets stuck is it's not clear what hidden complexity (especially soundness) may be overlooked.
I've instead opted for the route of defining a core language rigorously enough so that readers might convince themselves (or prove!) that the core language is sound and both today's Rust and the proposed extensions can be desugared to it.

The core idea here is to bring back typestate---in this presentation the ability for locations to change type.
With that, many nice abilities arise naturally.


## First-class "Initializedness"

Rust already has limited support for creating locations and initializing them later---see `let x;`.
The problem with its current support is that it's anti-modular: whatever sort of flow analysis pass implements this just looks at the body of a single function and does not allow any operation on the uninitialized local variable.
The solution is two-fold: first, being able to infer "initializedness"---what I am calling the status of whether something is initialized or not---from types alone, and second, allowing locations to change type.

The need for more types is simple enough to understand.
From a tool writer's perspective, types are *the* way to divide-and-conquer or suspend-and-resume some sort of global static analysis:  a little local analysis is done, code/data is tagged with what was proved, and that information can can now be used remotely.

One question is whether lvalues/locations and rvalues/values both need to know about initializedness: on one hand one only writes to or takes references to lvalues, and currently reading uninitialized locations is prohibited.
On the other hand, the type system doesn't currently discriminate between rvalues and lvalues, and in the interest of simplicity it would be nice to keep it that way.
Here's my tiebreaker: functional struct update (`{ foo: bar, ..baz }`) both could benefit from initializedness (field `foo` need not be initialized in `baz`) and only concerns rvalues.
(While a valid desugaring might introduce some temporaries and assign them, this is not the only approach.)
Therefore I opt to include initializedness to types for rvalues and lvalues alike.
Without any way to inspect an undefined value, this should be perfectly safe.

With that alone, however, an uninitialized location can never be used for anything, and an initialized location must stay initialized---we are worse off than before!
But, if we allow a location to change its type (as long as size and alignment is preserved), we get back where we started, and more!
So moving out would change the type of a location from `initialized T` to `uninitialized T`, and the opposite for writes.
("Dropping then writing" is best though of as two separate steps, but can still look like one step only in the surface language.
More on this and dropping in general later.)
In fact, we could even allow changing from `T` to `U` if they have the same size!
Likewise, we only need one uninitialized type per size.
That said, it's possible to stage all this in the core language or surface language, just starting with stateful initializedness for locations.

Let's now start to formalize our new MIR, limiting ourselves to what features have been introduced so far.

For convenience,
```
anything* ::= | anything ',' anything*
```
aka comma-separated repetition, 0 or more times.
As these grammars are really "language agnostic ADTs" and not here for parsing, I may play fast and loose with trailing commas and the like.

lvalues are global or whole-function scoped:
```
Static, s  ::= 'static0' | 'static1' | ...
Local,  l  ::= 'local0'  | 'local1'  | ...
Param,  p  ::= 'param0'  | 'param1'  | ...
LValue, lv ::= 'ret_slot' | Static | Local | Param
```

Types, constants, and rvalues are largely "what one would expect".
Additionally, there is a (size-indexed) uninitialized type and an inscrutable constant inhabiting it, and an absurd type, with no inhabitants:
```
Size,        n  ::= '0b' | '1b' | '2b' | ...
TypeBuiltin     ::= 'Uninit'<Size> | ! | ...
TypeParam,   tp ::= 'TParam0' | 'TParam1' | ...
TypeUserDef     ::= 'User0'   | 'User1'   | ...
Type,        t  ::= TypeBuiltin | TypeParam | TypeUserDef
```
The absurd type is so absurd it can be all sizes for all lvalues (thanks @RalfJung!); there is no need to give it a size index.

```
Constant, c  ::= 'uninit'::<Size> | ...
Operand,  o  ::= 'const'(Constant)
              |  'consume'(LValue)
Unop,     u  ::= ...
Binop,    b  ::= ...
RValue,   rv ::= 'use'(Operand)
              |  'unop'(Unop, Operand, Operand)
              |  'binop'(Binop, Operand, Operand)
```

An *lvalue context* represents the contents of each lvalue *at a node in the CFG*.
A well-formed lvalue context must assign a type to each lvalue exactly once---it is conceptually a function or total map from lvalues to types.
A *static context* is just an lvalue context restricted to statics.
```
LValueContext, LV ::= (LValue: Type)*
StaticContext, S  ::= (Static: Type)*
```

For now, we only will worry about `Copy` implementations, but more generally an *type context* keeps track of user defined types, type parameters, traits bounds.
A trait bound can only involve user-defined types, in which case it represents an impl, or it can involve type parameters, in which case it represents a postulate from a where clause.
[N.B. this roughly corresponds to rustc's `ParameterEnvironment`.]
```
Trait,       tr  ::= # some globally-unique identifier
TraitBound,  trb ::= Type ':' Trait
TypePremise      ::= TraitBound | TypeParam | TypeUserDef
TypeContext, TC  ::= TypePremise*
```
As a basic scoping rule, a parameter should come before any bound that uses it in a type context.

Nodes in the CFG we will think of as continuations: they do not return, and while they don't take any arguments, the types of locations can be enforced as a prerequisite to them being called.
```
Label,      k ::= 'enter' | 'exit'
               |  'k0' | 'k1' | ...
Node,       e ::= 'Assign'(LValue, Operand, Label)
               |  'DropCopy'(LValue, Label)
               |  'If'(Operand, Label, Label)
               |  'Call'(Operand, Label)
               |  'DeadCode'
               |  ... # et cetera
NodeType,  ¬t ::= ¬(LValueContext)
CfgContext, K ::= (Label : NodeType)*
```

And now the judgments.
Operands and rvalues have not one but two lvalue contexts, an "in context" and "out context".
This pattern allows us to thread some state.

Constants can become rvalues whenever, and the in-context and out-context are only constrained to be equal.
```
Const:
  TC  ⊢  c: t
  ────────────────────────────
  TC;  LV;  LV  ⊢  const(c): t
```

Consumption is move complex.
We need to uninitialize the lvalue iff the type is !Copy.
```
MoveConsume:
  ───────────────────────────────────────────────────────────────
  TC, t: !Copy;  LV, lv: t;  LV, lv: Uninit<_>  ⊢  consume(lv): t
```
```
CopyConsume:
  ──────────────────────────────────────────────────────
  TC, t: Copy;  LV, lv: t;  LV, lv: t  ⊢  consume(lv): t
```

The actual threading of the state is in the rvalue intruducers.
Note that the order of the threading does not matter---our state transformations are communicative.
```
Use:
  TC; LV₀; LV₁  ⊢  o: t
  ──────────────────────────
  TC; LV₀; LV₁  ⊢  use(o): t
```
```
UnOp:
  TC; LV₀; LV₁  ⊢  o: t
  u: fn(t) -> u         # primops need no context
  ─────────────────────────────
  TC; LV₀; LV₁  ⊢  use(u, o): u
```
```
BinOp:
  TC; LV₀; LV₁  ⊢  oₗ: t
  TC; LV₁; LV₂  ⊢  oᵣ: t
  b: fn(t, u) -> v       # primops need no context
  ──────────────────────────────────
  TC; LV₀; LV₂  ⊢  use(b, oₗ, oᵣ): u
```

Nodes do not have two lvalue contexts, because viewed as continuations they don't return.
The out contexts of their operand(s) instead constrain their successor(s).
Assignment is perhaps the most important operation:
```
Assign:
  TC; S, LV₀, lv: Uninit<_>;  S, LV₁, lv: Uninit<_>  ⊢  rv: t
  TC; S;  K  ⊢  k: ¬(LV₁, lv: t)
  ───────────────────────────────────────────────────────────
  TC; S;  K  ⊢  assign(lv, rv, k): ¬(LV₀, lv: Uninit<_>)
```
Note that the lvalue to be assigned must be uninitialized prior to assignment, and the rvalue must not affect it, so moving from an lvalue to itself is not prohibited.
[Also note that making `K, k: _ ⊢ ...` the consequent instead of making `... ⊢ k: _` a postulate would work equally well, but this is easier to read.]

Call resembles `Unop` and `Binop`, since its the moral equivalent for calling user-defined instead of primitive functions.
Functions do have type parameters, so we must substitute type args for type parameters.
While it's not too interesting now, it will become more interesting later.
```
Call:
  t₀ = for<tp*> fn(t₁..tₙ) -> tᵣ where trb*
  ∀i.
    TC; S, LVᵢ;  S, LVᵢ₊₁  ⊢ oᵢ : tᵢ [tₜₐ/tp]*
  TC, trb*; S;  K  ⊢  k: ¬(LVₙ₊₁, lv: tᵣ)
  ───────────────────────────────────────────────────────
  TC, trb*; S;  K  ⊢  call<tₜₐ*>(lv, rv*, k): ¬(LV₀, lv: Uninit<_>)
```

We can define diverging functions simply by never calling 'exit' and creating a cylic in the CFG instead.
But when calling a non-terminating function, we still need to provide a successor.
This unreachable node can be used whenever there exists an lvalue with type `!`
Since that is the return type of a diverging function, after we return we will have an lvalue with that type (the return slot), and thus we can use this as a successor.
This is also useful for unreachable branch in an enum match (corresponding to an absurd variant).
```
DeadCode:
  ───────────────────────────────────────────────
  TC; S;  K  ⊢  assign(lv, rv*, k): ¬(LV₀, lv: !)
```

In this formulation, everything is explicit, so we also need to drop copy types (even if such a node is compiled to nothing) to mark them as uninitialized.
```
CopyDrop:
  TC, t: Copy; S;  K  ⊢  k: ¬(LV, lv: Uninit<_>, lv: t)
  ─────────────────────────────────────────────────────
  TC, t: Copy; S;  K  ⊢  drop(lv, k): ¬(LV, lv: t)
```

And here is `if`.
I could go on, but hopefully the basic pattern is clear.
```
If:
  TC; S, LV₀;  S, LV₁  ⊢  o: t
  TC; S; K  ⊢  k₀: ¬(LV₁)
  TC; S; K  ⊢  k₁: ¬(LV₁)
  ──────────────────────────────────
  TC; S; K  ⊢  if(o, k₀, k₁): ¬(LV₀)
```

And finally, the big "let-rec" that ties the "knot" of continuations together into the CFG --- and a function.
Every node in the CFG is postulated (node `eᵢ`, with type `¬tᵢ`), and bound to a label (`k₀`).
```
Fn:
  k₀ = entry
  t₀ = ¬((s: tₛ)*, (a: tₚ)*, (l: Uninit<_>)*, ret_slot: Uninit<_>)
  ∀i.
    TC; # trait impls
    S;  # statics
    l*; # locals (just the location names, no types)
    K,  # user labels, K = { kₙ: ¬tₙ | n }
      exit:  ¬((s: tₛ)*, (a: Uninit<_>)*, (l: Uninit<_>)*, ret_slot: tᵣ);
    ⊢ eᵢ: ¬tᵢ
  ─────────────────────────────────────────────────────────────────────────────
  TC; S  ⊢  Mir { params, locals, labels: { (k: ¬t = e)* }, .. }: fn(tₚ*) -> tᵣ
```
Note the two special labels, 'enter' and 'exit'.
'enter' is defined like any other node, but must exist and match the function's signature.
Specifically, it requires that all locals are uninitialized, and all parameters are initialized to match the type of the function.
'exit' isn't defined at all, but bound in the CfgContext so nodes can choose to exit as a successor.
It requires that all locals and args are uninitialized, but the "return slot" is initialized.

For completeness, we can parameterize the MIR with type parameters and trait bounds like this:
```
FnGeneric:
  TC, tp*, trb*; S  ⊢  f: fn(tₚ*) -> tᵣ
  ───────────────────────────────────────────────────────────
  TC; S ⊢ (Λ<tp*, trb*> f): for<tp*> fn(tₚ*) -> tᵣ where trb*
```

Ok, make sense? I've of course left many parts of the existing MIR unaccounted for: compound lvalues, lifetimes, references, panicking, mutability, aliasing, and more.
Also, I only gave the introducers (I trust the MIRi devs to figure out the eliminators!).
Yet this IR is pretty advanced in some other ways.
Besides changing the types of locations, we have full support for linear types---note that everything must be manually deinitialized.
Going forward, I'll extend this IR little by little until everything should be covered.

[A final note, `CopyDrop` and `CopyConsume` could easily refer to different traits instead of both to `Copy`, to disassociate the ability to be memcopied from the ability to be forgotten.
I have proposed splitting `Copy` like this in the past, but will not mention it again, as nothing else depeons on this.


## Enum Switch

One thing that I haven't explicitly mentioned yet is the subtyping relation over continuation types.
There is no width subtyping because the lvalue must assign a type to all lvalues.
Otherwise, values could be forgotten without being dropped.
There is (contravariant) depth-subtyping, however:
```
SubContLValue:
  b <: a
  ────────────────────────────
  ¬(LV, lv: a) <: ¬(LV, lv: b)
```
the intuition being that a continuation can care only somewhat about an lvalue.
Overall, nothing non-standard here.

Why do I bring this up? Well, while the MIR is mostly safe, enum tagging currently needs a downcast in each branch.
Now the downcast is adjacent to the switch, so it's not that hard to verify, but still it would be nice to have a single node with a safe interface.
Enum variant subtypes have been proposed for a variety of reasons, but fit perfectly here.
Enum switch becomes:
```
Switch:
  (∪ₙ tₙ) :> t
  ∀i
    TC; S; K  ⊢  kᵢ: ¬(LV, lv: tᵢ)
  ────────────────────────────────────────────
  TC; S; K  ⊢  switch(lv, t, k*): ¬(LV, lv: t)
```
[On the first line, that's a union not the letter 'U'.] The union isn't me introducing union types (whew!), but just saying that these tᵢ "cover" t.
The nodes branched from the switch each expect a different variant, and the switch dispatches to the one expecting the variant that's actually there.


## Lifetimes

Niko's recent blog posts cover this very well, so I will build on them.

The "non-lexical" in "non-lexical lifetime" is valid, but leaves out the important detail that such lifetimes *are* lexical with respect to the MIR.
Indeed that this is one of the main motivations for the MIR.
Not only does this make lifetime inference as we currently do simpler, but it also means we can explicitly represent lifetime.
As I mentioned above, in formalisms like this, I believe everything should be explicit, and so lifetimes will be too.

Lifetimes will be abstract function-global labels, just as lvalues have been defined as abstract function-global labels.
Furthermore, just as lvalues can correspond to local variables or parameters, so lifetimes can exist internal to the function body or be parameters.
Finally, there is one static lifetime, but many static lvalues (less symmetry, oh well).
```
LifetimeLocal, 'l ::= '\'local0' | '\'local1' | ...
LifetimeParam, 'p ::= '\'param0' | '\'param1' | ...
Lifetime,      'a ::= '\'static' | LifetimeLocal | LifetimeParam
```

As a first approximation, continuation types will be extended to include the set of liftimes the node inhabits, hereafter called the "active lifetimes".
```
LifetimeContext, LC ::= Lifetime*
NodeType,        ¬t ::= ¬(LValueContext; LifetimeContext)
```
As lvalues contexts must be proper maps, so lifetime contexts must be proper sets when invoking any judgment.

All node introducers so far will be modified to simply propagate the lifetime context: whatever lifetimes include a node's successors will also include the node itself.
Similarly, there is no continuation subtyping related to "active liftimes", they must match exactly.
Now, everything so far alone does renders lifetimes worthless, because all nodes would inhabit the same lifetimes!
To remedy this, we'll have dedicated nodes to begin and end lifetimes: their single successor will have one more or less active lifetime than they do.
For now, lets define them as:
```
LifetimeBegin:
  TC; S; K  ⊢  k: ¬(LV; LC, 'l)
  ────────────────────────────────────
  TC; S; K  ⊢  begin('l, k): ¬(LV; LC)
```
```
LifetimeEnd:
  'l ∉ LV
  TC; S; K  ⊢  k: ¬(LV; LC)
  ──────────────────────────────────────
  TC; S; K  ⊢  end('l, k): ¬(LV; LC, 'l)
```
The additional postulate, that `'l` is not in any (current) type of any location, should ensure that values do not outlive their lifetime.
It would be nicer to use a "strict-outlives" relation, but we don't have that.
Because we do not support controvariant lifetimes, this is sufficient.

I should remark on the design principles that led me to this formalism.
Niko's [third blog post](http://smallcultfollowing.com/babysteps/blog/2016/05/09/non-lexical-lifetimes-adding-the-outlives-relation/) goes over the limitations of single-entry-multiple-exit lifetimes defined with dominators, and the series instead opts to define lifetimes as subsets of CFG nodes which satisfy some conditions.
He also pointed out that lifetimes could be thought of as "sets of paths" through a graph.
I like the imagining lifetimes as "sets of paths", and that leads me to believe we should focus on the path's endpoints more than their interiors.
A set of nodes, however, focuses on active lifetimes and leaves the lifetime boundary implicit, but having explicit start/end nodes does the opposite.
Also, while one could make variants of nodes that introduce lifetimes so we need not introduce extra "no-op" begin/end nodes, that would lead to either explosion of rules, or more complicated rules.

Niko's [second blog post](http://smallcultfollowing.com/babysteps/blog/2016/05/04/non-lexical-lifetimes-based-on-liveness/) on non-lexical lifetimes proposes that instead of requiring the types of binding to outlive the *scope* of the binding, we should merely require that it outlive the *live-range* of the binding.
In my formulation, that is a particularly natural strategy.
Consider that only during the lifetime in which a variable is live will its lvalue be given that type.
Its last use is in fact its destruction, after which the lvalue's type is `Uninit<_>`.
To me, this signifies that the "moral equivalent" of a scope for this IR is in fact exactly this "live-range" lifetime.
While it is possible to derive lifetimes in the core language based on the scopes in the surface language, they are fairly meaningless.

Niko's third blog post also goes over the need for an "outlives-at" relation.
The basic idea is that we often (always?) only care which lifetime ends later, and don't care which began earlier.
More on that for a bit, but note now that this is justification for introducing references with an already active lifetime.
Obviously the newly-introduced reference didn't exists from the beginning of the lifetime, but as long as it is destroyed before the lifetime ends, the lifetime *outlives* the reference *at* the moment of introduction.
Because lifetimes are based on scopes today, we are already allow the bounding lifetime of a reference to extend past the reference's last use, and thus can be confident that a dedicated sort of node just to end lifetimes is sufficiently expressive.
If allowing the creation of references in already active lifetimes is indeed sound, then a dedicated sort of node to begin lifetimes works too.

### Outliving

Now, let us talk about the outlives relationship in detail.
I tried to think to think of a situation where the new "outlives-at" relation wouldn't suffice, and the old "outlives" relation was needed, but I failed.
The rules I came up with, keep the "at" implicit however, so our `x: y` syntax will remain the same.

As before, a lifetime can bound another lifetime or a type.
Lifetime bounds are bundled in an bound context (running out of names, I am).
```
LifetimeBound, lb ::= Lifetime ':' Lifetime
                   |  Type     ':' Lifetime
BoundContext,  BC ::= LifetimeBound*
```

Recall the outlives relation defined in [RFC 1214](https://github.com/rust-lang/rfcs/blob/master/text/1214-projections-lifetimes-and-wf.md).
It didn't concern the terms/the CFG, but simply the derivation of outlive bounds from other outlive bounds.
We will use it here (with the slight exception of a different rule for unique references as those will be defined differently).
Where the judgements refer "the environment", we will make that precise by using the bound context.
Thus, prepend all judgements with `BC; ` in the original rules, like
```
BC; R ⊢ 'foo: 'bar
```
The logic of keeping this largely at is that, working with outlives-at judgements that all share the same "at", one can ignore the position altogether.
If that is not the case, RF 1214's outlives will need to be further modified.

Unfortunately, we must modify continuation types again, giving them---you guessed it---a bound context.
```
NodeType, ¬t ::= ¬(LValueContext; LifetimeContext; BoundContext)
```
Again, all existing rules will blindly propagate the bound context to their successors.
But, this time there is a subtyping rule:
```
SubContOblig:
  ∀lb ∈ OB₁.  OB₀; <>  ⊢ lb
  ──────────────────────────────
  ¬(LV; LC; OB₁) <: ¬(LV; LC; OB₀)
```
Note the the 0 and 1 subscripts are reversed from what one might expect.
Instead of imaging the bounds as *proofs our continuations require*, imagine them as
*obligations our continuations discharge*.
So, given what (all) successors are obligated to carry out, one can deduce bounds using RFC 1412's outlives, and give those new bounds as obligations the current node can carry out.

Why all this?
Consider that there is no evidence in the "past" or "present" with which to prove the outlives-at relation.
The best one can do is charge all successor to witness `'b` dying no later than `'a` for `'a: 'b`.
Consider also that if we had stayed with the original outlives relation, each node would both obligate its predecessors and require a proof from its predecessors.

Hopefully it is clear now that we will need to modify `LifetimeEnd`:
```
LifetimeEnd:
  'l ∉ LV
  TC; S; K  ⊢  k: ¬(LV; LC; BC)
  ───────────────────────────────────────────────────────────────
  TC; S; K  ⊢  end('l, k): ¬(LV; LC, 'l; BC, {'l: 'a | 'a ∈ LC })
```
The set-builder notation says we discharge obligations for each lifetime in `LC`.
(Of course, due the the subtyping rule, it's fine if the predecessor doesn't care about every lifetime in `LC` being outlived.)

We can now redefine `Call`, `Fn`, and `FnGeneric`.
`Call` has three additionally jobs.
First, it needs to provide lifetime arguments from the set of active lifetimes.
Second, it needs to substitute those as well for lifetime parameters in the argument types.
Third, it needs to propagate obligations to satisfy the lifetime bounds from the where clause.
```
Call:
  TC ⊢ trb*
  OB ⊢ lb*
  t₀ = for<tp*, 'p*> fn(t₁..tₙ) -> tᵣ where trb*, lb*
  ∀i.
    TC; S, LVᵢ;  S, LVᵢ₊₁  ⊢ oᵢ : tᵢ [tₜₐ/tp]* ['a/'p]*
  TC; S;  K  ⊢  k: ¬(LVₙ₊₁, lv: tᵣ; LC; OB)
  ────────────────────────────────────────────────────────────────────────
  TC; S;  K  ⊢  call<tₜₐ*, 'a*>(lv, rv*, k): ¬(LV₀, lv: Uninit<_>; LC; OB)
```
[I switched from `TC, trb* ⊢ ...` to making `TC ⊢ trb*` a separate postulate just for legibility.]

`Fn`, not `FnGeneric` is responsible for lifetime parameters and lifetime bounds.
lifetime parameters, and `'static`, become active lifetimes for `enter` and `exit`.
`exit` also satisfies obligations for all lifetime bounds, allowing the obligations to be back-propagated into the rest of the CFG.
```
Fn:
  k₀ = entry
  t₀ = ¬((s: tₛ)*, (a: tₚ)*, (l: Uninit<_>)*, ret_slot: Uninit<_>; 'static, 'p*)
  ∀i.
    TC; # trait impls
    S;  # statics
    l*; # locals (just the location names, no types)
    K,  # user labels, K = { kₙ: ¬tₙ | n }
      exit:  ¬((s: tₛ)*, (a: Uninit<_>)*, (l: Uninit<_>)*, ret_slot: tᵣ; 'static, 'p*; BC);
    ⊢ eᵢ: ¬tᵢ
  ─────────────────────────────────────────────────────────────────────────────────────────
  TC; S  ⊢  Mir { params, locals, labels: { (k: ¬t = e)* }, .. }:
            for<'p*> fn(tₚ*) -> tᵣ where BC
```

`FnGeneric` is basically the same but prepends type parameters to lifetime parameters and prepends trait bounds to lifetime bounds.
```
FnGeneric:
  TC, tp*, trb*; S  ⊢  f: for<'p*> fn(tₚ*) -> tᵣ where BC
  ────────────────────────────────────────────────────────────────────
  TC; S ⊢ (Λ<tp*, trb*> f): for<tp*, 'p*> fn(tₚ*) -> tᵣ where trb*, BC
```

I should note that the outlives-at relation defined this way has some perhaps surprising consequences.
Consider a CFG of a single loop with two lifetimes twice overlapping.
Cut and unrolled, the loop looks like:
```
   'a ┌─────────────────────┐
┅━━━━━┷━━━━┯═══════════╤════╧━━━━━┅
┄──────────┘        'b └──────────┄

  → CFG edge direction (time)
  ━ 'a: 'b
  ═ 'b: 'a
```
the imaginary cut is at the dotted lines, and the brackets labeled `'a` and `'b` denote each lifetime.
Moving from left to right, after `'b` ends and until 'a ends, `'a` can derive that `'b: 'a`, because `'b` is alive at `'a`'s ending.
But the other have of the CFG loop, the opposite can be derived!
This shows that no precaution is taken against a lifetimes re-resurrecting after they were presumed dead.
This might seem highly dangerous, but note that when a lifetime dies, nothing associated with it can still exist because no lvalue can include it in its type.
Thus, no pointer invalidation can occur.

To end the section, I want to close with Niko's most unruly example from the third blog.
In Rust, it looks like:

> ```rust
  let mut map1 = HashMap::new();
  let mut map2 = HashMap::new();
  let key = ...;
  let map_ref1 = &mut map1;
  let v1 = map_ref1.get_mut(&key);
  let v0;
  if some_condition {
      v0 = v1.unwrap();
  } else {
      let map_ref2 = &mut map2;
      let v2 = map_ref2.get_mut(&key);
      v0 = v2.unwrap();
      map1.insert(...);
  }
  use(v0);
> ```

As our CFG it looks like:

```
            A [ map1 = HashMap::new()       ]
            1 [ map2 = HashMap::new()       ]
            2 [ key: K = ...                ]
            3 [ begin('x)                   ]
            3 [ map_ref1 = &mut map1        ]
            4 [ v1 = map_ref1.get_mut(&key) ]
            5 [ if some_condition           ]
                      |               |
                     true           false
                      |               |
                      v               v
  B [ v0 = v1.unwrap() ]   C [ destroy(v0)                 ]
  1 [ goto             ]   1 [ end('x)                     ]
                      |    2 [ begin('x)                   ]
                      |    3 [ map_ref2 = &mut map2        ]
                      |    4 [ v2 = map_ref2.get_mut(&key) ]
                      |    5 [ begin('x)                   ]
                      |    6 [ v0 = v2.unwrap()            ]
                      |    7 [ map1.insert(...)            ]
                      |    8 [ goto                        ]
                      |               |
                      v               v
                    D [ use(v0)       ]
                    1 [ end('x)       ]
```

We can type this with a single lifetime!
Start before A3, to include v1.
V0's ref is given the same lifetime on both branches.
On the right branch, end and begin again before C3, as the next section will demostrate, this "clears" the borrow on map1.
Finally, begin again before assigning `v0` so that it can be given the lifetime as prescribed above.
Note that B1 and C8 have different sets of lvalues borrowed before the merge at D0.
That's fine.
One imagine borrowing and then immediately throwing away the reference, but the location must stayed borrowed until the lifetime the referenced was associated with ends.
Thus one can coerce lvalues to their borrowed equivalents.


## Unique References (Generalizing `&mut`)

[To be written]


## Appendix: Grammar and Rules in Full

All the extension and modifications of each section, squashed together.

### Grammar

```
anything* ::= | anything ',' anything*
```
```
Static, s  ::= 'static0' | 'static1' | ...
Local,  l  ::= 'local0'  | 'local1'  | ...
Param,  p  ::= 'param0'  | 'param1'  | ...
LValue, lv ::= 'ret_slot' | Static | Local | Param
```
```
Size,        n  ::= '0b' | '1b' | '2b' | ...
TypeBuiltin     ::= 'Uninit'<Size> | ...
TypeParam,   tp ::= 'TParam0' | 'TParam1' | ...
TypeUserDef     ::= 'User0'   | 'User1'   | ...
Type,        t  ::= TypeBuiltin | TypeParam | TypeUserDef
```
```
LifetimeLocal, 'l ::= '\'local0' | '\'local1' | ...
LifetimeParam, 'p ::= '\'param0' | '\'param1' | ...
Lifetime,      'a ::= '\'static' | LifetimeLocal | LifetimeParam
```
```
Constant, c  ::= 'uninit'::<Size> | ...
Operand,  o  ::= 'const'(Constant)
              |  'consume'(LValue)
Unop,     u  ::= ...
Binop,    b  ::= ...
RValue,   rv ::= 'use'(Operand)
              |  'unop'(Unop, Operand, Operand)
              |  'binop'(Binop, Operand, Operand)
```
```
LValueContext, LV ::= (LValue: Type)*
StaticContext, S  ::= (Static: Type)*
```
```
Trait,       tr  ::= # some globally-unique identifier
TraitBound,  trb ::= Type ':' Trait
TypePremise      ::= TraitBound | TypeParam | TypeUserDef
TypeContext, TC  ::= TypePremise*
```
```
LifetimeBound       ::= Lifetime ':' Lifetime
                     |  Type     ':' Lifetime
BoundContext,  BC ::= LifetimeBound*
```
```
Label,           k  ::= 'enter' | 'exit'
                     |  'k0' | 'k1' | ...
Node,            e  ::= 'Assign'(LValue, Operand, Label)
                     |  'DropCopy'(LValue, Label)
                     |  'If'(Operand, Label, Label)
                     |  ... # et cetera
LifetimeContext, LC ::= Lifetime*
NodeType,        ¬t ::= ¬(LValueContext; LifetimeContext; BoundContext)
CfgContext,      K  ::= (Label : NodeType)*
```

### Rules

#### Operand Introduction Rules
```
Const:
  TC  ⊢  c: t
  ────────────────────────────
  TC;  LV;  LV  ⊢  const(c): t
```
```
MoveConsume:
  ───────────────────────────────────────────────────────────────
  TC, t: !Copy;  LV, lv: t;  LV, lv: Uninit<_>  ⊢  consume(lv): t
```
```
CopyConsume:
  ──────────────────────────────────────────────────────
  TC, t: Copy;  LV, lv: t;  LV, lv: t  ⊢  consume(lv): t
```

#### RValue Introduction Rules
```
Use:
  TC; LV₀; LV₁  ⊢  o: t
  ──────────────────────────
  TC; LV₀; LV₁  ⊢  use(o): t
```
```
UnOp:
  TC; LV₀; LV₁  ⊢  o: t
  u: fn(t) -> u        # primops need no context
  ─────────────────────────────
  TC; LV₀; LV₁  ⊢  use(u, o): u
```
```
BinOp:
  TC; LV₀; LV₁  ⊢  oₗ: t
  TC; LV₁; LV₂  ⊢  oᵣ: t
  b: fn(t, u) -> v      # primops need no context
  ──────────────────────────────────
  TC; LV₀; LV₂  ⊢  use(b, oₗ, oᵣ): u
```

#### Node/Continuation Introduction Rules
```
Assign:
  TC; S, LV₀, lv: Uninit<_>;  S, LV₁, lv: Uninit<_>  ⊢  rv: t
  TC; S;  K  ⊢  k: ¬(LV₁, rv: t; LC; BC)
  ─────────────────────────────────────────────────────────────
  TC; S;  K  ⊢  assign(lv, o, k): ¬(LV₀, lv: Uninit<_>; LC; BC)
```
```
Call:
  TC ⊢ trb*
  OB ⊢ lb*
  t₀ = for<tp*, 'p*> fn(t₁..tₙ) -> tᵣ where trb*, lb*
  ∀i.
    TC; S, LVᵢ;  S, LVᵢ₊₁  ⊢ oᵢ : tᵢ [tₜₐ/tp]* ['a/'p]*
  TC; S;  K  ⊢  k: ¬(LVₙ₊₁, lv: tᵣ; LC; OB)
  ────────────────────────────────────────────────────────────────────────
  TC; S;  K  ⊢  call<tₜₐ*, 'a*>(lv, rv*, k): ¬(LV₀, lv: Uninit<_>; LC; OB)
```
```
DeadCode:
  ───────────────────────────────────────────────
  TC; S;  K  ⊢  assign(lv, rv*, k): ¬(LV₀, lv: !; LC; BC)
```
```
CopyDrop:
  TC, t: Copy; S;  K  ⊢  k: ¬(LV, lv: Uninit<_>, lv: t; LC; BC)
  ─────────────────────────────────────────────────────────────
  TC, t: Copy; S;  K  ⊢  drop(lv, k): ¬(LV, lv: t; LC; BC)
```
```
If:
  TC; S, LV₀;  S, LV₁  ⊢  o: t
  TC; S; K  ⊢  k₀: ¬(LV₁; LC; BC)
  TC; S; K  ⊢  k₁: ¬(LV₁; LC; BC)
  ──────────────────────────────────────────
  TC; S; K  ⊢  if(o, k₀, k₁): ¬(LV₀; LC; BC)
```
```
Switch:
  (∪ₙ tₙ) :> t
  ∀i
    TC; S; K  ⊢  kᵢ: ¬(LV, lv: tᵢ; LC; BC)
  ────────────────────────────────────────────────────
  TC; S; K  ⊢  switch(lv, t, k*): ¬(LV, lv: t; LC; BC)
```
```
LifetimeBegin:
  TC; S; K  ⊢  k: ¬(LV; LC, 'l; BC)
  ────────────────────────────────────────
  TC; S; K  ⊢  begin('l, k): ¬(LV; LC; BC)
```
```
LifetimeEnd:
  'l ∉ LV
  TC; S; K  ⊢  k: ¬(LV; LC; BC)
  ───────────────────────────────────────────────────────────────
  TC; S; K  ⊢  end('l, k): ¬(LV; LC, 'l; BC, {'l: 'a | 'a ∈ LC })
```

#### `Fn` Introduction Rules
```
Fn:
  k₀ = entry
  t₀ = ¬((s: tₛ)*, (a: tₚ)*, (l: Uninit<_>)*, ret_slot: Uninit<_>; 'p*, BC)
  ∀i.
    TC; # trait impls
    S;  # statics
    l*; # locals (just the location names, no types)
    K,  # user labels, K = { kₙ: ¬tₙ | n }
      exit:  ¬((s: tₛ)*, (a: Uninit<_>)*, (l: Uninit<_>)*, ret_slot: tᵣ; 'p*, BC);
    ⊢ eᵢ: ¬tᵢ
  ────────────────────────────────────────────────────────────────────────────────
  TC; S  ⊢  Mir { params, locals, labels: { (k: ¬t = e)* }, .. }:
            for<'p*> fn(tₚ*) -> tᵣ where BC
```
```
FnGeneric:
  TC, tp*, trb*; S  ⊢  f: for<'p*> fn(tₚ*) -> tᵣ where BC
  ────────────────────────────────────────────────────────────────────
  TC; S ⊢ (Λ<tp*, trb*> f): for<tp*, 'p*> fn(tₚ*) -> tᵣ where trb*, BC
```

#### Subtyping
```
SubRefl:
  ──────
  T <: T
```
```
SubTrans:
  T₀ <: T₁
  T₁ <: T₂
  ──────
  T₀ <: T₂
```
```
SubContLValue:
  b <: a
  ────────────────────────────────────
  ¬(LV, lv: a; LC; OB) <: ¬(LV, lv: b; LC; OB)
```
```
SubContOblig:
  ∀lb ∈ OB₁.  OB₀; <>  ⊢ lb
  ──────────────────────────────
  ¬(LV; LC; OB₁) <: ¬(LV; LC; OB₀)
```
