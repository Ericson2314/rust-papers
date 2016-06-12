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
Param,  a  ::= 'param0'  | 'param1'  | ...
LValue, lv ::= 'ret_slot' | Static | Local | Param
```

Types, constants, and rvalues are largely "what one would expect", with a (sized-indexed) uninitialized type, and uninitialized constant inhabiting it:
```
Size,     n  ::= '0b' | '1b' | '2b' | ...
Type,     t  ::= 'Uninit'<Size> | ...
Constant, c  ::= 'uninit'(Size) | ...
Operand,  o  ::= 'const'(Constant)
              |  'consume'(LValue)
Unop,     u  ::= ...
Binop,    b  ::= ...
RValue,   rv ::= 'use'(Operand)
              |  'unop'(Unop, Operand, Operand)
              |  'binop'(Binop, Operand, Operand)
```

An *lvalue context* represents the contents of each lvalue *at a node in the CFG*.
A well-formed lvalue context must assign a type to a lvalue only once---it is conceptually a map.
An unmentioned lvalue can have any type (with the right size) whatsoever.
A *static context* is just an lvalue context restricted to statics.
```
LValueContext, LV ::= (lv: t)*
StaticContext, S  ::= (s: t)*
```

For now, we only will worry about `Copy`, but more generally an *impl context* keeps track of traits and their implementations.
```
Trait,       tr ::= # some globally-unique identifier
ImplContext, I  ::= (t: i)*
```

Nodes in the CFG we will think of as continuations: they do not return, and while they don't take any arguments, the types of locations can be enforced as a prerequisite to them being called.
```
Label,      k ::= 'enter' | 'exit'
               |  'k0' | 'k1' | ...
Node,       e ::= 'Assign'(lv, o, k)
               |  'DropCopy'(lv, k)
               |  'If'(o, k, k)
               |  ... # et cetera
CfgContext, K ::= (label : ¬(LValueContext))*
```

And now the judgments.
Operands and rvalues have not one but two lvalue contexts, an "in context" and "out context".
This pattern allows us to thread some state.

Constants can become rvalues whenever, and the in-context and out-context are only constrained to be equal.
```
Const:
  I  ⊢  c: t
  ----------------------------
  I;  LV;  LV   ⊢  const(c): t
```

Consumption is move complex.
We need to uninitialize the lvalue iff the type is !Copy.
```
MoveConsume:
  ---------------------------------------------------------------
  I, t: !Copy;  LV, lv: t;  LV, lv: Uninit<_>   ⊢  consume(lv): t
```
```
CopyConsume:
  ------------------------------------------------------
  I, t: Copy;  LV, lv: t;  LV, lv: t   ⊢  consume(lv): t
```

The actual threading of the state is in the rvalue intruducers.
Note that the order of the threading does not matter---our state transformations are communicative.
```
Use:
  I; LV₀; LV₁  ⊢  o: t
  -------------------------
  I; LV₀; LV₁  ⊢  use(o): t
```
```
UnOp:
  I; LV₀; LV₁  ⊢  o: t
  u: fn(t) -> u        # primops need no context
  ----------------------------
  I; LV₀; LV₁  ⊢  use(u, o): u
```
```
BinOp:
  I; LV₀; LV₁  ⊢  oₗ: t
  I; LV₁; LV₂  ⊢  oᵣ: t
  b: fn(t, u) -> v      # primops need no context
  ---------------------------------
  I; LV₀; LV₂  ⊢  use(b, oₗ, oᵣ): u
```

Nodes do not have two lvalue contexts, because viewed as continuations they don't return.
The out contexts of their operand(s) instead constrain their successor(s).
Assignment is perhaps the most important operation:
```
Assign:
  I; S, LV₀, lv: Uninit<_>;  S, LV₁, lv: Uninit<_>  ⊢  o: t
  I; S;  K   ⊢  k: ¬(LV₁, lv: t)
  ---------------------------------------------------------
  I; S;  K   ⊢  assign(lv, o, k): ¬(LV₀, lv: Uninit<_>)
```
Note that the lvalue to be assigned must be uninitialized prior to assignment, and the rvalue must not affect it, so moving from an lvalue to itself is not prohibited.
[Also note that making `K, k: _ ⊢ ...` the consequent instead of making `... ⊢ k: _` a postulate would work equally well, but this is easier to read.]

In this formulation, everything is explicit, so we also need to drop copy types (even if such a node is compiled to nothing) to mark them as uninitialized.
```
CopyDrop:
  I, t: Copy; S;  K   ⊢  k: ¬(LV, lv: Uninit<_>, lv: t)
  -----------------------------------------------------
  I, t: Copy; S;  K   ⊢  drop(lv, k): ¬(LV, lv: t)
```

And here is `if`.
I could go on, but hopefully the basic pattern is clear.
```
If:
  I; S, LV₀;  S, LV₁  ⊢  o: t
  I; S; K  ⊢  k₀: ¬(LV₁)
  I; S; K  ⊢  k₁: ¬(LV₁)
  ---------------------------------
  I; S; K  ⊢  if(o, k₀, k₁): ¬(LV₀)
```

An finally, the big "let-rec" that ties the "knot" of continuations together into the CFG --- and a function.
Note that in addition to the user-defined continuations, 'exit' and 'enter' are automatically part of the context.
'enter' requires that all locals are uninitialized, and args match the type of the function.
'exit' requires that all locals and args are uninitialized, but the "return slot" is initialized.
```
Fn:
  ∀i
    I;  # trait impls
    S;  # statics
    l*; # locals (just the location names, no types)
    K,  # user labels, K = { lₙ: ¬tₙ | n }
      enter: ¬ ∧((s: tₛ)*, (a: tₐ)*,        (l: Uninit<_>)*, ret_slot: Uninit<_>),
      exit:  ¬ ∧((s: tₛ)*, (a: Uninit<_>)*, (l: Uninit<_>)*, ret_slot: tᵣ);
    ⊢ eᵢ: ¬tᵢ
  --------------------------------------------------------------------------------
  I; S  ⊢  Mir { args, locals, labels: { (k: ¬t = e)* }, .. }: fn(tₐ*) -> tᵣ
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
First, we have (contravariant) width subtyping:
```
SubContWidth:
  ¬(LV) <: ¬(LV, lv: a)
```
the intuition being that a continuation does not need to care about the current type of every lvalue.
Second we have (contravariant) depth-subtyping
```
SubContDepth:
  b <: a
  ----------------------------
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
    I; S; K  ⊢  kᵢ: ¬(LV, lv: tᵢ)
  -------------------------------------------
  I; S; K  ⊢  switch(lv, t, k*): ¬(LV, lv: t)
```
[On the first line, that's a union not the letter 'U'.] The union isn't me introducing union types (whew!), but just saying that these tᵢ "cover" t.
The nodes branched from the switch each expect a different variant, and the switch dispatches to the one expecting the variant that's actually there.
