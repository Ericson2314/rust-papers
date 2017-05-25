# All Valid Build-Plans Type-Check

# A cautionary tale

# Semver the Compatability relation relations

Semver induces two orders—newness (total) and compatability (partial).
Newness is the obvious lexigraphic ordering of the number lists.
Compatibility is the most important part of the spec.

True compatibility is deeply undecidable.
Henceforth we only consider interface compatibility—two items with the same name (i.e. full path including crate name) and type are assumed to be equal.

Chalk for traits ensures type checking respects compatibility relation.
This property is free without traits, but with traits the comparability relation and trait system need to negotiate.

The compatability relation is in fact a lattice—it is the dual of the subtyping lattice.
[Width subtyping induces union- and intersection-like meets and joins, and depth subtyping is merely induction on the tree structure.] The lattice is semi-bounded with the empty interface as the top type / bottom interface.

Rustc when invoked manually should ensure compatability with upstream rlibs, as is already proposed with chalk.
But with Cargo involved too, we can do better: we can instead use the meet [from the compatability perspective, join from the subtyping] of the interfaces of all allowed versions of each dependency (what a mouthful!).
In the case of a simple "interval" version requirement like "^1", the partial order structure is enough—just take the interface of version 1.
For more complicated version requirements, however, the full lattice structure is needed (e.g.
"everything that 1 and 2 have in common").

Why do we care? This means that crates will or will not type-check regardless of which of the incredibly huge number of possible solutions was chosen.
It's now possible—cheap even—to enforce that every valid build plan type checks!

## Dependency requirement changes are always non-breaking

There's a lot of misguided notions on whether breaking dep bumps make for a breaking change.

First of all, let's be clear: any answer but "never" is severely impractical.
If some bump we're to be a breaking change, however small, then all immediate deps would *themselves* need to make a breaking change, and so on for transitive deps.
Any AWAL library author not releaskng an update is enough to cut-off all children (especially with public deps).
This is horrible—the ecosystem, and even community, would undergo a schism between those preferring instability and those preferring stagnation.

Fortunately, such a bump need never be a breaking change.

There's two ways to look at the interface of crates with dependencies.
The first and simpler is that, since we "upcast" the deps to the join [subtyping perspective] of all allowed versions, the crate presents a single interface regardless of dep solving.
But consider this situation: foo depends on std-1.1, and bar depends on foo and std-1.2.
if foo has some function borrowing a hash map, bar better be able to use foo's function and std's 1.2-only methods on the same hashmap.
This means crates with deps' interfaces are actually (parametric) partial functions of their deps.
Transitive deps don't mean we need to worry about higher order functions.
We just have a "dependent" domain where the dep functions have already been applied to transitive deps so certain equalities of types hold.

The partiality is key here.
We can order functions a <= b as long as this is point-wise true on the intersection of their domains.
This technically means our order is now a preorder, as disjoint-domain functions are compatibility-equivalent.
Worse, that destroys the lattice.
But that's fine cause this accounting trick: we only need the lattices to normalize non-function interfaces: i.e.
crates with all deps instantiated with their normalized interfaces.
So when we need function interfaces we drop the lattice structure and when we need joins and meets we drop the function interfaces.
Crude, but adiquate.

We can enrich our lattice with the *absurd interface*, that of an invalid/unbuildable crate which pollutes the entire build plan.
Because this invalidates the build plan at *solving* time, however, this is perfectly safe and in fact the top of the compatability relation (bottom of subtype relation).
Partial function now become total ones

## Private dependencies

## Features

Monotonic on feature sets.

New default features assumed true.

Public private

## Automatic version bumps

## Portability

## Simultaneous type checking
