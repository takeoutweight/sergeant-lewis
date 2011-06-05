# sergeant-lewis #
## _Blue-Collar Static Analysis of Clojure Code_ ##

This project is about new ways to uncover logical crimes committed in Clojure code. If you squint it looks a bit like a dependent type system, save for the fact that it's ad-hoc, unsound, and a bit provincial when compared to its category theoretic superiors.

Who needs academic Oxford airs when there are bugs to be caught?

## Approach ##

_sergeant-lewis_ uses [Constraint Handling Rules](http://dtai.cs.kuleuven.be/projects/CHR/) to specify logical relationships between code expressions. CHR is being used in a somewhat roguish manner by treating constraint stores as first order values: stores can be terms in constraints which can be then imposed into higher order stores. 

For example, the constraint  [:Boolean true] is represented as the CHR store {:Boolean #{true}}. We can then propose a higher-order constraint [:Not {:Boolean #{true}}], which is a constraint with a store as its second term. Imagine, next, a modal-logic layer with the constraint [:Is 'some-variable {:Not #{{:Boolean #{true}}}}], which has a store as its third term.

I dislike the fact that CHR tends to assume a single ambient constraint store. My hope is that _sergeant-lewis_'s approach follows the example set by [miniKanren](http://mitpress.mit.edu/catalog/item/default.asp?ttype=2&tid=10663) in its rejection of Prolog's stateful, ambient fact database. For this reason, the Clojure-CHR implementation provides extra support for nested stores-as-terms (while staying close to the original CHR semantics). There are methods for both matching constraints within nested stores and also for applying arbitrary sets of rules to nested stores. There is no requirement to operate within a single, shared global store nor is there a single, shared global set of rewrite rules.

## Vision ##

This is currently not much more than a proof of concept of the Inception-style stores-within-constraints-within-stores idiom. It seems to lend itself to clean rewrite rules that express intelligible logical relationships. I would be thrilled to see this system one day allow for the specification of modular, domain-specific invariants in the spirit of [QuickCheck](http://www.haskell.org/haskellwiki/Introduction_to_QuickCheck).

Clojure-CHR also hasn't yet been integrated with core.logic. This, obviously, would represent an unstoppable crime-fighting duo.

## References ##

Nearly all the rewrite rules at this point are inspired by [Typed-Racket](http://docs.racket-lang.org/ts-guide/), most notably path-types (allowing type information to flow into/out-of collection types) and occurrence-types (speculative typing in code branches).
