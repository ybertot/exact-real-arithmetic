# Exact Real Arithmetic

This development describes algorithms for exact computation of real numbers,
including algorithms for addition, multiplication, multiplicative inverse,
and square roots.  The whole development is parameterized by a given basis B.
Each real number 'x' is represented by a function 'fx' from Z to Z, where
'fx n' represents the integral part of 'x * B ^ n'.  This representation is
described by the predicate `encadrement`.

The algorithms are taken from the PhD. Thesis of Valérie Ménissier-Morain.
A condensend presentation is available in article of the Journal of
Logic and  Algebraic Programming (Vol. 64, Issue 1, July 2005):
[Arbitrary precision real arithmetic: design and algorithms](https://www.sciencedirect.com/science/article/pii/S1567832604000748).

The initial development by J. Créci, Maintenance was long ensured by H.
Herbelin.

Elie Ancelin and Nicolas Magaud added contributions to this development by
providing proofs for the inverse function.

## Unsafe!

Version prior to December 10, 2019 contain axioms that are clearly
inconsistent.  This concerns all releases up to v8.10.0.  Ongoing work
intends to make a new release compatible with coq 8.10 that is axiom free.
Backporting to older version of coq will probably not happen, unless
popular demand is strong enough.

Plans for fixing are as follows:

 - Make the whole development into a functor, taking all the functions so far
 treated as parameters as an argument module.

 - Develop an extra module to provide an instanciation of all the functions,
   thus showing that all axioms can be verified starting from the axioms of
   real numbers and removing the cause of inconsistency.

 - Fix the place where erroneous axioms are being used.

## In the meantime.

There exist other implementations of exact real arithmetic.  Interested users
should look at the work of Russell O'Connor, Robbert Krebbers, and
Bas Spitters, where the proofs rely on the CoRN presentation of constructive
reals.