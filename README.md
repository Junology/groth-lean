# groth-lean
Formalization of internal math in Grothendieck topoi using Lean Theorem Prover.

In Grothendieck topoi, the following axioms are available:

 - Propositional Extensionality (`propext` in Lean standard lib);
 - Functional Extensionality (`funext` in Lean standard lib);
 - Definite Description (`definite_description` defined in this repo).

The following is NOT available:

 - Excluded Middle
 - Choice

## License
The project is released under BSD 2-clause Licence.
See LICENCE file for detail.

## Install
Although the project uses `leanproject`(https://leanprover-community.github.io/leanproject.html) to manage the repo, most parts of the project are independent of `mathlib` package.
Hence, in most cases, you can just clone the repo in the following standard way:

 ```
 git clone https://github.com/Junology/groth-lean
 ```

If `leanproject` is available on your environment, the following command:

 ```
 leanproject get https://github.com/Junology/groth-lean.git
 ```

