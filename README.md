# Homotopy type theory in Lean 3

[![Build Status](https://travis-ci.org/gebner/hott3.svg?branch=master)](https://travis-ci.org/gebner/hott3)

This repository contains a work-in-progress port of the [Lean 2 HoTT library](https://github.com/leanprover/lean2/tree/master/hott) to Lean 3.

## Design 

* No modifications to the Lean kernel are made. Since the Lean 3 kernel is inconsistent with univalence, we "disable" singleton elimination. Singleton elimination is the property that some `Prop`-valued inductive types (where terms can only be constructed in one way) can eliminate to `Type`. The main example is that the equality type `eq` which is defined to be in `Prop` can eliminate to `Type`, which is inconsistent with univalence. Whenever a definition/theorem with the `[hott]` attribute uses singleton elimination, we print an error. Currently we need to add this attribute to all definitions, but in future we expect to say once at the top of a file that all definitions/theorems in that file have the `[hott]` attribute. Without singleton elimination the system is conjectured to be consistent (if it isn't, we can easily extend the check).
* We add univalence as an axiom.
* We add HITs using Dan Licata's trick.
* We try to write domain-specific automation using the powerful metaprogramming language of Lean 3
* All declarations in Lean 3 `init` are available. This is necessary to get the basic tactics. This also means that some "unsafe" tactics are available which use the `Prop`-valued equality.
** don't use `rewrite`, use `rwr` instead
** `cases` sometimes uses singleton elimination. In this case, try replacing it with `induction`.
** `dsimp` is useful for definitional simplifying. It will rewrite all equalities marked with `[hsimp]`. Furthermore you can use `dsimp [foo]` to unfold/rewrite with `foo` (or `dsimp only [foo]` if you don't want to do anything else). For non-definitional simplifying, use `hsimp`.

## Contributing

* Feel free to help porting with files. 
** If you want you can open an issue to ask which files are currently being ported 
** For your convenience you can look [here](https://github.com/fpvandoorn/hott3/tree/searchreplace/from2) for files where some common changes are made with a simple regex-replace.
*** If you port a file from Spectral, make sure it hasn't been modified since september 2017.
** Modify the file to fix all errors in Lean 3. Common changes are listed [here](https://github.com/fpvandoorn/hott3/blob/searchreplace/from2/changes.txt)
** Make a pull request.
* Feel free to write any domain specific automation you want. Summary of wishlist:
** A better algorithm to prove truncatedness and connectedness
** A simple equivalence-maker (for example to prove that structures are sigma types)
** A induct-on-everything tactic (or maybe just induct-on-all-paths and destruct-all-pointed-objects)
** Maybe some tactic other than `dsimp` to do simplification on the goal which has the functionality of `esimp` in Lean 2.