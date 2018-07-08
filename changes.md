## Design changes w.r.t. Lean 2

There are many differences between Lean 2 and Lean 3 which will break Lean 2 files. Here is a list of additional changes in the HoTT library which will break other things

* Namespaces should be opened with a `hott` prefix to disambiguate from namespaces in the core library. Example: use `open hott.is_equiv` instead of `open is_equiv`.
* `+` can no longer be used for sum of types, use `⊎` (`\uplus`).
* `⁻¹` can no longer be used for inverse of functions, use `⁻¹ᶠ` (`\-1f`).
* `is_trunc_equiv_closed` and variants have the hypothesis `is_trunc _ _` as explicit arguments.
* `pi_pathover_*'` replaced with `pi_pathover_*` and vice versa (the only difference is the prime).
* The type family is explicit in `pathover_idp`, `pathover_idp_of_eq`, `sigma_equiv_sigma_left`, `squareover_ids_of_square`, `square_of_squareover_ids`, `sigma_equiv_of_is_contr_right`.
* `ap_compose'` is reversed (`ap_compose` remains the same).
* the first argument of `pinverse` is explicit (otherwise coercion doesn't work).
* `eq_equiv_homotopy` now has more explicit arguments.
* the projections of `sigma` have been renamed to `fst` and `snd`.
* removed notation `||`, use `∥` (type with `\||`) instead
* all imports are now prefixed with `hott.` as they would otherwise conflict with the core library
* `eq_of_homotopy_eta` removed (was duplicate of `eq_of_homotopy_apd10`)
* remove `*_on` eliminators for HITs.
* `ptrunctype`, `pconntype`, `ptruncconntype` have a pointed type as field (not a type and a point as two separate fields)
<!-- (to do) * renamed `eq_of_fn_eq_fn` to `inj` and `pathover_of_pathover_ap` to `pathover_compose` -->
