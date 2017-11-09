## Design changes w.r.t. Lean 2

There are many differences between Lean 2 and Lean 3 which will break Lean 2 files. Here is a list of additional changes in the HoTT library which will break other things

* `+` can no longer be used for sum of types, use `⊎` (`\uplus`).
* `⁻¹` can no longer be used for inverse of functions, use `⁻¹ᶠ` (`\-1f`).
* `is_trunc_equiv_closed` and variants have the hypothesis `is_trunc _ _` as explicit arguments.
* `pi_pathover_*'` replaced with `pi_pathover_*` and vice versa (the only difference is the prime).
* The type family is explicit in `pathover_idp`, `pathover_idp_of_eq`, `sigma_equiv_sigma_left`.
* `ap_compose'` is reversed (`ap_compose` remains the same).
* the first argument of `pinverse` is explicit (otherwise coercion doesn't work).
* `eq_equiv_homotopy` now has more explicit arguments.
* the projections of `sigma` have been renamed to `fst` and `snd`.
* removed notation `||`, use `∥` (type with `\||`) instead
<!-- (to do) * renamed `eq_of_fn_eq_fn` to `inj` -->