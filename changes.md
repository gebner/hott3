## Design changes w.r.t. Lean 2

There are many differences between Lean 2 and Lean 3 which will break Lean 2 files. Here is a list of additional changes in the HoTT library which will break other things

* `+` can no longer be used for sum of types, use `⊕` (`\oplus`)
* `⁻¹` can no longer be used for inverse of functions, use `⁻¹ᶠ` (`\-1f`)
* `is_trunc_equiv_closed` and variants have the hypothesis `is_trunc _ _` as explicit arguments.