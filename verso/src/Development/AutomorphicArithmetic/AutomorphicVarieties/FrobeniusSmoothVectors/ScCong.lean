import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `l _ c u a ha hcong`. Establish `hu` using `(sc_norm l c u.val).1`. Unfold `Sd.Cong at hcong`. Rewrite `hcong` using `[Units.val_pow_eq_pow_val, Units.val_one]`. Use `set x : PadicAlgCl l := ((u.val : c.O) : PadicAlgCl l) with hx`.

Use `set y : PadicAlgCl l := a.val with hy`. Establish `hy1 : ‖y‖ ≤ 1`. Establish `h` using `IsUltrametricDist.norm_add_le_max (y - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans (max_le ha.le hu)`.

Establish `hxy : ‖x + y‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hu hy1)`. Establish `hmem : (u.val ^ 2 - 1 : c.O) ∈ maximalIdeal c.O`. Rewrite using `[(sc_norm l c _).2]`. Establish `e : ((u.val ^ 2 - 1 : c.O) : PadicAlgCl l) = (x - y) * (x + y) + (y ^ 2 - 1)`. Rewrite using `[hx]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hcong)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Establish `: ‖x - y‖ < 1` using `by rw [← norm_neg, neg_sub]; exact ha`. Use polynomial arithmetic with `[norm_nonneg (x - y), norm_nonneg (x + y)]`. Use `ext`. Simplify using `only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]`. Rewrite using `[← sub_eq_zero]`.

Establish `h0` using `(residue_eq_zero_iff _).2 hmem`. Rewrite `h0` using `[map_sub, map_pow, map_one]`. Conclude with `h0`.
-/
theorem UpperTheory.V.Fr.sc_cong :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (u : c.Oˣ) (a : (Qbar l)ˣ), ‖a.val - u.val.1‖ < 1 → Sd.Cong (a ^ 2) 1 → Units.map (residue c.O).toMonoidHom u ^ 2 = 1 := by
  intro l _ c u a ha hcong
  have hu := (sc_norm l c u.val).1
  unfold Sd.Cong at hcong
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hcong
  set x : PadicAlgCl l := ((u.val : c.O) : PadicAlgCl l) with hx
  set y : PadicAlgCl l := a.val with hy
  have hy1 : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le ha.le hu)
  have hxy : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hu hy1)
  have hmem : (u.val ^ 2 - 1 : c.O) ∈ maximalIdeal c.O := by
    rw [(sc_norm l c _).2]
    have e : ((u.val ^ 2 - 1 : c.O) : PadicAlgCl l) = (x - y) * (x + y) + (y ^ 2 - 1) := by
      rw [hx]
      push_cast
      ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hcong)
    rw [norm_mul]
    have : ‖x - y‖ < 1 := by rw [← norm_neg, neg_sub]; exact ha
    nlinarith [norm_nonneg (x - y), norm_nonneg (x + y)]
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
  rw [← sub_eq_zero]
  have h0 := (residue_eq_zero_iff _).2 hmem
  rw [map_sub, map_pow, map_one] at h0
  exact h0
