import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section Basic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

/- English proof (translation)
Unfold `VGe`. Use `⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[h j, Fin.sum_univ_zero]`.
-/
theorem vge_of_zero {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    (h : ∀ j, s.f j = 0) (r : ℚ) : VGe D F v k α s r := by
  unfold VGe
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
  rw [h j, Fin.sum_univ_zero]

end Basic

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ D Q _ F _ _ v hv m _ R' β s hsupp hnu w hw q hq`. Take `⟨x, hx, hsum⟩` from `hw`. Establish `hxq : ∀ α, ((q : ℚ) : WithTop ℚ) ≤ v (x α)`. Introduce `α`. Distinguish the cases in `h : ∃ z, α = β + R' • z`.

Take `⟨z, rfl⟩` from `h`. Establish `h1` using `GC.valuation_ge_at_zero hϖ hv (hnu (β + R' • z)) (hx _)`. Use `le_trans (WithTop.coe_le_coe.2 ?_) h1` and prove the remaining obligations. Rewrite using `[zero_add]`. Conclude with `hq z`.

Use `push Not at h`. Conclude with `GC.valuation_ge_at_zero hϖ hv (vge_of_zero (v := v) (hsupp α h) q) (hx α)`. Take `⟨S, hS⟩` from `hsum q`. Establish `h1` using `hS S le_rfl`. Establish `h2 : ((q : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ S, x α)` using `AddValuation.map_le_sum v fun α _ => hxq α`.

Establish `h3` using `AddValuation.map_le_add v h1 h2`. Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem n4 : ValuationBoundAtZero := by
  intro V _ _ _ ϖ hϖ D Q _ F _ _ v hv m _ R' β s hsupp hnu w hw q hq
  classical
  obtain ⟨x, hx, hsum⟩ := hw
  have hxq : ∀ α, ((q : ℚ) : WithTop ℚ) ≤ v (x α) := by
    intro α
    by_cases h : ∃ z, α = β + R' • z
    · obtain ⟨z, rfl⟩ := h
      have h1 := GC.valuation_ge_at_zero hϖ hv (hnu (β + R' • z)) (hx _)
      refine le_trans (WithTop.coe_le_coe.2 ?_) h1
      rw [zero_add]; exact hq z
    · push Not at h
      exact GC.valuation_ge_at_zero hϖ hv (vge_of_zero (v := v) (hsupp α h) q) (hx α)
  obtain ⟨S, hS⟩ := hsum q
  have h1 := hS S le_rfl
  have h2 : ((q : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ S, x α) := AddValuation.map_le_sum v fun α _ => hxq α
  have h3 := AddValuation.map_le_add v h1 h2
  rwa [sub_add_cancel] at h3

section Q

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

/- English proof (translation)
Simplify using `only [bOf, zero_add, QForm.Q_zero hϖ D hQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bOf_zero_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (b : D.toPre.X) : bOf D.toPre Q 0 b = 0 := by
  simp only [bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [bOf_zero_left hϖ hQ]`. Consider the case `succ n ih => rw [succ_nsmul, QForm.bOf_add_left hϖ D hQ, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bOf_nsmul_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a b : D.toPre.X) :
    bOf D.toPre Q (n • a) b = n * bOf D.toPre Q a b := by
  induction n with
  | zero => simp [bOf_zero_left hϖ hQ]
  | succ n ih => rw [succ_nsmul, QForm.bOf_add_left hϖ D hQ, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [QForm.Q_zero hϖ D hQ]`. Consider the case `succ n ih`. Establish `h2` using `QForm.two_Q_eq hϖ D hQ a`. Establish `hb` using `bOf_nsmul_left hϖ hQ n a a`.

Establish `e : Q (n • a + a) = Q (n • a) + Q a + bOf D.toPre Q (n • a) a` using `by simp only [bOf]; ring`. Rewrite using `[succ_nsmul, e, ih, hb, ← h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Q_nsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a : D.toPre.X) : Q (n • a) = n ^ 2 * Q a := by
  induction n with
  | zero => simp [QForm.Q_zero hϖ D hQ]
  | succ n ih =>
    have h2 := QForm.two_Q_eq hϖ D hQ a
    have hb := bOf_nsmul_left hϖ hQ n a a
    have e : Q (n • a + a) = Q (n • a) + Q a + bOf D.toPre Q (n • a) a := by simp only [bOf]; ring
    rw [succ_nsmul, e, ih, hb, ← h2]; push_cast; ring

/- English proof (translation)
Establish `e1 : Q (α + k • m) = Q α + Q (k • m) + bOf D.toPre Q α (k • m)` using `by simp only [bOf]; ring`. Rewrite using `[e1, QForm.bOf_comm D α (k • m), bOf_nsmul_left hϖ hQ, Q_nsmul hϖ hQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_shift (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (α m : D.toPre.X) (k : ℕ) :
    Q (α + k • m) = Q α + k * (k * Q m + bOf D.toPre Q m α) := by
  have e1 : Q (α + k • m) = Q α + Q (k • m) + bOf D.toPre Q α (k • m) := by simp only [bOf]; ring
  rw [e1, QForm.bOf_comm D α (k • m), bOf_nsmul_left hϖ hQ, Q_nsmul hϖ hQ]; ring

end Q

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk S hS s r`. Use `⟨fun h α _ => h α, fun h χ => ?_⟩` and prove the remaining obligations. Take `⟨α, hα, m0, rfl⟩` from `hS χ`. Establish `H` using `SectionScalarValuation.fe_move hϖ hQ hv k m0 α s (h α hα)`. Establish `hk0 : (k : ℚ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`.

Establish `e : r + (Q α : ℚ) / k + ((k * Q m0 + bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k`. Rewrite using `[q_shift hϖ hQ α m0 k]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `H` using `[e]`. Then use the resulting hypothesis.
-/
theorem n1a : ValuationMinRepresentatives := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk S hS s r
  refine ⟨fun h α _ => h α, fun h χ => ?_⟩
  obtain ⟨α, hα, m0, rfl⟩ := hS χ
  have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s (h α hα)
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e : r + (Q α : ℚ) / k + ((k * Q m0 + bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
    rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
  rwa [e] at H

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) r.den_pos`. Establish `hv1 : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) = ((r.num : ℚ) : WithTop ℚ)` using `hv _ _ ⟨1, by simp⟩`. Establish `hpow : v (ζ ^ r.den) = r.den • v ζ` using `AddValuation.map_pow v ζ r.den`. Rewrite `hpow` using `[hζ, hv1]`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero r.den_nz`.

Establish `hne : v ζ ≠ ⊤`. Introduce `h`. Rewrite `hpow` using `[h, hk, succ_nsmul, WithTop.add_top]`. Conclude with `WithTop.coe_ne_top hpow`. Take `⟨x, hx⟩` from `WithTop.ne_top_iff_exists.1 hne`.

Rewrite `hpow` using `[← hx, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul]`. Establish `hq : (r.den : ℚ) ≠ 0` using `by exact_mod_cast r.den_nz`. Establish `hxr : x = r`. Establish `h2 : x = (r.num : ℚ) / (r.den : ℚ)` using `eq_div_of_mul_eq hq (by rw [mul_comm]; exact hpow.symm)`. Rewrite using `[h2, Rat.num_div_den]`.

Conclude with `⟨ζ, fun h0 => hne (by rw [h0, AddValuation.map_zero]), by rw [← hx, hxr]⟩`.
-/
theorem exists_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 < r) : ∃ ζ : F, ζ ≠ 0 ∧ v ζ = ((r : ℚ) : WithTop ℚ) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) r.den_pos
  have hv1 : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) =
      ((r.num : ℚ) : WithTop ℚ) := hv _ _ ⟨1, by simp⟩
  have hpow : v (ζ ^ r.den) = r.den • v ζ := AddValuation.map_pow v ζ r.den
  rw [hζ, hv1] at hpow
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero r.den_nz
  have hne : v ζ ≠ ⊤ := by
    intro h
    rw [h, hk, succ_nsmul, WithTop.add_top] at hpow
    exact WithTop.coe_ne_top hpow
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hx, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul] at hpow
  have hq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hxr : x = r := by
    have h2 : x = (r.num : ℚ) / (r.den : ℚ) := eq_div_of_mul_eq hq (by rw [mul_comm]; exact hpow.symm)
    rw [h2, Rat.num_div_den]
  exact ⟨ζ, fun h0 => hne (by rw [h0, AddValuation.map_zero]), by rw [← hx, hxr]⟩

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk s hs0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, hs⟩`. Take `⟨ζ, hζ0, hvζ⟩` from `exists_val_eq hv hr`. Use `⟨ζ, ζ⁻¹ • s, by rw [hvζ]; exact_mod_cast hr, ?_, (isSmul_iff ζ (ζ⁻¹ • s) s).2 (by rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul])⟩` and prove the remaining obligations.

Establish `h` using `NuGe.smul Q (q := -r) (by rw [AddValuation.map_inv, hvζ]; rfl) ((isSmul_iff _ _ _).2 rfl) hs`. Rewrite `h` using `[add_neg_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨ζ, s', hvζ, hs', hsm⟩`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hqle⟩ : ∃ q : ℚ, 0 < q ∧ ((q : ℚ) : WithTop ℚ) ≤ v ζ := by`. Consider the cases of `h : v ζ with`.

Consider the case `top => exact ⟨1, one_pos, le_top⟩`. Consider the case `coe y => rw [h] at hvζ; exact ⟨y, by exact_mod_cast hvζ, le_rfl⟩`. Conclude with `⟨0 + q, by linarith, NuGe.smul Q hqle hsm hs'⟩`.
-/
theorem n1c : PositiveValuationMaximalIdeal := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk s hs0
  constructor
  · rintro ⟨r, hr, hs⟩
    obtain ⟨ζ, hζ0, hvζ⟩ := exists_val_eq hv hr
    refine ⟨ζ, ζ⁻¹ • s, by rw [hvζ]; exact_mod_cast hr, ?_,
      (isSmul_iff ζ (ζ⁻¹ • s) s).2 (by rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul])⟩
    have h := NuGe.smul Q (q := -r) (by rw [AddValuation.map_inv, hvζ]; rfl) ((isSmul_iff _ _ _).2 rfl) hs
    rwa [add_neg_cancel] at h
  · rintro ⟨ζ, s', hvζ, hs', hsm⟩
    obtain ⟨q, hq, hqle⟩ : ∃ q : ℚ, 0 < q ∧ ((q : ℚ) : WithTop ℚ) ≤ v ζ := by
      cases h : v ζ with
      | top => exact ⟨1, one_pos, le_top⟩
      | coe y => rw [h] at hvζ; exact ⟨y, by exact_mod_cast hvζ, le_rfl⟩
    exact ⟨0 + q, by linarith, NuGe.smul Q hqle hsm hs'⟩

end ReciprocityTheory.ChartRestriction.G.DVR
