import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend

namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift

open MvPolynomial

section Clear

variable {A : Type} [CommRing A] [IsDomain A] {σ : Type}

/- English proof (translation)
Proceed by induction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem clear_denoms (P : MvPolynomial σ (FractionRing A)) :
    ∃ (b : A) (p : MvPolynomial σ A), b ≠ 0 ∧
      MvPolynomial.map (algebraMap A (FractionRing A)) p =
        MvPolynomial.C (algebraMap A (FractionRing A) b) * P := by
  induction P using MvPolynomial.induction_on
  next a =>
    obtain ⟨z, hz⟩ := IsLocalization.surj (nonZeroDivisors A) a
    refine ⟨z.2, C z.1, nonZeroDivisors.coe_ne_zero z.2, ?_⟩
    rw [MvPolynomial.map_C, ← hz, MvPolynomial.C_mul, mul_comm]
  next p q hp hq =>
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := hp
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := hq
    refine ⟨b₁ * b₂, C b₂ * p₁ + C b₁ * p₂, mul_ne_zero hb₁ hb₂, ?_⟩
    simp only [_root_.map_add, _root_.map_mul, MvPolynomial.map_C, h₁, h₂]
    ring
  next p n hp =>
    obtain ⟨b, q, hb, h⟩ := hp
    exact ⟨b, q * X n, hb, by rw [_root_.map_mul, MvPolynomial.map_X, h, mul_assoc]⟩

noncomputable def toFracY (A : Type) [CommRing A] [IsDomain A] (σ : Type) :
    MvPolynomial σ A →+* FractionRing (MvPolynomial σ (FractionRing A)) :=
  (algebraMap (MvPolynomial σ (FractionRing A)) _).comp (MvPolynomial.map (algebraMap A (FractionRing A)))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem toFracY_injective : Function.Injective (toFracY A σ) := by
  intro x y h
  have h' : algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) x) =
      algebraMap (MvPolynomial σ (FractionRing A)) (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) y) := h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
    (IsFractionRing.injective _ _ h')

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem isFractionRing_toFracY :
    letI := (toFracY A σ).toAlgebra
    IsFractionRing (MvPolynomial σ A) (FractionRing (MvPolynomial σ (FractionRing A))) := by
  letI := (toFracY A σ).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine IsUnit.mk0 _ (fun h => nonZeroDivisors.coe_ne_zero y (toFracY_injective ?_))
    rw [_root_.map_zero]
    exact h
  · intro z
    obtain ⟨uv, huv⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial σ (FractionRing A))) z
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := clear_denoms (uv.1 : MvPolynomial σ (FractionRing A))
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := clear_denoms (uv.2 : MvPolynomial σ (FractionRing A))
    have hv : (uv.2 : MvPolynomial σ (FractionRing A)) ≠ 0 := nonZeroDivisors.coe_ne_zero uv.2
    have hβ₂ : algebraMap A (FractionRing A) b₂ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb₂)
    have hp₂ne : p₂ ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at h₂
      exact mul_ne_zero (fun h => hβ₂ (MvPolynomial.C_eq_zero.mp h)) hv h₂.symm
    have hp₂ : C b₁ * p₂ ∈ nonZeroDivisors (MvPolynomial σ A) :=
      mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (fun h => hb₁ (MvPolynomial.C_eq_zero.mp h)) hp₂ne)
    refine ⟨⟨C b₂ * p₁, ⟨C b₁ * p₂, hp₂⟩⟩, ?_⟩
    show z * toFracY A σ (C b₁ * p₂) = toFracY A σ (C b₂ * p₁)
    simp only [toFracY, RingHom.coe_comp, Function.comp_apply, _root_.map_mul,
      MvPolynomial.map_C, h₁, h₂]
    linear_combination (algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₁)) *
      algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₂))) * huv
  · intro x y h
    exact ⟨1, by rw [toFracY_injective h]⟩

end Clear

section Disjoint

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem liftY_algebraMap (x : MvPolynomial σ L) :
    ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)
        (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) x) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.map (algebraMap L E) x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem linearIndependent_algebraMap_C_fractionRing
    [Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))]
    (hmap : algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY)
    {ι : Type} [Fintype ι] (e : ι → E) (he : LinearIndependent L e) :
    LinearIndependent (FractionRing (MvPolynomial σ L))
      (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (e i))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j)) = 0 := by
    simpa only [Algebra.smul_def] using hg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial σ L)) g
  have hb' : ∀ j, ∃ c : MvPolynomial σ L,
      algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) c =
        algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) * g j := by
    intro j
    obtain ⟨c, hc⟩ := RingHom.mem_rangeS.mp (hb j)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  choose a ha using hb'
  have key : ∀ j, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
      (MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY
          (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L)) *
        (algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
          algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j))) := by
    intro j
    rw [_root_.map_mul, ← liftY_algebraMap, ha j, _root_.map_mul, hmap, mul_assoc]
  have hsum : ∑ j, MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j) = 0 := by
    apply IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
    rw [_root_.map_zero, _root_.map_sum, Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum,
      hg', mul_zero]
  have hcoeff : ∀ m j, MvPolynomial.coeff m (a j) = 0 := by
    intro m
    have hsum' : ∑ j, MvPolynomial.C (e j) * MvPolynomial.map (algebraMap L E) (a j) = 0 := by
      simpa only [mul_comm] using hsum
    have h0 := congrArg (MvPolynomial.coeff m) hsum'
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      MvPolynomial.coeff_zero] at h0
    have h1 : ∑ j, MvPolynomial.coeff m (a j) • e j = 0 := by
      simpa only [Algebra.smul_def, mul_comm] using h0
    exact Fintype.linearIndependent_iff.mp he (fun j => MvPolynomial.coeff m (a j)) h1
  have hai : a i = 0 := by
    ext m
    rw [hcoeff m i, MvPolynomial.coeff_zero]
  have h2 := ha i
  rw [hai, _root_.map_zero] at h2
  have hβ : algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  exact (mul_eq_zero.mp h2.symm).resolve_left hβ

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finiteDimensional_of_liftY
    (hfin : letI := (VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
      FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))) :
    FiniteDimensional L E := by
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    (ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
  haveI : FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    hfin
  have hbound : ∀ s : Finset E, LinearIndependent L (fun x : s => (x : E)) →
      s.card ≤ Module.finrank (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := by
    intro s hs
    have hli := linearIndependent_algebraMap_C_fractionRing (σ := σ) rfl (fun x : s => (x : E)) hs
    simpa using hli.fintype_card_le_finrank
  have hr := rank_le hbound
  exact Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0))

end Disjoint

end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
