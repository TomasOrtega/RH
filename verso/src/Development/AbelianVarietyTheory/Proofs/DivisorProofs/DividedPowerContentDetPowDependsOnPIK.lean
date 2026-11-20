import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.DetPowContent

open GlobalTheory.DetPowShape

noncomputable def intCoeff (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) : ℤ :=
  (detZ i ^ k).coeff α * α.prod fun _ n => ((n.factorial : ℕ) : ℤ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cast_intCoeff (C : Type) [Field C] (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    ((intCoeff i k α : ℤ) : C) = (detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α := by
  rw [intCoeff, detPow_eq_map, MvPolynomial.coeff_map, Int.cast_mul, GlobalTheory.FGDepth.mfact]
  congr 1 <;> simp [Finsupp.prod]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_support_iff' (C : Type) [Field C] [CharZero C] (i k : ℕ) (α) :
    α ∈ (detPow C i k).support ↔ α ∈ (detZ i ^ k).support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, detPow_eq_map,
    MvPolynomial.coeff_map]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem intCoeff_ne_zero (i k : ℕ) (α) (h : α ∈ (detZ i ^ k).support) : intCoeff i k α ≠ 0 := by
  rw [intCoeff]
  refine mul_ne_zero (MvPolynomial.mem_support_iff.1 h) ?_
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact_mod_cast Nat.factorial_ne_zero _

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem v_intCast (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (m : C) = (((padicValNat p m.natAbs : ℕ) : ℝ) : WithTop ℝ) := by
  have h := GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv m.natAbs (Int.natAbs_ne_zero.2 hm)
  rcases Int.natAbs_eq m with h1 | h1
  · conv_lhs => rw [h1]
    simpa using h
  · conv_lhs => rw [h1, Int.cast_neg, v.map_neg]
    simpa using h

end GlobalTheory.DetPowContent

namespace GlobalTheory

open GlobalTheory.DetPowShape GlobalTheory.DetPowContent in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem detPow_content_const : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C]
    [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 →
      content v (detPow C i k) = (κ : EReal) := by
  intro p hp i k
  set S := (detZ i ^ k).support with hS
  have hne : S.Nonempty := by
    refine ⟨∑ a : Fin i, Finsupp.single ⟨a, a⟩ k, ?_⟩
    rw [← mem_support_iff' ℚ]
    rw [MvPolynomial.mem_support_iff, (detPow_shape ℚ i k).2.2.1]
    exact one_ne_zero
  let f : ((Σ _ : Fin i, Fin i) →₀ ℕ) → ℕ := fun α => padicValNat p (intCoeff i k α).natAbs
  obtain ⟨α0, hα0, hmin⟩ := S.exists_min_image f hne
  refine ⟨(f α0 : ℝ), fun C _ _ v hv => ?_⟩
  have hval : ∀ α ∈ S, GlobalTheory.FGDepth.toE (v ((detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α)) =
      ((f α : ℝ) : EReal) := by
    intro α hα
    rw [← cast_intCoeff, v_intCast C v p hp hv _ (intCoeff_ne_zero i k α hα)]
    rfl
  unfold GlobalTheory.FGDepth.content
  apply le_antisymm
  · refine iInf₂_le_of_le α0 ((mem_support_iff' C i k α0).2 hα0) ?_
    rw [hval α0 hα0]
  · refine le_iInf₂ fun α hα => ?_
    have hα' := (mem_support_iff' C i k α).1 hα
    rw [hval α hα']
    exact_mod_cast hmin α hα'

end GlobalTheory
