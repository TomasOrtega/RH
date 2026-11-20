import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open MvPolynomial Formalism.L2.Ker GlobalTheory.JetDeg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

private def frW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun k => if k.1 = τ then 1 else 0) fun _ => 0

omit [Fintype ι] in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem subD_hom_fr (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (frW a b τ) (subD K ι a b P) d := by
  have key : ∀ v : ι × Fin a × Fin a,
      IsWeightedHomogeneous (frW a b τ) (subD K ι a b (X v)) (AddMonoidHom.id ℕ (posW a τ v)) := by
    intro v
    simp only [subD, MvPolynomial.aeval_X, AddMonoidHom.id_apply]
    split_ifs with h
    · apply IsWeightedHomogeneous.sum
      intro β _
      have hm := (isWeightedHomogeneous_X K (frW a b τ) (Sum.inl (v.1, β, ⟨v.2.2, h⟩))).mul
        (isWeightedHomogeneous_X K (frW a b τ) (Sum.inr (v.1, β, v.2.1)))
      convert hm using 1
      simp [frW, posW]
    · exact isWeightedHomogeneous_zero K _ _
  simpa using algHom_hom (posW a τ) (frW a b τ) (AddMonoidHom.id ℕ) (subD K ι a b) key hP

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem weight_fr (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (posW b τ) (μ.comapDomain Sum.inl Sum.inl_injective.injOn) = Finsupp.weight (frW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [frW, posW]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem weight_der (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    ((μ.comapDomain Sum.inr Sum.inr_injective.injOn).sum fun v e => if v.1 = τ then e else 0) =
      Finsupp.weight (derW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [derW]

omit [DecidableEq ι] in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem jetLin_eq (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, coeff μ Q • (monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b) := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : (monomial μ (coeff μ Q) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      coeff μ Q • (basisMonomials _ K) μ := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem jetMap_congr_deg (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hV : JetInVV K lam lam' n) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) : jetMap J n P = jetMap J' n P := by
  set Q := subD K ι a b (GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) with hQ
  have hJ : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = jetLin J₀ Q := fun J₀ => rfl
  have hfr : ∀ τ, IsWeightedHomogeneous (frW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom_fr τ (sharp_hom n τ (VV_hom lam τ hP))
  have hder : ∀ τ, IsWeightedHomogeneous (derW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom τ (sharp_hom n τ (VV_hom lam τ hP))
  have hdeg : ∀ (J₀ : (DVar ι a b →₀ ℕ) → K) τ,
      IsWeightedHomogeneous (posW b τ) (jetLin J₀ Q) (∑ i, (lam τ).natW i + n τ * a) := by
    intro J₀ τ
    rw [jetLin_eq]
    apply IsWeightedHomogeneous.sum
    intro μ hμ
    rw [smul_monomial]
    apply isWeightedHomogeneous_monomial
    rw [weight_fr]
    exact hfr τ (mem_support_iff.mp hμ)
  by_cases hall : ∀ τ, ∑ i, (lam τ).natW i + n τ * a = ∑ i, (lam' τ).natW i
  · rw [hJ, hJ, jetLin_eq, jetLin_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hJJ : J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
        J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn) := by
      apply h
      intro τ
      rw [weight_der, ← hall τ]
      exact hder τ (mem_support_iff.mp hμ)
    rw [hJJ]
  · push_neg at hall
    obtain ⟨τ, hτ⟩ := hall
    have hz : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = 0 := by
      intro J₀
      by_contra hne
      have h1 := VV_hom lam' τ (hV J₀ P hP)
      have h2 := hdeg J₀ τ
      rw [← hJ] at h2
      exact hτ (IsWeightedHomogeneous.inj_right hne h2 h1)
    rw [hz J, hz J']

end SlopeTestRemainingChoices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.WildA.jetDeg :
    ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV K lam lam' n → ∀ J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K,
      (∀ m : Formalism.L2.Ker.DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m) →
      Formalism.L2.Ker.jetOp lam lam' J n = Formalism.L2.Ker.jetOp lam lam' J' n := by
  intro K _ _ ι _ _ a b lam lam' n hV J J' h
  refine LinearMap.ext fun P => ?_
  show Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J n P.1) = Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J' n P.1)
  rw [jetMap_congr_deg lam lam' n hV J J' h P.1 P.2]
