import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.PairingEigenspaceOrthogonal

/- English proof (translation)
Introduce `E _ _ _ c hc R _ K _ _ H _ _ I φ ρ Fil B hL σ σ' hne x hx y hy`. Establish `hadj` using `hL.2.2.2.2.2.2.2.2`. Establish `hne' : σ ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ'`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[h]`. Use extensionality with `z`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, IsCMField.complexConj_apply_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : orderC c, σ a ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hne' (GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc hall)`. Set `b : orderC c` to `⟨IsCMField.complexConj E (a : E), GlobalTheory.LatModel.HalfFormUnit.conj_mem_orderC a.2⟩`. Establish `hK : ∀ u v : K ⊗[R] H, B.baseChange K ((ρ a).baseChange K u) v = B.baseChange K u ((ρ b).baseChange K v)`. Introduce `u v`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add u1 u2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]`. Consider the case `tmul r m`. Proceed by induction on `v using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add v1 v2 h1 h2 => simp only [map_add, h1, h2]`. Consider the case `tmul r' m'`. Simplify using `only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]`. Rewrite using `[hadj a b rfl m m']`.

Establish `h1` using `hK x y`. Rewrite `h1` using `[GlobalTheory.LowerOps.act_of_mem_eigK hx a, GlobalTheory.LowerOps.act_of_mem_eigK hy b]`. Simplify using `only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h1`. Establish `hb : σ' (b : E) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a` using `rfl`. Rewrite `h1` using `[hb]`.

Establish `h2 : (σ a - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a) * B.baseChange K x y = 0` using `by rw [sub_mul, h1, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)`.
-/
theorem pairing_eig_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (H : Type) [AddCommGroup H] [Module R H]
    (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H) (B : LinearMap.BilinForm R H),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
    ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ, ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc R _ K _ _ H _ _ I φ ρ Fil B hL σ σ' hne x hx y hy
  have hadj := hL.2.2.2.2.2.2.2.2

  have hne' : σ ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' := by
    intro h; apply hne; rw [h]; ext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, IsCMField.complexConj_apply_apply]
  obtain ⟨a, ha⟩ : ∃ a : orderC c, σ a ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := by
    by_contra hall; push_neg at hall
    exact hne' (GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc hall)
  let b : orderC c := ⟨IsCMField.complexConj E (a : E), GlobalTheory.LatModel.HalfFormUnit.conj_mem_orderC a.2⟩
  have hK : ∀ u v : K ⊗[R] H, B.baseChange K ((ρ a).baseChange K u) v = B.baseChange K u ((ρ b).baseChange K v) := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u1 u2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]
    | tmul r m =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v1 v2 h1 h2 => simp only [map_add, h1, h2]
      | tmul r' m' =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        rw [hadj a b rfl m m']
  have h1 := hK x y
  rw [GlobalTheory.LowerOps.act_of_mem_eigK hx a, GlobalTheory.LowerOps.act_of_mem_eigK hy b] at h1
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have hb : σ' (b : E) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := rfl
  rw [hb] at h1
  have h2 : (σ a - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a) * B.baseChange K x y = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

end GlobalTheory.Div.PairingEigenspaceOrthogonal
