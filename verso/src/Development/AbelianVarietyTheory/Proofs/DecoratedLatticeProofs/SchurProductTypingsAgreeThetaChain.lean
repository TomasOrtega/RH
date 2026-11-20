import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.IPDictPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isInnerProduct_of_isMet' (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_tprod_ne {k : ℕ} (w : SmT (R.MY k)) (hw : w ≠ 0) : ∃ v : (R.MY k).Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra h
  push_neg at h
  have hid : (LinearMap.id : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k)) = 0 :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  exact hw (by simpa using LinearMap.congr_fun hid w)

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_vec (hC : R.IsChain) (t : T) {k : ℕ} (hk : k < D.R.m) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) :
    ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0 := by
  have hw : ∃ w : SmT (R.MY k), w ≠ 0 := by
    by_cases hkk : k + 1 < D.R.m
    · by_contra h
      push_neg at h
      exact (hC.ItY t k hkk).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItY k φ x))
    · obtain rfl : k = D.R.m - 1 := by omega
      by_contra h
      push_neg at h
      exact (hC.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItX φ x))
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv⟩ := exists_tprod_ne R w hw
  refine ⟨v, fun h0 => ?_⟩
  have hp := hm.posD (PiTensorProduct.tprod ℂ v) hv
  rw [hm.pure v v] at hp
  change 0 < (∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ).re at hp
  rw [h0] at hp
  simp at hp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ipDict (R : RealDat D A Ks) (F : Face D A) (hG : Given R F) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := exists_vec R hG.core.chain t hk hm
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet' R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet' R t k hm x y⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := fun R F hG => ipDict R F hG

end GlobalTheory.ChainTw.IPDictPf

end
