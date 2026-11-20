import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemmaStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelPurity

/- English proof (translation)
Introduce `hB E _ _ _ a ha π hinf hint`. Take `⟨μ, h1, h2⟩` from `GlobalTheory.T.exists_right_haar_measure E a`. Use `haveI := h1`. Use `haveI := h2`. Take `⟨s, hs⟩` from `GlobalTheory.T.aux_statement_20 E a ha π hinf`.

Take `⟨B, hH⟩` from `GlobalTheory.T.exists_invariant_hermitian_form hB E a μ (π.twist (GlobalTheory.CuspRep.Model.absC E s)) hs`. Establish `hm : ∀ τ, π.HasInfChar τ ((CG.mk π).infChar τ)` using `fun τ => by`. Take `⟨m, h⟩` from `hinf τ`. Establish `e : (CG.mk π).infChar τ = m` using `CG.HasInfChar.infChar_eq (π := CG.mk π) h`. Rewrite using `[e]`.

Conclude with `h`. Establish `hreal : ∀ τ, ∀ z ∈ (CG.mk π).infChar τ, (starRingEnd ℂ) z = z` using `fun τ z hz => by`. Take `⟨n, rfl⟩` from `hint τ z hz`. Establish `c2 : (starRingEnd ℂ) (2 : ℂ) = 2` using `map_ofNat _ 2`. Simplify using `[c2]`.

Establish `key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) = ((CG.mk π).infChar τ).map fun z => (-(starRingEnd ℂ) s - s) - z` using `fun τ => by`. Establish `t1` using `(hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)`. Establish `t2` using `(hm (NumberField.ComplexEmbedding.conjugate τ)).twist (GlobalTheory.CuspRep.Model.absC E s)`. Rewrite `t1`, `t2` using `[GlobalTheory.CuspRep.Model.expo_absC]`. Establish `e` using `GlobalTheory.T.infinitesimal_character_conjugate E a _ B hH τ _ _ t1 t2`.

Establish `e2` using `congrArg (Multiset.map fun z => z - s) e`. Simplify using `only [Multiset.map_map, Function.comp_def, add_sub_cancel_right, Multiset.map_id'] at e2`. Rewrite using `[e2]`. Use `Multiset.map_congr rfl fun z hz => ?_` and prove the remaining obligations. Rewrite using `[map_add, hreal τ z hz]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ₀ := by`. Apply `Multiset.card_pos_iff_exists_mem.1` to reduce the goal to its premises. Rewrite using `[CG.card_infChar]`.

Conclude with `ha`. Establish `hz' : (-(starRingEnd ℂ) s - s) - z ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ₀)`. Rewrite using `[key]`. Conclude with `Multiset.mem_map_of_mem _ hz`. Take `⟨n, hn⟩` from `hint _ z hz`.

Take `⟨n', hn'⟩` from `hint _ _ hz'`. Use `⟨n + n' + (a : ℤ) - 1, fun τ => ?_⟩` and prove the remaining obligations. Establish `e : (-(starRingEnd ℂ) s - s) = (((n + n' + (a : ℤ) - 1 : ℤ)) : ℂ)`. Use `push_cast`. Take the linear combination `hn' + hn`.

Establish `e2 : (starRingEnd ℂ).comp τ = NumberField.ComplexEmbedding.conjugate τ` using `RingHom.ext fun _ => rfl`. Rewrite using `[e2, key, e]`.
-/
theorem purity : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) → ∃ w₀ : ℤ, ∀ τ : E →+* ℂ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z := by
  intro hB E _ _ _ a ha π hinf hint
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_right_haar_measure E a
  haveI := h1
  haveI := h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.aux_statement_20 E a ha π hinf
  obtain ⟨B, hH⟩ := GlobalTheory.T.exists_invariant_hermitian_form hB E a μ (π.twist (GlobalTheory.CuspRep.Model.absC E s)) hs
  have hm : ∀ τ, π.HasInfChar τ ((CG.mk π).infChar τ) := fun τ => by
    obtain ⟨m, h⟩ := hinf τ
    have e : (CG.mk π).infChar τ = m := CG.HasInfChar.infChar_eq (π := CG.mk π) h
    rw [e]
    exact h
  have hreal : ∀ τ, ∀ z ∈ (CG.mk π).infChar τ, (starRingEnd ℂ) z = z := fun τ z hz => by
    obtain ⟨n, rfl⟩ := hint τ z hz
    have c2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    simp [c2]
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => (-(starRingEnd ℂ) s - s) - z := fun τ => by
    have t1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    have t2 := (hm (NumberField.ComplexEmbedding.conjugate τ)).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at t1 t2
    have e := GlobalTheory.T.infinitesimal_character_conjugate E a _ B hH τ _ _ t1 t2
    have e2 := congrArg (Multiset.map fun z => z - s) e
    simp only [Multiset.map_map, Function.comp_def, add_sub_cancel_right, Multiset.map_id'] at e2
    rw [e2]
    refine Multiset.map_congr rfl fun z hz => ?_
    rw [map_add, hreal τ z hz]
    ring
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ₀ := by
    apply Multiset.card_pos_iff_exists_mem.1
    rw [CG.card_infChar]
    exact ha
  have hz' : (-(starRingEnd ℂ) s - s) - z ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ₀) := by
    rw [key]
    exact Multiset.mem_map_of_mem _ hz
  obtain ⟨n, hn⟩ := hint _ z hz
  obtain ⟨n', hn'⟩ := hint _ _ hz'
  refine ⟨n + n' + (a : ℤ) - 1, fun τ => ?_⟩
  have e : (-(starRingEnd ℂ) s - s) = (((n + n' + (a : ℤ) - 1 : ℤ)) : ℂ) := by
    push_cast
    linear_combination hn' + hn
  have e2 : (starRingEnd ℂ).comp τ = NumberField.ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl
  rw [e2, key, e]

end GlobalTheory.CompanionTheory.ClozelPurity
