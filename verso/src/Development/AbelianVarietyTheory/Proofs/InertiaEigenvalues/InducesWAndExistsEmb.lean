import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
