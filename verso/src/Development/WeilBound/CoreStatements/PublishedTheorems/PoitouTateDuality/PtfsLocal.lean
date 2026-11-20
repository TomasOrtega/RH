import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

/- English proof (translation)
Establish `key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[ (v : HeightOneSpectrum (𝓞 K)).adicCompletion K] AlgebraicClosure ((v : HeightOneSpectrum …` using `K) (Av v)), Continuous ev ∧ Continuous ev.symm ∧ ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) := fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)`. Use `choose ι ev hc hc' hι using key`. Use `⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ => ?_⟩` and prove the remaining obligations. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `y`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `(ι v).injective` to reduce the goal to its premises. Establish `h1` using `GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K))) (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y`. Establish `h2` using `he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y`. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ι v ((e (toGS (AlgebraicClosure ℚ) _ ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) : AlgebraicClosure ℚ) = _`. Rewrite using `[h2, hι]`.
-/
theorem localCmp' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
