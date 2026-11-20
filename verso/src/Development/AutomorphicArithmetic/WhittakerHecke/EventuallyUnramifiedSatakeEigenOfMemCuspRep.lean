import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ D P f hf h`. Establish `hδ : D.δ ≠ 0` using `(by`. Introduce `e`. Use `D.neg (algebraMap ℚ ℝ)` as an intermediate fact. Rewrite `this` using `[e, map_zero]`.

Conclude with `lt_irrefl _ this)`. Establish `hF : ∀ᶠ w : H.P E in cofinite, H.Fix w f.1` using `(H.aeK E).2.2 f.1 (by`. Establish `hO : {k : GL (Fin 2) (Af E) | ∀ g, f.1 (g * finGL E 2 k) = f.1 g} = {k | finRep E 2 k f = f}` using `Set.ext fun k => ⟨fun hk => Subtype.ext (funext hk), fun hk g => congrFun (congrArg Subtype.val hk) g⟩`. Rewrite using `[hO]`. Conclude with `(P.cusp f hf).1.level)`.

Establish `hall : ∀ᶠ w : H.P E in cofinite, Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h))`. Establish `hint : ∀ᶠ w : H.P E in cofinite, H.cp w (rt D.θ) ∈ w.adicCompletionIntegers E` using `(rt D.θ).2.2`. Use `filter_upwards [hint, hF, (H.aeK E).1 h, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat P] with w h1 h2 h3 ⟨B, hB⟩`. Establish `hE : EigAt w B f.1` using `UpperTheory.V.Af.StrongMultiplicityOne.eigOfSat E 2 P w B ((CG.hasSat_mk P w B).1 hB) f hf h2`. Establish `ht` using `H.fixTr E w f.1 h h3`.

Conclude with `⟨h1, ht.1 h2, B, hB, ht.2 B hE⟩`. Establish `hfin` using `(Set.Finite.image (fun w : H.P E => w.under (𝓞 ℚ)) (show Set.Finite _ from hall)).compl_mem_cofinite`. Use `filter_upwards [H.gdAe ℚ D.δ hδ, hfin] with v hv hn`. Use `⟨hv, fun w hw => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hn ⟨w, hc, hw⟩`.
-/
theorem UpperTheory.eventually_unramified_satake_eigen_of_mem_cuspRep :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∀ᶠ v : H.P ℚ in cofinite, H.Gd D.δ v ∧ ∀ w : H.P E, w.under (𝓞 ℚ) = v → Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
  intro E _ _ _ D P f hf h
  have hδ : D.δ ≠ 0 := (by
    intro e
    have := D.neg (algebraMap ℚ ℝ)
    rw [e, map_zero] at this
    exact lt_irrefl _ this)
  have hF : ∀ᶠ w : H.P E in cofinite, H.Fix w f.1 :=
    (H.aeK E).2.2 f.1 (by
      have hO : {k : GL (Fin 2) (Af E) | ∀ g, f.1 (g * finGL E 2 k) = f.1 g} = {k | finRep E 2 k f = f} :=
        Set.ext fun k => ⟨fun hk => Subtype.ext (funext hk), fun hk g => congrFun (congrArg Subtype.val hk) g⟩
      rw [hO]
      exact (P.cusp f hf).1.level)
  have hall : ∀ᶠ w : H.P E in cofinite, Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
    have hint : ∀ᶠ w : H.P E in cofinite, H.cp w (rt D.θ) ∈ w.adicCompletionIntegers E := (rt D.θ).2.2
    filter_upwards [hint, hF, (H.aeK E).1 h, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat P] with w h1 h2 h3 ⟨B, hB⟩
    have hE : EigAt w B f.1 := UpperTheory.V.Af.StrongMultiplicityOne.eigOfSat E 2 P w B ((CG.hasSat_mk P w B).1 hB) f hf h2
    have ht := H.fixTr E w f.1 h h3
    exact ⟨h1, ht.1 h2, B, hB, ht.2 B hE⟩
  have hfin := (Set.Finite.image (fun w : H.P E => w.under (𝓞 ℚ)) (show Set.Finite _ from hall)).compl_mem_cofinite
  filter_upwards [H.gdAe ℚ D.δ hδ, hfin] with v hv hn
  refine ⟨hv, fun w hw => ?_⟩
  by_contra hc
  exact hn ⟨w, hc, hw⟩
