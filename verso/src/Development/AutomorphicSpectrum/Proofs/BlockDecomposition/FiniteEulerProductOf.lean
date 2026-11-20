import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprodStatement

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

namespace GlobalTheory.CompanionTheory.EulerAsm

/- English proof (translation)
Take `⟨Q, hQm, hQo⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hQ0 : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`. Use `⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩` and prove the remaining obligations. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Conclude with `(hQo.over).symm`.
-/
theorem exists_above {E : Type} [Field E] [NumberField E] [IsCMField E] (v : PlF E) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact (hQo.over).symm

/- English proof (translation)
Introduce `hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2`. Take `⟨hr, hth, hK, hKm⟩` from `hR hC E a b`. Establish `hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E` using `E) a b v).comap (pv a b v) := by`. Use extensionality with `x`. Rewrite using `[Subgroup.mem_iInf]`.

Conclude with `hKm x`. Take `⟨H1, H2, H3, H4, H5⟩` from `hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2`. Establish `main` using `GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5`. Rewrite using `[hKeq, main, hI E S hS]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Establish `key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v → twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) = twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)`. Introduce and unpack `w hw rfl`. Conclude with `hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw`. Take `⟨w0, hw0⟩` from `exists_above v`. Establish `h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v`.

Take `⟨u, ⟨huS, hu⟩, -⟩` from `hS w0`. Conclude with `⟨u, huS, hu.trans hw0⟩`. Simplify using `only [secPl, dif_pos h, Option.elim]`. Conclude with `key _ h.choose_spec.1 h.choose_spec.2`.
-/
theorem eulerFinOf' : EulerFinOf' := by
  intro hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  obtain ⟨hr, hth, hK, hKm⟩ := hR hC E a b
  have hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E := E) a b v).comap (pv a b v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact hKm x
  obtain ⟨H1, H2, H3, H4, H5⟩ := hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  have main := GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK
    (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5
  rw [hKeq, main, hI E S hS]
  refine finprod_congr fun v => ?_
  have key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v →
      twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) =
        twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w) := by
    rintro w hw rfl
    exact hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw
  obtain ⟨w0, hw0⟩ := exists_above v
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v := by
    obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w0
    exact ⟨u, huS, hu.trans hw0⟩
  simp only [secPl, dif_pos h, Option.elim]
  exact key _ h.choose_spec.1 h.choose_spec.2

end GlobalTheory.CompanionTheory.EulerAsm
