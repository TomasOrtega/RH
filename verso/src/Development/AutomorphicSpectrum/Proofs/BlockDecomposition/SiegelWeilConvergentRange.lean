import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ`. Take `⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩` from `GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1`. Take `⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩` from `GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1`. Take `⟨k, P, Q, hP, hQ, hsum⟩` from `id hΦ`. Establish `hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X))` using `fun i => GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl`.

Establish `hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b = (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b))`. Introduce `i b`. Set `A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ` to `fun x => P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * gramR (Ainf F) σ J x)))`. Set `B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ` to `fun y => Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J y)))`. Set `G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ` to `fun z => A z.1 * B z.2`.

Establish `e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b = ∫ X, G (projInf X, projFin X) ∂dx`. Unfold `starN`. Use `integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)` and prove the remaining obligations. Use `show _ * _ = G _`. Rewrite using `[GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]`.

Simplify using `only [G, A, B]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `hme.integral_map (μ := dx) G`. Establish `e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂` using `integral_prod_mul A B`. Rewrite using `[e1]`.

Use `e2.symm.trans ?_` and prove the remaining obligations. Rewrite using `[hmap, integral_smul_measure, e3, Complex.real_smul]`. Both sides reduce to the same expression. Establish `hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db`. Introduce `i`.

Establish `hA` using `GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)`. Establish `hB` using `GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)`. Establish `hAB` using `hA.mul_prod hB`. Establish `hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n => starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2) (db.map (fun b => (hermInf σ b, hermFin σ b)))`. Rewrite using `[hmap']`.

Conclude with `hAB.smul_measure hc'`. Use `(hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Conclude with `(hfac i b).symm`. Establish `hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b`.

Use function extensionality and compare the values at `b`. Unfold `starN`. Rewrite using `[← integral_finset_sum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)` and prove the remaining obligations. Use `show Φ X * _ = _`.

Rewrite using `[hsum, Finset.sum_mul]`. Rewrite using `[hdec]`. Conclude with `integrable_finset_sum _ fun i _ => hpure i`.
-/
theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finset_sum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finset_sum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
