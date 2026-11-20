import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinatesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ`. Establish `hcont` using `GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ`. Establish `hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2`. Establish `: (2 * n + 1 : ℝ) ≤ M` using `by exact_mod_cast hnM`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hint` using `(GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C`. Use `hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Use `hC b` as an intermediate fact. Simplify `this` using `[neg_div]`.
-/
theorem core_integrable {W : Type} [Fintype W] {n M : ℕ} (hnM : 2 * n < M) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (hJ : ∀ w, (J w).IsHermitian) (hJd : ∀ w, (J w).det ≠ 0) {N : ℕ}
    (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (W → hermC n)) (hν : ν.IsAddHaarMeasure) :
    Integrable (coreC J μ (fun X => f (e X))) ν := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ
  have hcont := GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ
  have hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2 := by
    have : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hint := (GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have := hC b
  simpa [neg_div] using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP`. Take `⟨ρ, e, hρ, he, heρ, -, -⟩` from `GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1`. Take `⟨a, ha, hinf, -, -, -⟩` from `GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ`. Take `⟨τ, Θ, hΘ⟩` from `GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ`. Take `⟨Ψ, hΨ, hΨν⟩` from `GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n`.

Take `⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩` from `GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M`. Take `⟨N, e₀, he₀, he₀s, f, hP⟩` from `hP`. Take `⟨hνH, hνI⟩` from `hΨν ν hν`. Take `⟨hμH, hμI⟩` from `hΦμ μ hμ`. Set `Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ` to `fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)`.

Establish `hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0` using `fun w => by`. Simplify using `using (map_ne_zero (ρ w)).2 ha`. Establish `hJc : ∀ w, (Jc w).IsHermitian` using `fun w => by`. Use extensionality with `i j`. Establish `h1` using `hJ.1 i j`.

Establish `h2` using `hcm.2.2.2 (τ w) (J j i)`. Simplify using `only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]`. Rewrite `h2` using `[h1]`. Rewrite using `[h2]`. Both sides reduce to the same expression.

Establish `hJd : ∀ w, (Jc w).det ≠ 0` using `fun w => by`. Simplify using `only [Jc, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ (hρa w)) ?_` and prove the remaining obligations. Establish `: (J.map (τ w)).det = τ w J.det`. Simplify using `using (RingHom.map_det (τ w) J).symm`.

Rewrite using `[this]`. Conclude with `(map_ne_zero (τ w)).2 hJ.2`. Set `e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)` to `Φ.symm.trans e₀`. Establish `he₂ : Continuous e₂` using `he₀.comp hΦs`. Establish `he₂s : Continuous e₂.symm` using `hΦc.comp he₀s`.

Establish `hcore` using `core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH`. Use `hνI _ hcore` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Use `show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b`. Rewrite using `[coreC, ← hμI]`.

Unfold `starLoc`. Use `integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)` and prove the remaining obligations. Use `show f (e₂ (Φ X)) * _ = P X * _`. Establish `hph` using `GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X`. Rewrite using `[hph, hP X]`.

Establish `h1 : e₂ (Φ X) = e₀ X` using `by simp [e₂]`. Establish `h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w` using `funext (hΨ b)`. Rewrite using `[h1, h2, hΦ X]`.
-/
theorem integrable_starLoc_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ
  obtain ⟨Ψ, hΨ, hΨν⟩ := GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩ := GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M
  obtain ⟨N, e₀, he₀, he₀s, f, hP⟩ := hP
  obtain ⟨hνH, hνI⟩ := hΨν ν hν
  obtain ⟨hμH, hμI⟩ := hΦμ μ hμ
  let Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ := fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)
  have hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0 := fun w => by
    simpa using (map_ne_zero (ρ w)).2 ha
  have hJc : ∀ w, (Jc w).IsHermitian := fun w => by
    ext i j
    have h1 := hJ.1 i j
    have h2 := hcm.2.2.2 (τ w) (J j i)
    simp only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [h1] at h2
    rw [h2]
    rfl
  have hJd : ∀ w, (Jc w).det ≠ 0 := fun w => by
    simp only [Jc, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (hρa w)) ?_
    have : (J.map (τ w)).det = τ w J.det := by
      simpa using (RingHom.map_det (τ w) J).symm
    rw [this]
    exact (map_ne_zero (τ w)).2 hJ.2
  let e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ) := Φ.symm.trans e₀
  have he₂ : Continuous e₂ := he₀.comp hΦs
  have he₂s : Continuous e₂.symm := hΦc.comp he₀s
  have hcore := core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH
  have := hνI _ hcore
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b
  rw [coreC, ← hμI]
  unfold starLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show f (e₂ (Φ X)) * _ = P X * _
  have hph := GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X
  rw [hph, hP X]
  have h1 : e₂ (Φ X) = e₀ X := by simp [e₂]
  have h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w := funext (hΨ b)
  rw [h1, h2, hΦ X]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
