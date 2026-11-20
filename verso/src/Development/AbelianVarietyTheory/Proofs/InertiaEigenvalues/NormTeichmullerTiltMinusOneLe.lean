import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Introduce `l _ K bk e he`. Establish `hker` using `(GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk).2.2`. Establish `hθmu : Per.θ l (mu e) = 0`. Simplify using `only [mu, map_sub, map_one]`. Simplify using `[he.1]`.

Use `⟨hker _ hθmu, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `set δ := (frobeniusEquiv (Per.Fl 2) 2).symm e with hδ`. Establish `hδ2 : δ ^ 2 = e`. Rewrite using `[hδ]`.

Conclude with `frobenius_apply_frobeniusEquiv_symm (Per.Fl 2) 2 e`. Establish `hu : δ.untilt ^ 2 = 1`. Rewrite using `[← map_pow, hδ2, he.1]`. Establish `hu' : δ.untilt = -1`. Establish `h1 : (δ.untilt - 1) * (δ.untilt + 1) = 0` using `by linear_combination hu`.

Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) he.2`. Take the linear combination `h`. Establish `hθa : Per.θ 2 (Per.tm δ + 1) = 0`. Simplify using `[hu']`.

Establish `ha` using `hker _ hθa`. Establish `hfac : mu e = (Per.tm δ + 1) * ((Per.tm δ + 1) - 2)`. Simplify using `only [mu]`. Rewrite using `[← hδ2]`. Use `show WittVector.teichmuller 2 (δ ^ 2) - 1 = _`.

Rewrite using `[map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖bk.iA ((Per.tm δ + 1) - 2)‖ ≤ (2 : ℝ)⁻¹`. Rewrite using `[map_sub]`. Establish `hn2 : ‖bk.iA 2‖ ≤ (2 : ℝ)⁻¹`.

Use `DiscBasic.norm_l_disc_le 2 (bk.ev X) bk.ρ₀` as an intermediate fact. Rewrite using `[map_ofNat]`. Simplify using `using this`. Rewrite using `[sub_eq_add_neg]`. Use `(DiscBasic.norm_add_le_max_disc 2 (bk.ev X) bk.ρ₀ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Simplify using `using ha`. Rewrite using `[norm_neg]`. Conclude with `hn2`. Rewrite using `[hfac, map_mul]`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations.

Establish `: ((2 : ℕ) : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹` using `by norm_num`. Rewrite using `[← this]`. Conclude with `mul_le_mul ha h2 (norm_nonneg _) (by positivity)`.
-/
theorem norm_iA_mu_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e →
    ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  intro l _ K bk e he
  have hker := (GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk).2.2
  have hθmu : Per.θ l (mu e) = 0 := by
    simp only [mu, map_sub, map_one]
    simp [he.1]
  refine ⟨hker _ hθmu, ?_⟩
  rintro rfl
  set δ := (frobeniusEquiv (Per.Fl 2) 2).symm e with hδ
  have hδ2 : δ ^ 2 = e := by
    rw [hδ]; exact frobenius_apply_frobeniusEquiv_symm (Per.Fl 2) 2 e
  have hu : δ.untilt ^ 2 = 1 := by
    rw [← map_pow, hδ2, he.1]
  have hu' : δ.untilt = -1 := by
    have h1 : (δ.untilt - 1) * (δ.untilt + 1) = 0 := by linear_combination hu
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) he.2
    · linear_combination h
  have hθa : Per.θ 2 (Per.tm δ + 1) = 0 := by
    simp [hu']
  have ha := hker _ hθa
  have hfac : mu e = (Per.tm δ + 1) * ((Per.tm δ + 1) - 2) := by
    simp only [mu]
    rw [← hδ2]
    show WittVector.teichmuller 2 (δ ^ 2) - 1 = _
    rw [map_pow]
    ring
  have h2 : ‖bk.iA ((Per.tm δ + 1) - 2)‖ ≤ (2 : ℝ)⁻¹ := by
    rw [map_sub]
    have hn2 : ‖bk.iA 2‖ ≤ (2 : ℝ)⁻¹ := by
      have := DiscBasic.norm_l_disc_le 2 (bk.ev X) bk.ρ₀
      rw [map_ofNat]; simpa using this
    rw [sub_eq_add_neg]
    refine (DiscBasic.norm_add_le_max_disc 2 (bk.ev X) bk.ρ₀ _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · rw [norm_neg]; exact hn2
  rw [hfac, map_mul]
  refine (norm_mul_le _ _).trans ?_
  have : ((2 : ℕ) : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
  rw [← this]
  exact mul_le_mul ha h2 (norm_nonneg _) (by positivity)

end GlobalTheory.BSP.BK
