import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

/- English proof (translation)
Introduce `l _ K bk N d ρ F hF`. Use `choose k β hβ using hF`. Establish `mono : ∀ {m n : ℕ}, m ≤ n → ∀ {k' : ℕ} {β' : Matrix (Fin d) (Fin d) bk.S}, F.IsBeta n k' β' → F.IsBeta m k' β'` using `fun h _ _ hb => ⟨hb.1, fun g i j => (pow_dvd_pow _ h).trans (hb.2 g i j)⟩`. Take `⟨ζ, e, h0, -, h1, hr⟩` from `GlobalTheory.MemLoc.exists_zeta_eps l`. Establish `he : e.untilt = 1` using `Subtype.ext (by`.

Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `this)`. Establish `hE : GlobalTheory.MemLoc.IsEps e` using `⟨he, fun hh => h1 (by`. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises.

Rewrite using `[← hr 1, map_one]`. Conclude with `congrArg Subtype.val hh)⟩`. Take `⟨hfil, -, hcomp, -⟩` from `GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE`. Take `⟨v, hv⟩` from `(isUnit_l_BdRp l).exists_left_inv`. Establish `hvk : ∀ a : ℕ, v ^ a * (l : Per.BdRp l) ^ a = 1` using `fun a => by rw [← mul_pow, hv, one_pow]`.

Use `set X : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => aDp l (bk.ev (β n i j)) with hX`. Use `set x : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => v ^ k n * X n i j with hx`. Establish `cauchy : ∀ m n, m ≤ n → ∀ i j, x n i j - x m i j ∈ Per.FilP l m`. Introduce `m n hmn i j`. Establish `h` using `GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow l K bk m N d ρ F (k m) (k n) (β m) (β n) (hβ m) (mono hmn (hβ n)) i j`.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h`. Establish `h2 : bk.ev bk.E ^ m ∣ bk.ev ((l : bk.S) ^ k n * β m i j - (l : bk.S) ^ k m * β n i j)`. Rewrite using `[← map_pow]`. Conclude with `map_dvd bk.ev h`. Establish `h3` using `((GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).2.2.1 _).2 h2`.

Simplify using `only [map_sub, map_mul, map_pow, map_natCast] at h3`. Establish `h4` using `Ideal.mul_mem_left (Per.FilP l m) (-(v ^ k n * v ^ k m)) h3`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [hx, hX]`. Take the linear combination `(v ^ k m * aDp l (bk.ev (β m i j))) * hvk (k n) - (v ^ k n * aDp l (bk.ev (β n i j))) * hvk (k m)`.

Establish `hmem : ∀ (n : ℕ) (y : Per.BdRp l), y ∈ (Ideal.span {aDp l (xi e)} ^ n • ⊤ : Submodule (Per.BdRp l) (Per.BdRp l)) ↔ y ∈ Per.FilP l n`. Introduce `n y`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfil]`. Establish `lim : ∀ i j, ∃ L : Per.BdRp l, ∀ n, x n i j - L ∈ Per.FilP l n`. Introduce `i j`.

Take `⟨L, hL⟩` from `hcomp.toIsPrecomplete.prec (f := fun n => x n i j) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, hmem, ← neg_sub]`. Conclude with `(Per.FilP l m).neg_mem (cauchy m n hmn i j))`. Conclude with `⟨L, fun n => (hmem n _).1 (SModEq.sub_mem.1 (hL n))⟩`. Use `choose B hB using lim`.

Use `⟨Matrix.of B, fun m => ⟨k m, β m, hβ m, fun i j => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `Ideal.mul_mem_left (Per.FilP l m) ((l : Per.BdRp l) ^ k m) (hB i j m)`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Matrix.of_apply, hx, hX]`. Take the linear combination `(-(aDp l (bk.ev (β m i j)))) * hvk (k m)`.
-/
theorem exists_beta_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ), F.IsDR → ∃ B : Matrix (Fin d) (Fin d) (Per.BdRp l), ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m := by
  intro l _ K bk N d ρ F hF
  choose k β hβ using hF
  have mono : ∀ {m n : ℕ}, m ≤ n → ∀ {k' : ℕ} {β' : Matrix (Fin d) (Fin d) bk.S}, F.IsBeta n k' β' → F.IsBeta m k' β' :=
    fun h _ _ hb => ⟨hb.1, fun g i j => (pow_dvd_pow _ h).trans (hb.2 g i j)⟩
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨hfil, -, hcomp, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE
  obtain ⟨v, hv⟩ := (isUnit_l_BdRp l).exists_left_inv
  have hvk : ∀ a : ℕ, v ^ a * (l : Per.BdRp l) ^ a = 1 := fun a => by rw [← mul_pow, hv, one_pow]
  set X : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => aDp l (bk.ev (β n i j)) with hX
  set x : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => v ^ k n * X n i j with hx
  have cauchy : ∀ m n, m ≤ n → ∀ i j, x n i j - x m i j ∈ Per.FilP l m := by
    intro m n hmn i j
    have h := GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow l K bk m N d ρ F (k m) (k n) (β m) (β n) (hβ m) (mono hmn (hβ n)) i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h2 : bk.ev bk.E ^ m ∣ bk.ev ((l : bk.S) ^ k n * β m i j - (l : bk.S) ^ k m * β n i j) := by
      rw [← map_pow]; exact map_dvd bk.ev h
    have h3 := ((GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).2.2.1 _).2 h2
    simp only [map_sub, map_mul, map_pow, map_natCast] at h3
    have h4 := Ideal.mul_mem_left (Per.FilP l m) (-(v ^ k n * v ^ k m)) h3
    convert h4 using 1
    simp only [hx, hX]
    linear_combination (v ^ k m * aDp l (bk.ev (β m i j))) * hvk (k n) - (v ^ k n * aDp l (bk.ev (β n i j))) * hvk (k m)
  have hmem : ∀ (n : ℕ) (y : Per.BdRp l), y ∈ (Ideal.span {aDp l (xi e)} ^ n • ⊤ : Submodule (Per.BdRp l) (Per.BdRp l)) ↔
      y ∈ Per.FilP l n := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfil]
  have lim : ∀ i j, ∃ L : Per.BdRp l, ∀ n, x n i j - L ∈ Per.FilP l n := by
    intro i j
    obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => x n i j) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hmem, ← neg_sub]
      exact (Per.FilP l m).neg_mem (cauchy m n hmn i j))
    exact ⟨L, fun n => (hmem n _).1 (SModEq.sub_mem.1 (hL n))⟩
  choose B hB using lim
  refine ⟨Matrix.of B, fun m => ⟨k m, β m, hβ m, fun i j => ?_⟩⟩
  have h := Ideal.mul_mem_left (Per.FilP l m) ((l : Per.BdRp l) ^ k m) (hB i j m)
  convert h using 1
  simp only [Matrix.of_apply, hx, hX]
  linear_combination (-(aDp l (bk.ev (β m i j)))) * hvk (k m)

end GlobalTheory.BKLim
