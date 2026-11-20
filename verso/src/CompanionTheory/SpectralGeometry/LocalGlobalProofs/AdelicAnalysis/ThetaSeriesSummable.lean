import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SummableGaussianCoset
import ReciprocityTheory.ThetaSummability.TailSumEstimates.LatSumPi
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaSum

open scoped Classical in

/- English proof (translation)
Rewrite using `[mixedEmbedding.norm_eq_sup'_normAtPlace]`. Take `⟨w, -, hw⟩` from `Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : InfinitePlace F => mixedEmbedding.normAtPlace w (mixedEmbedding F y))`. Rewrite using `[hw, mixedEmbedding.normAtPlace_apply]`. Conclude with `Finset.single_le_sum (f := fun w : InfinitePlace F => (w y) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)`.
-/
theorem norm_mixed_sq_le (F : Type) [Field F] [NumberField F] (y : F) :
    ‖mixedEmbedding F y‖ ^ 2 ≤ ∑ w : InfinitePlace F, (w y) ^ 2 := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun w : InfinitePlace F => mixedEmbedding.normAtPlace w (mixedEmbedding F y))
  rw [hw, mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => (w y) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ w)

/- English proof (translation)
Establish `hs` using `GlobalTheory.GaussCoset.summable_lattice (mixedEmbedding.integerLattice F) ha 0 0`. Set `e : 𝓞 F → mixedEmbedding.integerLattice F` to `fun r => ⟨mixedEmbedding F (r : F), ⟨r, rfl⟩⟩`. Establish `he : Function.Injective e` using `fun a b h => RingOfIntegers.coe_injective (mixedEmbedding_injective F (congrArg Subtype.val h))`. Use `Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun r => ?_) (hs.comp_injective he)` and prove the remaining obligations. Simplify using `only [Function.comp, e, sub_zero, zero_mul, add_zero]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use `norm_mixed_sq_le F (r : F)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem summable_integers (F : Type) [Field F] [NumberField F] {a : ℝ} (ha : 0 < a) :
    Summable fun r : 𝓞 F => Real.exp (-a * ∑ w : InfinitePlace F, (w (r : F)) ^ 2) := by
  classical
  have hs := GlobalTheory.GaussCoset.summable_lattice (mixedEmbedding.integerLattice F) ha 0 0
  let e : 𝓞 F → mixedEmbedding.integerLattice F :=
    fun r => ⟨mixedEmbedding F (r : F), ⟨r, rfl⟩⟩
  have he : Function.Injective e := fun a b h =>
    RingOfIntegers.coe_injective (mixedEmbedding_injective F (congrArg Subtype.val h))
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun r => ?_) (hs.comp_injective he)
  simp only [Function.comp, e, sub_zero, zero_mul, add_zero]
  apply Real.exp_le_exp.2
  have := norm_mixed_sq_le F (r : F)
  nlinarith

/- English proof (translation)
Set `e` to `Fintype.equivFin ι`. Establish `h` using `(ReciprocityTheory.ThetaSummability.Est.summable_and_tsum_pi_prod (fun (_ : Fin (Fintype.card ι)) (r : 𝓞 F) => Real.exp (-a * ∑ w : InfinitePlace F, (w (r : F)) ^ 2)) (fun _ _ => (Real.exp_pos _).le) (fun _ => summable_integers F ha)).1`. Establish `h2` using `(e.arrowCongr (Equiv.refl (𝓞 F))).summable_iff.2 h`. Use `h2.congr fun r => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp, id]`.

Rewrite using `[Equiv.prod_comp e.symm (fun j => Real.exp (-a * ∑ w : InfinitePlace F, (w (r j : F)) ^ 2)), ← Real.exp_sum, Finset.mul_sum]`.
-/
theorem summable_pi_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] {a : ℝ}
    (ha : 0 < a) :
    Summable fun r : ι → 𝓞 F =>
      Real.exp (-a * ∑ j, ∑ w : InfinitePlace F, (w (r j : F)) ^ 2) := by
  classical
  let e := Fintype.equivFin ι
  have h := (ReciprocityTheory.ThetaSummability.Est.summable_and_tsum_pi_prod
    (fun (_ : Fin (Fintype.card ι)) (r : 𝓞 F) =>
      Real.exp (-a * ∑ w : InfinitePlace F, (w (r : F)) ^ 2))
    (fun _ _ => (Real.exp_pos _).le) (fun _ => summable_integers F ha)).1
  have h2 := (e.arrowCongr (Equiv.refl (𝓞 F))).summable_iff.2 h
  refine h2.congr fun r => ?_
  simp only [Function.comp, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp, id]
  rw [Equiv.prod_comp e.symm (fun j => Real.exp (-a * ∑ w : InfinitePlace F, (w (r j : F)) ^ 2)),
    ← Real.exp_sum, Finset.mul_sum]

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with he | hne` into its components or cases. Use `⟨1, one_pos, fun v => ?_⟩` and prove the remaining obligations. Establish `: v = 0` using `Subsingleton.elim _ _`. Simplify using `[this]`. Establish `hcomp : IsCompact (Metric.sphere (0 : ι → ℝ) 1)` using `isCompact_sphere 0 1`.

Establish `hnon : (Metric.sphere (0 : ι → ℝ) 1).Nonempty` using `NormedSpace.sphere_nonempty.2 zero_le_one`. Establish `hcont : Continuous fun v : ι → ℝ => (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v))`. Establish `h1 : Continuous fun v : ι → ℝ => g *ᵥ v` using `continuous_const.matrix_mulVec continuous_id`. Conclude with `h1.dotProduct (continuous_const.matrix_mulVec h1)`. Take `⟨u, hu, hmin⟩` from `hcomp.exists_isMinOn hnon hcont.continuousOn`.

Establish `hpos : ∀ v : ι → ℝ, v ≠ 0 → 0 < (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v))`. Introduce `v hv`. Establish `hgv : g *ᵥ v ≠ 0`. Introduce `h0`. Conclude with `hv (Matrix.eq_zero_of_mulVec_eq_zero (isUnit_iff_ne_zero.1 hg) h0)`.

Simplify using `using hP.dotProduct_mulVec_pos hgv`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hu`. Use `⟨_, hpos u hu0, fun v => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Establish `hn : ‖v‖ ≠ 0` using `norm_ne_zero_iff.2 hv`. Establish `hs : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1`. Simplify using `[norm_smul, hn]`.

Establish `h3` using `hmin hs`. Simplify using `only [Set.mem_setOf_eq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h3`. Establish `h4 : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * ((g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v))))) = (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← h4, mul_comm]`.

Conclude with `mul_le_mul_of_nonneg_left h3 (by positivity)`.
-/
theorem exists_quad_lower {ι : Type} [Fintype ι] [DecidableEq ι] (P g : Matrix ι ι ℝ) (hP : P.PosDef)
    (hg : IsUnit g.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ι → ℝ, c * ‖v‖ ^ 2 ≤ (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v)) := by
  rcases isEmpty_or_nonempty ι with he | hne
  · refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim _ _
    simp [this]
  have hcomp : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hnon : (Metric.sphere (0 : ι → ℝ) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hcont : Continuous fun v : ι → ℝ => (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v)) := by
    have h1 : Continuous fun v : ι → ℝ => g *ᵥ v := continuous_const.matrix_mulVec continuous_id
    exact h1.dotProduct (continuous_const.matrix_mulVec h1)
  obtain ⟨u, hu, hmin⟩ := hcomp.exists_isMinOn hnon hcont.continuousOn
  have hpos : ∀ v : ι → ℝ, v ≠ 0 → 0 < (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v)) := by
    intro v hv
    have hgv : g *ᵥ v ≠ 0 := by
      intro h0
      exact hv (Matrix.eq_zero_of_mulVec_eq_zero (isUnit_iff_ne_zero.1 hg) h0)
    simpa using hP.dotProduct_mulVec_pos hgv
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine ⟨_, hpos u hu0, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hs : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hn]
  have h3 := hmin hs
  simp only [Set.mem_setOf_eq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h3
  have h4 : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * ((g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v))))) =
      (g *ᵥ v) ⬝ᵥ (P *ᵥ (g *ᵥ v)) := by
    field_simp
  rw [← h4, mul_comm]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Take `⟨u, hu⟩` from `hC`. Rewrite `h1` using `[← hu]`. Use `isUnit_iff_exists_inv.2 ⟨G.det * (u : R) * ((u⁻¹ : Rˣ) : R), ?_⟩` and prove the remaining obligations.

Establish `h2 : G.det * G.det * (u : R) = (u : R)` using `by linear_combination h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isUnit_det_of_orth {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (G C : Matrix ι ι R)
    (h : Gᵀ * C * G = C) (hC : IsUnit C.det) : IsUnit G.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  obtain ⟨u, hu⟩ := hC
  rw [← hu] at h1
  refine isUnit_iff_exists_inv.2 ⟨G.det * (u : R) * ((u⁻¹ : Rˣ) : R), ?_⟩
  have h2 : G.det * G.det * (u : R) = (u : R) := by linear_combination h1
  calc G.det * (G.det * (u : R) * ((u⁻¹ : Rˣ) : R)) = G.det * G.det * (u : R) * ((u⁻¹ : Rˣ) : R) := by ring
    _ = 1 := by rw [h2]; simp

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[gauss, Complex.norm_exp, Complex.re_sum, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `[Complex.sub_re, Complex.mul_re, Complex.mul_im]`.
-/
theorem norm_gauss (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ) :
    ‖gauss B ρ P τ x‖ =
      Real.exp (-∑ w, Real.pi * (τ w).im * (x w ⬝ᵥ (P w *ᵥ x w))) := by
  rw [gauss, Complex.norm_exp, Complex.re_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]

/- English proof (translation)
Establish `: (Bf B).det = algebraMap F (A F) B.det`. Rewrite using `[Bf, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(isUnit_iff_ne_zero.2 h).map _`.
-/
theorem isUnit_det_Bf (B : Matrix ι ι F) (h : B.det ≠ 0) : IsUnit (Bf B).det := by
  have : (Bf B).det = algebraMap F (A F) B.det := by
    rw [Bf, RingHom.map_det]; rfl
  rw [this]
  exact (isUnit_iff_ne_zero.2 h).map _

/- English proof (translation)
Take `⟨-, -, -, hdet, hρ, hP, -⟩` from `hQ`. Establish `hu : ∀ w, IsUnit (gi w).det` using `fun w => isUnit_det_of_orth _ (B.map (ρ w)) (hgi w) (by`. Establish `: (B.map (ρ w)).det = ρ w B.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `(isUnit_iff_ne_zero.2 hdet).map _)`. Establish `hb` using `fun w => exists_quad_lower (P w) (gi w) (hP w) (hu w)`. Use `choose c hc hc' using hb`. Take `⟨w0, hw0⟩` from `Finite.exists_min fun w => Real.pi * (τ w).im * c w`.

Use `set d := Real.pi * (τ w0).im * c w0 with hd`. Establish `hdpos : 0 < d` using `mul_pos (mul_pos Real.pi_pos (hτ w0)) (hc w0)`. Establish `hwv : ∀ (w : InfinitePlace F) (y : F), w y = |ρ w y|` using `fun w y => by`. Rewrite using `[← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]`. Use `⟨d / (Fintype.card ι + 1), by positivity, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_gauss]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use `set v : InfinitePlace F → ι → ℝ := fun w j => ρ w (x j) with hv`. Establish `h1 : ∀ w, d * ‖v w‖ ^ 2 ≤ Real.pi * (τ w).im * ((gi w *ᵥ v w) ⬝ᵥ (P w *ᵥ (gi w *ᵥ v w)))` using `fun w => by`. Establish `e1 : 0 < Real.pi * (τ w).im` using `mul_pos Real.pi_pos (hτ w)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ w, ‖v w‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations. Establish `: w (x j) ≤ ‖v w‖`.

Rewrite using `[hwv]`. Conclude with `norm_le_pi_norm (v w) j`. Establish `h0 : 0 ≤ w (x j)` using `AbsoluteValue.nonneg _ _`. Use `gcongr`. Use `_ = _ := by simp`.

Establish `h3 : d * ∑ w, ‖v w‖ ^ 2 ≤ ∑ w, Real.pi * (τ w).im * ((gi w *ᵥ v w) ⬝ᵥ (P w *ᵥ (gi w *ᵥ v w)))`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun w _ => h1 w`. Establish `h4 : 0 ≤ ∑ w, ‖v w‖ ^ 2` using `Finset.sum_nonneg fun _ _ => by positivity`. Establish `hk : (0 : ℝ) < Fintype.card ι + 1` using `by positivity`.

Establish `h5 : d / (Fintype.card ι + 1) * ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤ d * ∑ w, ‖v w‖ ^ 2`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ hk]`. Establish `h6 : ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤ ((Fintype.card ι : ℝ) + 1) * ∑ w, ‖v w‖ ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gauss_bound {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    {gi : InfinitePlace F → Matrix ι ι ℝ} (hgi : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w))
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ι → F, ‖gauss B ρ P τ (fun w => gi w *ᵥ fun j => ρ w (x j))‖ ≤
      Real.exp (-a * ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2) := by
  obtain ⟨-, -, -, hdet, hρ, hP, -⟩ := hQ
  have hu : ∀ w, IsUnit (gi w).det := fun w => isUnit_det_of_orth _ (B.map (ρ w)) (hgi w) (by
    have : (B.map (ρ w)).det = ρ w B.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.2 hdet).map _)
  have hb := fun w => exists_quad_lower (P w) (gi w) (hP w) (hu w)
  choose c hc hc' using hb
  obtain ⟨w0, hw0⟩ := Finite.exists_min fun w => Real.pi * (τ w).im * c w
  set d := Real.pi * (τ w0).im * c w0 with hd
  have hdpos : 0 < d := mul_pos (mul_pos Real.pi_pos (hτ w0)) (hc w0)
  have hwv : ∀ (w : InfinitePlace F) (y : F), w y = |ρ w y| := fun w y => by
    rw [← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨d / (Fintype.card ι + 1), by positivity, fun x => ?_⟩
  rw [norm_gauss]
  apply Real.exp_le_exp.2
  set v : InfinitePlace F → ι → ℝ := fun w j => ρ w (x j) with hv
  have h1 : ∀ w, d * ‖v w‖ ^ 2 ≤ Real.pi * (τ w).im *
      ((gi w *ᵥ v w) ⬝ᵥ (P w *ᵥ (gi w *ᵥ v w))) := fun w => by
    have e1 : 0 < Real.pi * (τ w).im := mul_pos Real.pi_pos (hτ w)
    calc d * ‖v w‖ ^ 2 ≤ (Real.pi * (τ w).im * c w) * ‖v w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hw0 w) (by positivity)
      _ = Real.pi * (τ w).im * (c w * ‖v w‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc' w _) e1.le
  have h2 : ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ w, ‖v w‖ ^ 2 := by
    calc ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤ ∑ _j : ι, ∑ w, ‖v w‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => ?_
          have : w (x j) ≤ ‖v w‖ := by
            rw [hwv]
            exact norm_le_pi_norm (v w) j
          have h0 : 0 ≤ w (x j) := AbsoluteValue.nonneg _ _
          gcongr
      _ = _ := by simp
  have h3 : d * ∑ w, ‖v w‖ ^ 2 ≤ ∑ w, Real.pi * (τ w).im *
      ((gi w *ᵥ v w) ⬝ᵥ (P w *ᵥ (gi w *ᵥ v w))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => h1 w
  have h4 : 0 ≤ ∑ w, ‖v w‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hk : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  have h5 : d / (Fintype.card ι + 1) * ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤
      d * ∑ w, ‖v w‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk]
    have h6 : ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2 ≤
        ((Fintype.card ι : ℝ) + 1) * ∑ w, ‖v w‖ ^ 2 := by nlinarith
    calc d * ∑ j, ∑ w : InfinitePlace F, (w (x j)) ^ 2
        ≤ d * (((Fintype.card ι : ℝ) + 1) * ∑ w, ‖v w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h6 hdpos.le
      _ = d * (∑ w, ‖v w‖ ^ 2) * ((Fintype.card ι : ℝ) + 1) := by ring
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hInt, -, hCpt, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hcont : ∀ j, Continuous fun y : ι → A F => (gf⁻¹ *ᵥ y) j` using `fun j => (continuous_apply j).comp (continuous_const.matrix_mulVec continuous_id)`. Establish `hK : IsCompact (⋃ j, (fun y : ι → A F => (gf⁻¹ *ᵥ y) j) '' tsupport φ)` using `isCompact_iUnion fun j => hφ.2.isCompact.image (hcont j)`. Take `⟨N, hN, hNK⟩` from `hCpt _ hK`. Use `⟨N, hN, fun x hx j => ?_⟩` and prove the remaining obligations.

Establish `hmem` using `subset_tsupport φ (Function.mem_support.2 hx)`. Establish `h1 : (gf⁻¹ *ᵥ (gf *ᵥ fun j => algebraMap F (A F) (x j))) j = algebraMap F (A F) (x j)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `h2` using `hNK _ (Set.mem_iUnion.2 ⟨j, _, hmem, h1⟩)`. Establish `h3 : (N : A F) * algebraMap F (A F) (x j) = algebraMap F (A F) ((N : F) * x j)`.

Rewrite using `[map_mul, map_natCast]`. Rewrite `h2` using `[h3]`. Conclude with `(hInt _).1 h2`.
-/
theorem support_denominator {gf : Matrix ι ι (A F)} (hu : IsUnit gf.det) {φ : (ι → A F) → ℂ}
    (hφ : SB φ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ι → F, φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) ≠ 0 →
      ∀ j, ∃ r : 𝓞 F, (r : F) = (N : F) * x j := by
  obtain ⟨-, -, -, -, -, -, hInt, -, hCpt, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hcont : ∀ j, Continuous fun y : ι → A F => (gf⁻¹ *ᵥ y) j := fun j =>
    (continuous_apply j).comp (continuous_const.matrix_mulVec continuous_id)
  have hK : IsCompact (⋃ j, (fun y : ι → A F => (gf⁻¹ *ᵥ y) j) '' tsupport φ) :=
    isCompact_iUnion fun j => hφ.2.isCompact.image (hcont j)
  obtain ⟨N, hN, hNK⟩ := hCpt _ hK
  refine ⟨N, hN, fun x hx j => ?_⟩
  have hmem := subset_tsupport φ (Function.mem_support.2 hx)
  have h1 : (gf⁻¹ *ᵥ (gf *ᵥ fun j => algebraMap F (A F) (x j))) j = algebraMap F (A F) (x j) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have h2 := hNK _ (Set.mem_iUnion.2 ⟨j, _, hmem, h1⟩)
  have h3 : (N : A F) * algebraMap F (A F) (x j) = algebraMap F (A F) ((N : F) * x j) := by
    rw [map_mul, map_natCast]
  rw [h3] at h2
  exact (hInt _).1 h2

/- English proof (translation)
Establish `hu : IsUnit gf.det` using `isUnit_det_of_orth gf (Bf B) hO.1 (isUnit_det_Bf B hQ.2.2.2.1)`. Take `⟨N, hN, hsupp⟩` from `support_denominator hu hφ`. Take `⟨C, hC⟩` from `hφ.1.continuous.bounded_above_of_compact_support hφ.2`. Take `⟨a, ha, hg⟩` from `gauss_bound hQ hO.2 hτ`. Establish `hNF : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Establish `hNR : (0 : ℝ) < N` using `Nat.cast_pos.2 hN`. Set `i : (ι → 𝓞 F) → (ι → F)` to `fun r j => (r j : F) / N`. Establish `hi : Function.Injective i` using `fun r s h => funext fun j => by`. Use `congrFun h j` as an intermediate fact. Conclude with `RingOfIntegers.coe_injective ((div_left_inj' hNF).1 this)`.

Establish `hz : ∀ x, x ∉ Set.range i → ‖thTerm B ρ P gf gi φ τ x‖ = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `h1 : φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) ≠ 0`. Introduce `h0`.

Conclude with `hne (by simp [thTerm, h0])`. Use `choose r hr using hsupp x h1`. Conclude with `hx ⟨r, funext fun j => by simp only [i]; rw [hr j]; field_simp⟩`. Use `(hi.summable_iff hz).1 ?_` and prove the remaining obligations. Establish `hs` using `(summable_pi_integers F ι (a := a / (N : ℝ) ^ 2) (by positivity)).mul_left C`.

Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_) hs` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[thTerm, norm_mul]`. Establish `hwN : ∀ (w : InfinitePlace F) (y : 𝓞 F), (w ((y : F) / N)) ^ 2 = (w (y : F)) ^ 2 / (N : ℝ) ^ 2`. Introduce `w y`.

Establish `: w (N : F) = N`. Rewrite using `[← InfinitePlace.norm_embedding_eq, map_natCast, Complex.norm_natCast]`. Rewrite using `[map_div₀, this, div_pow]`. Establish `hb` using `hg (i r)`. Establish `he : ∑ j, ∑ w : InfinitePlace F, (w (i r j)) ^ 2 = (∑ j, ∑ w : InfinitePlace F, (w (r j : F)) ^ 2) / (N : ℝ) ^ 2`.

Simplify using `only [i, hwN, Finset.sum_div]`. Rewrite `hb` using `[he]`. Establish `hb2 : ‖gauss B ρ P τ (fun w => gi w *ᵥ fun j => ρ w (i r j))‖ ≤ Real.exp (-(a / (N : ℝ) ^ 2) * ∑ j, ∑ w : InfinitePlace F, (w (r j : F)) ^ 2)`. Use `hb.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_le_mul (hC _) hb2 (norm_nonneg _) ((norm_nonneg _).trans (hC 0))`.
-/
theorem summable_thTerm {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P) {gf : Matrix ι ι (A F)}
    {gi : InfinitePlace F → Matrix ι ι ℝ} (hO : IsOrth B ρ gf gi) {τ : InfinitePlace F → ℂ}
    (hτ : ∀ w, 0 < (τ w).im) {φ : (ι → A F) → ℂ} (hφ : SB φ) :
    Summable fun x => ‖thTerm B ρ P gf gi φ τ x‖ := by
  have hu : IsUnit gf.det := isUnit_det_of_orth gf (Bf B) hO.1 (isUnit_det_Bf B hQ.2.2.2.1)
  obtain ⟨N, hN, hsupp⟩ := support_denominator hu hφ
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  obtain ⟨a, ha, hg⟩ := gauss_bound hQ hO.2 hτ
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNR : (0 : ℝ) < N := Nat.cast_pos.2 hN
  let i : (ι → 𝓞 F) → (ι → F) := fun r j => (r j : F) / N
  have hi : Function.Injective i := fun r s h => funext fun j => by
    have := congrFun h j
    exact RingOfIntegers.coe_injective ((div_left_inj' hNF).1 this)
  have hz : ∀ x, x ∉ Set.range i → ‖thTerm B ρ P gf gi φ τ x‖ = 0 := by
    intro x hx
    by_contra hne
    have h1 : φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) ≠ 0 := by
      intro h0
      exact hne (by simp [thTerm, h0])
    choose r hr using hsupp x h1
    exact hx ⟨r, funext fun j => by simp only [i]; rw [hr j]; field_simp⟩
  refine (hi.summable_iff hz).1 ?_
  have hs := (summable_pi_integers F ι (a := a / (N : ℝ) ^ 2) (by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_) hs
  simp only [Function.comp]
  rw [thTerm, norm_mul]
  have hwN : ∀ (w : InfinitePlace F) (y : 𝓞 F), (w ((y : F) / N)) ^ 2 = (w (y : F)) ^ 2 / (N : ℝ) ^ 2 := by
    intro w y
    have : w (N : F) = N := by
      rw [← InfinitePlace.norm_embedding_eq, map_natCast, Complex.norm_natCast]
    rw [map_div₀, this, div_pow]
  have hb := hg (i r)
  have he : ∑ j, ∑ w : InfinitePlace F, (w (i r j)) ^ 2 =
      (∑ j, ∑ w : InfinitePlace F, (w (r j : F)) ^ 2) / (N : ℝ) ^ 2 := by
    simp only [i, hwN, Finset.sum_div]
  rw [he] at hb
  have hb2 : ‖gauss B ρ P τ (fun w => gi w *ᵥ fun j => ρ w (i r j))‖ ≤
      Real.exp (-(a / (N : ℝ) ^ 2) * ∑ j, ∑ w : InfinitePlace F, (w (r j : F)) ^ 2) := by
    refine hb.trans (le_of_eq ?_)
    congr 1
    ring
  exact mul_le_mul (hC _) hb2 (norm_nonneg _) ((norm_nonneg _).trans (hC 0))

def mulOh (N : ℕ) : Set (A F) := {x | ∃ y ∈ Oh F, x = (N : A F) * y}

def vecN (gf : Matrix ι ι (A F)) (N : ℕ) : Set (ι → A F) := {y | ∀ i, (gf⁻¹ *ᵥ y) i ∈ mulOh (F := F) N}

def indN (gf : Matrix ι ι (A F)) (N : ℕ) : (ι → A F) → ℂ := Set.indicator (vecN gf N) fun _ => 1

/- English proof (translation)
Take `⟨-, -, hT2, hOc, -, -, -, -, -, hOpenN⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hTc : IsCompact (mulOh (F` using `F) N) := by`. Establish `: mulOh (F` using `F) N = (fun y : A F => (N : A F) * y) '' Oh F := by`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Rewrite using `[this]`.

Conclude with `hOc.image (continuous_const.mul continuous_id)`. Establish `hc : IsCompact (vecN gf N)`. Establish `: vecN gf N = (fun v : ι → A F => gf *ᵥ v) '' Set.pi Set.univ fun _ => mulOh (F` using `F) N := by`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Use `⟨gf⁻¹ *ᵥ y, fun i _ => hy i, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Introduce and unpack `⟨v, hv, rfl⟩ i`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Conclude with `hv i (Set.mem_univ i)`. Rewrite using `[this]`. Conclude with `(isCompact_univ_pi fun _ => hTc).image (continuous_const.matrix_mulVec continuous_id)`. Establish `ho : IsOpen (vecN gf N)`.

Establish `: vecN gf N = ⋂ i, (fun y : ι → A F => (gf⁻¹ *ᵥ y) i) ⁻¹' mulOh (F` using `F) N := by`. Use extensionality with `y`. Simplify using `[vecN]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => (hOpenN N hN).preimage ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id))`.

Use `⟨?_, .intro hc fun y hy => Set.indicator_of_notMem hy _⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_exists_open _).2 fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ vecN gf N`. Conclude with `⟨_, ho, hy, fun z hz => by rw [indN, Set.indicator_of_mem hz, Set.indicator_of_mem hy]⟩`. Conclude with `⟨_, hc.isClosed.isOpen_compl, hy, fun z hz => by`.

Rewrite using `[indN, Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]⟩`.
-/
theorem sb_indN {gf : Matrix ι ι (A F)} (hu : IsUnit gf.det) {N : ℕ} (hN : 0 < N) :
    SB (indN gf N) := by
  obtain ⟨-, -, hT2, hOc, -, -, -, -, -, hOpenN⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hTc : IsCompact (mulOh (F := F) N) := by
    have : mulOh (F := F) N = (fun y : A F => (N : A F) * y) '' Oh F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [this]
    exact hOc.image (continuous_const.mul continuous_id)
  have hc : IsCompact (vecN gf N) := by
    have : vecN gf N = (fun v : ι → A F => gf *ᵥ v) '' Set.pi Set.univ fun _ => mulOh (F := F) N := by
      ext y
      constructor
      · intro hy
        refine ⟨gf⁻¹ *ᵥ y, fun i _ => hy i, ?_⟩
        simp only
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      · rintro ⟨v, hv, rfl⟩ i
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
        exact hv i (Set.mem_univ i)
    rw [this]
    exact (isCompact_univ_pi fun _ => hTc).image (continuous_const.matrix_mulVec continuous_id)
  have ho : IsOpen (vecN gf N) := by
    have : vecN gf N = ⋂ i, (fun y : ι → A F => (gf⁻¹ *ᵥ y) i) ⁻¹' mulOh (F := F) N := by
      ext y
      simp [vecN]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (hOpenN N hN).preimage ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id))
  refine ⟨?_, .intro hc fun y hy => Set.indicator_of_notMem hy _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
  by_cases hy : y ∈ vecN gf N
  · exact ⟨_, ho, hy, fun z hz => by rw [indN, Set.indicator_of_mem hz, Set.indicator_of_mem hy]⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hy, fun z hz => by
      rw [indN, Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]⟩

/- English proof (translation)
Introduce `v`. Establish `h : ∀ m : ℕ, (m : A F) v = (m : v.adicCompletion F)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rfl`.

Consider the case `succ m ih`. Rewrite using `[Nat.cast_succ, Nat.cast_succ, ← ih]`. Both sides reduce to the same expression. Use `show (n : A F) v * z v ∈ _`. Rewrite using `[h]`.

Conclude with `mul_mem (natCast_mem _ n) (hz v)`.
-/
theorem natCast_mul_mem_Oh (n : ℕ) {z : A F} (hz : z ∈ Oh F) : (n : A F) * z ∈ Oh F := by
  intro v
  have h : ∀ m : ℕ, (m : A F) v = (m : v.adicCompletion F) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Nat.cast_succ, Nat.cast_succ, ← ih]
      rfl
  show (n : A F) v * z v ∈ _
  rw [h]
  exact mul_mem (natCast_mem _ n) (hz v)

/- English proof (translation)
Introduce `y hy i`. Take `⟨z, hz, h⟩` from `hy i`. Conclude with `⟨_, natCast_mul_mem_Oh n hz, by rw [h]; simp⟩`.
-/
theorem vecN_subset (gf : Matrix ι ι (A F)) (n : ℕ) : vecN gf n ⊆ vecN gf 1 := by
  intro y hy i
  obtain ⟨z, hz, h⟩ := hy i
  exact ⟨_, natCast_mul_mem_Oh n hz, by rw [h]; simp⟩

/- English proof (translation)
Use `⟨⌈|Algebra.norm ℚ y|⌉₊, fun n hn r hr => ?_⟩` and prove the remaining obligations. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `hy (by simpa using hr)`. Establish `hnr : (1 : ℚ) ≤ |Algebra.norm ℚ (r : F)|`.

Rewrite using `[← Algebra.coe_norm_int r]`. Establish `: Algebra.norm ℤ r ≠ 0`. Rewrite using `[Ne, Algebra.norm_eq_zero_iff]`. Conclude with `hr0`. Conclude with `Int.one_le_abs this` after adjusting the coercions.

Establish `hd : 0 < Module.finrank ℚ F` using `Module.finrank_pos`. Establish `h1 : Algebra.norm ℚ y = ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F * Algebra.norm ℚ (r : F)`. Rewrite using `[hr, map_mul]`. Use `congr 1`. Establish `: ((n + 1 : ℕ) : F) = algebraMap ℚ F ((n + 1 : ℕ) : ℚ)` using `by simp`.

Rewrite using `[this, Algebra.norm_algebraMap]`. Establish `h2 : ((n + 1 : ℕ) : ℚ) ≤ ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F` using `le_self_pow₀ (by simp) hd.ne'`. Establish `h3 : ((n + 1 : ℕ) : ℚ) ≤ |Algebra.norm ℚ y|`. Rewrite using `[h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F)]`. Use polynomial arithmetic with `[show (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) by positivity]`.

Establish `h4 : |Algebra.norm ℚ y| ≤ (n : ℚ)` using `(Nat.le_ceil _).trans (by exact_mod_cast hn)`. Establish `h5 : ((n + 1 : ℕ) : ℚ) = n + 1` using `by push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_not_multiple {y : F} (hy : y ≠ 0) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ r : 𝓞 F, y ≠ ((n + 1 : ℕ) : F) * (r : F) := by
  refine ⟨⌈|Algebra.norm ℚ y|⌉₊, fun n hn r hr => ?_⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hr)
  have hnr : (1 : ℚ) ≤ |Algebra.norm ℚ (r : F)| := by
    rw [← Algebra.coe_norm_int r]
    have : Algebra.norm ℤ r ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hr0
    exact_mod_cast Int.one_le_abs this
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have h1 : Algebra.norm ℚ y = ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F * Algebra.norm ℚ (r : F) := by
    rw [hr, map_mul]
    congr 1
    have : ((n + 1 : ℕ) : F) = algebraMap ℚ F ((n + 1 : ℕ) : ℚ) := by simp
    rw [this, Algebra.norm_algebraMap]
  have h2 : ((n + 1 : ℕ) : ℚ) ≤ ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F :=
    le_self_pow₀ (by simp) hd.ne'
  have h3 : ((n + 1 : ℕ) : ℚ) ≤ |Algebra.norm ℚ y| := by
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) ^ Module.finrank ℚ F)]
    nlinarith [show (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) by positivity]
  have h4 : |Algebra.norm ℚ y| ≤ (n : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h5 : ((n + 1 : ℕ) : ℚ) = n + 1 := by push_cast; ring
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hInt, -, -, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hx`. Take `⟨n₀, hn₀⟩` from `exists_not_multiple (F := F) hj`. Use `filter_upwards [Filter.eventually_ge_atTop n₀] with n hn`. Use `Set.indicator_of_notMem (fun hm => ?_) _` and prove the remaining obligations.

Take `⟨z, hz, h⟩` from `hm j`. Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `hNF : ((n + 1 : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)`. Establish `hzz : z = algebraMap F (A F) (x j / ((n + 1 : ℕ) : F))`. Establish `h1 : algebraMap F (A F) ((n + 1 : ℕ) : F) * algebraMap F (A F) (x j / ((n + 1 : ℕ) : F)) = algebraMap F (A F) (x j)`.

Rewrite using `[← map_mul, mul_div_cancel₀ _ hNF]`. Establish `h2 : algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * algebraMap F (A F) ((n + 1 : ℕ) : F) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hNF, map_one]`. Establish `h3 : ((n + 1 : ℕ) : A F) = algebraMap F (A F) ((n + 1 : ℕ) : F)`. Rewrite using `[map_natCast]`.

Rewrite `h` using `[h3, ← h1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, one_mul]`. Use `_ = algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * (algebraMap F (A F) ((n + 1 : ℕ) : F) * z) := by ring`. Use `_ = algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * (algebraMap F (A F) ((n + 1 : ℕ) : F) * algebraMap F (A F) (x j / ((n + 1 : ℕ) : F))) := by rw [← h]`.

Use `_ = _ := by rw [← mul_assoc, h2, one_mul]`. Rewrite `hz` using `[hzz]`. Take `⟨r, hr⟩` from `(hInt _).1 hz`. Use `hn₀ n hn r ?_` and prove the remaining obligations. Rewrite using `[hr, mul_div_cancel₀ _ hNF]`.
-/
theorem indN_eventually_zero {gf : Matrix ι ι (A F)} (hu : IsUnit gf.det) {x : ι → F} (hx : x ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop, indN gf (n + 1) (gf *ᵥ fun j => algebraMap F (A F) (x j)) = 0 := by
  obtain ⟨-, -, -, -, -, -, hInt, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  obtain ⟨n₀, hn₀⟩ := exists_not_multiple (F := F) hj
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  refine Set.indicator_of_notMem (fun hm => ?_) _
  obtain ⟨z, hz, h⟩ := hm j
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  have hNF : ((n + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
  have hzz : z = algebraMap F (A F) (x j / ((n + 1 : ℕ) : F)) := by
    have h1 : algebraMap F (A F) ((n + 1 : ℕ) : F) * algebraMap F (A F) (x j / ((n + 1 : ℕ) : F)) =
        algebraMap F (A F) (x j) := by
      rw [← map_mul, mul_div_cancel₀ _ hNF]
    have h2 : algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * algebraMap F (A F) ((n + 1 : ℕ) : F) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hNF, map_one]
    have h3 : ((n + 1 : ℕ) : A F) = algebraMap F (A F) ((n + 1 : ℕ) : F) := by
      rw [map_natCast]
    rw [h3, ← h1] at h
    calc z = algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * algebraMap F (A F) ((n + 1 : ℕ) : F) * z := by
          rw [h2, one_mul]
      _ = algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * (algebraMap F (A F) ((n + 1 : ℕ) : F) * z) := by ring
      _ = algebraMap F (A F) (((n + 1 : ℕ) : F)⁻¹) * (algebraMap F (A F) ((n + 1 : ℕ) : F) *
            algebraMap F (A F) (x j / ((n + 1 : ℕ) : F))) := by rw [← h]
      _ = _ := by rw [← mul_assoc, h2, one_mul]
  rw [hzz] at hz
  obtain ⟨r, hr⟩ := (hInt _).1 hz
  refine hn₀ n hn r ?_
  rw [hr, mul_div_cancel₀ _ hNF]

/- English proof (translation)
Use `Set.indicator_of_mem (fun i => ⟨0, h0, ?_⟩) _` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem indN_zero (gf : Matrix ι ι (A F)) (n : ℕ) (h0 : (0 : A F) ∈ Oh F) : indN gf n 0 = 1 := by
  refine Set.indicator_of_mem (fun i => ⟨0, h0, ?_⟩) _
  simp

/- English proof (translation)
Establish `hu : IsUnit gf.det` using `isUnit_det_of_orth gf (Bf B) hO.1 (isUnit_det_Bf B hQ.2.2.2.1)`. Establish `h0 : (0 : A F) ∈ Oh F` using `fun v => zero_mem _`. Establish `hbound` using `summable_thTerm hQ hO hτ (sb_indN hu one_pos)`. Establish `hlim : Filter.Tendsto (fun n : ℕ => theta B ρ P gf gi (indN gf (n + 1)) τ) Filter.atTop (𝓝 (∑' x : ι → F, if x = 0 then (1 : ℂ) else 0))`. Use `tendsto_tsum_of_dominated_convergence hbound (fun x => ?_) (.of_forall fun n x => ?_)` and prove the remaining obligations.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `: ∀ n : ℕ, thTerm B ρ P gf gi (indN gf (n + 1)) τ 0 = 1`. Introduce `n`. Establish `e1 : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0`.

Simplify using the standard rewrite rules. Conclude with `Matrix.mulVec_zero _`. Establish `e2 : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0` using `fun w => by`. Establish `: (fun j => ρ w ((0 : ι → F) j)) = 0`. Use extensionality with `j`.

Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.mulVec_zero]`. Rewrite using `[thTerm, e1, indN_zero gf _ h0]`. Simplify using `only [e2]`. Simplify using `[gauss]`.

Simplify using `only [this, if_true]`. Conclude with `tendsto_const_nhds`. Rewrite using `[if_neg hx]`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [indN_eventually_zero hu hx] with n hn`.

Rewrite using `[thTerm, hn, zero_mul]`. Rewrite using `[thTerm, thTerm, norm_mul, norm_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Distinguish the cases in `hm : (gf *ᵥ fun j => algebraMap F (A F) (x j)) ∈ vecN gf (n + 1)`. Rewrite using `[indN, indN, Set.indicator_of_mem hm, Set.indicator_of_mem (vecN_subset gf _ hm)]`.

Rewrite using `[indN, Set.indicator_of_notMem hm]`. Simplify using the standard rewrite rules. Rewrite `hlim` using `[tsum_ite_eq]`. Take `⟨n, hn⟩` from `(hlim.eventually_ne one_ne_zero).exists`. Conclude with `⟨_, sb_indN hu n.succ_pos, hn⟩`.
-/
theorem exists_theta_ne_zero {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P) {gf : Matrix ι ι (A F)}
    {gi : InfinitePlace F → Matrix ι ι ℝ} (hO : IsOrth B ρ gf gi) {τ : InfinitePlace F → ℂ}
    (hτ : ∀ w, 0 < (τ w).im) : ∃ φ : (ι → A F) → ℂ, SB φ ∧ theta B ρ P gf gi φ τ ≠ 0 := by
  classical
  have hu : IsUnit gf.det := isUnit_det_of_orth gf (Bf B) hO.1 (isUnit_det_Bf B hQ.2.2.2.1)
  have h0 : (0 : A F) ∈ Oh F := fun v => zero_mem _
  have hbound := summable_thTerm hQ hO hτ (sb_indN hu one_pos)
  have hlim : Filter.Tendsto (fun n : ℕ => theta B ρ P gf gi (indN gf (n + 1)) τ) Filter.atTop
      (𝓝 (∑' x : ι → F, if x = 0 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun x => ?_) (.of_forall fun n x => ?_)
    · by_cases hx : x = 0
      · subst hx
        have : ∀ n : ℕ, thTerm B ρ P gf gi (indN gf (n + 1)) τ 0 = 1 := by
          intro n
          have e1 : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
            simp
            exact Matrix.mulVec_zero _
          have e2 : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0 := fun w => by
            have : (fun j => ρ w ((0 : ι → F) j)) = 0 := by
              ext j
              simp
            rw [this, Matrix.mulVec_zero]
          rw [thTerm, e1, indN_zero gf _ h0]
          simp only [e2]
          simp [gauss]
        simp only [this, if_true]
        exact tendsto_const_nhds
      · rw [if_neg hx]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [indN_eventually_zero hu hx] with n hn
        rw [thTerm, hn, zero_mul]
    · rw [thTerm, thTerm, norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      by_cases hm : (gf *ᵥ fun j => algebraMap F (A F) (x j)) ∈ vecN gf (n + 1)
      · rw [indN, indN, Set.indicator_of_mem hm, Set.indicator_of_mem (vecN_subset gf _ hm)]
      · rw [indN, Set.indicator_of_notMem hm]
        simp
  rw [tsum_ite_eq] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_ne one_ne_zero).exists
  exact ⟨_, sb_indN hu n.succ_pos, hn⟩

end Global

/- English proof (translation)
Introduce `F _ _ ι _ _ M B ρ P hQ gf gi hO τ hτ`. Conclude with `⟨fun φ hφ => summable_thTerm hQ hO hτ hφ, exists_theta_ne_zero hQ hO hτ⟩`.
-/
theorem theta_summable_and_ne_zero : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ φ : (ι → A F) → ℂ, SB φ → Summable fun x => ‖thTerm B ρ P gf gi φ τ x‖) ∧ ∃ φ : (ι → A F) → ℂ, SB φ ∧ theta B ρ P gf gi φ τ ≠ 0 := by
  intro F _ _ ι _ _ M B ρ P hQ gf gi hO τ hτ
  exact ⟨fun φ hφ => summable_thTerm hQ hO hτ hφ, exists_theta_ne_zero hQ hO hτ⟩

end GlobalTheory.CompanionTheory.SW.ThetaSum
