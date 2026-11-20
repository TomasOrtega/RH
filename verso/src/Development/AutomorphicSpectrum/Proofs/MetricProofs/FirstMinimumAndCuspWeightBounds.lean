import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open scoped MatrixOrder InnerProductSpace

/- English proof (translation)
Establish `h0 : 0 ≤ G` using `hG.nonneg`. Use `set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt G with hBdef`. Establish `hs : IsSelfAdjoint B` using `(CFC.sqrt_nonneg G).isSelfAdjoint`. Establish `hBt : Bᵀ = B`. Rewrite using `[← conjTranspose_eq_transpose_of_trivial]`.

Conclude with `hs.star_eq`. Establish `hGB : G = Bᵀ * B`. Rewrite using `[hBt]`. Conclude with `(CFC.sqrt_mul_sqrt_self G h0).symm`. Establish `hdB : B.det ≠ 0`.

Introduce `h0'`. Rewrite `hdet` using `[hGB, det_mul, det_transpose, h0']`. Simplify using `at hdet`. Set `a : Fin n → EuclideanSpace ℝ (Fin n)` to `fun i => WithLp.toLp 2 (fun k => B k i)`. Establish `hin : ∀ i j, ⟪a i, a j⟫_ℝ = G i j`.

Introduce `i j`. Rewrite using `[hGB, Matrix.mul_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[a, mul_comm]`. Establish `hli : LinearIndependent ℝ a`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hz : B *ᵥ c = 0`. Use function extensionality and compare the values at `k`. Use `congrArg (fun w : EuclideanSpace ℝ (Fin n) => w k) hc` as an intermediate fact.

Simplify `this` using `[a, Matrix.mulVec, dotProduct, mul_comm]`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdB hz` as an intermediate fact. Introduce `i`. Conclude with `congrFun this i`. Establish `hne : Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`.

Establish `hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))` using `by simp`. Set `bb : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hbb : ∀ i, bb i = a i` using `fun i => by simp [bb]`. Establish `hcov : ZLattice.covolume (Submodule.span ℤ (Set.range bb)) = √G.det`. Rewrite using `[GlobalTheory.covolume_span_basis_eq_sqrt_det_gram bb]`.

Use `congr 2`. Use extensionality with `i j`. Rewrite using `[Matrix.gram_apply, hbb, hbb, hin]`. Establish `hmink` using `GroundTheory.Heights₂.Heights.LowerBound.MinkowskiCovolumeBound.proof (EuclideanSpace ℝ (Fin n)) (by simpa using hn) (Submodule.span ℤ (Set.range bb))`. Establish `hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n` using `by simp`.

Rewrite `hmink` using `[hfin, hcov]`. Use `le_trans ?_ hmink` and prove the remaining obligations. Establish `hfm : lam ≤ GroundTheory.Heights₂.Heights.LowerBound.firstMinimum (Submodule.span ℤ (Set.range bb))`. Use `le_csInf ?_ ?_` and prove the remaining obligations. Use `⟨_, bb ⟨0, hn⟩, Submodule.subset_span ⟨_, rfl⟩, bb.ne_zero _, rfl⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨v, hv, hv0, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hv`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hv0`.

Establish `hq` using `h c hc`. Establish `hnorm : ‖∑ i, c i • bb i‖ ^ 2 = ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j`. Establish `e : ∑ i, c i • bb i = ∑ i, (c i : ℝ) • a i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hbb, Int.cast_smul_eq_zsmul]`.

Rewrite using `[e, ← real_inner_self_eq_norm_sq, sum_inner]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[real_inner_smul_left, real_inner_smul_right, hin]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hq` using `[← hnorm]`. Conclude with `(sq_le_sq₀ hlam (norm_nonneg _)).1 hq`. Use `gcongr`.
-/
theorem hermite_gram_minkowski {n : ℕ} (hn : 1 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hdet : 0 < G.det)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (h : ∀ c : Fin n → ℤ, c ≠ 0 → lam ^ 2 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j) :
    (lam / √(n : ℝ)) ^ n ≤ √G.det := by
  have h0 : 0 ≤ G := hG.nonneg
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt G with hBdef
  have hs : IsSelfAdjoint B := (CFC.sqrt_nonneg G).isSelfAdjoint
  have hBt : Bᵀ = B := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hs.star_eq
  have hGB : G = Bᵀ * B := by
    rw [hBt]; exact (CFC.sqrt_mul_sqrt_self G h0).symm
  have hdB : B.det ≠ 0 := by
    intro h0'
    rw [hGB, det_mul, det_transpose, h0'] at hdet
    simp at hdet
  let a : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (fun k => B k i)
  have hin : ∀ i j, ⟪a i, a j⟫_ℝ = G i j := by
    intro i j
    rw [hGB, Matrix.mul_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [a, mul_comm]
  have hli : LinearIndependent ℝ a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hz : B *ᵥ c = 0 := by
      funext k
      have := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w k) hc
      simpa [a, Matrix.mulVec, dotProduct, mul_comm] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero hdB hz
    intro i
    exact congrFun this i
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let bb : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ∀ i, bb i = a i := fun i => by simp [bb]
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range bb)) = √G.det := by
    rw [GlobalTheory.covolume_span_basis_eq_sqrt_det_gram bb]
    congr 2
    ext i j
    rw [Matrix.gram_apply, hbb, hbb, hin]
  have hmink := GroundTheory.Heights₂.Heights.LowerBound.MinkowskiCovolumeBound.proof (EuclideanSpace ℝ (Fin n))
    (by simpa using hn) (Submodule.span ℤ (Set.range bb))
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [hfin, hcov] at hmink
  refine le_trans ?_ hmink
  have hfm : lam ≤ GroundTheory.Heights₂.Heights.LowerBound.firstMinimum (Submodule.span ℤ (Set.range bb)) := by
    refine le_csInf ?_ ?_
    · refine ⟨_, bb ⟨0, hn⟩, Submodule.subset_span ⟨_, rfl⟩, bb.ne_zero _, rfl⟩
    · rintro x ⟨v, hv, hv0, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
      have hc : c ≠ 0 := by
        rintro rfl
        simp at hv0
      have hq := h c hc
      have hnorm : ‖∑ i, c i • bb i‖ ^ 2 = ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
        have e : ∑ i, c i • bb i = ∑ i, (c i : ℝ) • a i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hbb, Int.cast_smul_eq_zsmul]
        rw [e, ← real_inner_self_eq_norm_sq, sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_left, real_inner_smul_right, hin]
        ring
      rw [← hnorm] at hq
      exact (sq_le_sq₀ hlam (norm_nonneg _)).1 hq
  gcongr

namespace RiemLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] (R : RiemLat E g Λ)

/- English proof (translation)
Use `show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x`. Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]`.
-/
theorem conj_hermitianForm_symm (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[ip]`. Conclude with `(R.pos x hx).le`.
-/
theorem ip_self_re_nonneg (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [ip]
  · exact (R.pos x hx).le

def hermitianSemiInnerProductCore : PreInnerProductSpace.Core ℂ (Fin g → ℂ) where
  inner x y := R.ip x y
  conj_inner_symm x y := R.conj_hermitianForm_symm x y
  re_inner_nonneg x := R.ip_self_re_nonneg x
  add_left x y z := by simp [ip, star_add, mulVec_add, dotProduct_add]
  smul_left x y r := by simp [ip, star_smul, mulVec_smul, dotProduct_smul]

def realPartBilinForm : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun x y => (R.ip x y).re)
    (fun x y z => by simp [ip, star_add, mulVec_add, dotProduct_add])
    (fun c x y => by
      have : star (c • x) = c • star x := by
        funext i; simp
      simp [ip, this, mulVec_smul, dotProduct_smul])
    (fun x y z => by simp [ip, add_dotProduct])
    (fun c x y => by simp [ip, smul_dotProduct])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reForm_apply_alt (x y : Fin g → ℂ) : R.realPartBilinForm x y = (R.ip x y).re := rfl

/- English proof (translation)
The claim follows from `R.ip_self_re_nonneg _`.
-/
theorem normSq_nonneg_bis (v : Λ) : 0 ≤ R.normSq v := R.ip_self_re_nonneg _

/- English proof (translation)
Use `letI := R.hermitianSemiInnerProductCore`. Establish `h` using `InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (R.P y) (R.P x)`. Establish `h1 : ‖R.ip (R.P x) (R.P y)‖ = ‖R.ip (R.P y) (R.P x)‖`. Rewrite using `[← R.conj_hermitianForm_symm (R.P x) (R.P y), RCLike.norm_conj]`. Establish `him : (R.ip (R.P y) (R.P x)).im = R.form x y` using `R.im x y`.

Establish `h2 : |((R.form x y : ℤ) : ℝ)| ≤ ‖R.ip (R.P y) (R.P x)‖`. Rewrite using `[← him]`. Conclude with `Complex.abs_im_le_norm _`. Establish `h3 : ‖R.ip (R.P y) (R.P x)‖ * ‖R.ip (R.P x) (R.P y)‖ ≤ R.normSq y * R.normSq x` using `h`. Rewrite `h3` using `[h1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem integral_form_sq_le_mul_normSq (x y : Λ) : ((R.form x y : ℤ) : ℝ) ^ 2 ≤ R.normSq x * R.normSq y := by
  letI := R.hermitianSemiInnerProductCore
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (R.P y) (R.P x)
  have h1 : ‖R.ip (R.P x) (R.P y)‖ = ‖R.ip (R.P y) (R.P x)‖ := by
    rw [← R.conj_hermitianForm_symm (R.P x) (R.P y), RCLike.norm_conj]
  have him : (R.ip (R.P y) (R.P x)).im = R.form x y := R.im x y
  have h2 : |((R.form x y : ℤ) : ℝ)| ≤ ‖R.ip (R.P y) (R.P x)‖ := by
    rw [← him]; exact Complex.abs_im_le_norm _
  have h3 : ‖R.ip (R.P y) (R.P x)‖ * ‖R.ip (R.P x) (R.P y)‖ ≤ R.normSq y * R.normSq x := h
  rw [h1] at h3
  calc ((R.form x y : ℤ) : ℝ) ^ 2 = |((R.form x y : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ ‖R.ip (R.P y) (R.P x)‖ ^ 2 := by gcongr
    _ ≤ R.normSq x * R.normSq y := by nlinarith

/- English proof (translation)
Use `haveI := R.free`. Use `haveI := R.fin`. Set `e` to `Module.finBasis ℤ Λ`. Use `set S : ℝ := 1 + ∑ i, √(R.normSq (e i)) with hS`. Establish `hS0 : 0 < S`.

Establish `: 0 ≤ ∑ i, √(R.normSq (e i))` using `Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨1 / S, by positivity, fun v hv => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, R.form v (e i) ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `hv` to reduce the goal to its premises. Apply `R.unimod.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `e.ext (by simpa using hall)`.

Establish `h1 : (1 : ℝ) ≤ ((R.form v (e i) : ℤ) : ℝ) ^ 2`. Establish `: (1 : ℤ) ≤ (R.form v (e i)) ^ 2`. Use `Int.one_le_abs hi` as an intermediate fact. Use polynomial arithmetic with `[sq_abs (R.form v (e i))]`. Conclude with `this` after adjusting the coercions.

Establish `h2` using `h1.trans (R.integral_form_sq_le_mul_normSq v (e i))`. Establish `h3 : √(R.normSq (e i)) ≤ S`. Establish `: √(R.normSq (e i)) ≤ ∑ j, √(R.normSq (e j))` using `Finset.single_le_sum (f := fun j => √(R.normSq (e j))) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ i)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (1 : ℝ) ≤ √(R.normSq v) * √(R.normSq (e i))`.

Rewrite using `[← Real.sqrt_mul (R.normSq_nonneg_bis v)]`. Conclude with `Real.one_le_sqrt.2 h2`. Rewrite using `[div_le_iff₀ hS0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pos_le_sqrt_normSq : ∃ c : ℝ, 0 < c ∧ ∀ v : Λ, v ≠ 0 → c ≤ √(R.normSq v) := by
  haveI := R.free
  haveI := R.fin
  let e := Module.finBasis ℤ Λ
  set S : ℝ := 1 + ∑ i, √(R.normSq (e i)) with hS
  have hS0 : 0 < S := by
    have : 0 ≤ ∑ i, √(R.normSq (e i)) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    linarith
  refine ⟨1 / S, by positivity, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, R.form v (e i) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hv
    apply R.unimod.1
    rw [map_zero]
    exact e.ext (by simpa using hall)
  have h1 : (1 : ℝ) ≤ ((R.form v (e i) : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (R.form v (e i)) ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (R.form v (e i))]
    exact_mod_cast this
  have h2 := h1.trans (R.integral_form_sq_le_mul_normSq v (e i))
  have h3 : √(R.normSq (e i)) ≤ S := by
    have : √(R.normSq (e i)) ≤ ∑ j, √(R.normSq (e j)) :=
      Finset.single_le_sum (f := fun j => √(R.normSq (e j))) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
    linarith
  have h4 : (1 : ℝ) ≤ √(R.normSq v) * √(R.normSq (e i)) := by
    rw [← Real.sqrt_mul (R.normSq_nonneg_bis v)]
    exact Real.one_le_sqrt.2 h2
  rw [div_le_iff₀ hS0]
  calc (1 : ℝ) ≤ √(R.normSq v) * √(R.normSq (e i)) := h4
    _ ≤ √(R.normSq v) * S := by gcongr

/- English proof (translation)
The claim follows from `csInf_le ⟨0, by rintro x ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, hv, rfl⟩`.
-/
theorem lam1_le_alt (v : Λ) (hv : v ≠ 0) : R.lam1 ≤ √(R.normSq v) :=
  csInf_le ⟨0, by rintro x ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, hv, rfl⟩

/- English proof (translation)
Take `⟨c, hc, h⟩` from `R.exists_pos_le_sqrt_normSq`. Take `⟨v, hv⟩` from `exists_ne (0 : Λ)`. Use `hc.trans_le (le_csInf ⟨_, v, hv, rfl⟩ ?_)` and prove the remaining obligations. Introduce and unpack `x ⟨w, hw, rfl⟩`. Conclude with `h w hw`.
-/
theorem firstMinimum_pos_ter [Nontrivial Λ] : 0 < R.lam1 := by
  obtain ⟨c, hc, h⟩ := R.exists_pos_le_sqrt_normSq
  obtain ⟨v, hv⟩ := exists_ne (0 : Λ)
  refine hc.trans_le (le_csInf ⟨_, v, hv, rfl⟩ ?_)
  rintro x ⟨w, hw, rfl⟩
  exact h w hw

/- English proof (translation)
Use `PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, of_apply, star_trivial]`. Rewrite using `[← R.conj_hermitianForm_symm (u i) (u j), Complex.conj_re]`. Establish `h` using `R.ip_self_re_nonneg (∑ i, x i • u i)`.

Establish `e : (R.ip (∑ i, x i • u i) (∑ i, x i • u i)).re = star x ⬝ᵥ (Matrix.of fun i j => (R.ip (u i) (u j)).re) *ᵥ x`. Rewrite using `[← reForm_apply_alt]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, reForm_apply_alt]`. Simplify using `[dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem gram_re_posSemidef {n : ℕ} (u : Fin n → Fin g → ℂ) :
    (Matrix.of fun i j => (R.ip (u i) (u j)).re).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [conjTranspose_apply, of_apply, star_trivial]
    rw [← R.conj_hermitianForm_symm (u i) (u j), Complex.conj_re]
  · have h := R.ip_self_re_nonneg (∑ i, x i • u i)
    have e : (R.ip (∑ i, x i • u i) (∑ i, x i • u i)).re =
        star x ⬝ᵥ (Matrix.of fun i j => (R.ip (u i) (u j)).re) *ᵥ x := by
      rw [← reForm_apply_alt]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, reForm_apply_alt]
      simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [e] at h

/- English proof (translation)
Unfold `eigComp`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `zero_mem _`.
-/
theorem eigComp_mem_alt (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    eigComp ρ s x ∈ eigSp ρ s := by
  unfold eigComp
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem _

/- English proof (translation)
Establish `hli` using `(GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Ψ R I hI (σ τ)).2 r v hv.2.1 hv.2.2.1`. Set `w : Fin r → eigSp R.B (σ τ)` to `fun a => ⟨eigComp R.B (σ τ) (R.P (v a)), eigComp_mem_alt _ _ _⟩`. Establish `hw : LinearIndependent ℂ w` using `LinearIndependent.of_comp (eigSp R.B (σ τ)).subtype hli`. Use `hw.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[hm τ]`.

Simplify using `using this`.
-/
theorem card_le_of_isNzFamily {σ : Ψ → (𝓞 E →+* ℂ)} {m : ℕ} (hm : R.HasRank σ m) (τ : Ψ)
    {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) {r : ℕ} {v : Fin r → Λ} (hv : IsNzFamily I r v) : r ≤ m := by
  have hli := (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Ψ R I hI (σ τ)).2 r v hv.2.1 hv.2.2.1
  let w : Fin r → eigSp R.B (σ τ) := fun a => ⟨eigComp R.B (σ τ) (R.P (v a)), eigComp_mem_alt _ _ _⟩
  have hw : LinearIndependent ℂ w := LinearIndependent.of_comp (eigSp R.B (σ τ)).subtype hli
  have := hw.fintype_card_le_finrank
  rw [hm τ] at this
  simpa using this

include R in

/- English proof (translation)
Use `haveI := R.free`. Use `haveI := R.fin`. Establish `hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap)` using `Subtype.val_injective`. Use `haveI hfin : Module.Finite ℤ I := Module.Finite.of_injective _ hinj`. Use `haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)`.

Conclude with `⟨Module.free_of_finite_type_torsion_free', hfin⟩`.
-/
theorem free_finite_submodule (I : Submodule (𝓞 E) Λ) : Module.Free ℤ I ∧ Module.Finite ℤ I := by
  haveI := R.free
  haveI := R.fin
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI hfin : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

/- English proof (translation)
Take `⟨⟨r, v, hv⟩, hall⟩` from `GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hI0`. Take `⟨-, hN, hr⟩` from `hall r v hv`. Establish `hrm : r ≤ m` using `R.card_le_of_isNzFamily hm τ hI hv`. Use `⟨?_, hr ▸ hrm⟩` and prove the remaining obligations. Take `⟨hfree, hfinI⟩` from `R.free_finite_submodule I`.

Use `set rd : ℝ := |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) with hrd`. Establish `hrd1 : 1 ≤ rd`. Use `Real.one_le_rpow ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs (discr_ne_zero E)` after adjusting the coercions.

Set `b` to `Module.finBasis ℤ I`. Use `set n := Module.finrank ℤ I with hndef`. Take `⟨hn, hdet⟩` from `GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ R σ I hσ hI hI0 n b`. Use `set f := Fintype.card Ψ with hf`. Establish `hf1 : 1 ≤ f` using `Fintype.card_pos_iff.2 ⟨τ⟩`.

Establish `hr1 : 1 ≤ r` using `hv.1`. Rewrite `hn`, `hdet` using `[← hr]`. Use `set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re with hG`. Establish `hpos : 0 < R.nz σ I * rd ^ (f * r)` using `by positivity`. Establish `hdet0 : 0 < G.det` using `by rw [hdet]; positivity`.

Establish `hn1 : 1 ≤ n`. Rewrite using `[hn]`. Use polynomial arithmetic with `[Nat.mul_le_mul hf1 hr1]`. Establish `hmink` using `hermite_gram_minkowski hn1 G (R.gram_re_posSemidef _) hdet0 R.lam1 hlam.le (by`. Introduce `c hc`.

Use `set w : Λ := ∑ i, c i • (b i : Λ) with hw`. Establish `hw0 : w ≠ 0`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Establish `h1 : ∑ i, c i • b i = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `h0` using `[hw]`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent c h1 i`. Establish `h1` using `R.lam1_le_alt w hw0`.

Establish `h2 : R.lam1 ^ 2 ≤ R.normSq w`. Use `pow_le_pow_left₀ hlam.le h1 2` as an intermediate fact. Rewrite `this` using `[Real.sq_sqrt (R.normSq_nonneg_bis w)]`. Then use the resulting hypothesis. Establish `h3 : R.P w = ∑ i, (c i : ℝ) • R.P (b i : Λ)`. Rewrite using `[hw, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Establish `h4 : R.normSq w = ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j` using `by show (R.ip (R.P w) (R.P w)).re = _`. Rewrite using `[h3, ← reForm_apply_alt]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, reForm_apply_alt]`.

Simplify using `only [smul_eq_mul, Finset.mul_sum, hG, of_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[h4] at h2)` and apply the resulting hypothesis. Rewrite `hmink` using `[hdet, Real.sqrt_sq hpos.le]`.

Establish `hcast : (n : ℝ) = 2 * f * r` using `by rw [hn]; push_cast; ring`. Rewrite `hmink` using `[hcast]`. Rewrite `hmink` using `[hn]`. Use `GroundTheory.Heights₂.Heights.LowerBound.CuspWeightBound.proof f m r rd R.lam1 (R.nz σ I) _ { one_le_f := hf1 one_le_j' := hm1 one_le_ρ := hr1 ρ_le_j' := hrm one_le_rd := hrd1 lam_pos := hlam NI_pos := hN covol_pos := hpos covol_eq := rfl minkowski := hmink }` as an intermediate fact. Conclude with `this`.
-/
theorem neg_log_covolume_le {σ : Ψ → (𝓞 E →+* ℂ)} {m : ℕ} (hσ : IsCMFam σ) (hm : R.HasRank σ m) (hm1 : 1 ≤ m) (τ : Ψ)
    (hlam : 0 < R.lam1) {I : Submodule (𝓞 E) Λ} (hI : IsIsoSub R.form I) (hI0 : I ≠ ⊥) :
    -Real.log (R.nz σ I) ≤ Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) +
        Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) ∧
      Module.finrank (𝓞 E) I ≤ m := by
  obtain ⟨⟨r, v, hv⟩, hall⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hI0
  obtain ⟨-, hN, hr⟩ := hall r v hv
  have hrm : r ≤ m := R.card_le_of_isNzFamily hm τ hI hv
  refine ⟨?_, hr ▸ hrm⟩
  obtain ⟨hfree, hfinI⟩ := R.free_finite_submodule I
  set rd : ℝ := |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) with hrd
  have hrd1 : 1 ≤ rd := by
    refine Real.one_le_rpow ?_ (by positivity)
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  let b := Module.finBasis ℤ I
  set n := Module.finrank ℤ I with hndef
  obtain ⟨hn, hdet⟩ := GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ R σ I hσ hI hI0 n b
  set f := Fintype.card Ψ with hf
  have hf1 : 1 ≤ f := Fintype.card_pos_iff.2 ⟨τ⟩
  have hr1 : 1 ≤ r := hv.1
  rw [← hr] at hn hdet
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re with hG
  have hpos : 0 < R.nz σ I * rd ^ (f * r) := by positivity
  have hdet0 : 0 < G.det := by rw [hdet]; positivity
  have hn1 : 1 ≤ n := by
    rw [hn]; nlinarith [Nat.mul_le_mul hf1 hr1]
  have hmink := hermite_gram_minkowski hn1 G (R.gram_re_posSemidef _) hdet0 R.lam1 hlam.le (by
    intro c hc
    set w : Λ := ∑ i, c i • (b i : Λ) with hw
    have hw0 : w ≠ 0 := by
      intro h0
      apply hc
      have h1 : ∑ i, c i • b i = 0 := by
        apply Subtype.ext
        simpa [hw] using h0
      funext i
      exact Fintype.linearIndependent_iff.1 b.linearIndependent c h1 i
    have h1 := R.lam1_le_alt w hw0
    have h2 : R.lam1 ^ 2 ≤ R.normSq w := by
      have := pow_le_pow_left₀ hlam.le h1 2
      rwa [Real.sq_sqrt (R.normSq_nonneg_bis w)] at this
    have h3 : R.P w = ∑ i, (c i : ℝ) • R.P (b i : Λ) := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
    have h4 : R.normSq w = ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
      show (R.ip (R.P w) (R.P w)).re = _
      rw [h3, ← reForm_apply_alt]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, reForm_apply_alt]
      simp only [smul_eq_mul, Finset.mul_sum, hG, of_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [h4] at h2)
  rw [hdet, Real.sqrt_sq hpos.le] at hmink
  have hcast : (n : ℝ) = 2 * f * r := by rw [hn]; push_cast; ring
  rw [hcast] at hmink
  rw [hn] at hmink
  have := GroundTheory.Heights₂.Heights.LowerBound.CuspWeightBound.proof f m r rd R.lam1 (R.nz σ I) _
    { one_le_f := hf1
      one_le_j' := hm1
      one_le_ρ := hr1
      ρ_le_j' := hrm
      one_le_rd := hrd1
      lam_pos := hlam
      NI_pos := hN
      covol_pos := hpos
      covol_eq := rfl
      minkowski := hmink }
  exact this

end RiemLat

open RiemLat in

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ Ψ _ R σ m hσ hm hm1`. Choose the witnesses or unpack the hypotheses as in `⟨τ⟩ : Nonempty Ψ := by`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `Fintype.card_pos_iff.mp (by rw [Embeddings.card]; exact Module.finrank_pos)`. Assume the negation of the conclusion as `hΨ`. Rewrite `hΨ` using `[not_nonempty_iff]`.

Establish `h` using `hσ.2 (φ.comp (algebraMap (𝓞 E) E))`. Simplify using `only [IsEmpty.exists_iff, not_false_eq_true, iff_true] at h`. Establish `hg : g ≠ 0`. Introduce and unpack `rfl`. Establish `h` using `hm τ`.

Rewrite `h` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers. Use `haveI : Nontrivial Λ := by haveI := R.free haveI := R.fin`. Conclude with `Module.nontrivial_of_finrank_pos (R := ℤ) (by rw [R.rank]; omega)`. Establish `hlam` using `R.firstMinimum_pos_ter`.

Use `set bound : ℝ := Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) with hbound`. Establish `hterm : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}, x ≤ bound`. Introduce and unpack `x ⟨I, hI, rfl⟩`. Conclude with `(R.neg_log_covolume_le hσ hm hm1 τ hlam hI.2.2 hI.1).1`. Establish `hbdd : BddAbove {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}` using `⟨bound, hterm⟩`.

Establish `hb0 : 0 ≤ bound`. Establish `hrd1 : 1 ≤ |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))`. Use `Real.one_le_rpow ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs (discr_ne_zero E)` after adjusting the coercions.

Establish `hf1 : (1 : ℝ) ≤ Fintype.card Ψ`. Conclude with `Fintype.card_pos_iff.2 ⟨τ⟩` after adjusting the coercions. Establish `hm1' : (1 : ℝ) ≤ m` using `by exact_mod_cast hm1`. Establish `h1 : 0 ≤ Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))`. Use `Real.log_nonneg ?_` and prove the remaining obligations.

Establish `h2 : (1 : ℝ) ≤ Fintype.card Ψ * m` using `one_le_mul_of_one_le_of_one_le hf1 hm1'`. Establish `h3` using `one_le_mul_of_one_le_of_one_le h2 hrd1`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : 0 ≤ max 0 (Real.log (1 / R.lam1))` using `le_max_left _ _`. Rewrite using `[hbound]`.

Check the signs of the components of the expression. Use `⟨hlam, R.lam1_le_alt, fun I hI => ⟨?_, (R.neg_log_covolume_le hσ hm hm1 τ hlam hI.2.2 hI.1).2⟩, le_max_left _ _, ?_⟩` and prove the remaining obligations. Conclude with `(le_csSup hbdd ⟨I, hI, rfl⟩).trans (le_max_right _ _)`. Use `max_le hb0 ?_` and prove the remaining obligations. Distinguish the cases in `hne : {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}.Nonempty`.

Conclude with `csSup_le hne hterm`. Rewrite using `[Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]`. Conclude with `hb0`.
-/
theorem cuspW_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsCMFam σ → R.HasRank σ m → 1 ≤ m → 0 < R.lam1 ∧ (∀ v : Λ, v ≠ 0 → R.lam1 ≤ Real.sqrt (R.normSq v)) ∧ (∀ I, R.IsCusp I → -Real.log (R.nz σ I) ≤ R.cuspW σ ∧ Module.finrank (𝓞 E) I ≤ m) ∧ 0 ≤ R.cuspW σ ∧ R.cuspW σ ≤ Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ m hσ hm hm1
  obtain ⟨τ⟩ : Nonempty Ψ := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := Fintype.card_pos_iff.mp (by rw [Embeddings.card]; exact Module.finrank_pos)
    by_contra hΨ
    rw [not_nonempty_iff] at hΨ
    have h := hσ.2 (φ.comp (algebraMap (𝓞 E) E))
    simp only [IsEmpty.exists_iff, not_false_eq_true, iff_true] at h
  have hg : g ≠ 0 := by
    rintro rfl
    have h := hm τ
    rw [Module.finrank_zero_of_subsingleton] at h
    omega
  haveI : Nontrivial Λ := by
    haveI := R.free
    haveI := R.fin
    exact Module.nontrivial_of_finrank_pos (R := ℤ) (by rw [R.rank]; omega)
  have hlam := R.firstMinimum_pos_ter
  set bound : ℝ := Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) with hbound
  have hterm : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}, x ≤ bound := by
    rintro x ⟨I, hI, rfl⟩
    exact (R.neg_log_covolume_le hσ hm hm1 τ hlam hI.2.2 hI.1).1
  have hbdd : BddAbove {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)} := ⟨bound, hterm⟩
  have hb0 : 0 ≤ bound := by
    have hrd1 : 1 ≤ |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := by
      refine Real.one_le_rpow ?_ (by positivity)
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (discr_ne_zero E)
    have hf1 : (1 : ℝ) ≤ Fintype.card Ψ := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨τ⟩
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h1 : 0 ≤ Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) := by
      refine Real.log_nonneg ?_
      have h2 : (1 : ℝ) ≤ Fintype.card Ψ * m := one_le_mul_of_one_le_of_one_le hf1 hm1'
      have h3 := one_le_mul_of_one_le_of_one_le h2 hrd1
      nlinarith
    have h4 : 0 ≤ max 0 (Real.log (1 / R.lam1)) := le_max_left _ _
    rw [hbound]
    positivity
  refine ⟨hlam, R.lam1_le_alt, fun I hI => ⟨?_, (R.neg_log_covolume_le hσ hm hm1 τ hlam hI.2.2 hI.1).2⟩, le_max_left _ _, ?_⟩
  · exact (le_csSup hbdd ⟨I, hI, rfl⟩).trans (le_max_right _ _)
  · refine max_le hb0 ?_
    by_cases hne : {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}.Nonempty
    · exact csSup_le hne hterm
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]
      exact hb0

end GlobalTheory.CompanionTheory.Ar.Cusp
