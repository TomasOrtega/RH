import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.EuclideanAtlasPointwiseNormSqUnitSection
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply

namespace GlobalTheory.L2Kaehler

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

variable {n : ℕ}

def herm (H : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H j k * ξ j * (starRingEnd ℂ) (ξ k)).re

def pairBar (v ξ : Fin n → ℂ) : ℂ := ∑ k, v k * (starRingEnd ℂ) (ξ k)

def coNormSq (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H⁻¹ j k * v j * (starRingEnd ℂ) (v k)).re

/- English proof (translation)
Simplify using `only [herm, star_star, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by`. Rewrite using `[Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_eq (H : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) :
    herm H ξ = (star (star ξ) ⬝ᵥ H *ᵥ star ξ).re := by
  simp only [herm, star_star, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    rw [Complex.conj_conj]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coNormSq_eq_herm (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    coNormSq H v = herm H⁻¹ v := rfl

/- English proof (translation)
Rewrite using `[herm_eq]`. Conclude with `hH.posSemidef.re_dotProduct_nonneg _`.
-/
theorem herm_nonneg {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (ξ : Fin n → ℂ) :
    0 ≤ herm H ξ := by
  rw [herm_eq]; exact hH.posSemidef.re_dotProduct_nonneg _

/- English proof (translation)
The claim follows from `herm_nonneg hH.inv v`.
-/
theorem coNormSq_nonneg {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (v : Fin n → ℂ) :
    0 ≤ coNormSq H v := herm_nonneg hH.inv v

/- English proof (translation)
Simplify using `[herm, Matrix.one_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]`.
-/
theorem herm_one (ξ : Fin n → ℂ) : herm 1 ξ = ∑ k, ‖ξ k‖ ^ 2 := by
  simp [herm, Matrix.one_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

/- English proof (translation)
Rewrite using `[coNormSq_eq_herm, inv_one, herm_one]`.
-/
theorem coNormSq_one (v : Fin n → ℂ) : coNormSq 1 v = ∑ k, ‖v k‖ ^ 2 := by
  rw [coNormSq_eq_herm, inv_one, herm_one]

/- English proof (translation)
Establish `hu : IsUnit H.det` using `(Matrix.isUnit_iff_isUnit_det H).1 hH.isUnit`. Establish `h1 : ∀ x, star (H⁻¹ *ᵥ star v) ⬝ᵥ H *ᵥ x = v ⬝ᵥ x` using `fun x => by`. Rewrite using `[Matrix.star_mulVec, star_star, hH.inv.isHermitian.eq, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Establish `h2 : ∀ ξ, pairBar v ξ = v ⬝ᵥ star ξ` using `fun ξ => rfl`. Use `⟨fun ξ => by rw [h1, h2], ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[herm_eq, star_star, star_star, h1, coNormSq_eq_herm, herm_eq, star_star]`. Rewrite using `[h2, star_star, coNormSq_eq_herm, herm_eq]`. Use `(hH.inv.posSemidef.dotProduct_mulVec_nonneg (star v))` as an intermediate fact. Rewrite `this`, the goal using `[star_star]`. Conclude with `Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.1 this).2.symm)`.
-/
theorem dual_vector {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (v : Fin n → ℂ) :
    (∀ ξ, pairBar v ξ = star (H⁻¹ *ᵥ star v) ⬝ᵥ H *ᵥ star ξ) ∧
      coNormSq H v = herm H (star (H⁻¹ *ᵥ star v)) ∧
      pairBar v (star (H⁻¹ *ᵥ star v)) = (coNormSq H v : ℂ) := by
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).1 hH.isUnit
  have h1 : ∀ x, star (H⁻¹ *ᵥ star v) ⬝ᵥ H *ᵥ x = v ⬝ᵥ x := fun x => by
    rw [Matrix.star_mulVec, star_star, hH.inv.isHermitian.eq, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have h2 : ∀ ξ, pairBar v ξ = v ⬝ᵥ star ξ := fun ξ => rfl
  refine ⟨fun ξ => by rw [h1, h2], ?_, ?_⟩
  · rw [herm_eq, star_star, star_star, h1, coNormSq_eq_herm, herm_eq, star_star]
  · rw [h2, star_star, coNormSq_eq_herm, herm_eq]
    have := (hH.inv.posSemidef.dotProduct_mulVec_nonneg (star v))
    rw [star_star] at this ⊢
    exact Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.1 this).2.symm)

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `dual_vector hH v`. Set `c : PreInnerProductSpace.Core ℂ (Fin n → ℂ)` to `{ inner x y := star x ⬝ᵥ H *ᵥ y conj_inner_symm x y := by`. Rewrite using `[starRingEnd_apply, Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH.isHermitian.eq, ← Matrix.dotProduct_mulVec]`. Use `re_inner_nonneg x := hH.posSemidef.re_dotProduct_nonneg x`. Use `add_left := by simp only [star_add, add_dotProduct, forall_const]`.

Use `smul_left x y r := by simp [star_smul] }`. Use `@InnerProductSpace.Core.inner_mul_inner_self_le ℂ _ _ _ _ c (H⁻¹ *ᵥ star v) (star ξ)` as an intermediate fact. Establish `h3` using `@InnerProductSpace.Core.norm_inner_symm ℂ _ _ _ _ c (H⁻¹ *ᵥ star v) (star ξ)`. Rewrite `this` using `[← h3]`. Rewrite using `[h1, h2, herm_eq, herm_eq, star_star (H⁻¹ *ᵥ star v), sq]`.

Conclude with `this`.
-/
theorem norm_pairBar_sq_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (v ξ : Fin n → ℂ) :
    ‖pairBar v ξ‖ ^ 2 ≤ coNormSq H v * herm H ξ := by
  obtain ⟨h1, h2, -⟩ := dual_vector hH v
  let c : PreInnerProductSpace.Core ℂ (Fin n → ℂ) :=
    { inner x y := star x ⬝ᵥ H *ᵥ y
      conj_inner_symm x y := by
        rw [starRingEnd_apply, Matrix.star_dotProduct, star_star, Matrix.star_mulVec,
          hH.isHermitian.eq, ← Matrix.dotProduct_mulVec]
      re_inner_nonneg x := hH.posSemidef.re_dotProduct_nonneg x
      add_left := by simp only [star_add, add_dotProduct, forall_const]
      smul_left x y r := by simp [star_smul] }
  have := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ _ _ _ _ c (H⁻¹ *ᵥ star v) (star ξ)
  have h3 := @InnerProductSpace.Core.norm_inner_symm ℂ _ _ _ _ c (H⁻¹ *ᵥ star v) (star ξ)
  rw [← h3] at this
  rw [h1, h2, herm_eq, herm_eq, star_star (H⁻¹ *ᵥ star v), sq]
  exact this

/- English proof (translation)
Use `⟨fun hle ξ => (norm_pairBar_sq_le hH v ξ).trans (mul_le_mul_of_nonneg_right hle (herm_nonneg hH ξ)), fun hξ => ?_⟩` and prove the remaining obligations. Take `⟨-, h2, h3⟩` from `dual_vector hH v`. Use `hξ (star (H⁻¹ *ᵥ star v))` as an intermediate fact. Rewrite `this` using `[h3, ← h2, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `h0` using `coNormSq_nonneg hH v`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem coNormSq_le_iff {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (v : Fin n → ℂ) {h : ℝ}
    (hh : 0 ≤ h) : coNormSq H v ≤ h ↔ ∀ ξ, ‖pairBar v ξ‖ ^ 2 ≤ h * herm H ξ := by
  refine ⟨fun hle ξ => (norm_pairBar_sq_le hH v ξ).trans
    (mul_le_mul_of_nonneg_right hle (herm_nonneg hH ξ)), fun hξ => ?_⟩
  obtain ⟨-, h2, h3⟩ := dual_vector hH v
  have := hξ (star (H⁻¹ *ᵥ star v))
  rw [h3, ← h2, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  have h0 := coNormSq_nonneg hH v
  nlinarith

section Atlas

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def push (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y) (ξ : Fin n → ℂ) : Fin n → ℂ :=
  (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp

structure IsKaehler (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) :
    Prop where
  smooth : ∀ i j k, ContDiffOn ℝ ∞ (fun v => H i ((A.chart i).symm v) j k) (A.chart i).target
  posDef : ∀ i y, y ∈ (A.chart i).source → (H i y).PosDef
  trans : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
    herm (H i y) ξ = herm (H j y) (push A i j y ξ)
  closed : ∀ i, ∀ v ∈ (A.chart i).target, ∀ j k l,
    wd n l (fun w => H i ((A.chart i).symm w) j k) v =
      wd n j (fun w => H i ((A.chart i).symm w) l k) v

def IsC1Path (A : WeightedAtlas n Y ι La) (γ : ℝ → Y) : Prop :=
  ContinuousOn γ (Set.Icc 0 1) ∧
    ∀ i, ContDiffOn ℝ 1 (A.chart i ∘ γ) (Set.Icc 0 1 ∩ γ ⁻¹' (A.chart i).source)

def pathLength (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (γ : ℝ → Y) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt
    (herm (H (A.pick (γ t)) (γ t)) (deriv (A.chart (A.pick (γ t)) ∘ γ) t).ofLp))

def lengthDist (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (x y : Y) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Y) (_ : IsC1Path A γ) (_ : γ 0 = x) (_ : γ 1 = y), pathLength A H γ

def IsCauchySeq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (u : ℕ → Y) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ k ≥ N, lengthDist A H (u m) (u k) < ε

def IsComplete (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ u : ℕ → Y, IsCauchySeq A H u → ∃ x, MapClusterPt x atTop u

/- English proof (translation)
Introduce `u hu` and use `(h u hu).imp fun _ hx => hx.mapClusterPt`.
-/
theorem isComplete_of_tendsto (A : WeightedAtlas n Y ι La)
    (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ u : ℕ → Y, IsCauchySeq A H u → ∃ x, Tendsto u atTop (𝓝 x)) : IsComplete A H :=
  fun u hu => (h u hu).imp fun _ hx => hx.mapClusterPt

/- English proof (translation)
Introduce `u hu`. Take `⟨N, hN⟩` from `hu r hr`. Take `⟨K, hK, hb⟩` from `h (u N)`. Take `⟨x, -, hx⟩` from `hK.exists_mapClusterPt (f := atTop) (u := u) (le_principal_iff.2 (mem_map.2 (eventually_atTop.2 ⟨N, fun k hk => hb _ (hN N le_rfl k hk)⟩)))`. Conclude with `⟨x, hx⟩`.
-/
theorem isComplete_of_compact_balls (A : WeightedAtlas n Y ι La)
    (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) {r : ℝ≥0∞} (hr : 0 < r)
    (h : ∀ x, ∃ K, IsCompact K ∧ ∀ y, lengthDist A H x y < r → y ∈ K) : IsComplete A H := by
  intro u hu
  obtain ⟨N, hN⟩ := hu r hr
  obtain ⟨K, hK, hb⟩ := h (u N)
  obtain ⟨x, -, hx⟩ := hK.exists_mapClusterPt (f := atTop) (u := u)
    (le_principal_iff.2 (mem_map.2 (eventually_atTop.2 ⟨N, fun k hk => hb _ (hN N le_rfl k hk)⟩)))
  exact ⟨x, hx⟩

def IsForm (A : WeightedAtlas n Y ι La) (la : La) (v : ι → Y → Fin n → ℂ) : Prop :=
  (∀ i k, ContDiffOn ℝ ∞ (fun w => v i ((A.chart i).symm w) k) (A.chart i).target) ∧
    ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
      pairBar (v i y) ξ = A.g (A.kap + la) i j y * pairBar (v j y) (push A i j y ξ)

def IsDbarClosed (A : WeightedAtlas n Y ι La) (v : ι → Y → Fin n → ℂ) : Prop :=
  ∀ i, ∀ w ∈ (A.chart i).target, ∀ k l,
    wdb n l (fun x => v i ((A.chart i).symm x) k) w = wdb n k (fun x => v i ((A.chart i).symm x) l) w

def dbar (A : WeightedAtlas n Y ι La) (u : ι → Y → ℂ) : ι → Y → Fin n → ℂ :=
  fun i y k => wdb n k (u i ∘ (A.chart i).symm) (A.chart i y)

def formNsq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) (la : La)
    (v : ι → Y → Fin n → ℂ) (y : Y) : ℝ :=
  coNormSq (H (A.pick y) y) (v (A.pick y) y) * Real.exp (-A.ph (A.kap + la) (A.pick y) y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairBar_dbar (A : WeightedAtlas n Y ι La) (u : ι → Y → ℂ) (i : ι) (y : Y)
    (ξ : Fin n → ℂ) : pairBar (dbar A u i y) ξ = A.dbarAt i u y ξ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem herm_hessAt (A : WeightedAtlas n Y ι La) (i : ι) (f : Y → ℝ) (y : Y) (ξ : Fin n → ℂ) :
    herm (A.hessAt i f y) ξ = A.leviAt i f y ξ := rfl

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fderiv ℝ g) U` using `hg.fderiv_of_isOpen hU (by simp)`. Conclude with `((h1.clm_apply contDiffOn_const).sub (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2`.
-/
theorem contDiffOn_wd {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    (k : Fin n) : ContDiffOn ℝ ∞ (wd n k g) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
  exact ((h1.clm_apply contDiffOn_const).sub
    (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fderiv ℝ g) U` using `hg.fderiv_of_isOpen hU (by simp)`. Conclude with `((h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2`.
-/
theorem contDiffOn_wdb {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    (k : Fin n) : ContDiffOn ℝ ∞ (wdb n k g) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
  exact ((h1.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))).div_const 2

/- English proof (translation)
Use `set g : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg`. Establish `hg2 : ContDiffAt ℝ 2 g x` using `Complex.ofRealCLM.contDiff.contDiffAt.comp x hf`. Establish `hgc : (fun w => (starRingEnd ℂ) (g w)) = g` using `funext fun w => by simp [g]`. Establish `hH : (cHess n g x).IsHermitian`. Use extensionality with `j k`.

Simplify using `only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]`. Use `show (starRingEnd ℂ) (wd n k (wdb n j g) x) = wd n j (wdb n k g) x`. Establish `h1 : (fun w => (starRingEnd ℂ) (wdb n j g w)) = wd n j g`. Use function extensionality and compare the values at `w`. Rewrite using `[← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]`.

Rewrite using `[← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun y hy => ?_` and prove the remaining obligations. Establish `hre` using `herm_eq (cHess n g x) (star y)`. Simplify using `only [star_star] at hre`. Establish `him` using `hH.im_star_dotProduct_mulVec_self y`.

Use `Complex.lt_def.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hre]; exact hL _ (by simpa using hy)`. Simplify using `using him.symm`.
-/
theorem posDef_cHess {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosDef := by
  set g : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => (starRingEnd ℂ) (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => (starRingEnd ℂ) (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun y hy => ?_
  have hre := herm_eq (cHess n g x) (star y)
  simp only [star_star] at hre
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.lt_def.2 ⟨?_, ?_⟩
  · rw [← hre]; exact hL _ (by simpa using hy)
  · simpa using him.symm

/- English proof (translation)
Establish `hR : ∀ i, ContDiffOn ℝ ∞ (fun v => A.ph la i ((A.chart i).symm v) + f ((A.chart i).symm v)) (A.chart i).target` using `fun i => (A.smooth_ph la i).add (hf i)`. Use `set g : ι → V n → ℂ := fun i v => ((A.ph la i ((A.chart i).symm v) + f ((A.chart i).symm v) : ℝ) : ℂ) with hg`. Establish `hC : ∀ i, ContDiffOn ℝ ∞ (g i) (A.chart i).target` using `fun i => Complex.ofRealCLM.contDiff.comp_contDiffOn (hR i)`. Establish `hE : ∀ i j k, ∀ v ∈ (A.chart i).target, A.hessAt i (fun x => A.ph la i x + f x) ((A.chart i).symm v) j k = wd n j (wdb n k (g i)) v` using `fun i j k v hv => by`. Simplify using `only [WeightedAtlas.hessAt, cHess, Matrix.of_apply, (A.chart i).right_inv hv, hg]`.

Use `⟨fun i j k => ?_, fun i y hy => ?_, fun i j y hi hj ξ => ?_, fun i v hv j k l => ?_⟩` and prove the remaining obligations. Conclude with `(contDiffOn_wd (A.chart i).open_target (contDiffOn_wdb (A.chart i).open_target (hC i) k) j).congr (hE i j k)`. Conclude with `posDef_cHess (((hR i).contDiffAt ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hy))).of_le (by norm_cast)) (hpos i y hy)`. Conclude with `A.levi_transfer la f hf i j hi hj ξ`. Establish `hn` using `(A.chart i).open_target.mem_nhds hv`.

Rewrite using `[wd_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (hE i j k)), wd_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (hE i l k))]`. Conclude with `comm_wd_wd _ _ (((contDiffOn_wdb (A.chart i).open_target (hC i) k).contDiffAt hn).of_le (by norm_cast)) l j`.
-/
theorem isKaehler_hessAt (A : WeightedAtlas n Y ι La) (la : La) {f : Y → ℝ} (hf : A.SmoothFn f)
    (hpos : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (fun x => A.ph la i x + f x) y ξ) :
    IsKaehler A (fun i y => A.hessAt i (fun x => A.ph la i x + f x) y) := by
  have hR : ∀ i, ContDiffOn ℝ ∞ (fun v => A.ph la i ((A.chart i).symm v) + f ((A.chart i).symm v))
      (A.chart i).target := fun i => (A.smooth_ph la i).add (hf i)
  set g : ι → V n → ℂ := fun i v =>
    ((A.ph la i ((A.chart i).symm v) + f ((A.chart i).symm v) : ℝ) : ℂ) with hg
  have hC : ∀ i, ContDiffOn ℝ ∞ (g i) (A.chart i).target := fun i =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hR i)
  have hE : ∀ i j k, ∀ v ∈ (A.chart i).target,
      A.hessAt i (fun x => A.ph la i x + f x) ((A.chart i).symm v) j k =
        wd n j (wdb n k (g i)) v := fun i j k v hv => by
    simp only [WeightedAtlas.hessAt, cHess, Matrix.of_apply, (A.chart i).right_inv hv, hg]
  refine ⟨fun i j k => ?_, fun i y hy => ?_, fun i j y hi hj ξ => ?_, fun i v hv j k l => ?_⟩
  · exact (contDiffOn_wd (A.chart i).open_target
      (contDiffOn_wdb (A.chart i).open_target (hC i) k) j).congr (hE i j k)
  · exact posDef_cHess (((hR i).contDiffAt ((A.chart i).open_target.mem_nhds
      ((A.chart i).map_source hy))).of_le (by norm_cast)) (hpos i y hy)
  · exact A.levi_transfer la f hf i j hi hj ξ
  · have hn := (A.chart i).open_target.mem_nhds hv
    rw [wd_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (hE i j k)),
      wd_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (hE i l k))]
    exact comm_wd_wd _ _ (((contDiffOn_wdb (A.chart i).open_target (hC i) k).contDiffAt hn).of_le
      (by norm_cast)) l j

/- English proof (translation)
Introduce `w hw` and use `by simp only [dbar, (A.chart i).right_inv hw]`.
-/
theorem dbar_symm (A : WeightedAtlas n Y ι La) (u : ι → Y → ℂ) (i : ι) (k : Fin n) :
    ∀ w ∈ (A.chart i).target,
      dbar A u i ((A.chart i).symm w) k = wdb n k (u i ∘ (A.chart i).symm) w := fun w hw => by
  simp only [dbar, (A.chart i).right_inv hw]

/- English proof (translation)
Use `⟨fun i k => (contDiffOn_wdb (A.chart i).open_target (hu.1 i) k).congr (dbar_symm A u i k), fun i j y hi hj ξ => ?_⟩` and prove the remaining obligations. Use `set Φ := (A.chart j) ∘ (A.chart i).symm with hΦdef`. Establish `hv0` using `A.mem_ovl hi hj`. Establish `hO : ovl A.chart i j ∈ 𝓝 (A.chart i y)` using `(A.isOpen_ovl i j).mem_nhds hv0`. Establish `hΦ : DifferentiableAt ℂ Φ (A.chart i y)` using `(A.trans_contDiffAt hi hj).differentiableAt (by norm_num)`.

Establish `hΦv : Φ (A.chart i y) = A.chart j y` using `by simp [Φ, (A.chart i).left_inv hi]`. Use `set G := A.g (A.kap + la) i j ∘ (A.chart i).symm`. Establish `hG : DifferentiableAt ℂ G (A.chart i y)` using `(A.holo_g _ i j).differentiableAt hO`. Use `set β := u j ∘ (A.chart j).symm`. Establish `hβ : DifferentiableAt ℝ β (Φ (A.chart i y))`.

Rewrite using `[hΦv]`. Conclude with `((hu.1 j).contDiffAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).differentiableAt (by simp)`. Establish `hev : (u i ∘ (A.chart i).symm) =ᶠ[𝓝 (A.chart i y)] fun v => (β ∘ Φ) v * G v` using `by filter_upwards [hO] with v hv`. Establish `h2 : (A.chart i).symm v ∈ (A.chart j).source` using `hv.2`. Simplify using `only [Function.comp, β, G, Φ, (A.chart j).left_inv h2]`.

Rewrite using `[hu.2 i j _ ((A.chart i).map_target hv.1) h2, mul_comm]`. Rewrite using `[pairBar_dbar, pairBar_dbar, WeightedAtlas.dbarAt_eq, WeightedAtlas.dbarAt_eq, hev.fderiv_eq, fderiv_fun_mul (hβ.comp _ (hΦ.restrictScalars ℝ)) (hG.restrictScalars ℝ), dbv_add, dbv_smul, dbv_smul, dbv_holo hG, mul_zero, zero_add, dbv_comp hβ hΦ, hΦv]`. Simplify using `only [G, Function.comp, (A.chart i).left_inv hi, push, WithLp.toLp_ofLp]`. Both sides reduce to the same expression.
-/
theorem isForm_dbar (A : WeightedAtlas n Y ι La) {la : La} {u : ι → Y → ℂ}
    (hu : A.IsSSec (A.kap + la) u) : IsForm A la (dbar A u) := by
  refine ⟨fun i k => (contDiffOn_wdb (A.chart i).open_target (hu.1 i) k).congr
    (dbar_symm A u i k), fun i j y hi hj ξ => ?_⟩
  set Φ := (A.chart j) ∘ (A.chart i).symm with hΦdef
  have hv0 := A.mem_ovl hi hj
  have hO : ovl A.chart i j ∈ 𝓝 (A.chart i y) := (A.isOpen_ovl i j).mem_nhds hv0
  have hΦ : DifferentiableAt ℂ Φ (A.chart i y) :=
    (A.trans_contDiffAt hi hj).differentiableAt (by norm_num)
  have hΦv : Φ (A.chart i y) = A.chart j y := by simp [Φ, (A.chart i).left_inv hi]
  set G := A.g (A.kap + la) i j ∘ (A.chart i).symm
  have hG : DifferentiableAt ℂ G (A.chart i y) := (A.holo_g _ i j).differentiableAt hO
  set β := u j ∘ (A.chart j).symm
  have hβ : DifferentiableAt ℝ β (Φ (A.chart i y)) := by
    rw [hΦv]
    exact ((hu.1 j).contDiffAt ((A.chart j).open_target.mem_nhds
      ((A.chart j).map_source hj))).differentiableAt (by simp)
  have hev : (u i ∘ (A.chart i).symm) =ᶠ[𝓝 (A.chart i y)] fun v => (β ∘ Φ) v * G v := by
    filter_upwards [hO] with v hv
    have h2 : (A.chart i).symm v ∈ (A.chart j).source := hv.2
    simp only [Function.comp, β, G, Φ, (A.chart j).left_inv h2]
    rw [hu.2 i j _ ((A.chart i).map_target hv.1) h2, mul_comm]
  rw [pairBar_dbar, pairBar_dbar, WeightedAtlas.dbarAt_eq, WeightedAtlas.dbarAt_eq, hev.fderiv_eq,
    fderiv_fun_mul (hβ.comp _ (hΦ.restrictScalars ℝ)) (hG.restrictScalars ℝ), dbv_add, dbv_smul,
    dbv_smul, dbv_holo hG, mul_zero, zero_add, dbv_comp hβ hΦ, hΦv]
  simp only [G, Function.comp, (A.chart i).left_inv hi, push, WithLp.toLp_ofLp]
  rfl

/- English proof (translation)
Introduce `i w hw k l`. Establish `hn` using `(A.chart i).open_target.mem_nhds hw`. Rewrite using `[wdb_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (dbar_symm A u i k)), wdb_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (dbar_symm A u i l))]`. Conclude with `comm_wdb_wdb _ _ (((hu.1 i).contDiffAt hn).of_le (by norm_cast)) l k`.
-/
theorem isDbarClosed_dbar (A : WeightedAtlas n Y ι La) {la : La} {u : ι → Y → ℂ}
    (hu : A.IsSSec la u) : IsDbarClosed A (dbar A u) := by
  intro i w hw k l
  have hn := (A.chart i).open_target.mem_nhds hw
  rw [wdb_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (dbar_symm A u i k)),
    wdb_congr n _ _ _ _ (Filter.eventuallyEq_of_mem hn (dbar_symm A u i l))]
  exact comm_wdb_wdb _ _ (((hu.1 i).contDiffAt hn).of_le (by norm_cast)) l k

end Atlas

section Flat

open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds

/- English proof (translation)
Establish `: ((atlas n).chart () ∘ ((atlas n).chart ()).symm) = id` using `rfl`. Simplify using `[push, this]`.
-/
theorem push_flat (y : V n) (ξ : Fin n → ℂ) : push (atlas n) () () y ξ = ξ := by
  have : ((atlas n).chart () ∘ ((atlas n).chart ()).symm) = id := rfl
  simp [push, this]

/- English proof (translation)
The claim follows from `contDiffOn_const posDef _ _ _ := Matrix.PosDef.one trans _ _ y _ _ ξ := by rw [push_flat] closed _ _ _ _ _ _ := by simp [wd]`.
-/
theorem isKaehler_flat : IsKaehler (atlas n) (fun _ _ => 1) where
  smooth _ _ _ := contDiffOn_const
  posDef _ _ _ := Matrix.PosDef.one
  trans _ _ y _ _ ξ := by rw [push_flat]
  closed _ _ _ _ _ _ := by simp [wd]

/- English proof (translation)
Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[herm_one, ← ofReal_norm_eq_enorm, EuclideanSpace.norm_eq]`. Both sides reduce to the same expression.
-/
theorem pathLength_flat (γ : ℝ → V n) :
    pathLength (atlas n) (fun _ _ => 1) γ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv γ t‖ₑ := by
  refine lintegral_congr fun t => ?_
  rw [herm_one, ← ofReal_norm_eq_enorm, EuclideanSpace.norm_eq]
  rfl

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t` using `fun t => by`. Simplify using `using ((hasDerivAt_id t).smul_const (y - x)).const_add x`. Establish `hc : ContDiff ℝ 1 (fun s : ℝ => x + s • (y - x))` using `by fun_prop`. Use `iInf_le_of_le (fun s : ℝ => x + s • (y - x)) (iInf_le_of_le ⟨hc.continuous.continuousOn, fun _ => hc.contDiffOn⟩ (iInf_le_of_le (by simp) (iInf_le_of_le (by simp) ?_)))` and prove the remaining obligations.

Rewrite using `[pathLength_flat]`. Simplify using `[(hd _).deriv, edist_comm x y, edist_eq_enorm_sub]`. Use `le_iInf fun γ => le_iInf fun hγ => le_iInf fun h0 => le_iInf fun h1 => ?_` and prove the remaining obligations. Establish `h` using `hγ.2 ()`. Establish `hs : Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ((atlas n).chart ()).source = Set.Icc 0 1`.

Simplify using `[ExponentialProfileBounds.atlas]`. Rewrite `h` using `[hs]`. Use `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := γ) h zero_le_one` as an intermediate fact. Rewrite using `[pathLength_flat, edist_comm, edist_eq_enorm_sub, ← h0, ← h1]` and apply the resulting hypothesis.
-/
theorem lengthDist_flat (x y : V n) : lengthDist (atlas n) (fun _ _ => 1) x y = edist x y := by
  refine le_antisymm ?_ ?_
  · have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := fun t => by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hc : ContDiff ℝ 1 (fun s : ℝ => x + s • (y - x)) := by fun_prop
    refine iInf_le_of_le (fun s : ℝ => x + s • (y - x)) (iInf_le_of_le
      ⟨hc.continuous.continuousOn, fun _ => hc.contDiffOn⟩
      (iInf_le_of_le (by simp) (iInf_le_of_le (by simp) ?_)))
    rw [pathLength_flat]
    simp [(hd _).deriv, edist_comm x y, edist_eq_enorm_sub]
  · refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun h0 => le_iInf fun h1 => ?_
    have h := hγ.2 ()
    have hs : Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' ((atlas n).chart ()).source = Set.Icc 0 1 := by
      simp [ExponentialProfileBounds.atlas]
    rw [hs] at h
    have := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := γ) h zero_le_one
    rwa [pathLength_flat, edist_comm, edist_eq_enorm_sub, ← h0, ← h1]

/- English proof (translation)
Use `isComplete_of_compact_balls _ _ zero_lt_one fun x => ⟨Metric.closedBall x 1, isCompact_closedBall x 1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[lengthDist_flat, edist_dist, ENNReal.ofReal_lt_one]`. Conclude with `Metric.mem_closedBall'.2 hy.le`.
-/
theorem isComplete_flat : IsComplete (atlas n) (fun _ _ => 1) := by
  refine isComplete_of_compact_balls _ _ zero_lt_one fun x =>
    ⟨Metric.closedBall x 1, isCompact_closedBall x 1, fun y hy => ?_⟩
  rw [lengthDist_flat, edist_dist, ENNReal.ofReal_lt_one] at hy
  exact Metric.mem_closedBall'.2 hy.le

/- English proof (translation)
Establish `hf : (fun v : V n => ((((atlas n).ph 0 () (((atlas n).chart ()).symm v) + ‖((atlas n).chart ()).symm v‖ ^ 2 : ℝ)) : ℂ)) = fun v => ((∑ k, Complex.normSq (v k) : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`. Simplify using `[ExponentialProfileBounds.atlas, norm_sq_eq', Complex.normSq_eq_norm_sq]`. Simplify using `only [WeightedAtlas.leviAt]`. Rewrite using `[hf, leviV_ofReal_sum (fun k => contDiffAt_normSq_comp (contDiff_coord k).contDiffAt), herm_one, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `: ∀ j, wd n j (fun v : V n => v m) y = if m = j then 1 else 0`. Introduce `j`. Rewrite using `[wd_of_differentiableAt (differentiable_coord m y), (hasFDerivAt_coord m y).fderiv]`. Simplify using `[bas]`.

Rewrite using `[leviV_normSq_comp (contDiff_coord m).contDiffAt]`. Express the relevant statement in the definitionally equal form `(((Complex.normSq (∑ j, wd n j (fun v : V n => v m) y * ξ j)) : ℝ) : ℂ).re = _`. Simplify using `[this, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]`.
-/
theorem leviAt_flat (y : V n) (ξ : Fin n → ℂ) :
    (atlas n).leviAt () (fun x => (atlas n).ph 0 () x + ‖x‖ ^ 2) y ξ = herm 1 ξ := by
  have hf : (fun v : V n => ((((atlas n).ph 0 () (((atlas n).chart ()).symm v) +
      ‖((atlas n).chart ()).symm v‖ ^ 2 : ℝ)) : ℂ)) =
      fun v => ((∑ k, Complex.normSq (v k) : ℝ) : ℂ) := by
    funext v; simp [ExponentialProfileBounds.atlas, norm_sq_eq', Complex.normSq_eq_norm_sq]
  simp only [WeightedAtlas.leviAt]
  rw [hf, leviV_ofReal_sum (fun k => contDiffAt_normSq_comp (contDiff_coord k).contDiffAt),
    herm_one, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ j, wd n j (fun v : V n => v m) y = if m = j then 1 else 0 := by
    intro j
    rw [wd_of_differentiableAt (differentiable_coord m y), (hasFDerivAt_coord m y).fderiv]
    simp [bas]
  rw [leviV_normSq_comp (contDiff_coord m).contDiffAt]
  change (((Complex.normSq (∑ j, wd n j (fun v : V n => v m) y * ξ j)) : ℝ) : ℂ).re = _
  simp [this, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

/- English proof (translation)
Use `⟨isKaehler_flat, isComplete_flat, fun _ => (contDiff_norm_sq ℝ).contDiffOn, fun _ y _ ξ => by rw [one_mul, leviAt_flat], ⟨fun _ _ => contDiffOn_const, fun _ _ y _ _ ξ => by rw [push_flat]; simp [ExponentialProfileBounds.atlas]⟩, fun _ _ _ _ _ => by simp [wdb], ?_⟩` and prove the remaining obligations. Establish `h` using `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V n) (b := 1) (by simp) 0 0).norm.const_mul (coNormSq 1 c)`. Use `lt_of_eq_of_lt ?_ h.lintegral_lt_top` and prove the remaining obligations. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `[formNsq, ExponentialProfileBounds.atlas, Complex.norm_exp, ← Complex.ofReal_pow]`.
-/
theorem hypotheses_flat (c : Fin n → ℂ) :
    IsKaehler (atlas n) (fun _ _ => 1) ∧ IsComplete (atlas n) (fun _ _ => 1) ∧
    (atlas n).SmoothFn (fun x => ‖x‖ ^ 2) ∧
    (∀ i y, y ∈ ((atlas n).chart i).source → ∀ ξ : Fin n → ℂ,
      1 * herm 1 ξ ≤ (atlas n).leviAt i (fun x => (atlas n).ph 0 i x + ‖x‖ ^ 2) y ξ) ∧
    IsForm (atlas n) 0 (fun _ _ => c) ∧ IsDbarClosed (atlas n) (fun _ _ => c) ∧
    ∫⁻ y, ENNReal.ofReal (formNsq (atlas n) (fun _ _ => 1) 0 (fun _ _ => c) y *
      Real.exp (-‖y‖ ^ 2)) ∂(atlas n).mu < ⊤ := by
  refine ⟨isKaehler_flat, isComplete_flat, fun _ => (contDiff_norm_sq ℝ).contDiffOn,
    fun _ y _ ξ => by rw [one_mul, leviAt_flat], ⟨fun _ _ => contDiffOn_const,
      fun _ _ y _ _ ξ => by rw [push_flat]; simp [ExponentialProfileBounds.atlas]⟩, fun _ _ _ _ _ => by simp [wdb], ?_⟩
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V n) (b := 1)
    (by simp) 0 0).norm.const_mul (coNormSq 1 c)
  refine lt_of_eq_of_lt ?_ h.lintegral_lt_top
  refine lintegral_congr fun y => ?_
  simp [formNsq, ExponentialProfileBounds.atlas, Complex.norm_exp, ← Complex.ofReal_pow]

end Flat

end

end GlobalTheory.L2Kaehler

namespace GlobalTheory.Published

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.L2Kaehler
open scoped ENNReal

def DbarCompleteKaehler : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (la : La) (ps : Y → ℝ) (ε : ℝ) (v : ι → Y → Fin n → ℂ),
    IsKaehler A H → IsComplete A H → A.SmoothFn ps → 0 < ε →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      ε * herm (H i y) ξ ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ) →
    IsForm A la v → IsDbarClosed A v →
    ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu < ⊤ →
    ∃ u : ι → Y → ℂ, A.IsSSec (A.kap + la) u ∧
      (∀ i y, y ∈ (A.chart i).source → dbar A u i y = v i y) ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) u y * Real.exp (-ps y)) ∂A.mu ≤
        ENNReal.ofReal ε⁻¹ *
          ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu

/- English proof (translation)
Take `⟨u, hu, hdu, hb⟩` from `hP n Y ι La A H la ps ε _ hK hc hps hε hcurv (isForm_dbar A hF) (isDbarClosed_dbar A hF) hfin`. Use `⟨F₀ - u, ⟨fun i w hw => ?_, fun i j y _ hi hj => ?_⟩, by rwa [sub_sub_cancel]⟩` and prove the remaining obligations. Establish `hn` using `(A.chart i).open_target.mem_nhds hw.1`. Establish `h1 : DifferentiableAt ℝ (F₀ i ∘ (A.chart i).symm) w` using `((hF.1 i).contDiffAt hn).differentiableAt (by simp)`. Establish `h2 : DifferentiableAt ℝ (u i ∘ (A.chart i).symm) w` using `((hu.1 i).contDiffAt hn).differentiableAt (by simp)`.

Establish `h3 : ∀ ζ : V n, dbv (fderiv ℝ (F₀ i ∘ (A.chart i).symm) w) ζ = dbv (fderiv ℝ (u i ∘ (A.chart i).symm) w) ζ` using `fun ζ => by`. Rewrite using `[← sum_wdb_eq, ← sum_wdb_eq]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← dbar_symm A F₀ i k w hw.1, ← dbar_symm A u i k w hw.1, hdu i _ ((A.chart i).map_target hw.1)]`. Establish `h4` using `h1.hasFDerivAt.sub h2.hasFDerivAt`.

Use `set D := fderiv ℝ (F₀ i ∘ (A.chart i).symm) w - fderiv ℝ (u i ∘ (A.chart i).symm) w with hD`. Establish `hI : ∀ ζ : V n, D (Complex.I • ζ) = Complex.I * D ζ` using `fun ζ => by`. Use `h3 ζ` as an intermediate fact. Simplify using `only [dbv] at this`. Simplify using `only [hD, ContinuousLinearMap.sub_apply]`.

Take the linear combination `(-2 * Complex.I) * this + (fderiv ℝ (F₀ i ∘ (A.chart i).symm) w (Complex.I • ζ) - fderiv ℝ (u i ∘ (A.chart i).symm) w (Complex.I • ζ)) * Complex.I_sq`. Set `L : V n →L[ℂ] ℂ` to `{ toFun := D, map_add' := D.map_add map_smul' := fun c ζ => by`. Rewrite using `[clm_smul_decomp, hI, RingHom.id_apply, smul_eq_mul]`. Use `conv_rhs => rw [← Complex.re_add_im c]`. Expand and normalize the polynomial expressions, which then agree.

Use `cont := D.cont }`. Conclude with `(hasFDerivAt_of_restrictScalars ℝ (f' := L) h4 (by ext; rfl)).differentiableAt |>.differentiableWithinAt`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hF.2 i j y hi hj, hu.2 i j y hi hj, mul_sub]`.
-/
theorem DbarCompleteKaehler.exists_holo (hP : DbarCompleteKaehler)
    {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (la : La) (ps : Y → ℝ) (ε : ℝ) (F₀ : ι → Y → ℂ)
    (hK : IsKaehler A H) (hc : IsComplete A H) (hps : A.SmoothFn ps) (hε : 0 < ε)
    (hcurv : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      ε * herm (H i y) ξ ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ)
    (hF : A.IsSSec (A.kap + la) F₀)
    (hfin : ∫⁻ y, ENNReal.ofReal (formNsq A H la (dbar A F₀) y * Real.exp (-ps y)) ∂A.mu < ⊤) :
    ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) (F₀ - F) y * Real.exp (-ps y)) ∂A.mu ≤
        ENNReal.ofReal ε⁻¹ *
          ∫⁻ y, ENNReal.ofReal (formNsq A H la (dbar A F₀) y * Real.exp (-ps y)) ∂A.mu := by
  obtain ⟨u, hu, hdu, hb⟩ := hP n Y ι La A H la ps ε _ hK hc hps hε hcurv (isForm_dbar A hF)
    (isDbarClosed_dbar A hF) hfin
  refine ⟨F₀ - u, ⟨fun i w hw => ?_, fun i j y _ hi hj => ?_⟩, by rwa [sub_sub_cancel]⟩
  · have hn := (A.chart i).open_target.mem_nhds hw.1
    have h1 : DifferentiableAt ℝ (F₀ i ∘ (A.chart i).symm) w :=
      ((hF.1 i).contDiffAt hn).differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (u i ∘ (A.chart i).symm) w :=
      ((hu.1 i).contDiffAt hn).differentiableAt (by simp)
    have h3 : ∀ ζ : V n, dbv (fderiv ℝ (F₀ i ∘ (A.chart i).symm) w) ζ =
        dbv (fderiv ℝ (u i ∘ (A.chart i).symm) w) ζ := fun ζ => by
      rw [← sum_wdb_eq, ← sum_wdb_eq]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← dbar_symm A F₀ i k w hw.1, ← dbar_symm A u i k w hw.1,
        hdu i _ ((A.chart i).map_target hw.1)]
    have h4 := h1.hasFDerivAt.sub h2.hasFDerivAt
    set D := fderiv ℝ (F₀ i ∘ (A.chart i).symm) w - fderiv ℝ (u i ∘ (A.chart i).symm) w with hD
    have hI : ∀ ζ : V n, D (Complex.I • ζ) = Complex.I * D ζ := fun ζ => by
      have := h3 ζ
      simp only [dbv] at this
      simp only [hD, ContinuousLinearMap.sub_apply]
      linear_combination (-2 * Complex.I) * this +
        (fderiv ℝ (F₀ i ∘ (A.chart i).symm) w (Complex.I • ζ) -
          fderiv ℝ (u i ∘ (A.chart i).symm) w (Complex.I • ζ)) * Complex.I_sq
    let L : V n →L[ℂ] ℂ :=
      { toFun := D, map_add' := D.map_add
        map_smul' := fun c ζ => by
          rw [clm_smul_decomp, hI, RingHom.id_apply, smul_eq_mul]
          conv_rhs => rw [← Complex.re_add_im c]
          ring
        cont := D.cont }
    exact (hasFDerivAt_of_restrictScalars ℝ (f' := L) h4 (by ext; rfl)).differentiableAt
      |>.differentiableWithinAt
  · simp only [Pi.sub_apply]
    rw [hF.2 i j y hi hj, hu.2 i j y hi hj, mul_sub]

end GlobalTheory.Published
