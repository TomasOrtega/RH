import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnitriJac

open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (u : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a c => if h : c < a then u ⟨(a, c), h⟩ else 0

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Establish `h1 : ∑ q : Low r, f q.1.1 q.1.2 * u q = ∑ q : Low r, f q.1.1 q.1.2 * lowMat u q.1.1 q.1.2`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `[lowMat, q.2]`. Rewrite using `[h1, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (by simp) (fun p : Fin r × Fin r => f p.1 p.2 * lowMat u p.1 p.2), Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `[lowMat, h]`.
-/
theorem sum_low {r : ℕ} (u : Low r → ℂ) (f : Fin r → Fin r → ℂ) :
    ∑ q : Low r, f q.1.1 q.1.2 * u q = ∑ a, ∑ c, f a c * lowMat u a c := by
  rw [← Fintype.sum_prod_type']
  have h1 : ∑ q : Low r, f q.1.1 q.1.2 * u q
      = ∑ q : Low r, f q.1.1 q.1.2 * lowMat u q.1.1 q.1.2 := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [lowMat, q.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (by simp)
    (fun p : Fin r × Fin r => f p.1 p.2 * lowMat u p.1 p.2), Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rfl
  · simp [lowMat, h]

def leftM {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0

def adM {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2

/- English proof (translation)
Use `sum_low u (fun a c => if p.1.2 = c then N p.1.1 a else 0)` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, leftM, Matrix.of_apply]`. Rewrite using `[this, Matrix.mul_apply]`. Simplify using the standard rewrite rules.
-/
theorem leftM_mulVec {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (leftM N *ᵥ u) p = (N * lowMat u) p.1.1 p.1.2 := by
  have := sum_low u (fun a c => if p.1.2 = c then N p.1.1 a else 0)
  simp only [Matrix.mulVec, dotProduct, leftM, Matrix.of_apply]
  rw [this, Matrix.mul_apply]
  simp

/- English proof (translation)
Use `sum_low u (fun a c => B p.1.1 a * B⁻¹ c p.1.2)` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, adM, Matrix.of_apply]`. Rewrite using `[this, Matrix.mul_apply, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adM_mulVec {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (adM B *ᵥ u) p = (B * lowMat u * B⁻¹) p.1.1 p.1.2 := by
  have := sum_low u (fun a c => B p.1.1 a * B⁻¹ c p.1.2)
  simp only [Matrix.mulVec, dotProduct, adM, Matrix.of_apply]
  rw [this, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Use extensionality with `a c`. Distinguish the cases in `h : c < a`. Simplify using `only [lowMat, Matrix.of_apply, dif_pos h]`. Conclude with `leftM_mulVec N u ⟨(a, c), h⟩`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [lowMat, Matrix.of_apply, dif_neg h]`. Use `symm`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : c < k`. Rewrite using `[hN.1 a k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]`.

Rewrite using `[dif_neg hk, mul_zero]`.
-/
theorem lowMat_leftM {r : ℕ} {N : Matrix (Fin r) (Fin r) ℂ} (hN : LowU N) (u : Low r → ℂ) :
    lowMat (leftM N *ᵥ u) = N * lowMat u := by
  ext a c
  by_cases h : c < a
  · simp only [lowMat, Matrix.of_apply, dif_pos h]
    exact leftM_mulVec N u ⟨(a, c), h⟩
  · rw [Matrix.mul_apply]
    simp only [lowMat, Matrix.of_apply, dif_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [hN.1 a k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [dif_neg hk, mul_zero]

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _` and prove the remaining obligations. Conclude with `DifferentiableAt.fun_finsetProd fun i _ => h _ _`.
-/
theorem differentiableAt_det {r : ℕ} (A : ℂ → Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (h : ∀ i j, DifferentiableAt ℂ (fun s => A s i j) t) :
    DifferentiableAt ℂ (fun s => (A s).det) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact DifferentiableAt.fun_finsetProd fun i _ => h _ _

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Use `differentiableAt_det _ t fun k l => ?_` and prove the remaining obligations. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `differentiableAt_const _`.

Conclude with `h _ _`.
-/
theorem differentiableAt_adjugate {r : ℕ} (A : ℂ → Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (h : ∀ i j, DifferentiableAt ℂ (fun s => A s i j) t) (i j : Fin r) :
    DifferentiableAt ℂ (fun s => (A s).adjugate i j) t := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det _ t fun k l => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h _ _

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]`. Conclude with `HasDerivAt.fun_sum fun k _ => (hA i k).fun_mul (hB k j)`.
-/
theorem hasDerivAt_mul {r : ℕ} {A B : ℂ → Matrix (Fin r) (Fin r) ℂ} {A' B' : Matrix (Fin r) (Fin r) ℂ}
    {t : ℂ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).fun_mul (hB k j)

/- English proof (translation)
Establish `hgN : ∀ i j, HasDerivAt (fun s => (g * N s) i j) ((g * N') i j) 0`. Introduce `i j`. Use `hasDerivAt_mul (A := fun _ => g) (A' := 0) (fun i j => hasDerivAt_const _ _) hN i j` as an intermediate fact. Simplify using `using this`. Establish `hbe : ∀ i j, (fun s => b s i j) =ᶠ[𝓝 0] fun s => ((M s).adjugate * (g * N s)) i j`.

Introduce `i j`. Use `filter_upwards [h] with s hs`. Rewrite using `[hs.1, ← Matrix.mul_assoc, Matrix.adjugate_mul, hMd, one_smul, Matrix.one_mul]`. Establish `hbdiff : ∀ i j, DifferentiableAt ℂ (fun s => b s i j) 0`. Introduce `i j`.

Use `DifferentiableAt.congr_of_eventuallyEq ?_ (hbe i j)` and prove the remaining obligations. Conclude with `(hasDerivAt_mul (A := fun s => (M s).adjugate) (A' := Matrix.of fun i j => deriv (fun s => (M s).adjugate i j) 0) (fun i j => (differentiableAt_adjugate M 0 (fun i j => (hM i j).differentiableAt) i j).hasDerivAt) hgN i j).differentiableAt`. Use `set b' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => deriv (fun s => b s i j) 0 with hb'`. Establish `hb : ∀ i j, HasDerivAt (fun s => b s i j) (b' i j) 0` using `fun i j => (hbdiff i j).hasDerivAt`. Establish `hup : b'.BlockTriangular id`.

Introduce `i j hij`. Establish `: (fun s => b s i j) =ᶠ[𝓝 0] fun _ => (0 : ℂ)` using `by filter_upwards [h] with s hs using hs.2 i j hij`. Use `show deriv (fun s => b s i j) 0 = 0`. Rewrite using `[this.deriv_eq]`. Simplify using the standard rewrite rules.

Establish `hrel : g * N' = M' * b 0 + M 0 * b'`. Use extensionality with `i j`. Use `(hgN i j).unique (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_mul hM hb i j) ?_)` and prove the remaining obligations. Use `filter_upwards [h] with s hs`. Rewrite using `[hs.1]`.

Establish `h0` using `h.self_of_nhds`. Establish `uM : IsUnit (M 0).det` using `by rw [hMd]; exact isUnit_one`. Establish `uN : IsUnit (N 0).det` using `by rw [hNd]; exact isUnit_one`. Establish `ub : IsUnit (b 0).det` using `isUnit_iff_ne_zero.mpr hbd`. Establish `hg : g = M 0 * b 0 * (N 0)⁻¹`.

Rewrite using `[← h0.1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uN, Matrix.mul_one]`. Establish `key : b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹ = (M 0)⁻¹ * M' + b' * (b 0)⁻¹`. Establish `e1 : b 0 * ((N 0)⁻¹ * N') = (M 0)⁻¹ * (g * N')`. Rewrite using `[hg]`. Simplify using `only [← Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul _ uM, Matrix.one_mul]`. Rewrite using `[e1, hrel, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (M 0)⁻¹ (M 0), Matrix.nonsing_inv_mul _ uM, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]`. Establish `hbinv : ((b 0)⁻¹).BlockTriangular id`. Set `_` to `Matrix.invertibleOfIsUnitDet _ ub`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular fun i j hij => h0.2 i j hij`.

Rewrite using `[key, Matrix.add_apply, (hup.mul hbinv) hca, add_zero]`.
-/
theorem deriv_rel {r : ℕ} {N M b : ℂ → Matrix (Fin r) (Fin r) ℂ} {g N' M' : Matrix (Fin r) (Fin r) ℂ}
    (hN : ∀ i j, HasDerivAt (fun s => N s i j) (N' i j) 0)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) 0)
    (hMd : ∀ s, (M s).det = 1) (hNd : (N 0).det = 1) (hbd : (b 0).det ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℂ), g * N s = M s * b s ∧ ∀ a c : Fin r, c < a → b s a c = 0)
    (a c : Fin r) (hca : c < a) :
    ((M 0)⁻¹ * M') a c = (b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹) a c := by
  have hgN : ∀ i j, HasDerivAt (fun s => (g * N s) i j) ((g * N') i j) 0 := by
    intro i j
    have := hasDerivAt_mul (A := fun _ => g) (A' := 0) (fun i j => hasDerivAt_const _ _) hN i j
    simpa using this
  have hbe : ∀ i j, (fun s => b s i j) =ᶠ[𝓝 0] fun s => ((M s).adjugate * (g * N s)) i j := by
    intro i j
    filter_upwards [h] with s hs
    rw [hs.1, ← Matrix.mul_assoc, Matrix.adjugate_mul, hMd, one_smul, Matrix.one_mul]
  have hbdiff : ∀ i j, DifferentiableAt ℂ (fun s => b s i j) 0 := by
    intro i j
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hbe i j)
    exact (hasDerivAt_mul (A := fun s => (M s).adjugate)
      (A' := Matrix.of fun i j => deriv (fun s => (M s).adjugate i j) 0)
      (fun i j => (differentiableAt_adjugate M 0 (fun i j => (hM i j).differentiableAt) i j).hasDerivAt)
      hgN i j).differentiableAt
  set b' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => deriv (fun s => b s i j) 0 with hb'
  have hb : ∀ i j, HasDerivAt (fun s => b s i j) (b' i j) 0 := fun i j => (hbdiff i j).hasDerivAt
  have hup : b'.BlockTriangular id := by
    intro i j hij
    have : (fun s => b s i j) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [h] with s hs using hs.2 i j hij
    show deriv (fun s => b s i j) 0 = 0
    rw [this.deriv_eq]; simp
  have hrel : g * N' = M' * b 0 + M 0 * b' := by
    ext i j
    refine (hgN i j).unique (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_mul hM hb i j) ?_)
    filter_upwards [h] with s hs
    rw [hs.1]
  have h0 := h.self_of_nhds
  have uM : IsUnit (M 0).det := by rw [hMd]; exact isUnit_one
  have uN : IsUnit (N 0).det := by rw [hNd]; exact isUnit_one
  have ub : IsUnit (b 0).det := isUnit_iff_ne_zero.mpr hbd
  have hg : g = M 0 * b 0 * (N 0)⁻¹ := by
    rw [← h0.1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uN, Matrix.mul_one]
  have key : b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹ = (M 0)⁻¹ * M' + b' * (b 0)⁻¹ := by
    have e1 : b 0 * ((N 0)⁻¹ * N') = (M 0)⁻¹ * (g * N') := by
      rw [hg]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ uM, Matrix.one_mul]
    rw [e1, hrel, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (M 0)⁻¹ (M 0),
      Matrix.nonsing_inv_mul _ uM, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]
  have hbinv : ((b 0)⁻¹).BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet _ ub
    exact Matrix.blockTriangular_inv_of_blockTriangular fun i j hij => h0.2 i j hij
  rw [key, Matrix.add_apply, (hup.mul hbinv) hca, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def crd {r : ℕ} (X : Data E r) (v : V (nd X)) (τ : X.Ψ) : Low r → ℂ :=
  fun p => v ((Fintype.equivFin (Ent X)) ⟨τ, p⟩)

/- English proof (translation)
Simplify using `only [mat, nmat, lowMat, Matrix.of_apply]`. Distinguish the cases in `h : j < i`. Simplify using `only [dif_pos h, crd]`. Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(i, j), h⟩⟩)).hasFDerivAt.comp_hasDerivAt t hw`. Simplify using `only [dif_neg h]`.

Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_nmat {r : ℕ} (X : Data E r) {w : ℂ → V (nd X)} {w' : V (nd X)} {t : ℂ}
    (hw : HasDerivAt w w' t) (τ : X.Ψ) (i j : Fin r) :
    HasDerivAt (fun s => mat (nmat X (w s)) τ i j) (lowMat (crd X w' τ) i j) t := by
  simp only [mat, nmat, lowMat, Matrix.of_apply]
  by_cases h : j < i
  · simp only [dif_pos h, crd]
    exact (EuclideanSpace.proj (𝕜 := ℂ)
      ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(i, j), h⟩⟩)).hasFDerivAt.comp_hasDerivAt t hw
  · simp only [dif_neg h]
    exact hasDerivAt_const _ _

/- English proof (translation)
Use `set G : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ with hG`. Establish `hrel : ∀ y ∈ U, mat x0 τ * mat (nmat X y) τ = G * (mat (nmat X (Φ y)) τ * mat (bf y) τ)`. Introduce `y hy`. Use `congrFun (h y hy).2.2 τ` as an intermediate fact. Rewrite using `[hG, Matrix.mul_assoc, ← Matrix.mul_assoc (mat x1 τ)]`.

Conclude with `this`. Establish `uG : IsUnit G.det`. Establish `h1 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0` using `((h z hz).1 τ).1`. Rewrite `h1` using `[hrel z hz, Matrix.det_mul]`. Conclude with `isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h1)`.

Establish `hl : HasDerivAt (fun s : ℂ => z + s • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z`. Establish `hΦz : HasFDerivAt Φ (fderiv ℂ Φ z) (z + (0 : ℂ) • v)`. Simplify using `using (hΦ.differentiableAt (hU.mem_nhds hz)).hasFDerivAt`. Establish `hl2 : HasDerivAt (fun s : ℂ => Φ (z + s • v)) (fderiv ℂ Φ z v) 0` using `hΦz.comp_hasDerivAt (0 : ℂ) hl`.

Establish `hev : ∀ᶠ s in 𝓝 (0 : ℂ), z + s • v ∈ U` using `hl.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))`. Use function extensionality and compare the values at `p`. Use `deriv_rel (N := fun s => mat (nmat X (z + s • v)) τ) (M := fun s => mat (nmat X (Φ (z + s • v))) τ) (b := fun s => mat (bf (z + s • v)) τ) (g := G⁻¹ * mat x0 τ) (hasDerivAt_nmat X hl τ) (hasDerivAt_nmat X hl2 τ) (fun s => (nmat_lowU X _ τ).det) (nmat_lowU X _ τ).det (by simpa usi …` as an intermediate fact. Use `⟨?_, fun a c hca => ((h _ hs).2.1 τ).2 a c hca⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hrel _ hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uG, Matrix.one_mul])`.

Use the proof step `p.1.1 p.1.2 p.2`. Simplify using `only [zero_smul, add_zero] at this`. Rewrite using `[leftM_mulVec, ← Matrix.mulVec_mulVec, adM_mulVec, lowMat_leftM (nmat_lowU X z τ).inv]`. Conclude with `this`.
-/
theorem fderiv_rel {r : ℕ} (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r) (hU : IsOpen U)
    (hΦ : DifferentiableOn ℂ Φ U)
    (h : ∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z)))
    (z : V (nd X)) (hz : z ∈ U) (v : V (nd X)) (τ : X.Ψ) :
    leftM (mat (nmat X (Φ z)) τ)⁻¹ *ᵥ crd X (fderiv ℂ Φ z v) τ =
      (adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) *ᵥ crd X v τ := by
  set G : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ with hG
  have hrel : ∀ y ∈ U, mat x0 τ * mat (nmat X y) τ = G * (mat (nmat X (Φ y)) τ * mat (bf y) τ) := by
    intro y hy
    have := congrFun (h y hy).2.2 τ
    rw [hG, Matrix.mul_assoc, ← Matrix.mul_assoc (mat x1 τ)]
    exact this
  have uG : IsUnit G.det := by
    have h1 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := ((h z hz).1 τ).1
    rw [hrel z hz, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h1)
  have hl : HasDerivAt (fun s : ℂ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hΦz : HasFDerivAt Φ (fderiv ℂ Φ z) (z + (0 : ℂ) • v) := by
    simpa using (hΦ.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hl2 : HasDerivAt (fun s : ℂ => Φ (z + s • v)) (fderiv ℂ Φ z v) 0 :=
    hΦz.comp_hasDerivAt (0 : ℂ) hl
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), z + s • v ∈ U :=
    hl.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  funext p
  have := deriv_rel (N := fun s => mat (nmat X (z + s • v)) τ)
    (M := fun s => mat (nmat X (Φ (z + s • v))) τ) (b := fun s => mat (bf (z + s • v)) τ)
    (g := G⁻¹ * mat x0 τ) (hasDerivAt_nmat X hl τ) (hasDerivAt_nmat X hl2 τ)
    (fun s => (nmat_lowU X _ τ).det) (nmat_lowU X _ τ).det
    (by simpa using ((h z hz).2.1 τ).1)
    (by
      filter_upwards [hev] with s hs
      refine ⟨?_, fun a c hca => ((h _ hs).2.1 τ).2 a c hca⟩
      rw [Matrix.mul_assoc, hrel _ hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uG, Matrix.one_mul])
    p.1.1 p.1.2 p.2
  simp only [zero_smul, add_zero] at this
  rw [leftM_mulVec, ← Matrix.mulVec_mulVec, adM_mulVec, lowMat_leftM (nmat_lowU X z τ).inv]
  exact this

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]`.
-/
theorem blockDiagonal_mulVec {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
    (A : o → Matrix m m ℂ) (u : m × o → ℂ) (p : m) (τ : o) :
    (Matrix.blockDiagonal A *ᵥ u) (p, τ) = (A τ *ᵥ fun q => u (q, τ)) p := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

/- English proof (translation)
Introduce `hAd hL r X x0 x1 γ U Φ bf hU hΦ h z hz`. Set `e : Low r × X.Ψ ≃ Fin (nd X)` to `(Equiv.prodComm _ _).trans (Fintype.equivFin (Ent X))`. Set `β : Module.Basis (Low r × X.Ψ) ℂ (V (nd X))` to `(EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis.reindex e.symm`. Establish `hβ : ∀ (v : V (nd X)) (τ : X.Ψ), (fun q => β.repr v (q, τ)) = crd X v τ`. Introduce `v τ`.

Use function extensionality and compare the values at `q`. Simplify using `only [β, Module.Basis.repr_reindex_apply, Equiv.symm_symm, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]`. Both sides reduce to the same expression. Use `set D : V (nd X) →ₗ[ℂ] V (nd X) := (fderiv ℂ Φ z).toLinearMap with hD`. Establish `hmat : Matrix.blockDiagonal (fun τ => leftM (mat (nmat X (Φ z)) τ)⁻¹) * LinearMap.toMatrix β β D = Matrix.blockDiagonal (fun τ => adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹)`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩ : ∃ v, (β.repr v : Low r × X.Ψ → ℂ) = u` from `⟨β.equivFun.symm u, by`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩`. Simplify using `only [Matrix.toLin'_apply]`.

Rewrite using `[← Matrix.mulVec_mulVec, LinearMap.toMatrix_mulVec_repr]`. Use function extensionality and compare the values at `⟨p, τ⟩`. Rewrite using `[blockDiagonal_mulVec, blockDiagonal_mulVec, hβ, hβ]`. Conclude with `congrFun (fderiv_rel X x0 x1 γ U Φ bf hU hΦ h z hz v τ) p`. Establish `hdet` using `congrArg Matrix.det hmat`.

Establish `hL' : ∀ (y : V (nd X)) (τ : X.Ψ), (leftM (mat (nmat X y) τ)⁻¹).det = 1` using `fun y τ => by`. Use `hL r _ (nmat_lowU X y τ).inv.1 (nmat_lowU X y τ).inv.2` as an intermediate fact. Conclude with `this`. Establish `hA' : ∀ τ : X.Ψ, (adM (mat (bf z) τ)).det = ∏ a : Fin r, bf z τ a a ^ kapW X τ a` using `fun τ => by`. Use `hAd r (mat (bf z) τ) ((h z hz).2.1 τ).1 ((h z hz).2.1 τ).2` as an intermediate fact.

Conclude with `this`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_blockDiagonal, LinearMap.det_toMatrix]`. Simplify using `only [Matrix.det_mul, hL', hA', Finset.prod_const_one, one_mul, mul_one] at hdet`. Conclude with `hdet`.
-/
theorem kapGG_of_det :
    (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) → (∀ (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ), (∀ a c : Fin r, a < c → N a c = 0) → (∀ a, N a a = 1) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1) → (KapGGStatement (E := E)) := by
  classical
  intro hAd hL r X x0 x1 γ U Φ bf hU hΦ h z hz
  let e : Low r × X.Ψ ≃ Fin (nd X) := (Equiv.prodComm _ _).trans (Fintype.equivFin (Ent X))
  let β : Module.Basis (Low r × X.Ψ) ℂ (V (nd X)) :=
    (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis.reindex e.symm
  have hβ : ∀ (v : V (nd X)) (τ : X.Ψ), (fun q => β.repr v (q, τ)) = crd X v τ := by
    intro v τ
    funext q
    simp only [β, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rfl
  set D : V (nd X) →ₗ[ℂ] V (nd X) := (fderiv ℂ Φ z).toLinearMap with hD
  have hmat : Matrix.blockDiagonal (fun τ => leftM (mat (nmat X (Φ z)) τ)⁻¹) * LinearMap.toMatrix β β D =
      Matrix.blockDiagonal (fun τ => adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ : ∃ v, (β.repr v : Low r × X.Ψ → ℂ) = u := ⟨β.equivFun.symm u, by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix_mulVec_repr]
    funext ⟨p, τ⟩
    rw [blockDiagonal_mulVec, blockDiagonal_mulVec, hβ, hβ]
    exact congrFun (fderiv_rel X x0 x1 γ U Φ bf hU hΦ h z hz v τ) p
  have hdet := congrArg Matrix.det hmat
  have hL' : ∀ (y : V (nd X)) (τ : X.Ψ), (leftM (mat (nmat X y) τ)⁻¹).det = 1 := fun y τ => by
    have := hL r _ (nmat_lowU X y τ).inv.1 (nmat_lowU X y τ).inv.2
    exact this
  have hA' : ∀ τ : X.Ψ, (adM (mat (bf z) τ)).det = ∏ a : Fin r, bf z τ a a ^ kapW X τ a := fun τ => by
    have := hAd r (mat (bf z) τ) ((h z hz).2.1 τ).1 ((h z hz).2.1 τ).2
    exact this
  rw [Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_blockDiagonal, LinearMap.det_toMatrix] at hdet
  simp only [Matrix.det_mul, hL', hA', Finset.prod_const_one, one_mul, mul_one] at hdet
  exact hdet

end

end GlobalTheory.UnitriJac
