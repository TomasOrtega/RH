import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BfSubRight

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Unfold `Bf`. Simplify using `[Pi.single_apply]`.
-/
lemma Bf_single (Z : X.Coord) (τ : X.Ψ) (j k : Fin r) :
    Bf X Z τ (Pi.single j 1) (Pi.single k 1) = Gp X Z τ j k := by
  unfold Bf
  simp [Pi.single_apply]

/- English proof (translation)
Establish `h2 : Bf X Z τ t v = 0` using `by rw [Bf_conj, h1, map_zero]`. Simplify using `only [Bf_sub_left, Bf_sub_right]`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Bf_split (Z : X.Coord) (τ : X.Ψ) (v t : Fin r → ℂ) (h1 : Bf X Z τ v t = 0) :
    Bf X Z τ v v = Bf X Z τ (v - t) (v - t) - Bf X Z τ t t := by
  have h2 : Bf X Z τ t v = 0 := by rw [Bf_conj, h1, map_zero]
  simp only [Bf_sub_left, Bf_sub_right]
  rw [h1, h2]
  ring

/- English proof (translation)
Rewrite using `[← gram_xZ X ho Z τ]`. Conclude with `blk_det X (xZ_mem_dom X hx ho hZ) τ c`.
-/
lemma blk_Gp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (c : Fin r) : (blk (Gp X Z τ) c).det ≠ 0 := by
  rw [← gram_xZ X ho Z τ]
  exact blk_det X (xZ_mem_dom X hx ho hZ) τ c

/- English proof (translation)
Establish `hG : gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ` using `gram_xZ X ho Z τ`. Unfold `dOf uOf`. Rewrite using `[hG]`. Use `set M := mat (X.xZ x Z) τ with hM`. Use `set U := uMat (Gp X Z τ) with hU`.

Establish `hcol : col (M * U) k = ∑ a, U a k • col M a`. Use function extensionality and compare the values at `i`. Simplify using `[col, Matrix.mul_apply, Finset.sum_apply, mul_comm]`. Use `show hermC τ.1 X.Gm (col (M * U) k) (col (M * U) k) = _`. Rewrite using `[hcol, hermC_quad]`.

Unfold `Bf`. Rewrite using `[← hG]`. Both sides reduce to the same expression.
-/
lemma dOf_eq {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) (k : Fin r) :
    dOf X (X.xZ x Z) τ k = Bf X Z τ (fun a => uMat (Gp X Z τ) a k) (fun a => uMat (Gp X Z τ) a k) := by
  have hG : gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := gram_xZ X ho Z τ
  unfold dOf uOf
  rw [hG]
  set M := mat (X.xZ x Z) τ with hM
  set U := uMat (Gp X Z τ) with hU
  have hcol : col (M * U) k = ∑ a, U a k • col M a := by
    funext i
    simp [col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  show hermC τ.1 X.Gm (col (M * U) k) (col (M * U) k) = _
  rw [hcol, hermC_quad]
  unfold Bf
  rw [← hG]
  rfl

/- English proof (translation)
Establish `hdet` using `blk_Gp X hx ho hZ τ`. Establish `hz0 : 0 ≤ X.zN Z` using `Real.iSup_nonneg fun τ => opN_nonneg _`. Establish `hz1 : 0 ≤ 1 - X.zN Z ^ 2` using `by nlinarith`. Rewrite using `[dOf_eq X ho Z τ k]`. Use `set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv`.

Establish `hvk : v k = 1` using `by simp [hv, uMat]`. Establish `hvgt : ∀ b, k < b → v b = 0`. Introduce `b hb`. Simplify using `[hv, uMat, hb.ne', not_lt.mpr hb.le]`. Use `set t : Fin r → ℂ := fun b => if b < k then v b else 0 with ht`.

Establish `ht0 : ∀ b, k ≤ b → t b = 0` using `fun b hb => by simp [ht, not_lt.mpr hb]`. Establish `hvt : Bf X Z τ v t = 0` using `Bf_gv_zero X Z τ hdet k t ht0`. Establish `hsplit` using `Bf_split X Z τ v t hvt`. Establish `hsingle : v - t = Pi.single k 1`. Use function extensionality and compare the values at `b`.

Break down `lt_trichotomy b k with hb | hb | hb` into its components or cases. Simplify using `[ht, hb, hb.ne]`. Rewrite using `[hb]`. Simplify using `[ht, hvk]`. Simplify using `[ht, not_lt.mpr hb.le, hvgt b hb, hb.ne']`.

Rewrite `hsplit` using `[hsingle, Bf_single]`. Establish `hvn : ∀ m, v (nI X m) = 0` using `fun m => hvgt _ (by`. Rewrite using `[Fin.lt_def]`. Simplify using `[nI]`. Use the proof step `omega)`.

Establish `hlow` using `Bf_pos_ge X Z τ v hvn`. Establish `hkk : Fin.castLE X.p0_le (⟨k, hk⟩ : Fin X.p0) = k` using `Fin.ext rfl`. Establish `hnsq : 1 ≤ nsq (Pv X v)`. Unfold `nsq Pv`. Use `Finset.single_le_sum (f := fun j : Fin X.p0 => ‖v (Fin.castLE X.p0_le j)‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ (⟨k, hk⟩ : Fin X.p0))` as an intermediate fact.

Simplify using `only [hkk, hvk, norm_one, one_pow] at this`. Conclude with `this`. Establish `htn : ∀ m, t (nI X m) = 0` using `fun m => ht0 _ (by`. Rewrite using `[Fin.le_def]`. Simplify using `[nI]`.

Use the proof step `omega)`. Establish `htpos` using `Bf_pos_ge X Z τ t htn`. Establish `hnsqt : 0 ≤ nsq (Pv X t)` using `Finset.sum_nonneg fun j _ => by positivity`. Establish `hGkk : (Gp X Z τ k k).re ≤ 1`. Rewrite using `[← hkk, Gp_pp]`.

Simplify using `only [if_true, Complex.sub_re, Complex.one_re, Complex.re_sum]`. Establish `: 0 ≤ ∑ m, (Z τ m ⟨k, hk⟩ * conj (Z τ m ⟨k, hk⟩)).re` using `Finset.sum_nonneg fun m _ => by`. Rewrite using `[Complex.mul_conj]`. Simplify using `[Complex.normSq_nonneg]`. Combine the linear equalities and inequalities to obtain the conclusion.

Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hsplit, Complex.sub_re]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pivot_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    1 - X.zN Z ^ 2 ≤ (dOf X (X.xZ x Z) τ k).re ∧ (dOf X (X.xZ x Z) τ k).re ≤ 1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ k]
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  have hvgt : ∀ b, k < b → v b = 0 := by
    intro b hb
    simp [hv, uMat, hb.ne', not_lt.mpr hb.le]
  set t : Fin r → ℂ := fun b => if b < k then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by simp [ht, not_lt.mpr hb]
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have hsingle : v - t = Pi.single k 1 := by
    funext b
    rcases lt_trichotomy b k with hb | hb | hb
    · simp [ht, hb, hb.ne]
    · rw [hb]
      simp [ht, hvk]
    · simp [ht, not_lt.mpr hb.le, hvgt b hb, hb.ne']
  rw [hsingle, Bf_single] at hsplit
  have hvn : ∀ m, v (nI X m) = 0 := fun m => hvgt _ (by
    rw [Fin.lt_def]
    simp [nI]
    omega)
  have hlow := Bf_pos_ge X Z τ v hvn
  have hkk : Fin.castLE X.p0_le (⟨k, hk⟩ : Fin X.p0) = k := Fin.ext rfl
  have hnsq : 1 ≤ nsq (Pv X v) := by
    unfold nsq Pv
    have := Finset.single_le_sum (f := fun j : Fin X.p0 => ‖v (Fin.castLE X.p0_le j)‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ (⟨k, hk⟩ : Fin X.p0))
    simp only [hkk, hvk, norm_one, one_pow] at this
    exact this
  have htn : ∀ m, t (nI X m) = 0 := fun m => ht0 _ (by
    rw [Fin.le_def]
    simp [nI]
    omega)
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hGkk : (Gp X Z τ k k).re ≤ 1 := by
    rw [← hkk, Gp_pp]
    simp only [if_true, Complex.sub_re, Complex.one_re, Complex.re_sum]
    have : 0 ≤ ∑ m, (Z τ m ⟨k, hk⟩ * conj (Z τ m ⟨k, hk⟩)).re :=
      Finset.sum_nonneg fun m _ => by
        rw [Complex.mul_conj]
        simp [Complex.normSq_nonneg]
    linarith
  constructor
  · nlinarith
  · rw [hsplit, Complex.sub_re]
    nlinarith

/- English proof (translation)
Establish `hdet` using `blk_Gp X hx ho hZ τ`. Establish `hz0 : 0 ≤ X.zN Z` using `Real.iSup_nonneg fun τ => opN_nonneg _`. Establish `hz1 : 0 ≤ 1 - X.zN Z ^ 2` using `by nlinarith`. Rewrite using `[dOf_eq X ho Z τ (nI X m0)]`. Use `set k := nI X m0 with hkdef`.

Use `set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv`. Establish `hvk : v k = 1` using `by simp [hv, uMat]`. Use `set t : Fin r → ℂ := fun b => if (b : ℕ) < X.p0 then v b else 0 with ht`. Establish `ht0 : ∀ b, k ≤ b → t b = 0` using `fun b hb => by`. Establish `hb' : ¬ ((b : ℕ) < X.p0)`.

Rewrite `hb` using `[Fin.le_def]`. Simplify using `[hkdef, nI] at hb`. Use linear arithmetic over natural numbers and integers. Simplify using `[ht, hb']`. Establish `hvt : Bf X Z τ v t = 0` using `Bf_gv_zero X Z τ hdet k t ht0`.

Establish `hsplit` using `Bf_split X Z τ v t hvt`. Establish `htn : ∀ m, t (nI X m) = 0` using `fun m => by simp [ht, nI]`. Establish `htpos` using `Bf_pos_ge X Z τ t htn`. Establish `hnsqt : 0 ≤ nsq (Pv X t)` using `Finset.sum_nonneg fun j _ => by positivity`. Establish `hre` using `Bf_self_re X Z τ (v - t)`.

Establish `hP0 : Pv X (v - t) = 0`. Use function extensionality and compare the values at `a`. Establish `ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0` using `by simp [Fin.coe_castLE]`. Simplify using `[Pv, ht, ha]`. Establish `hNm : Nv X Z τ (v - t) m0 = 1`.

Establish `h1 : ∀ c : Fin X.p0, (v - t) (Fin.castLE X.p0_le c) = 0` using `fun c => congrFun hP0 c`. Simplify using `only [Nv, h1, mul_zero, Finset.sum_const_zero, add_zero]`. Rewrite using `[Pi.sub_apply, ← hkdef, hvk, ht0 k le_rfl, sub_zero]`. Establish `hN : 1 ≤ nsq (Nv X Z τ (v - t))`. Unfold `nsq`.

Use `Finset.single_le_sum (f := fun j => ‖Nv X Z τ (v - t) j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ m0)` as an intermediate fact. Simplify using `only [hNm, norm_one, one_pow] at this`. Conclude with `this`. Establish `hn0 : nsq (0 : Fin X.p0 → ℂ) = 0` using `by simp [nsq]`. Rewrite using `[hsplit, Complex.sub_re, hre, hP0, hn0]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pivot_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (m0 : Fin (r - X.p0)) : (dOf X (X.xZ x Z) τ (nI X m0)).re ≤ -1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ (nI X m0)]
  set k := nI X m0 with hkdef
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  set t : Fin r → ℂ := fun b => if (b : ℕ) < X.p0 then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by
    have hb' : ¬ ((b : ℕ) < X.p0) := by
      rw [Fin.le_def] at hb
      simp [hkdef, nI] at hb
      omega
    simp [ht, hb']
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have htn : ∀ m, t (nI X m) = 0 := fun m => by simp [ht, nI]
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hre := Bf_self_re X Z τ (v - t)
  have hP0 : Pv X (v - t) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp [Fin.coe_castLE]
    simp [Pv, ht, ha]
  have hNm : Nv X Z τ (v - t) m0 = 1 := by
    have h1 : ∀ c : Fin X.p0, (v - t) (Fin.castLE X.p0_le c) = 0 := fun c => congrFun hP0 c
    simp only [Nv, h1, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Pi.sub_apply, ← hkdef, hvk, ht0 k le_rfl, sub_zero]
  have hN : 1 ≤ nsq (Nv X Z τ (v - t)) := by
    unfold nsq
    have := Finset.single_le_sum (f := fun j => ‖Nv X Z τ (v - t) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ m0)
    simp only [hNm, norm_one, one_pow] at this
    exact this
  have hn0 : nsq (0 : Fin X.p0 → ℂ) = 0 := by simp [nsq]
  rw [hsplit, Complex.sub_re, hre, hP0, hn0]
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
