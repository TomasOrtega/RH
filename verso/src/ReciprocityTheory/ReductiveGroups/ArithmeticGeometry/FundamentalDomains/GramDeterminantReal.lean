import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := by simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
The claim follows from `(hL τ G v).map_add u u'`.
-/
theorem hC_add_left (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := (hL τ G v).map_add u u'

/- English proof (translation)
The claim follows from `(hL τ G v).map_sub u u'`.
-/
theorem hC_sub_left (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := (hL τ G v).map_sub u u'

/- English proof (translation)
The claim follows from `(hL τ G v).map_smul a u`.
-/
theorem hermC_smul_left (a : ℂ) (u v : Fin r → ℂ) : hermC τ G (a • u) v = a * hermC τ G u v := (hL τ G v).map_smul a u

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(hL τ G v) (∑ b, w b • f b) = ∑ b, w b * (hL τ G v) (f b)`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`.
-/
theorem hC_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, w b • f b) v = ∑ b, w b * hermC τ G (f b) v := by
  change (hL τ G v) (∑ b, w b • f b) = ∑ b, w b * (hL τ G v) (f b)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

def gramF {n : ℕ} (f : Fin n → Fin r → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => hermC τ G (f a) (f b)

section Proj
variable {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)

def cv : Fin n → ℂ := fun a => hermC τ G e (f a)

def yv : Fin n → ℂ := Matrix.vecMul (cv τ G f e) (gramF τ G f)⁻¹

def pv : Fin r → ℂ := ∑ b, yv τ G f e b • f b

def mt : ℂ := ∑ a, ∑ b, cv τ G f e a * (gramF τ G f)⁻¹ a b * conj (cv τ G f e b)

/- English proof (translation)
Establish `h1 : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e`. Unfold `yv`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]`. Unfold `pv`. Rewrite using `[hC_sum_left, ← h1]`.

Simplify using `only [Matrix.vecMul, dotProduct, gramF, Matrix.of_apply]`.
-/
theorem pv_orth (hA : IsUnit (gramF τ G f).det) (d : Fin n) :
    hermC τ G (pv τ G f e) (f d) = cv τ G f e d := by
  have h1 : Matrix.vecMul (yv τ G f e) (gramF τ G f) = cv τ G f e := by
    unfold yv
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  unfold pv
  rw [hC_sum_left, ← h1]
  simp only [Matrix.vecMul, dotProduct, gramF, Matrix.of_apply]

end Proj

section StepDef
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

def dv : Fin r → ℂ := pv τ G f e - pv τ G (fun a : Fin n => f a.castSucc) e

/- English proof (translation)
Unfold `dv`. Rewrite using `[hC_sub_left, pv_orth τ G f e hA d.castSucc, pv_orth τ G _ e hA' d]`. Conclude with `sub_self _`.
-/
theorem dv_orth (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) (d : Fin n) :
    hermC τ G (dv τ G f e) (f d.castSucc) = 0 := by
  unfold dv
  rw [hC_sub_left, pv_orth τ G f e hA d.castSucc, pv_orth τ G _ e hA' d]
  exact sub_self _

/- English proof (translation)
Establish `hv : Matrix.vecMul w (gramF τ G f) = 0`. Use function extensionality and compare the values at `d`. Establish `hd` using `h d`. Rewrite `hd` using `[hC_sum_left]`. Simplify `hd` using `[Matrix.vecMul, dotProduct, gramF]`.

Establish `hw : w = 0`. Establish `h2` using `congrArg (fun x => Matrix.vecMul x (gramF τ G f)⁻¹) hv`. Simplify `h2` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA]`. Simplify using `[hw]`.
-/
theorem comb_orth_zero {n : ℕ} (f : Fin n → Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (w : Fin n → ℂ) (h : ∀ d, hermC τ G (∑ b, w b • f b) (f d) = 0) : ∑ b, w b • f b = 0 := by
  have hv : Matrix.vecMul w (gramF τ G f) = 0 := by
    funext d
    have hd := h d
    rw [hC_sum_left] at hd
    simpa [Matrix.vecMul, dotProduct, gramF] using hd
  have hw : w = 0 := by
    have h2 := congrArg (fun x => Matrix.vecMul x (gramF τ G f)⁻¹) hv
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA] using h2
  simp [hw]

/- English proof (translation)
Unfold `dv pv`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last]`.
-/
theorem dv_eq {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) :
    dv τ G f e = ∑ b, (yv τ G f e b -
      Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b) • f b := by
  unfold dv pv
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/- English proof (translation)
Establish `h : dv τ G f e = ∑ a : Fin n, (yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) • f a.castSucc`. Rewrite using `[dv_eq, Fin.sum_univ_castSucc]`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last, hy]`. Rewrite using `[h]`. Use `comb_orth_zero τ G (fun a : Fin n => f a.castSucc) hA' (fun a => yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) ?_` and prove the remaining obligations.

Introduce `d`. Establish `hd` using `dv_orth τ G f e hA hA' d`. Rewrite `hd` using `[h]`. Conclude with `hd`.
-/
theorem dv_zero {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det)
    (hy : yv τ G f e (Fin.last n) = 0) : dv τ G f e = 0 := by
  have h : dv τ G f e = ∑ a : Fin n,
      (yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) • f a.castSucc := by
    rw [dv_eq, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, hy]
  rw [h]
  refine comb_orth_zero τ G (fun a : Fin n => f a.castSucc) hA'
    (fun a => yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) ?_
  intro d
  have hd := dv_orth τ G f e hA hA' d
  rw [h] at hd
  exact hd

end StepDef

variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG

/- English proof (translation)
Simplify using `only [hermC, map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hG x y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hC_conj (u v : Fin r → ℂ) : hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hG x y]
  ring

/- English proof (translation)
The claim follows from `Complex.conj_eq_iff_im.mp (hC_conj hG u u).symm`.
-/
theorem hC_self_real (u : Fin r → ℂ) : (hermC τ G u u).im = 0 := Complex.conj_eq_iff_im.mp (hC_conj hG u u).symm

/- English proof (translation)
Simplify using `only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem hC_add_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hC_sub_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermC_smul_right (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hC_conj hG (∑ b, w b • f b) v, hC_sum_left, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hC_conj hG (f b) v]`.
-/
theorem hC_sum_right {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G v (∑ b, w b • f b) = ∑ b, conj (w b) * hermC τ G v (f b) := by
  rw [hC_conj hG (∑ b, w b • f b) v, hC_sum_left, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, hC_conj hG (f b) v]

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [gramF, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[hC_sum_left]`. Repeatedly rewrite using `[hC_sum_right hG]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramF_comb {n : ℕ} (f : Fin n → Fin r → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    gramF τ G (fun a => ∑ b, M b a • f b) = Mᵀ * gramF τ G f * M.map conj := by
  ext a c
  simp only [gramF, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hC_sum_left]
  simp_rw [hC_sum_right hG]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/- English proof (translation)
Rewrite using `[gramF_comb hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Use `congr 1`. Conclude with `((starRingEnd ℂ).map_det M).symm`.
-/
theorem det_gramF_comb {n : ℕ} (f : Fin n → Fin r → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (gramF τ G (fun a => ∑ b, M b a • f b)).det = M.det * (gramF τ G f).det * conj M.det := by
  rw [gramF_comb hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact ((starRingEnd ℂ).map_det M).symm

/- English proof (translation)
Establish `h : (gramF τ G f)ᴴ = gramF τ G f`. Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [gramF, Matrix.of_apply]`. Rewrite using `[hC_conj hG (f b) (f a), starRingEnd_apply]`.

Establish `h2` using `Matrix.det_conjTranspose (gramF τ G f)`. Rewrite `h2` using `[h]`. Apply `Complex.conj_eq_iff_im.mp` to reduce the goal to its premises. Rewrite using `[starRingEnd_apply]`. Conclude with `h2.symm`.
-/
theorem det_gramF_real {n : ℕ} (f : Fin n → Fin r → ℂ) : (gramF τ G f).det.im = 0 := by
  have h : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have h2 := Matrix.det_conjTranspose (gramF τ G f)
  rw [h] at h2
  apply Complex.conj_eq_iff_im.mp
  rw [starRingEnd_apply]
  exact h2.symm

/- English proof (translation)
Rewrite using `[show hermC τ G (pv τ G f e) (pv τ G f e) = hermC τ G (pv τ G f e) (∑ b, yv τ G f e b • f b) from rfl, hC_sum_right hG]`. Simplify using `only [pv_orth τ G f e hA]`.
-/
theorem hC_pv_self {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) = ∑ b, conj (yv τ G f e b) * cv τ G f e b := by
  rw [show hermC τ G (pv τ G f e) (pv τ G f e) =
      hermC τ G (pv τ G f e) (∑ b, yv τ G f e b • f b) from rfl, hC_sum_right hG]
  simp only [pv_orth τ G f e hA]

/- English proof (translation)
Rewrite using `[hC_pv_self hG f e hA]`. Establish `hH : (gramF τ G f)ᴴ = gramF τ G f`. Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [gramF, Matrix.of_apply]`.

Rewrite using `[hC_conj hG (f b) (f a), starRingEnd_apply]`. Establish `hI : ∀ a b, conj ((gramF τ G f)⁻¹ a b) = (gramF τ G f)⁻¹ b a`. Introduce `a b`. Establish `h3` using `congrFun (congrFun (Matrix.conjTranspose_nonsing_inv (gramF τ G f)) b) a`. Rewrite `h3` using `[hH, Matrix.conjTranspose_apply]`.

Rewrite using `[starRingEnd_apply]`. Conclude with `h3`. Unfold `mt yv`. Simplify using `only [Matrix.vecMul, dotProduct, map_sum, map_mul, hI, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mt_eq {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det) :
    mt τ G f e = hermC τ G (pv τ G f e) (pv τ G f e) := by
  rw [hC_pv_self hG f e hA]
  have hH : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have hI : ∀ a b, conj ((gramF τ G f)⁻¹ a b) = (gramF τ G f)⁻¹ b a := by
    intro a b
    have h3 := congrFun (congrFun (Matrix.conjTranspose_nonsing_inv (gramF τ G f)) b) a
    rw [hH, Matrix.conjTranspose_apply] at h3
    rw [starRingEnd_apply]
    exact h3
  unfold mt yv
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hI, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

section Step
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

/- English proof (translation)
Establish `hp : pv τ G f e = pv τ G (fun a : Fin n => f a.castSucc) e + dv τ G f e`. Unfold `dv`. Normalize the expressions using the abelian group laws. Establish `h0 : hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) = 0`. Rewrite using `[show hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) = hermC τ G (dv τ G f e) (∑ b, yv τ G (fun a : Fin n => f a.castSucc) e b • f b.castSucc) from rfl, hC_sum_right hG]`.

Conclude with `Finset.sum_eq_zero fun b _ => by simp only [dv_orth τ G f e hA hA' b, mul_zero]`. Establish `h1 : hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e) (dv τ G f e) = 0`. Rewrite using `[hC_conj hG (dv τ G f e) _, h0, map_zero]`. Rewrite using `[hp, hC_add_left, hC_add_right hG, hC_add_right hG, h0, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pv_pyth (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) =
      hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e)
        (pv τ G (fun a : Fin n => f a.castSucc) e) + hermC τ G (dv τ G f e) (dv τ G f e) := by
  have hp : pv τ G f e = pv τ G (fun a : Fin n => f a.castSucc) e + dv τ G f e := by
    unfold dv
    abel
  have h0 : hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) = 0 := by
    rw [show hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) =
        hermC τ G (dv τ G f e) (∑ b, yv τ G (fun a : Fin n => f a.castSucc) e b • f b.castSucc)
        from rfl, hC_sum_right hG]
    exact Finset.sum_eq_zero fun b _ => by simp only [dv_orth τ G f e hA hA' b, mul_zero]
  have h1 : hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e) (dv τ G f e) = 0 := by
    rw [hC_conj hG (dv τ G f e) _, h0, map_zero]
  rw [hp, hC_add_left, hC_add_right hG, hC_add_right hG, h0, h1]
  ring

/- English proof (translation)
Take `⟨M, hMdef⟩ : ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M = Matrix.of fun b a => if a = Fin.last n then (yv τ G f e b - Fin.snoc (α` from `fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b) else if b = a then 1 else 0 := ⟨_, rfl⟩`. Take `⟨g, hgdef⟩ : ∃ g : Fin (n + 1) → Fin r → ℂ, g = fun a => ∑ b, M b a • f b` from `⟨_, rfl⟩`. Establish `hgl : g (Fin.last n) = dv τ G f e`. Rewrite using `[hgdef, dv_eq]`. Simplify using `[hMdef]`.

Establish `hgc : ∀ a : Fin n, g a.castSucc = f a.castSucc`. Introduce `a`. Rewrite using `[hgdef]`. Simplify using `[hMdef, Fin.castSucc_ne_last]`. Establish `hM : M.det = yv τ G f e (Fin.last n)`.

Rewrite using `[Matrix.det_of_upperTriangular, Fin.prod_univ_castSucc]`. Simplify using `[hMdef, Fin.castSucc_ne_last]`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `hj : j ≠ Fin.last n` using `ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last i))`.

Simplify using `[hMdef, hj, ne_of_gt hij']`. Establish `hgram : (gramF τ G g).det = (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e)`. Rewrite using `[Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]`. Establish `hsub : (gramF τ G g).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = gramF τ G (fun a : Fin n => f a.castSucc)`. Use extensionality with `i j`.

Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last, gramF, Matrix.of_apply, hgc]`. Establish `hz0 : ∀ i : Fin n, gramF τ G g i.castSucc (Fin.last n) = 0`. Introduce `i`. Simplify using `only [gramF, Matrix.of_apply, hgc, hgl]`. Rewrite using `[hC_conj hG (dv τ G f e) (f i.castSucc), dv_orth τ G f e hA hA' i, map_zero]`.

Establish `hll : gramF τ G g (Fin.last n) (Fin.last n) = hermC τ G (dv τ G f e) (dv τ G f e)`. Simplify using `only [gramF, Matrix.of_apply, hgl]`. Establish `hsgn : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1`. Rewrite using `[← two_mul, pow_mul]`. Evaluate the numerical expressions.

Simplify using `only [hz0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]`. Rewrite using `[hsub, hll, hsgn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd` using `det_gramF_comb hG f M`. Rewrite `hd` using `[← hgdef, hgram, hM]`.

Rewrite using `[hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_step (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) =
      yv τ G f e (Fin.last n) * conj (yv τ G f e (Fin.last n)) * (gramF τ G f).det := by
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M = Matrix.of fun b a =>
      if a = Fin.last n then
        (yv τ G f e b - Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b)
      else if b = a then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Fin (n + 1) → Fin r → ℂ, g = fun a => ∑ b, M b a • f b := ⟨_, rfl⟩
  have hgl : g (Fin.last n) = dv τ G f e := by
    rw [hgdef, dv_eq]
    simp [hMdef]
  have hgc : ∀ a : Fin n, g a.castSucc = f a.castSucc := by
    intro a
    rw [hgdef]
    simp [hMdef, Fin.castSucc_ne_last]
  have hM : M.det = yv τ G f e (Fin.last n) := by
    rw [Matrix.det_of_upperTriangular, Fin.prod_univ_castSucc]
    · simp [hMdef, Fin.castSucc_ne_last]
    · intro i j hij
      have hij' : j < i := hij
      have hj : j ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last i))
      simp [hMdef, hj, ne_of_gt hij']
  have hgram : (gramF τ G g).det =
      (gramF τ G (fun a : Fin n => f a.castSucc)).det * hermC τ G (dv τ G f e) (dv τ G f e) := by
    rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]
    have hsub : (gramF τ G g).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
        gramF τ G (fun a : Fin n => f a.castSucc) := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, gramF, Matrix.of_apply, hgc]
    have hz0 : ∀ i : Fin n, gramF τ G g i.castSucc (Fin.last n) = 0 := by
      intro i
      simp only [gramF, Matrix.of_apply, hgc, hgl]
      rw [hC_conj hG (dv τ G f e) (f i.castSucc), dv_orth τ G f e hA hA' i, map_zero]
    have hll : gramF τ G g (Fin.last n) (Fin.last n) = hermC τ G (dv τ G f e) (dv τ G f e) := by
      simp only [gramF, Matrix.of_apply, hgl]
    have hsgn : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    simp only [hz0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hsub, hll, hsgn]
    ring
  have hd := det_gramF_comb hG f M
  rw [← hgdef, hgram, hM] at hd
  rw [hd]
  ring

end Step

end

end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
