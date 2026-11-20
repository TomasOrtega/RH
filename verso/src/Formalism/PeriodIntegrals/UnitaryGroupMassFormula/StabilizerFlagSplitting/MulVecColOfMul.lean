import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.PrjMulVecOfL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.UnitR

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

def Ym (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' γ j i

def Pm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : B.Mat k r :=
  Proj.prj (Hpk k r) (Ym k r z z' γ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma Ym_col (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j) :
    (fun i => Ym k r z z' γ i j) = gramVec k r z z' γ j := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Ym, mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
lemma Ym_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c) :
    Ym k r z z' γ *ᵥ c = ∑ j, c j • gramVec k r z z' γ j := by
  ext i
  simp [Ym, mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Simplify using `only [herm, mulVec, dotProduct, mul_apply, conjTranspose_apply, Ym, of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
lemma L_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) (j) :
    (((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  simp only [herm, mulVec, dotProduct, mul_apply, conjTranspose_apply, Ym, of_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[gramM, ← L_mulVec]`. Simplify using `only [mulVec, dotProduct, mul_apply, Ym, of_apply]`.
-/
lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    gramM k r z z' γ = (Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ := by
  ext i j
  rw [gramM, ← L_mulVec]
  simp only [mulVec, dotProduct, mul_apply, Ym, of_apply]

/- English proof (translation)
Establish `: (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Ym k r z z' γ)ᴴ`. Use extensionality with `i j`. Simplify using `[Ym, conjTranspose_apply]`. Rewrite using `[Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, this]`.
-/
lemma mem_U_iff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) :
    v ∈ Uperp k r z z' γ ↔ ((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  have : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Ym k r z z' γ)ᴴ := by
    ext i j; simp [Ym, conjTranspose_apply]
  rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, this]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (GBasic.Hpk_sq k r)`. Rewrite `h` using `[det_mul, det_one]`. Conclude with `isUnit_iff_ne_zero.2 (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h)`.
-/
lemma hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (GBasic.Hpk_sq k r)
  rw [det_mul, det_one] at h
  exact isUnit_iff_ne_zero.2 (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h)

/- English proof (translation)
The claim follows from `(uHGroup _ _ (hpk_unit k r)).1`.
-/
lemma GV_one (k r : ℕ) : (1 : B.Mat k r) ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).1

/- English proof (translation)
The claim follows from `(uHGroup _ _ (hpk_unit k r)).2.1 g hg h hh`.
-/
lemma GV_mul (k r : ℕ) {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).2.1 g hg h hh

/- English proof (translation)
The claim follows from `((uHGroup _ _ (hpk_unit k r)).2.2 g hg).1`.
-/
lemma GV_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).1

/- English proof (translation)
The claim follows from `((uHGroup _ _ (hpk_unit k r)).2.2 g hg).2`.
-/
lemma GV_inv (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).2

/- English proof (translation)
The claim follows from `hg`.
-/
lemma GV_eq (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : gᴴ * Hpk k r * g = Hpk k r := hg

/- English proof (translation)
Rewrite using `[← gram_eq]`. Establish `h` using `gGram k r z z' hs.2.1.1 hs.2.2.1 γ hp.1`. Establish `hne : (gramM k r z z' γ).det ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`.

Use `hp.2` as an intermediate fact. Establish `h1 : (Gf k r z z' γ : ℝ) = 0` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `isUnit_iff_ne_zero.2 hne`.
-/
lemma gram_unit (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : IsUnit ((Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ).det := by
  rw [← gram_eq]
  have h := gGram k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  have hne : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    have := hp.2
    have h1 : (Gf k r z z' γ : ℝ) = 0 := by exact_mod_cast h
    linarith
  exact isUnit_iff_ne_zero.2 hne

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`. Rewrite using `[GV_eq k r hg]`.
-/
lemma herm_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [GV_eq k r hg]

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (h j) i` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, mul_apply]`.
-/
lemma mul_eq_of_cols {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : ∀ j, A *ᵥ (fun i => C i j) = fun i => C i j) :
    A * C = C := by
  ext i j
  have := congrFun (h j) i
  simpa [mulVec, dotProduct, mul_apply] using this

/- English proof (translation)
Use extensionality with `i`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, mul_apply]`.
-/
lemma mulVec_col_of_mul {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : A * C = C) (j : m) :
    A *ᵥ (fun i => C i j) = fun i => C i j := by
  ext i
  have := congrFun (congrFun h i) j
  simpa [mulVec, dotProduct, mul_apply] using this

/- English proof (translation)
Introduce `a`. Use the proof step `induction' ht : a.val using Nat.strong_induction_on with t ih generalizing a`. Establish `hsp : Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1) ≤ LinearMap.ker (Matrix.mulVecLin ((g - 1) ^ t))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`.

Establish `hb : b.1.val < t` using `by rw [← ht]; exact b.2`. Use `ih b.1.val hb b.1 rfl` as an intermediate fact. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]`. Establish `e : t = (t - (b.1.val + 1)) + (b.1.val + 1)` using `by omega`. Rewrite using `[e, pow_add, ← mulVec_mulVec, this, mulVec_zero]`.

Establish `h1` using `hsp (hv a)`. Simplify using `only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1`. Rewrite using `[pow_succ, ← mulVec_mulVec, sub_mulVec, one_mulVec]`. Conclude with `h1`.
-/
lemma flag_nilp {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ (a.val + 1)) *ᵥ v a = 0 := by
  intro a
  induction' ht : a.val using Nat.strong_induction_on with t ih generalizing a
  have hsp : Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1) ≤
      LinearMap.ker (Matrix.mulVecLin ((g - 1) ^ t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : b.1.val < t := by rw [← ht]; exact b.2
    have := ih b.1.val hb b.1 rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have e : t = (t - (b.1.val + 1)) + (b.1.val + 1) := by omega
    rw [e, pow_add, ← mulVec_mulVec, this, mulVec_zero]
  have h1 := hsp (hv a)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1
  rw [pow_succ, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  exact h1

/- English proof (translation)
Introduce `a`. Establish `e : m = (m - (a.val + 1)) + (a.val + 1)` using `by omega`. Rewrite using `[e, pow_add, ← mulVec_mulVec, flag_nilp g v hv a, mulVec_zero]`.
-/
lemma flag_nilp_all {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ m) *ᵥ v a = 0 := by
  intro a
  have e : m = (m - (a.val + 1)) + (a.val + 1) := by omega
  rw [e, pow_add, ← mulVec_mulVec, flag_nilp g v hv a, mulVec_zero]

/- English proof (translation)
The claim follows from `| 0 => by simp [h1] | p + 1 => by rw [pow_succ, conj_pow A G Gi h1 h2 p, pow_succ] calc Gi * A ^ p * G * (Gi * A * G) = Gi * A ^ p * (G * Gi) * A * G := by noncomm_ring _ = Gi * (A ^ p * A) * G := by rw [h2]; noncomm_ring`.
-/
lemma conj_pow {N : ℕ} (A G Gi : Matrix (Fin N) (Fin N) ℂ) (h1 : Gi * G = 1) (h2 : G * Gi = 1) :
    ∀ p : ℕ, (Gi * A * G) ^ p = Gi * A ^ p * G
  | 0 => by simp [h1]
  | p + 1 => by
    rw [pow_succ, conj_pow A G Gi h1 h2 p, pow_succ]
    calc Gi * A ^ p * G * (Gi * A * G) = Gi * A ^ p * (G * Gi) * A * G := by noncomm_ring
      _ = Gi * (A ^ p * A) * G := by rw [h2]; noncomm_ring

/- English proof (translation)
Unfold `fvec`. Rewrite using `[dif_pos a.isLt]`.
-/
lemma fvec_lt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
  unfold fvec; rw [dif_pos a.isLt]

end PI.StabSplit
