import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SBasic

open Matrix

noncomputable section

namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL

variable {k r : ℕ}

def fcol (k r : ℕ) (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h1 : i.val < r then e ⟨i.val, h1⟩
  else if h2 : i.val < r + k then wf ⟨i.val - r, by omega⟩
  else if h3 : i.val = r + k then z0
  else f ⟨2 * r + k - i.val, by have := i.isLt; omega⟩

def Pm (k r : ℕ) (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun a j => fcol k r e f wf z0 j a

/- English proof (translation)
Simplify using `only [hJ, Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, star_sum, star_mul', star_star]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
lemma hJ_swap {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp <;> ring

section Frame

variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
lemma pm_mulVec_single (j : Fin (2 * r + k + 1)) :
    Pm k r e f wf z0 *ᵥ Pi.single j 1 = fcol k r e f wf z0 j := by
  rw [Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[Pm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
lemma pm_mulVec_eq_sum (c : Fin (2 * r + k + 1) → ℂ) :
    Pm k r e f wf z0 *ᵥ c = ∑ j, c j • fcol k r e f wf z0 j := by
  funext a
  simp [Pm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hJ, Jm, Matrix.mul_diagonal, Matrix.mulVec_diagonal, dotProduct, Matrix.conjTranspose_apply, Pm, Matrix.of_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl (fun s _ => by ring)` and prove the remaining obligations.
-/
lemma gram_apply (i j : Fin (2 * r + k + 1)) :
    ((Pm k r e f wf z0)ᴴ * Jm ε * Pm k r e f wf z0) i j =
      hJ ε (fcol k r e f wf z0 i) (fcol k r e f wf z0 j) := by
  rw [Matrix.mul_apply]
  simp only [hJ, Jm, Matrix.mul_diagonal, Matrix.mulVec_diagonal, dotProduct,
    Matrix.conjTranspose_apply, Pm, Matrix.of_apply, Pi.star_apply]
  refine Finset.sum_congr rfl (fun s _ => by ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pmH_J_mulVec_apply (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    ((Pm k r e f wf z0)ᴴ *ᵥ (Jm ε *ᵥ y)) i = hJ ε (fcol k r e f wf z0 i) y := by
  rfl

variable (hF : IsFrameJ ε e f wf z0)
include hF

/- English proof (translation)
Establish `fe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0` using `fun a b => by`. Apply the tactic sequence `rw [hJ_swap, hF.ef]; split_ifs with h1 h2 h2 <;> simp_all`. Establish `ze : ∀ a, hJ ε z0 (e a) = 0` using `fun a => by rw [hJ_swap, hF.ez, star_zero]`. Establish `zf : ∀ a, hJ ε z0 (f a) = 0` using `fun a => by rw [hJ_swap, hF.fz, star_zero]`. Establish `we : ∀ c a, hJ ε (wf a) (e c) = 0` using `fun c a => by rw [hJ_swap, hF.ew, star_zero]`.

Establish `wf' : ∀ c a, hJ ε (wf a) (f c) = 0` using `fun c a => by rw [hJ_swap, hF.fw, star_zero]`. Establish `wz : ∀ a, hJ ε (wf a) z0 = 0` using `fun a => by rw [hJ_swap, hF.zw, star_zero]`. Use extensionality with `i j`. Rewrite using `[gram_apply]`. Establish `hi` using `i.isLt`.

Establish `hj` using `j.isLt`. Simplify using `only [Hpk, Fin.ext_iff, fcol]`. Apply the tactic sequence `split_ifs <;>`. Apply the tactic sequence `simp only [hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw, fe, ze, zf, we, wf', wz, Fin.mk.injEq] <;>`. Apply the tactic sequence `(try split_ifs) <;> first | rfl | (exfalso; omega)`.
-/
lemma gram_eq_Hpk : (Pm k r e f wf z0)ᴴ * Jm ε * Pm k r e f wf z0 = Hpk k r := by
  have fe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [hJ_swap, hF.ef]; split_ifs with h1 h2 h2 <;> simp_all
  have ze : ∀ a, hJ ε z0 (e a) = 0 := fun a => by rw [hJ_swap, hF.ez, star_zero]
  have zf : ∀ a, hJ ε z0 (f a) = 0 := fun a => by rw [hJ_swap, hF.fz, star_zero]
  have we : ∀ c a, hJ ε (wf a) (e c) = 0 := fun c a => by rw [hJ_swap, hF.ew, star_zero]
  have wf' : ∀ c a, hJ ε (wf a) (f c) = 0 := fun c a => by rw [hJ_swap, hF.fw, star_zero]
  have wz : ∀ a, hJ ε (wf a) z0 = 0 := fun a => by rw [hJ_swap, hF.zw, star_zero]
  ext i j
  rw [gram_apply]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff, fcol]
  split_ifs <;>
    simp only [hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw, fe, ze, zf, we, wf',
      wz, Fin.mk.injEq] <;>
    (try split_ifs) <;> first | rfl | (exfalso; omega)

def Qm (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Hpk k r * (Pm k r e f wf z0)ᴴ * Jm ε

/- English proof (translation)
Unfold `Qm`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm ε), gram_eq_Hpk hF, Hpk_mul_self]`.
-/
lemma qm_mul_pm : Qm k r ε e f wf z0 * Pm k r e f wf z0 = 1 := by
  unfold Qm
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm ε), gram_eq_Hpk hF, Hpk_mul_self]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp (qm_mul_pm hF)`.
-/
lemma pm_mul_qm : Pm k r e f wf z0 * Qm k r ε e f wf z0 = 1 := mul_eq_one_comm.mp (qm_mul_pm hF)

/- English proof (translation)
Rewrite using `[← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, qm_mul_pm hF, Matrix.one_mulVec]`.
-/
lemma qm_mulVec_fcol (j : Fin (2 * r + k + 1)) :
    Qm k r ε e f wf z0 *ᵥ fcol k r e f wf z0 j = Pi.single j 1 := by
  rw [← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, qm_mul_pm hF,
    Matrix.one_mulVec]

/- English proof (translation)
Unfold `Qm`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Hpk_mulVec_apply, pmH_J_mulVec_apply]`.
-/
lemma qm_mulVec_apply (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Qm k r ε e f wf z0 *ᵥ y) i = epsI k r i * hJ ε (fcol k r e f wf z0 (piI k r i)) y := by
  unfold Qm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Hpk_mulVec_apply, pmH_J_mulVec_apply]

omit hF in
/- English proof (translation)
Unfold `fcol`. Rewrite using `[dif_pos (by simp [eI])]`. Both sides reduce to the same expression.
-/
lemma fcol_eI (a : Fin r) : fcol k r e f wf z0 (eI k r a) = e a := by
  unfold fcol
  rw [dif_pos (by simp [eI])]
  rfl

omit hF in
/- English proof (translation)
Unfold `fcol`. Rewrite using `[dif_pos hj]`.
-/
lemma fcol_lt (j : Fin (2 * r + k + 1)) (hj : j.val < r) : fcol k r e f wf z0 j = e ⟨j.val, hj⟩ := by
  unfold fcol
  rw [dif_pos hj]

/- English proof (translation)
Unfold `fcol`. Rewrite using `[dif_neg (by omega)]`. Use `split_ifs with h2 h3`. Conclude with `hF.ew a _`. Conclude with `hF.ez a`.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.
-/
lemma fcol_mid_orth {j : Fin (2 * r + k + 1)} (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    hJ ε (e a) (fcol k r e f wf z0 j) = 0 := by
  unfold fcol
  rw [dif_neg (by omega)]
  split_ifs with h2 h3
  · exact hF.ew a _
  · exact hF.ez a
  · exfalso; omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Set `W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ)` to `{ carrier := {v | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qm k r ε e f wf z0 *ᵥ v) i = 0} add_mem' := fun {x y} hx hy i hi => by`. Rewrite using `[Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]`. Use the proof step `zero_mem' := fun i _ => by simp`.

Use the proof step `smul_mem' := fun c x hx i hi => by`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero] }`. Establish `hle : spanLt e a ≤ W`. Unfold `spanLt`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨b, hb, rfl⟩ i hi`. Establish `hb' : b.val < a` using `hb`. Establish `hfb : e b = fcol k r e f wf z0 ⟨b.val, by omega⟩` using `by simp [fcol, b.isLt]`. Use `show (Qm k r ε e f wf z0 *ᵥ e b) i = 0`. Rewrite using `[hfb, qm_mulVec_fcol hF, Pi.single_apply, if_neg]`.

Introduce `h`. Rewrite `h` using `[Fin.ext_iff]`. Simplify using `only at h`. Use linear arithmetic over natural numbers and integers. Conclude with `hle hv`.

Introduce `hv`. Establish `hv' : v = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, pm_mul_qm hF, Matrix.one_mulVec]`. Rewrite using `[hv', pm_mulVec_eq_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : a ≤ j.val`. Rewrite using `[hv j hj, zero_smul]`. Conclude with `Submodule.zero_mem _`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, by omega⟩, ?_, ?_⟩)` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[fcol_lt j (by omega)]`.
-/
lemma mem_spanLt_iff {a : ℕ} (ha : a ≤ r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ spanLt e a ↔ ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qm k r ε e f wf z0 *ᵥ v) i = 0 := by
  constructor
  · intro hv
    let W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
      { carrier := {v | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qm k r ε e f wf z0 *ᵥ v) i = 0}
        add_mem' := fun {x y} hx hy i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c x hx i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero] }
    have hle : spanLt e a ≤ W := by
      unfold spanLt
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩ i hi
      have hb' : b.val < a := hb
      have hfb : e b = fcol k r e f wf z0 ⟨b.val, by omega⟩ := by simp [fcol, b.isLt]
      show (Qm k r ε e f wf z0 *ᵥ e b) i = 0
      rw [hfb, qm_mulVec_fcol hF, Pi.single_apply, if_neg]
      intro h
      rw [Fin.ext_iff] at h
      simp only at h
      omega
    exact hle hv
  · intro hv
    have hv' : v = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, pm_mul_qm hF, Matrix.one_mulVec]
    rw [hv', pm_mulVec_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : a ≤ j.val
    · rw [hv j hj, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, by omega⟩, ?_, ?_⟩)
      · simp only [Set.mem_ofPred_eq]; omega
      · rw [fcol_lt j (by omega)]

/- English proof (translation)
Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, qm_mulVec_fcol hF, ← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Pi.sub_apply, Matrix.mulVec_single_one]`. Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
lemma colm (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Qm k r ε e f wf z0 *ᵥ ((g - 1) *ᵥ fcol k r e f wf z0 j)) i =
      (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i j - (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, qm_mulVec_fcol hF,
    ← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Pi.sub_apply, Matrix.mulVec_single_one]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

/- English proof (translation)
Establish `hPQ` using `pm_mul_qm hF`. Establish `hQH : (Qm k r ε e f wf z0)ᴴ = Jm ε * (Pm k r e f wf z0 * Hpk k r)`. Unfold `Qm`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Hpk_conjTranspose]`. Establish `hK : (Qm k r ε e f wf z0)ᴴ * Hpk k r * Qm k r ε e f wf z0 = Jm ε`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQH]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jm ε := by rw [Hpk_mul_self, Matrix.mul_one, hPQ, Matrix.mul_one]`. Rewrite using `[← hK]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
lemma conj_form (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (Qm k r ε e f wf z0 * g * Pm k r e f wf z0)ᴴ * Hpk k r * (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) =
      (Pm k r e f wf z0)ᴴ * (gᴴ * Jm ε * g) * Pm k r e f wf z0 := by
  have hPQ := pm_mul_qm hF
  have hQH : (Qm k r ε e f wf z0)ᴴ = Jm ε * (Pm k r e f wf z0 * Hpk k r) := by
    unfold Qm
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose,
      Hpk_conjTranspose]
  have hK : (Qm k r ε e f wf z0)ᴴ * Hpk k r * Qm k r ε e f wf z0 = Jm ε := by
    calc (Qm k r ε e f wf z0)ᴴ * Hpk k r * Qm k r ε e f wf z0
        = Jm ε * (Pm k r e f wf z0 * (Hpk k r * Hpk k r) * Qm k r ε e f wf z0) := by
          rw [hQH]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [Hpk_mul_self, Matrix.mul_one, hPQ, Matrix.mul_one]
  rw [← hK]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Establish `hPQ` using `pm_mul_qm hF`. Establish `hQP' : (Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]`. Establish `back : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0 = X`. Introduce `X`.

Rewrite using `[show (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0 = ((Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ) * X * (Pm k r e f wf z0 * Qm k r ε e f wf z0) by`. Simplify using `only [Matrix.mul_assoc], hQP', hPQ, Matrix.one_mul, Matrix.mul_one]`. Use `show gᴴ * Jm ε * g = Jm ε ↔ _ = _`. Rewrite using `[conj_form hF, ← gram_eq_Hpk hF]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h]`. Introduce `h`. Rewrite using `[← back (gᴴ * Jm ε * g), h, back]`.
-/
lemma inUJ_iff_UH (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    inUJ ε g ↔ Qm k r ε e f wf z0 * g * Pm k r e f wf z0 ∈ UH (Hpk k r) := by
  have hPQ := pm_mul_qm hF
  have hQP' : (Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  have back : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0 = X := by
    intro X
    rw [show (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0
        = ((Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ) * X * (Pm k r e f wf z0 * Qm k r ε e f wf z0) by
          simp only [Matrix.mul_assoc], hQP', hPQ, Matrix.one_mul, Matrix.mul_one]
  show gᴴ * Jm ε * g = Jm ε ↔ _ = _
  rw [conj_form hF, ← gram_eq_Hpk hF]
  constructor
  · intro h; rw [h]
  · intro h
    rw [← back (gᴴ * Jm ε * g), h, back]

/- English proof (translation)
Establish `hPQ` using `pm_mul_qm hF`. Establish `hE : (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ↔ (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i (eI k r a) = if i = eI k r a then 1 else 0)`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[mem_spanLt_iff hF a.isLt.le]`. Use `forall_congr' fun i => imp_congr_right fun _ => ?_` and prove the remaining obligations.

Rewrite using `[← fcol_eI (k := k) (e := e) (f := f) (wf := wf) (z0 := z0) a, colm hF, sub_eq_zero, Matrix.one_apply]`. Establish `hM : (∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → (g - 1) *ᵥ fcol k r e f wf z0 j ∈ spanLt e r) ↔ (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i j = if i = j then 1 else 0)`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hj1 hj2 hi`. Use `(mem_spanLt_iff hF le_rfl _).1 (h j hj1 hj2) i hi` as an intermediate fact.

Rewrite `this` using `[colm hF, sub_eq_zero, Matrix.one_apply]`. Then use the resulting hypothesis. Introduce `h j hj1 hj2`. Rewrite using `[mem_spanLt_iff hF le_rfl]`. Introduce `i hi`. Rewrite using `[colm hF, sub_eq_zero, Matrix.one_apply]`.

Conclude with `h i j hj1 hj2 hi`. Simplify using `only [Nset, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, ⟨hS1, _⟩, hN⟩`. Conclude with `⟨(inUJ_iff_UH hF g).1 hu, hE.1 hS1, hM.1 fun j hj1 hj2 => hN _ (fcol_mid_orth hF hj1 hj2)⟩`.

Introduce and unpack `⟨hu, h2, h3⟩`. Establish `hmid` using `hM.2 h3`. Establish `hE2` using `hE.2 h2`. Establish `hzr : (g - 1) *ᵥ z0 ∈ spanLt e r`. Use `hmid ⟨r + k, by omega⟩ (by simp) (by simp)` as an intermediate fact.

Establish `hf : fcol k r e f wf z0 ⟨r + k, by omega⟩ = z0` using `by simp [fcol]`. Rewrite `this` using `[hf]`. Then use the resulting hypothesis. Use `⟨(inUJ_iff_UH hF g).2 hu, ⟨hE2, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hzz : z = c⁻¹ • z0` using `by rw [hz, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[hzz, Matrix.mulVec_smul]`.

Conclude with `Submodule.smul_mem _ _ hzr`. Introduce `y hy`. Establish `hy' : y = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]`. Rewrite using `[hy', pm_mulVec_eq_sum, Matrix.mulVec_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Distinguish the cases in `hj : j.val < r`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `hE2 ⟨j.val, hj⟩` as an intermediate fact.

Rewrite using `[fcol_lt j hj]`. Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Conclude with `Set.image_mono fun b hb => lt_trans hb hj`. Distinguish the cases in `hj' : j.val ≤ r + k`. Conclude with `Submodule.smul_mem _ _ (hmid j (by omega) hj')`.

Establish `hv` using `piI_val (k := k) (r := r) j`. Apply the tactic sequence `have hpl : (piI k r j).val < r := by rw [hv]; split_ifs <;> omega`. Rewrite using `[qm_mulVec_apply hF, fcol_lt _ hpl, hy, mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem frame_conj_iff {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) (hz : z0 = c • z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (inUJ ε g ∧ InN ε e z g) ↔ Qm k r ε e f wf z0 * g * Pm k r e f wf z0 ∈ Nset k r := by
  have hPQ := pm_mul_qm hF
  have hE : (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ↔
      (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i (eI k r a) = if i = eI k r a then 1 else 0) := by
    refine forall_congr' fun a => ?_
    rw [mem_spanLt_iff hF a.isLt.le]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [← fcol_eI (k := k) (e := e) (f := f) (wf := wf) (z0 := z0) a, colm hF, sub_eq_zero, Matrix.one_apply]
  have hM : (∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
        (g - 1) *ᵥ fcol k r e f wf z0 j ∈ spanLt e r) ↔
      (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i j = if i = j then 1 else 0) := by
    constructor
    · intro h i j hj1 hj2 hi
      have := (mem_spanLt_iff hF le_rfl _).1 (h j hj1 hj2) i hi
      rwa [colm hF, sub_eq_zero, Matrix.one_apply] at this
    · intro h j hj1 hj2
      rw [mem_spanLt_iff hF le_rfl]
      intro i hi
      rw [colm hF, sub_eq_zero, Matrix.one_apply]
      exact h i j hj1 hj2 hi
  simp only [Nset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, ⟨hS1, _⟩, hN⟩
    exact ⟨(inUJ_iff_UH hF g).1 hu, hE.1 hS1, hM.1 fun j hj1 hj2 => hN _ (fcol_mid_orth hF hj1 hj2)⟩
  · rintro ⟨hu, h2, h3⟩
    have hmid := hM.2 h3
    have hE2 := hE.2 h2
    have hzr : (g - 1) *ᵥ z0 ∈ spanLt e r := by
      have := hmid ⟨r + k, by omega⟩ (by simp) (by simp)
      have hf : fcol k r e f wf z0 ⟨r + k, by omega⟩ = z0 := by simp [fcol]
      rwa [hf] at this
    refine ⟨(inUJ_iff_UH hF g).2 hu, ⟨hE2, ?_⟩, ?_⟩
    · have hzz : z = c⁻¹ • z0 := by rw [hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hzz, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ hzr
    · intro y hy
      have hy' : y = Pm k r e f wf z0 *ᵥ (Qm k r ε e f wf z0 *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      rw [hy', pm_mulVec_eq_sum, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      by_cases hj : j.val < r
      · refine Submodule.smul_mem _ _ ?_
        have := hE2 ⟨j.val, hj⟩
        rw [fcol_lt j hj]
        refine Submodule.span_mono ?_ this
        exact Set.image_mono fun b hb => lt_trans hb hj
      by_cases hj' : j.val ≤ r + k
      · exact Submodule.smul_mem _ _ (hmid j (by omega) hj')
      · have hv := piI_val (k := k) (r := r) j
        have hpl : (piI k r j).val < r := by rw [hv]; split_ifs <;> omega
        rw [qm_mulVec_apply hF, fcol_lt _ hpl, hy, mul_zero, zero_smul]
        exact Submodule.zero_mem _

end Frame

/- English proof (translation)
Introduce `k r ε e f wf z0 z c hF hc hz`. Conclude with `⟨Pm k r e f wf z0, Qm k r ε e f wf z0, qm_mul_pm hF, pm_mul_qm hF, fun g => frame_conj_iff hF hc hz g⟩`.
-/
theorem frame_conjugation_unimodular : FrameConj := by
  intro k r ε e f wf z0 z c hF hc hz
  exact ⟨Pm k r e f wf z0, Qm k r ε e f wf z0, qm_mul_pm hF, pm_mul_qm hF, fun g => frame_conj_iff hF hc hz g⟩

end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
