import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def iF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := eI k (1 + r') (a0 r')

def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := esI k (1 + r') (a0 r')

def lv (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := levPos k 1 r' j

def res (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (lv k r' j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma iF_val : (iF k r').val = 0 := rfl
/- English proof (translation)
Simplify using `[iL, esI, a0]`.
-/
lemma iL_val : (iL k r').val = 2 * (1 + r') + k := by simp [iL, esI, a0]
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma lv_val (j : Fin (2 * r' + k + 1)) : (lv k r' j).val = j.val + 1 := rfl

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[iF_val, iL_val]`. Use linear arithmetic over natural numbers and integers.
-/
lemma iF_ne_iL : iF k r' ≠ iL k r' := by
  intro h; have := congrArg Fin.val h; rw [iF_val, iL_val] at this; omega
/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[iF_val, lv_val]`. Use linear arithmetic over natural numbers and integers.
-/
lemma lv_ne_iF (j : Fin (2 * r' + k + 1)) : lv k r' j ≠ iF k r' := by
  intro h; have := congrArg Fin.val h; rw [iF_val, lv_val] at this; omega
/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[iL_val, lv_val]`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma lv_ne_iL (j : Fin (2 * r' + k + 1)) : lv k r' j ≠ iL k r' := by
  intro h; have := congrArg Fin.val h; rw [iL_val, lv_val] at this; have := j.isLt; omega
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h; have := congrArg Fin.val h; rw [lv_val, lv_val] at this; exact Fin.ext (by omega)`. Introduce and unpack `rfl`. Both sides reduce to the same expression.
-/
lemma lv_inj (i j : Fin (2 * r' + k + 1)) : lv k r' i = lv k r' j ↔ i = j := by
  constructor
  · intro h; have := congrArg Fin.val h; rw [lv_val, lv_val] at this; exact Fin.ext (by omega)
  · rintro rfl; rfl

/- English proof (translation)
Distinguish the cases in `h0 : p.val = 0`. Use the proof step `left; exact Fin.ext (by rw [iF_val]; exact h0)`. Distinguish the cases in `h1 : p.val = 2 * (1 + r') + k`. Use the proof step `right; left; exact Fin.ext (by rw [iL_val]; exact h1)`. Use `right`.

Use `right`. Use `p.isLt` as an intermediate fact. Conclude with `⟨⟨p.val - 1, by omega⟩, Fin.ext (by rw [lv_val]; simp only; omega)⟩`.
-/
lemma cases3 (p : Fin (2 * (1 + r') + k + 1)) : p = iF k r' ∨ p = iL k r' ∨ ∃ j, p = lv k r' j := by
  by_cases h0 : p.val = 0
  · left; exact Fin.ext (by rw [iF_val]; exact h0)
  by_cases h1 : p.val = 2 * (1 + r') + k
  · right; left; exact Fin.ext (by rw [iL_val]; exact h1)
  · right; right
    have := p.isLt
    exact ⟨⟨p.val - 1, by omega⟩, Fin.ext (by rw [lv_val]; simp only; omega)⟩

/- English proof (translation)
Establish `h : (2 * r' + k + 1) + 1 + 1 = 2 * (1 + r') + k + 1` using `by omega`. Rewrite using `[← (finCongr h).sum_comp, Fin.sum_univ_succ, Fin.sum_univ_castSucc]`. Establish `e0 : finCongr h 0 = iF k r'` using `Fin.ext (by rw [iF_val]; rfl)`. Establish `e1 : finCongr h (Fin.succ (Fin.last _)) = iL k r'` using `Fin.ext (by rw [iL_val]; simp)`. Establish `e2 : ∀ j : Fin (2 * r' + k + 1), finCongr h (Fin.succ (Fin.castSucc j)) = lv k r' j`.

Introduce `j; exact Fin.ext (by rw [lv_val]; simp)`. Rewrite using `[e0, e1]`. Simplify using `only [e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum3 (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f (iF k r') + ∑ j, f (lv k r' j) + f (iL k r') := by
  have h : (2 * r' + k + 1) + 1 + 1 = 2 * (1 + r') + k + 1 := by omega
  rw [← (finCongr h).sum_comp, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have e0 : finCongr h 0 = iF k r' := Fin.ext (by rw [iF_val]; rfl)
  have e1 : finCongr h (Fin.succ (Fin.last _)) = iL k r' := Fin.ext (by rw [iL_val]; simp)
  have e2 : ∀ j : Fin (2 * r' + k + 1), finCongr h (Fin.succ (Fin.castSucc j)) = lv k r' j := by
    intro j; exact Fin.ext (by rw [lv_val]; simp)
  rw [e0, e1]
  simp only [e2]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `p`. Break down `cases3 p with rfl | rfl | ⟨j, rfl⟩` into its components or cases. Conclude with `hF`. Conclude with `hL`. Conclude with `congrFun hm j`.
-/
lemma vext {u w : Fin (2 * (1 + r') + k + 1) → ℂ} (hF : u (iF k r') = w (iF k r')) (hm : res u = res w)
    (hL : u (iL k r') = w (iL k r')) : u = w := by
  funext p
  rcases cases3 p with rfl | rfl | ⟨j, rfl⟩
  · exact hF
  · exact hL
  · exact congrFun hm j

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (WeylGroupFacts.tau k r i)]`. Rewrite using `[WeylGroupFacts.hpk_row, if_pos rfl]`. Introduce `m _ hm`. Rewrite using `[WeylGroupFacts.hpk_row, if_neg hm, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma hpk_mulVec (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = WeylGroupFacts.sgn k r i * u (WeylGroupFacts.tau k r i) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (WeylGroupFacts.tau k r i)]
  · rw [WeylGroupFacts.hpk_row, if_pos rfl]
  · intro m _ hm
    rw [WeylGroupFacts.hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
The claim follows from `if_pos h`.
-/
lemma tau_out {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : i.val < r ∨ r + k < i.val) :
    (WeylGroupFacts.tau k r i).val = 2 * r + k - i.val := if_pos h

/- English proof (translation)
The claim follows from `if_neg h`.
-/
lemma tau_mid {k r : ℕ} (i : Fin (2 * r + k + 1)) (h : ¬ (i.val < r ∨ r + k < i.val)) :
    (WeylGroupFacts.tau k r i).val = i.val := if_neg h

/- English proof (translation)
Establish `tF : WeylGroupFacts.tau k (1 + r') (iF k r') = iL k r'`. Apply `Fin.ext; rw [iL_val, tau_out _ (by rw [iF_val]; omega), iF_val]; omega` to reduce the goal to its premises. Establish `tL : WeylGroupFacts.tau k (1 + r') (iL k r') = iF k r'`. Apply `Fin.ext; rw [iF_val, tau_out _ (by rw [iL_val]; omega), iL_val]; omega` to reduce the goal to its premises. Establish `tm : ∀ j, WeylGroupFacts.tau k (1 + r') (lv k r' j) = lv k r' (WeylGroupFacts.tau k r' j)`.

Introduce `j`. Use `j.isLt` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[lv_val]`. Distinguish the cases in `hj : j.val < r' ∨ r' + k < j.val`.

Rewrite using `[tau_out _ hj, tau_out _ (by rw [lv_val]; omega), lv_val]; omega`. Rewrite using `[tau_mid _ hj, tau_mid _ (by rw [lv_val]; omega), lv_val]`. Establish `sF : WeylGroupFacts.sgn k (1 + r') (iF k r') = 1` using `if_neg (by rw [iF_val]; omega)`. Establish `sL : WeylGroupFacts.sgn k (1 + r') (iL k r') = 1` using `if_neg (by rw [iL_val]; omega)`. Establish `sm : ∀ j, WeylGroupFacts.sgn k (1 + r') (lv k r' j) = WeylGroupFacts.sgn k r' j`.

Introduce `j`. Distinguish the cases in `hj : j.val = r' + k`. Rewrite using `[WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_pos hj, if_pos (by rw [lv_val]; omega)]`. Rewrite using `[WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_neg hj, if_neg (by rw [lv_val]; omega)]`. Simplify using `only [herm, dotProduct, hpk_mulVec, Pi.star_apply]`.

Rewrite using `[sum3]`. Simplify using `only [tF, tL, tm, sF, sL, sm, res, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm3 (u w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u w =
      star (w (iF k r')) * u (iL k r') + star (w (iL k r')) * u (iF k r') + herm (Hpk k r') (res u) (res w) := by
  have tF : WeylGroupFacts.tau k (1 + r') (iF k r') = iL k r' := by
    apply Fin.ext; rw [iL_val, tau_out _ (by rw [iF_val]; omega), iF_val]; omega
  have tL : WeylGroupFacts.tau k (1 + r') (iL k r') = iF k r' := by
    apply Fin.ext; rw [iF_val, tau_out _ (by rw [iL_val]; omega), iL_val]; omega
  have tm : ∀ j, WeylGroupFacts.tau k (1 + r') (lv k r' j) = lv k r' (WeylGroupFacts.tau k r' j) := by
    intro j
    have := j.isLt
    apply Fin.ext; rw [lv_val]
    by_cases hj : j.val < r' ∨ r' + k < j.val
    · rw [tau_out _ hj, tau_out _ (by rw [lv_val]; omega), lv_val]; omega
    · rw [tau_mid _ hj, tau_mid _ (by rw [lv_val]; omega), lv_val]
  have sF : WeylGroupFacts.sgn k (1 + r') (iF k r') = 1 := if_neg (by rw [iF_val]; omega)
  have sL : WeylGroupFacts.sgn k (1 + r') (iL k r') = 1 := if_neg (by rw [iL_val]; omega)
  have sm : ∀ j, WeylGroupFacts.sgn k (1 + r') (lv k r' j) = WeylGroupFacts.sgn k r' j := by
    intro j
    by_cases hj : j.val = r' + k
    · rw [WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_pos hj, if_pos (by rw [lv_val]; omega)]
    · rw [WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_neg hj, if_neg (by rw [lv_val]; omega)]
  simp only [herm, dotProduct, hpk_mulVec, Pi.star_apply]
  rw [sum3]
  simp only [tF, tL, tm, sF, sL, sm, res, one_mul]
  ring

/- English proof (translation)
Simplify using `[herm, mulVec_add, dotProduct_add]`.
-/
lemma herm_add_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u u' w : Fin m → ℂ) :
    herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[herm, add_dotProduct]`.
-/
lemma herm_add_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u w w' : Fin m → ℂ) :
    herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, add_dotProduct]

/- English proof (translation)
Simplify using `[herm, mulVec_smul, dotProduct_smul]`.
-/
lemma herm_smul_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (u w : Fin m → ℂ) :
    herm H (c • u) w = c * herm H u w := by
  simp [herm, mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[herm, star_smul, smul_dotProduct]`.
-/
lemma herm_smul_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (u w : Fin m → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp [herm, star_smul, smul_dotProduct]

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma herm_zero_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) : herm H 0 w = 0 := by
  simp [herm]

/- English proof (translation)
Simplify using `[herm]`.
-/
lemma herm_zero_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) : herm H u 0 = 0 := by
  simp [herm]

/- English proof (translation)
Use `show gᴴ * H * g = H`. Use extensionality with `i j`. Establish `h1` using `h (Pi.single j 1) (Pi.single i 1)`. Establish `h2 : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w`. Introduce `u w`.

Rewrite using `[herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`. Rewrite `h1` using `[h2, ggHerm_bvec_right, ggHerm_bvec_right]`. Simplify using `using h1`.
-/
lemma uh_of_herm {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  have h2 : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w := by
    intro u w
    rw [herm, herm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [h2, ggHerm_bvec_right, ggHerm_bvec_right] at h1
  simpa using h1

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (h (Pi.single j 1)) i` as an intermediate fact. Simplify using `using this`.
-/
lemma mat_ext {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

/- English proof (translation)
Simplify using `[e0, bvec, iF]`.
-/
@[simp] lemma base_vector_first_eq_one : e0 k r' (iF k r') = 1 := by simp [e0, bvec, iF]
/- English proof (translation)
Use `(iF_ne_iL (k := k) (r' := r')).symm` as an intermediate fact. Simplify using `only [e0, bvec]`. Conclude with `Pi.single_eq_of_ne this _`.
-/
@[simp] lemma base_vector_last_eq_zero : e0 k r' (iL k r') = 0 := by
  have := (iF_ne_iL (k := k) (r' := r')).symm
  simp only [e0, bvec]; exact Pi.single_eq_of_ne this _
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [e0, bvec, res]`. Conclude with `Pi.single_eq_of_ne (lv_ne_iF j) _`.
-/
@[simp] lemma base_vector_restriction_zero : res (e0 k r') = 0 := by
  funext j; simp only [e0, bvec, res]; exact Pi.single_eq_of_ne (lv_ne_iF j) _
/- English proof (translation)
Simplify using `only [es0, bvec]`. Conclude with `Pi.single_eq_of_ne iF_ne_iL _`.
-/
@[simp] lemma dual_base_vector_first_eq_zero : es0 k r' (iF k r') = 0 := by
  simp only [es0, bvec]; exact Pi.single_eq_of_ne iF_ne_iL _
/- English proof (translation)
Simplify using `[es0, bvec, iL]`.
-/
@[simp] lemma dual_base_vector_last : es0 k r' (iL k r') = 1 := by simp [es0, bvec, iL]
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [es0, bvec, res]`. Conclude with `Pi.single_eq_of_ne (lv_ne_iL j) _`.
-/
@[simp] lemma dual_base_vector_restriction_zero : res (es0 k r') = 0 := by
  funext j; simp only [es0, bvec, res]; exact Pi.single_eq_of_ne (lv_ne_iL j) _
/- English proof (translation)
Simplify using `only [liftVec]; rw [dif_neg (by rw [iF_val]; omega)]`.
-/
@[simp] lemma lift_F (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iF k r') = 0 := by
  simp only [liftVec]; rw [dif_neg (by rw [iF_val]; omega)]
/- English proof (translation)
Simplify using `only [liftVec]; rw [dif_neg (by rw [iL_val]; omega)]`.
-/
@[simp] lemma lift_L (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iL k r') = 0 := by
  simp only [liftVec]; rw [dif_neg (by rw [iL_val]; omega)]
/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `j.isLt` as an intermediate fact. Simplify using `only [liftVec, res]; rw [dif_pos (by rw [lv_val]; omega)]`. Use `congr 1`.
-/
@[simp] lemma lift_res (y : Fin (2 * r' + k + 1) → ℂ) : res (liftVec k 1 r' y) = y := by
  funext j
  have := j.isLt
  simp only [liftVec, res]; rw [dif_pos (by rw [lv_val]; omega)]
  congr 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma res_add (u w : Fin (2 * (1 + r') + k + 1) → ℂ) : res (u + w) = res u + res w := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma res_sub (u w : Fin (2 * (1 + r') + k + 1) → ℂ) : res (u - w) = res u - res w := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma res_smul (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : res (c • u) = c • res u := rfl

/- English proof (translation)
Rewrite using `[herm3]`. Simplify using `[herm_zero_right]`.
-/
lemma hermitian_form_base_vector_right (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (e0 k r') = u (iL k r') := by
  rw [herm3]; simp [herm_zero_right]

/- English proof (translation)
Rewrite using `[herm3]`. Simplify using the standard rewrite rules.
-/
lemma herm_lift (u : Fin (2 * (1 + r') + k + 1) → ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (liftVec k 1 r' y) = herm (Hpk k r') (res u) y := by
  rw [herm3]; simp

/- English proof (translation)
Unfold `ιLev; rw [dif_neg (by rw [iF_val]; omega)]`.
-/
lemma lev_F (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (iF k r') q = if iF k r' = q then 1 else 0 := by
  unfold ιLev; rw [dif_neg (by rw [iF_val]; omega)]

/- English proof (translation)
Unfold `ιLev; rw [dif_neg (by rw [iL_val]; omega)]`.
-/
lemma lev_L (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (iL k r') q = if iL k r' = q then 1 else 0 := by
  unfold ιLev; rw [dif_neg (by rw [iL_val]; omega)]

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Unfold `ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_neg (by rw [iF_val]; omega)]`.
-/
lemma lev_mF (g : Mat k r') (i : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (lv k r' i) (iF k r') = 0 := by
  have := i.isLt
  unfold ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_neg (by rw [iF_val]; omega)]

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Unfold `ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_neg (by rw [iL_val]; omega)]`.
-/
lemma lev_mL (g : Mat k r') (i : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (lv k r' i) (iL k r') = 0 := by
  have := i.isLt
  unfold ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_neg (by rw [iL_val]; omega)]

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Unfold `ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_pos (by rw [lv_val]; omega)]`. Use `congr 1`.
-/
lemma lev_mm (g : Mat k r') (i j : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (lv k r' i) (lv k r' j) = g i j := by
  have := i.isLt
  have := j.isLt
  unfold ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_pos (by rw [lv_val]; omega)]
  congr 1

/- English proof (translation)
Simplify using `[mulVec, dotProduct, lev_F]`.
-/
lemma lev_mulVec_F (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (iF k r') = u (iF k r') := by
  simp [mulVec, dotProduct, lev_F]

/- English proof (translation)
Simplify using `[mulVec, dotProduct, lev_L]`.
-/
lemma lev_mulVec_L (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (iL k r') = u (iL k r') := by
  simp [mulVec, dotProduct, lev_L]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [res, mulVec, dotProduct]`. Rewrite using `[sum3]`. Simplify using `only [lev_mF, lev_mL, lev_mm, zero_mul, zero_add, add_zero]`.
-/
lemma lev_mulVec_res (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res (ιLev k 1 r' g *ᵥ u) = g *ᵥ res u := by
  funext i
  simp only [res, mulVec, dotProduct]
  rw [sum3]
  simp only [lev_mF, lev_mL, lev_mm, zero_mul, zero_add, add_zero]

/- English proof (translation)
Apply `uh_of_herm` to reduce the goal to its premises. Introduce `u w`. Rewrite using `[herm3, herm3 u w, lev_mulVec_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_L, lev_mulVec_res, lev_mulVec_res, ggHerm_unitary _ _ hg]`.
-/
lemma lev_uh {g : Mat k r'} (hg : g ∈ UH (Hpk k r')) : ιLev k 1 r' g ∈ UH (Hpk k (1 + r')) := by
  apply uh_of_herm
  intro u w
  rw [herm3, herm3 u w, lev_mulVec_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_L, lev_mulVec_res, lev_mulVec_res,
    ggHerm_unitary _ _ hg]

/- English proof (translation)
Rewrite `hg`, the goal using `[WeylGroupFacts.nset_iff]`. Use `⟨lev_uh hg.1, ?_⟩` and prove the remaining obligations. Introduce `i j hj hi`. Break down `cases3 i with rfl | rfl | ⟨i', rfl⟩` into its components or cases. Conclude with `lev_F g j`.

Conclude with `lev_L g j`. Break down `cases3 j with rfl | rfl | ⟨j', rfl⟩` into its components or cases. Rewrite using `[lev_mF, if_neg (lv_ne_iF i')]`. Rewrite `hj` using `[iL_val]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hj`, `hi` using `[lv_val]`. Rewrite `hi` using `[lv_val]`. Rewrite using `[lev_mm, hg.2 i' j' (by omega) (by omega)]`. Simplify using `only [lv_inj]`.
-/
lemma lev_n {g : Mat k r'} (hg : g ∈ Nset k r') : ιLev k 1 r' g ∈ Nset k (1 + r') := by
  rw [WeylGroupFacts.nset_iff] at hg ⊢
  refine ⟨lev_uh hg.1, ?_⟩
  intro i j hj hi
  rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
  · exact lev_F g j
  · exact lev_L g j
  · rcases cases3 j with rfl | rfl | ⟨j', rfl⟩
    · rw [lev_mF, if_neg (lv_ne_iF i')]
    · rw [iL_val] at hj; omega
    · rw [lv_val] at hj hi
      rw [lv_val] at hi
      rw [lev_mm, hg.2 i' j' (by omega) (by omega)]
      simp only [lv_inj]

/- English proof (translation)
Simplify using `only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v : Fin m → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i`. Introduce `w φ`. Simplify using `only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h1, herm_sum, herm_sum]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.
-/
lemma heisAct (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r') := by
  ext i
  simp only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, herm_sum, herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[heis0, heisAct, hermitian_form_base_vector_right, herm_lift]`. Simplify using the standard rewrite rules.
-/
lemma heis_F (x : HPar k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (heis0 k r' x *ᵥ u) (iF k r') = u (iF k r') - herm (Hpk k r') (res u) x.1 + u (iL k r') * hb k r' x.1 x.2 := by
  rw [heis0, heisAct, hermitian_form_base_vector_right, herm_lift]
  simp

/- English proof (translation)
Rewrite using `[heis0, heisAct, hermitian_form_base_vector_right, herm_lift]`. Simplify using the standard rewrite rules.
-/
lemma heis_L (x : HPar k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (heis0 k r' x *ᵥ u) (iL k r') = u (iL k r') := by
  rw [heis0, heisAct, hermitian_form_base_vector_right, herm_lift]
  simp

/- English proof (translation)
Rewrite using `[heis0, heisAct, hermitian_form_base_vector_right, herm_lift]`. Simplify using `[res_add, res_sub, res_smul]`.
-/
lemma heis_res (x : HPar k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res (heis0 k r' x *ᵥ u) = res u + u (iL k r') • x.1 := by
  rw [heis0, heisAct, hermitian_form_base_vector_right, herm_lift]
  simp [res_add, res_sub, res_smul]

/- English proof (translation)
Establish `h` using `ggHerm_swap (Hpk k r') (GBasic.Hpk_herm k r') y y`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`.

Simplify using `only [Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma herm_self_real (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k r') y y = ((herm (Hpk k r') y y).re : ℂ) := by
  have h := ggHerm_swap (Hpk k r') (GBasic.Hpk_herm k r') y y
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

/- English proof (translation)
Rewrite using `[herm_self_real y]`. Apply the tactic sequence `apply Complex.ext <;> simp [hb]`.
-/
lemma hb_add_star (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + star (hb k r' y s) = - herm (Hpk k r') y y := by
  rw [herm_self_real y]
  apply Complex.ext <;> simp [hb]

/- English proof (translation)
Apply `uh_of_herm` to reduce the goal to its premises. Introduce `u w`. Rewrite using `[herm3, herm3 u w, heis_F, heis_F, heis_L, heis_L, heis_res, heis_res]`. Simplify using `only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_add, star_sub, star_mul']`. Rewrite using `[← ggHerm_swap (Hpk k r') (GBasic.Hpk_herm k r') x.1 (res w)]`.

Establish `h` using `hb_add_star x.1 x.2`. Take the linear combination `(star (w (iL k r')) * u (iL k r')) * h`.
-/
lemma heis_uh (x : HPar k r') : heis0 k r' x ∈ UH (Hpk k (1 + r')) := by
  apply uh_of_herm
  intro u w
  rw [herm3, herm3 u w, heis_F, heis_F, heis_L, heis_L, heis_res, heis_res]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_add, star_sub, star_mul']
  rw [← ggHerm_swap (Hpk k r') (GBasic.Hpk_herm k r') x.1 (res w)]
  have h := hb_add_star x.1 x.2
  linear_combination (star (w (iL k r')) * u (iL k r')) * h

/- English proof (translation)
Simplify using `[bvec]`.
-/
lemma ent {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : g i j = (g *ᵥ bvec j) i := by
  simp [bvec]

/- English proof (translation)
Apply `vext` to reduce the goal to its premises. Rewrite using `[lift_F]`. Conclude with `Pi.single_eq_of_ne (lv_ne_iF j).symm _`. Rewrite using `[lift_res]`. Use function extensionality and compare the values at `i`.

Simplify using `only [res, bvec, Pi.single_apply, lv_inj]`. Rewrite using `[lift_L]`. Conclude with `Pi.single_eq_of_ne (lv_ne_iL j).symm _`.
-/
lemma bvec_lv (j : Fin (2 * r' + k + 1)) : bvec (lv k r' j) = liftVec k 1 r' (bvec j) := by
  apply vext
  · rw [lift_F]; exact Pi.single_eq_of_ne (lv_ne_iF j).symm _
  · rw [lift_res]; funext i
    simp only [res, bvec, Pi.single_apply, lv_inj]
  · rw [lift_L]; exact Pi.single_eq_of_ne (lv_ne_iL j).symm _

/- English proof (translation)
Rewrite using `[WeylGroupFacts.nset_iff]`. Use `⟨heis_uh x, ?_⟩` and prove the remaining obligations. Introduce `i j hj hi`. Rewrite using `[ent (heis0 k r' x) i j]`. Break down `cases3 j with rfl | rfl | ⟨j', rfl⟩` into its components or cases.

Establish `: bvec (iF k r') = e0 k r'` using `rfl`. Rewrite using `[this]`. Break down `cases3 i with rfl | rfl | ⟨i', rfl⟩` into its components or cases. Rewrite using `[heis_F]`. Simplify using `[herm_zero_left]`.

Rewrite using `[heis_L]`. Simplify using `[iF_ne_iL.symm]`. Use `congrFun (heis_res x (e0 k r')) i'` as an intermediate fact. Simplify using `only [res] at this`. Rewrite using `[this]`.

Simplify using `[lv_ne_iF]`. Rewrite `hj` using `[iL_val]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[bvec_lv]`. Break down `cases3 i with rfl | rfl | ⟨i', rfl⟩` into its components or cases.

Rewrite `hi` using `[iF_val, lv_val]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[heis_L, lift_L, if_neg (lv_ne_iL j').symm]`. Use `congrFun (heis_res x (liftVec k 1 r' (bvec j'))) i'` as an intermediate fact. Rewrite `this` using `[lift_res, lift_L]`.

Simplify using `only [res] at this`. Rewrite using `[this]`. Simplify using `[bvec, Pi.single_apply, lv_inj]`.
-/
lemma heis_n (x : HPar k r') : heis0 k r' x ∈ Nset k (1 + r') := by
  rw [WeylGroupFacts.nset_iff]
  refine ⟨heis_uh x, ?_⟩
  intro i j hj hi
  rw [ent (heis0 k r' x) i j]
  rcases cases3 j with rfl | rfl | ⟨j', rfl⟩
  · have : bvec (iF k r') = e0 k r' := rfl
    rw [this]
    rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
    · rw [heis_F]; simp [herm_zero_left]
    · rw [heis_L]; simp [iF_ne_iL.symm]
    · have := congrFun (heis_res x (e0 k r')) i'
      simp only [res] at this
      rw [this]; simp [lv_ne_iF]
  · rw [iL_val] at hj; omega
  · rw [bvec_lv]
    rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
    · rw [iF_val, lv_val] at hi; omega
    · rw [heis_L, lift_L, if_neg (lv_ne_iL j').symm]
    · have := congrFun (heis_res x (liftVec k 1 r' (bvec j'))) i'
      rw [lift_res, lift_L] at this
      simp only [res] at this
      rw [this]
      simp [bvec, Pi.single_apply, lv_inj]

def blk (g : Mat k (1 + r')) : Mat k r' := fun i j => g (lv k r' i) (lv k r' j)

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum3]`. Both sides reduce to the same expression.
-/
lemma mulVec3 (g : Mat k (1 + r')) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    (g *ᵥ u) p = g p (iF k r') * u (iF k r') + ∑ j, g p (lv k r' j) * res u j + g p (iL k r') * u (iL k r') := by
  simp only [mulVec, dotProduct]
  rw [sum3]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [res]`. Rewrite using `[mulVec3, lift_F, lift_L, lift_res]`. Simplify using `[blk, mulVec, dotProduct]`.
-/
lemma blk_mulVec (g : Mat k (1 + r')) (z : Fin (2 * r' + k + 1) → ℂ) :
    blk g *ᵥ z = res (g *ᵥ liftVec k 1 r' z) := by
  funext i
  simp only [res]
  rw [mulVec3, lift_F, lift_L, lift_res]
  simp [blk, mulVec, dotProduct]

/- English proof (translation)
Apply `mat_ext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[blk_mulVec, ← mulVec_mulVec, heis_res, lev_mulVec_res, lev_mulVec_L, lift_res, lift_L]`. Simplify using the standard rewrite rules.
-/
lemma blk_heis_lev (x : HPar k r') (n : Mat k r') : blk (heis0 k r' x * ιLev k 1 r' n) = n := by
  apply mat_ext
  intro z
  rw [blk_mulVec, ← mulVec_mulVec, heis_res, lev_mulVec_res, lev_mulVec_L, lift_res, lift_L]
  simp

/- English proof (translation)
Rewrite `hg` using `[WeylGroupFacts.nset_iff]`. Take `⟨hU, hc⟩` from `hg`. Establish `inv` using `ggHerm_unitary (Hpk k (1 + r')) g hU`. Establish `cF : ∀ p, g p (iF k r') = if p = iF k r' then 1 else 0`. Introduce `p`.

Conclude with `hc p (iF k r') (by rw [iF_val]; omega) (by rw [iF_val]; omega)`. Establish `ge : g *ᵥ e0 k r' = e0 k r'`. Use function extensionality and compare the values at `p`. Use `ent g p (iF k r')` as an intermediate fact. Rewrite `this` using `[cF]`.

Use `show (g *ᵥ bvec (iF k r')) p = bvec (iF k r') p`. Rewrite using `[← this, bvec, Pi.single_apply]`. Establish `gL : ∀ u, (g *ᵥ u) (iL k r') = u (iL k r')`. Introduce `u`. Rewrite using `[← hermitian_form_base_vector_right (g *ᵥ u), ← hermitian_form_base_vector_right u, ← inv u (e0 k r'), ge]`.

Use `set y : Fin (2 * r' + k + 1) → ℂ := fun i => g (lv k r' i) (iL k r') with hy`. Use `set β : ℂ := g (iF k r') (iL k r') with hβ`. Use `set aa : (Fin (2 * r' + k + 1) → ℂ) → ℂ := fun z => ∑ j, g (iF k r') (lv k r' j) * z j with haa`. Establish `gF : ∀ u, (g *ᵥ u) (iF k r') = u (iF k r') + aa (res u) + β * u (iL k r')`. Introduce `u`.

Rewrite using `[mulVec3, cF, if_pos rfl, one_mul]`. Establish `gm : ∀ u, res (g *ᵥ u) = blk g *ᵥ res u + u (iL k r') • y`. Introduce `u`. Use function extensionality and compare the values at `i`. Simplify using `only [res]`.

Rewrite using `[mulVec3, cF, if_neg (lv_ne_iF i)]`. Simplify using `[blk, mulVec, dotProduct, res, hy, mul_comm]`. Establish `r1 : ∀ z, aa z = - herm (Hpk k r') (blk g *ᵥ z) y`. Introduce `z`. Establish `h` using `inv (liftVec k 1 r' z) (es0 k r')`.

Rewrite `h` using `[herm3, herm3 (liftVec k 1 r' z), gF, gF, gL, gL, gm, gm]`. Simplify using `[herm_zero_right] at h`. Take the linear combination `h`. Establish `r2 : β + star β = - herm (Hpk k r') y y`. Establish `h` using `inv (es0 k r') (es0 k r')`.

Rewrite `h` using `[herm3, herm3 (es0 k r'), gF, gL, gm]`. Simplify using `[herm_zero_right, haa] at h`. Rewrite using `[Complex.star_def]`. Take the linear combination `h`. Establish `r3 : β = hb k r' y β.im`.

Rewrite `r2` using `[herm_self_real y]`. Use `congrArg Complex.re r2` as an intermediate fact. Simplify using `at this`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hb]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hb]`. Use `⟨(y, β.im), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WeylGroupFacts.nset_iff]`. Prove the components needed by the constructor for the conclusion.

Apply `uh_of_herm` to reduce the goal to its premises. Introduce `z z'`. Establish `h` using `inv (liftVec k 1 r' z) (liftVec k 1 r' z')`. Rewrite `h` using `[herm3, herm3 (liftVec k 1 r' z), gL, gL, gm, gm]`. Simplify using `using h`.

Introduce `i j hj hi show g (lv k r' i) (lv k r' j) = _`. Rewrite using `[hc _ _ (by rw [lv_val]; omega) (by rw [lv_val, lv_val]; omega)]`. Simplify using `only [lv_inj]`. Apply `mat_ext` to reduce the goal to its premises. Introduce `u`.

Rewrite using `[← mulVec_mulVec]`. Apply `vext` to reduce the goal to its premises. Rewrite using `[heis_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_res, gF, r1]`. Simplify using `only`. Rewrite using `[← r3]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heis_res, lev_mulVec_res, lev_mulVec_L, gm]`. Rewrite using `[heis_L, lev_mulVec_L, gL]`.
-/
lemma n_decomp {g : Mat k (1 + r')} (hg : g ∈ Nset k (1 + r')) :
    ∃ x : HPar k r', blk g ∈ Nset k r' ∧ g = heis0 k r' x * ιLev k 1 r' (blk g) := by
  rw [WeylGroupFacts.nset_iff] at hg
  obtain ⟨hU, hc⟩ := hg
  have inv := ggHerm_unitary (Hpk k (1 + r')) g hU

  have cF : ∀ p, g p (iF k r') = if p = iF k r' then 1 else 0 := by
    intro p
    exact hc p (iF k r') (by rw [iF_val]; omega) (by rw [iF_val]; omega)
  have ge : g *ᵥ e0 k r' = e0 k r' := by
    funext p
    have := ent g p (iF k r')
    rw [cF] at this
    show (g *ᵥ bvec (iF k r')) p = bvec (iF k r') p
    rw [← this, bvec, Pi.single_apply]

  have gL : ∀ u, (g *ᵥ u) (iL k r') = u (iL k r') := by
    intro u
    rw [← hermitian_form_base_vector_right (g *ᵥ u), ← hermitian_form_base_vector_right u, ← inv u (e0 k r'), ge]
  set y : Fin (2 * r' + k + 1) → ℂ := fun i => g (lv k r' i) (iL k r') with hy
  set β : ℂ := g (iF k r') (iL k r') with hβ
  set aa : (Fin (2 * r' + k + 1) → ℂ) → ℂ := fun z => ∑ j, g (iF k r') (lv k r' j) * z j with haa
  have gF : ∀ u, (g *ᵥ u) (iF k r') = u (iF k r') + aa (res u) + β * u (iL k r') := by
    intro u
    rw [mulVec3, cF, if_pos rfl, one_mul]
  have gm : ∀ u, res (g *ᵥ u) = blk g *ᵥ res u + u (iL k r') • y := by
    intro u
    funext i
    simp only [res]
    rw [mulVec3, cF, if_neg (lv_ne_iF i)]
    simp [blk, mulVec, dotProduct, res, hy, mul_comm]

  have r1 : ∀ z, aa z = - herm (Hpk k r') (blk g *ᵥ z) y := by
    intro z
    have h := inv (liftVec k 1 r' z) (es0 k r')
    rw [herm3, herm3 (liftVec k 1 r' z), gF, gF, gL, gL, gm, gm] at h
    simp [herm_zero_right] at h
    linear_combination h
  have r2 : β + star β = - herm (Hpk k r') y y := by
    have h := inv (es0 k r') (es0 k r')
    rw [herm3, herm3 (es0 k r'), gF, gL, gm] at h
    simp [herm_zero_right, haa] at h
    rw [Complex.star_def]
    linear_combination h
  have r3 : β = hb k r' y β.im := by
    rw [herm_self_real y] at r2
    have := congrArg Complex.re r2
    simp at this
    apply Complex.ext
    · simp [hb]; linarith
    · simp [hb]
  refine ⟨(y, β.im), ?_, ?_⟩
  · rw [WeylGroupFacts.nset_iff]
    constructor
    · apply uh_of_herm
      intro z z'
      have h := inv (liftVec k 1 r' z) (liftVec k 1 r' z')
      rw [herm3, herm3 (liftVec k 1 r' z), gL, gL, gm, gm] at h
      simpa using h
    · intro i j hj hi
      show g (lv k r' i) (lv k r' j) = _
      rw [hc _ _ (by rw [lv_val]; omega) (by rw [lv_val, lv_val]; omega)]
      simp only [lv_inj]
  · apply mat_ext
    intro u
    rw [← mulVec_mulVec]
    apply vext
    · rw [heis_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_res, gF, r1]
      simp only
      rw [← r3]
      ring
    · rw [heis_res, lev_mulVec_res, lev_mulVec_L, gm]
    · rw [heis_L, lev_mulVec_L, gL]

def rho (x : Mt k (1 + r')) : Mt k (1 + r') := ιLev k 1 r' (blk (Matrix.of x))

/- English proof (translation)
Apply `continuous_pi` to reduce the goal to its premises. Introduce `p`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `q`. Use `show Continuous fun x : Mt k (1 + r') => ιLev k 1 r' (blk (Matrix.of x)) p q`.

Break down `cases3 p with rfl | rfl | ⟨i, rfl⟩` into its components or cases. Simplify using `only [lev_F]`. Conclude with `continuous_const`. Simplify using `only [lev_L]`. Conclude with `continuous_const`.

Break down `cases3 q with rfl | rfl | ⟨j, rfl⟩` into its components or cases. Simplify using `only [lev_mF]`. Conclude with `continuous_const`. Simplify using `only [lev_mL]`. Conclude with `continuous_const`.

Simplify using `only [lev_mm] show Continuous fun x : Mt k (1 + r') => x (lv k r' i) (lv k r' j)`. Conclude with `(continuous_apply _).comp (continuous_apply _)`.
-/
lemma rho_cont : Continuous (rho (k := k) (r' := r')) := by
  apply continuous_pi; intro p
  apply continuous_pi; intro q
  show Continuous fun x : Mt k (1 + r') => ιLev k 1 r' (blk (Matrix.of x)) p q
  rcases cases3 p with rfl | rfl | ⟨i, rfl⟩
  · simp only [lev_F]; exact continuous_const
  · simp only [lev_L]; exact continuous_const
  · rcases cases3 q with rfl | rfl | ⟨j, rfl⟩
    · simp only [lev_mF]; exact continuous_const
    · simp only [lev_mL]; exact continuous_const
    · simp only [lev_mm]
      show Continuous fun x : Mt k (1 + r') => x (lv k r' i) (lv k r' j)
      exact (continuous_apply _).comp (continuous_apply _)

end Formalism.FourierDecayAlt.P.B2x6

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6

/- English proof (translation)
Introduce `k r'`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨x, hn, he⟩` from `n_decomp hg`.

Conclude with `⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' (blk g), ⟨blk g, hn, rfl⟩, he⟩`. Introduce and unpack `⟨a, ⟨x, rfl⟩, b, ⟨n, hn, rfl⟩, rfl⟩`. Conclude with `WeylGroupFacts.mem_n_mul (heis_n x) (lev_n hn)`.
-/
theorem unipotent_heisenberg_decomposition : Formalism.FourierDecayAlt.B2.NDecomp := by
  intro k r'
  ext g
  constructor
  · intro hg
    obtain ⟨x, hn, he⟩ := n_decomp hg
    exact ⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' (blk g), ⟨blk g, hn, rfl⟩, he⟩
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨n, hn, rfl⟩, rfl⟩
    exact WeylGroupFacts.mem_n_mul (heis_n x) (lev_n hn)

/- English proof (translation)
Introduce `hS hLev hCN hHC hHH hConj hConjM hD k r' μ' hμ'`. Establish `hL` using `hLev k r' (Nset k r') μ' (hCN k r') hμ'`. Establish `h1 : ∀ b ∈ ιLev k 1 r' '' Nset k r', ∀ a ∈ Hset k r', b * a * b⁻¹ ∈ Hset k r'`. Introduce and unpack `b ⟨n, hn, rfl⟩ a ⟨x, rfl⟩`. Rewrite using `[hConj k r' n hn.1 x]`.

Conclude with `⟨_, rfl⟩`. Establish `h2 : IsClosed (mulSet (Hset k r') (ιLev k 1 r' '' Nset k r'))`. Rewrite using `[← hD k r']`. Conclude with `(hCN k (1 + r')).closed`. Establish `h3 : ∀ a ∈ Hset k r', ∀ b ∈ ιLev k 1 r' '' Nset k r', rho (a * b) = b`.

Introduce and unpack `a ⟨x, rfl⟩ b ⟨n, _, rfl⟩`. Use `show ιLev k 1 r' (blk (heis0 k r' x * ιLev k 1 r' n)) = ιLev k 1 r' n`. Rewrite using `[blk_heis_lev]`. Establish `h4 : ∀ b ∈ ιLev k 1 r' '' Nset k r', (μHeis k r').map (conjM b) = μHeis k r'`. Introduce and unpack `b ⟨n, hn, rfl⟩`.

Conclude with `hConjM k r' n hn.1`. Establish `h` using `hS k (1 + r') (Hset k r') (ιLev k 1 r' '' Nset k r') (μHeis k r') (μ'.map (levM k r')) rho (hHC k r').2 hL.1 h1 h2 rho_cont h3 (hHH k r') hL.2 h4`. Rewrite using `[hD k r']`. Conclude with `h.2`.
-/
theorem unipotent_recursion_of_parts : Formalism.FourierDecayAlt.B2.AssembleNRec := by
  intro hS hLev hCN hHC hHH hConj hConjM hD k r' μ' hμ'
  have hL := hLev k r' (Nset k r') μ' (hCN k r') hμ'
  have h1 : ∀ b ∈ ιLev k 1 r' '' Nset k r', ∀ a ∈ Hset k r', b * a * b⁻¹ ∈ Hset k r' := by
    rintro b ⟨n, hn, rfl⟩ a ⟨x, rfl⟩
    rw [hConj k r' n hn.1 x]
    exact ⟨_, rfl⟩
  have h2 : IsClosed (mulSet (Hset k r') (ιLev k 1 r' '' Nset k r')) := by
    rw [← hD k r']
    exact (hCN k (1 + r')).closed
  have h3 : ∀ a ∈ Hset k r', ∀ b ∈ ιLev k 1 r' '' Nset k r', rho (a * b) = b := by
    rintro a ⟨x, rfl⟩ b ⟨n, _, rfl⟩
    show ιLev k 1 r' (blk (heis0 k r' x * ιLev k 1 r' n)) = ιLev k 1 r' n
    rw [blk_heis_lev]
  have h4 : ∀ b ∈ ιLev k 1 r' '' Nset k r', (μHeis k r').map (conjM b) = μHeis k r' := by
    rintro b ⟨n, hn, rfl⟩
    exact hConjM k r' n hn.1
  have h := hS k (1 + r') (Hset k r') (ιLev k 1 r' '' Nset k r') (μHeis k r') (μ'.map (levM k r')) rho
    (hHC k r').2 hL.1 h1 h2 rho_cont h3 (hHH k r') hL.2 h4
  rw [hD k r']
  exact h.2

/- English proof (translation)
Introduce `k`. Use extensionality with `g`. Rewrite using `[Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, _, h⟩`.

Use extensionality with `i j`. Use `h i j (Nat.zero_le _) (by have := j.isLt; omega) (Nat.zero_le _)` as an intermediate fact. Rewrite using `[this, Matrix.one_apply]`. Introduce and unpack `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show (1 : Mat k 0)ᴴ * Hpk k 0 * 1 = Hpk k 0`. Simplify using the standard rewrite rules. Introduce `a`. Conclude with `a.elim0`. Introduce `i j _ _ _`.

Rewrite using `[Matrix.one_apply]`.
-/
theorem unipotent_haar_base_case : Formalism.FourierDecayAlt.B2.NBase := by
  intro k
  ext g
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, _, h⟩
    ext i j
    have := h i j (Nat.zero_le _) (by have := j.isLt; omega) (Nat.zero_le _)
    rw [this, Matrix.one_apply]
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Mat k 0)ᴴ * Hpk k 0 * 1 = Hpk k 0
      simp
    · intro a; exact a.elim0
    · intro i j _ _ _; rw [Matrix.one_apply]

/- English proof (translation)
Introduce `hR hB k r`. Proceed by induction on `r with`. Consider the case `zero`. Set `o : Mt k 0` to `(1 : Mat k 0)`. Use `⟨Measure.dirac o, ?_⟩` and prove the remaining obligations.

Rewrite using `[hB k]`. Establish `hl : (lmulM (1 : Mat k 0)) = id` using `by funext x; simp [lmulM]; rfl`. Establish `hr : (rmulF (1 : Mat k 0)) = id` using `by funext x; simp [rmulF]; rfl`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Measure.dirac o ({o}ᶜ : Set (Mt k 0)) = 0`.

Rewrite using `[Measure.dirac_apply' _ (MeasurableSet.singleton o).compl]`. Simplify using the standard rewrite rules. Introduce `a ha`. Rewrite using `[Set.mem_singleton_iff.mp ha, hl, Measure.map_id]`. Introduce `a ha`.

Rewrite using `[Set.mem_singleton_iff.mp ha, hr, Measure.map_id]`. Introduce `K _`. Conclude with `measure_lt_top _ _`. Conclude with `IsProbabilityMeasure.ne_zero _`. Consider the case `succ r' ih`.

Take `⟨μ', h'⟩` from `ih`. Rewrite using `[Nat.add_comm r' 1]`. Conclude with `⟨_, hR k r' μ' h'⟩`.
-/
theorem unipotent_haar_of_parts : Formalism.FourierDecayAlt.B2.AssembleHaarN := by
  intro hR hB k r
  induction r with
  | zero =>
    let o : Mt k 0 := (1 : Mat k 0)
    refine ⟨Measure.dirac o, ?_⟩
    rw [hB k]
    have hl : (lmulM (1 : Mat k 0)) = id := by funext x; simp [lmulM]; rfl
    have hr : (rmulF (1 : Mat k 0)) = id := by funext x; simp [rmulF]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show Measure.dirac o ({o}ᶜ : Set (Mt k 0)) = 0
      rw [Measure.dirac_apply' _ (MeasurableSet.singleton o).compl]
      simp
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha, hl, Measure.map_id]
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha, hr, Measure.map_id]
    · intro K _
      exact measure_lt_top _ _
    · exact IsProbabilityMeasure.ne_zero _
  | succ r' ih =>
    obtain ⟨μ', h'⟩ := ih
    rw [Nat.add_comm r' 1]
    exact ⟨_, hR k r' μ' h'⟩

/- English proof (translation)
The claim follows from `unipotent_recursion_of_parts semidirect_product_haar levi_haar_measure_exists unipotent_radical_closed heisenberg_subgroup_closed heisenberg_haar_measure heisenberg_conjugation_by_levi heisenberg_levi_conjugation_measure unipotent_heisenberg_decomposition`.
-/
theorem unipotent_haar_recursion : Formalism.FourierDecayAlt.B2.NRecHaar :=
  unipotent_recursion_of_parts semidirect_product_haar levi_haar_measure_exists unipotent_radical_closed heisenberg_subgroup_closed heisenberg_haar_measure
    heisenberg_conjugation_by_levi heisenberg_levi_conjugation_measure unipotent_heisenberg_decomposition

/- English proof (translation)
The claim follows from `unipotent_haar_of_parts unipotent_haar_recursion unipotent_haar_base_case`.
-/
theorem unipotent_haar_exists : Formalism.FourierDecayAlt.B2.HaarNExists :=
  unipotent_haar_of_parts unipotent_haar_recursion unipotent_haar_base_case

end Formalism.FourierDecayAlt.P
