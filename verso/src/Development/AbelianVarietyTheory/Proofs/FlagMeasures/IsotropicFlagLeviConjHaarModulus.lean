import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNilradicalFinrankAndAbsDetConjStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedFormOrthogonalFinrankDetUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasisReTraceMulConjTransposeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmulStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagModulus

open Formalism.REAL (Jm inG UJ Jm_mul_self Jm_conjTranspose)

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]`.
-/
theorem form_adj (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Jm ε *ᵥ ((Jm ε * Xᴴ * Jm ε) *ᵥ y)) = star (X *ᵥ x) ⬝ᵥ (Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/- English proof (translation)
Establish `h2` using `congrArg star h`. Rewrite `h2` using `[Matrix.star_dotProduct, star_star, Matrix.star_mulVec, Jm_conjTranspose, ← Matrix.dotProduct_mulVec, star_zero]`. Conclude with `h2`.
-/
theorem form_symm {x y : Fin n → ℂ} (h : star x ⬝ᵥ (Jm ε *ᵥ y) = 0) : star y ⬝ᵥ (Jm ε *ᵥ x) = 0 := by
  have h2 := congrArg star h
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, Jm_conjTranspose, ← Matrix.dotProduct_mulVec,
    star_zero] at h2
  exact h2

/- English proof (translation)
Establish `h0 : Xᴴ * Jm ε + Jm ε * X = 0` using `h`. Establish `h1 : Xᴴ * Jm ε = -(Jm ε * X)` using `eq_neg_of_add_eq_zero_left h0`. Establish `hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε` using `m.2`. Establish `hgi : (uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹ = Jm ε` using `(m⁻¹).2`. Establish `hr : uMat m * uMat m⁻¹ = 1` using `GlobalTheory.FlagLeviGroup.uMat_mul_inv m`.

Establish `hl : uMat m⁻¹ * uMat m = 1` using `GlobalTheory.FlagLeviGroup.uMat_inv_mul m`. Establish `e1 : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (uMat m⁻¹)ᴴ * Jm ε = Jm ε * uMat m`. Combine the equalities or inequalities in the displayed calculation.

Use `show (uMat m * X * uMat m⁻¹)ᴴ * Jm ε + Jm ε * (uMat m * X * uMat m⁻¹) = 0`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (uMat m⁻¹)ᴴ * (Xᴴ * Jm ε) * uMat m⁻¹ + Jm ε * (uMat m * X * uMat m⁻¹) := by`.

Rewrite using `[e1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = -((uMat m⁻¹)ᴴ * Jm ε * X * uMat m⁻¹) + Jm ε * (uMat m * X * uMat m⁻¹) := by`. Rewrite using `[h1]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.

Use `_ = 0 := by`. Rewrite using `[e2]`. Simplify using `only [Matrix.mul_assoc]`. Conclude with `neg_add_cancel _`.
-/
theorem inG_conj (m : UJ ε) {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) : inG ε (uMat m * X * uMat m⁻¹) := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := h
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  have hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
  have hgi : (uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹ = Jm ε := (m⁻¹).2
  have hr : uMat m * uMat m⁻¹ = 1 := GlobalTheory.FlagLeviGroup.uMat_mul_inv m
  have hl : uMat m⁻¹ * uMat m = 1 := GlobalTheory.FlagLeviGroup.uMat_inv_mul m
  have e1 : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹ := by
    calc (uMat m)ᴴ * Jm ε = (uMat m)ᴴ * Jm ε * (uMat m * uMat m⁻¹) := by rw [hr, Matrix.mul_one]
      _ = ((uMat m)ᴴ * Jm ε * uMat m) * uMat m⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * uMat m⁻¹ := by rw [hg]
  have e2 : (uMat m⁻¹)ᴴ * Jm ε = Jm ε * uMat m := by
    calc (uMat m⁻¹)ᴴ * Jm ε = (uMat m⁻¹)ᴴ * Jm ε * (uMat m⁻¹ * uMat m) := by rw [hl, Matrix.mul_one]
      _ = ((uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹) * uMat m := by simp only [Matrix.mul_assoc]
      _ = Jm ε * uMat m := by rw [hgi]
  show (uMat m * X * uMat m⁻¹)ᴴ * Jm ε + Jm ε * (uMat m * X * uMat m⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (uMat m⁻¹)ᴴ * (Xᴴ * (uMat m)ᴴ) * Jm ε + Jm ε * (uMat m * X * uMat m⁻¹)
      = (uMat m⁻¹)ᴴ * Xᴴ * ((uMat m)ᴴ * Jm ε) + Jm ε * (uMat m * X * uMat m⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = (uMat m⁻¹)ᴴ * (Xᴴ * Jm ε) * uMat m⁻¹ + Jm ε * (uMat m * X * uMat m⁻¹) := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = -((uMat m⁻¹)ᴴ * Jm ε * X * uMat m⁻¹) + Jm ε * (uMat m * X * uMat m⁻¹) := by
        rw [h1]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = 0 := by
        rw [e2]; simp only [Matrix.mul_assoc]; exact neg_add_cancel _

variable (ε) in

def perpJ (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | ∀ x ∈ V, star x ⬝ᵥ (Jm ε *ᵥ y) = 0}
  add_mem' := fun {y z} hy hz x hx => by
    rw [Matrix.mulVec_add, dotProduct_add, hy x hx, hz x hx, add_zero]
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c y hy x hx => by
    rw [Matrix.mulVec_smul, dotProduct_smul, hy x hx, smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_perpJ {V : Submodule ℂ (Fin n → ℂ)} {y : Fin n → ℂ} :
    y ∈ perpJ ε V ↔ ∀ x ∈ V, star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := Iff.rfl

variable (ε) in

def lieSub : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | inG ε X}
  add_mem' := fun {X Y} hX hY => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    have h2 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
    change (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]
  zero_mem' := by simp [inG]
  smul_mem' := fun c X hX => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    change (c • X)ᴴ * Jm ε + Jm ε * (c • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

def lower (F : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s}
  add_mem' := fun {X Y} hX hY s hs y hy => by
    rw [Matrix.add_mulVec]; exact (F s).add_mem (hX s hs y hy) (hY s hs y hy)
  zero_mem' := fun s _ y _ => by simp
  smul_mem' := fun c X hX s hs y hy => by
    rw [Matrix.smul_mulVec]; exact (F s).smul_mem c (hX s hs y hy)

variable {a : ℕ}

def natFlag (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (s : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  W ⟨min s a, by omega⟩

variable (ε) in

def dblFlag (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (s : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  if s ≤ a then natFlag W s else perpJ ε (natFlag W (2 * a + 1 - s))

variable {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

/- English proof (translation)
Rewrite using `[dblFlag, if_pos hs]`.
-/
theorem dblFlag_le {s : ℕ} (hs : s ≤ a) : dblFlag ε W s = natFlag W s := by rw [dblFlag, if_pos hs]

/- English proof (translation)
Rewrite using `[dblFlag_le (Nat.lt_succ_iff.mp i.isLt)]`. Conclude with `congrArg W (Fin.ext (min_eq_left (Nat.lt_succ_iff.mp i.isLt)))`.
-/
theorem dblFlag_fin (i : Fin (a + 1)) : dblFlag ε W i = W i := by
  rw [dblFlag_le (Nat.lt_succ_iff.mp i.isLt)]
  exact congrArg W (Fin.ext (min_eq_left (Nat.lt_succ_iff.mp i.isLt)))

/- English proof (translation)
Rewrite using `[← Fin.val_succ]`. Conclude with `dblFlag_fin i.succ`.
-/
theorem dblFlag_succ (i : Fin a) : dblFlag ε W (i + 1) = W i.succ := by
  rw [← Fin.val_succ]
  exact dblFlag_fin i.succ

/- English proof (translation)
Establish `h` using `dblFlag_fin (ε := ε) (W := W) i.castSucc`. Rewrite `h` using `[Fin.val_castSucc]`. Then use the resulting hypothesis.
-/
theorem dblFlag_castSucc (i : Fin a) : dblFlag ε W i = W i.castSucc := by
  have h := dblFlag_fin (ε := ε) (W := W) i.castSucc
  rwa [Fin.val_castSucc] at h

/- English proof (translation)
Establish `h` using `dblFlag_fin (ε := ε) (W := W) (Fin.last a)`. Rewrite `h` using `[Fin.val_last]`. Then use the resulting hypothesis.
-/
theorem dblFlag_last : dblFlag ε W a = W (Fin.last a) := by
  have h := dblFlag_fin (ε := ε) (W := W) (Fin.last a)
  rwa [Fin.val_last] at h

/- English proof (translation)
Rewrite using `[dblFlag_le hs, dblFlag, if_neg (by omega), show 2 * a + 1 - (2 * a + 1 - s) = s by omega]`.
-/
theorem dblFlag_sub {s : ℕ} (hs : s ≤ a) : dblFlag ε W (2 * a + 1 - s) = perpJ ε (dblFlag ε W s) := by
  rw [dblFlag_le hs, dblFlag, if_neg (by omega), show 2 * a + 1 - (2 * a + 1 - s) = s by omega]

/- English proof (translation)
Distinguish the cases in `h : s ≤ a`. Conclude with `dblFlag_sub h`. Establish `ht : 2 * a + 1 - s ≤ a` using `by omega`. Establish `e` using `dblFlag_sub (ε := ε) (W := W) ht`. Rewrite `e` using `[show 2 * a + 1 - (2 * a + 1 - s) = s by omega]`.

Rewrite using `[e]`. Establish `h40` using `GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W (2 * a + 1 - s)) (perpJ ε (dblFlag ε W (2 * a + 1 - s))) (fun y => mem_perpJ)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[mem_perpJ]`.

Introduce `y hy`. Rewrite `hy` using `[mem_perpJ]`. Conclude with `form_symm (hy x hx)`. Introduce `x hx`. Rewrite `hx` using `[mem_perpJ]`.

Conclude with `h40.2.1 x hx`.
-/
theorem dblFlag_dual {s : ℕ} (hs : s ≤ 2 * a + 1) :
    dblFlag ε W (2 * a + 1 - s) = perpJ ε (dblFlag ε W s) := by
  by_cases h : s ≤ a
  · exact dblFlag_sub h
  · have ht : 2 * a + 1 - s ≤ a := by omega
    have e := dblFlag_sub (ε := ε) (W := W) ht
    rw [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at e
    rw [e]
    have h40 := GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W (2 * a + 1 - s)) (perpJ ε (dblFlag ε W (2 * a + 1 - s)))
      (fun y => mem_perpJ)
    apply le_antisymm
    · intro x hx
      rw [mem_perpJ]
      intro y hy
      rw [mem_perpJ] at hy
      exact form_symm (hy x hx)
    · intro x hx
      rw [mem_perpJ] at hx
      exact h40.2.1 x hx

/- English proof (translation)
Establish `nm : ∀ {s t : ℕ}, s ≤ t → natFlag W s ≤ natFlag W t` using `fun {s t} h => hW.2.1 (show (⟨min s a, by omega⟩ : Fin (a + 1)) ≤ ⟨min t a, by omega⟩ from Fin.mk_le_mk.2 (min_le_min_right a h))`. Establish `anti : ∀ {V V' : Submodule ℂ (Fin n → ℂ)}, V ≤ V' → perpJ ε V' ≤ perpJ ε V`. Introduce `V V' h y hy`. Rewrite `hy`, the goal using `[mem_perpJ]`. Conclude with `fun x hx => hy x (h hx)`.

Establish `hl : natFlag W a = W (Fin.last a)` using `congrArg W (Fin.ext (min_self a))`. Establish `iso : natFlag W a ≤ perpJ ε (natFlag W a)`. Rewrite using `[hl]`. Introduce `x hx`. Rewrite using `[mem_perpJ]`.

Introduce `x' hx'`. Conclude with `hW.2.2.2 x' hx' x hx`. Introduce `s t hst`. Distinguish the cases in `ht : t ≤ a`. Rewrite using `[dblFlag_le (hst.trans ht), dblFlag_le ht]`.

Conclude with `nm hst`. Establish `et : dblFlag ε W t = perpJ ε (natFlag W (2 * a + 1 - t))` using `by rw [dblFlag, if_neg ht]`. Distinguish the cases in `hs : s ≤ a`. Rewrite using `[dblFlag_le hs, et]`. Conclude with `(nm hs).trans (iso.trans (anti (nm (by omega))))`.

Establish `es : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s))` using `by rw [dblFlag, if_neg hs]`. Rewrite using `[es, et]`. Conclude with `anti (nm (by omega))`.
-/
theorem dblFlag_mono (hW : IsIsoFlag ε j W) : Monotone (dblFlag ε W) := by
  have nm : ∀ {s t : ℕ}, s ≤ t → natFlag W s ≤ natFlag W t := fun {s t} h =>
    hW.2.1 (show (⟨min s a, by omega⟩ : Fin (a + 1)) ≤ ⟨min t a, by omega⟩ from
      Fin.mk_le_mk.2 (min_le_min_right a h))
  have anti : ∀ {V V' : Submodule ℂ (Fin n → ℂ)}, V ≤ V' → perpJ ε V' ≤ perpJ ε V := by
    intro V V' h y hy
    rw [mem_perpJ] at hy ⊢
    exact fun x hx => hy x (h hx)
  have hl : natFlag W a = W (Fin.last a) := congrArg W (Fin.ext (min_self a))
  have iso : natFlag W a ≤ perpJ ε (natFlag W a) := by
    rw [hl]
    intro x hx
    rw [mem_perpJ]
    intro x' hx'
    exact hW.2.2.2 x' hx' x hx
  intro s t hst
  by_cases ht : t ≤ a
  · rw [dblFlag_le (hst.trans ht), dblFlag_le ht]
    exact nm hst
  · have et : dblFlag ε W t = perpJ ε (natFlag W (2 * a + 1 - t)) := by rw [dblFlag, if_neg ht]
    by_cases hs : s ≤ a
    · rw [dblFlag_le hs, et]
      exact (nm hs).trans (iso.trans (anti (nm (by omega))))
    · have es : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s)) := by rw [dblFlag, if_neg hs]
      rw [es, et]
      exact anti (nm (by omega))

/- English proof (translation)
Rewrite using `[dblFlag_le (Nat.zero_le a)]`. Establish `e : (⟨min 0 a, by omega⟩ : Fin (a + 1)) = 0` using `Fin.ext (by simp)`. Use `show W ⟨min 0 a, by omega⟩ = ⊥`. Rewrite using `[e]`. Conclude with `hW.1`.
-/
theorem dblFlag_zero (hW : IsIsoFlag ε j W) : dblFlag ε W 0 = ⊥ := by
  rw [dblFlag_le (Nat.zero_le a)]
  have e : (⟨min 0 a, by omega⟩ : Fin (a + 1)) = 0 := Fin.ext (by simp)
  show W ⟨min 0 a, by omega⟩ = ⊥
  rw [e]
  exact hW.1

/- English proof (translation)
Establish `e` using `dblFlag_sub (ε := ε) (W := W) (Nat.zero_le a)`. Rewrite `e` using `[Nat.sub_zero, dblFlag_zero hW]`. Rewrite using `[e, eq_top_iff]`. Introduce `y _`. Rewrite using `[mem_perpJ]`.

Introduce `x hx`. Rewrite using `[(Submodule.mem_bot ℂ).1 hx, star_zero, zero_dotProduct]`.
-/
theorem dblFlag_top (hW : IsIsoFlag ε j W) : dblFlag ε W (2 * a + 1) = ⊤ := by
  have e := dblFlag_sub (ε := ε) (W := W) (Nat.zero_le a)
  rw [Nat.sub_zero, dblFlag_zero hW] at e
  rw [e, eq_top_iff]
  intro y _
  rw [mem_perpJ]
  intro x hx
  rw [(Submodule.mem_bot ℂ).1 hx, star_zero, zero_dotProduct]

/- English proof (translation)
Introduce `y hy`. Distinguish the cases in `hs : s ≤ a`. Rewrite `hy`, the goal using `[dblFlag_le hs]`. Conclude with `hm _ y hy`. Establish `e : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s))` using `by rw [dblFlag, if_neg hs]`.

Rewrite `hy`, the goal using `[e, mem_perpJ]`. Introduce `x hx`. Establish `h1` using `GlobalTheory.FlagLeviGroup.form_inv m⁻¹ x y`. Rewrite `h1` using `[inv_inv]`. Rewrite using `[h1]`.

Conclude with `hy _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (natFlag W (2 * a + 1 - s)) (hm _) x hx)`.
-/
theorem dblFlag_keeps (m : UJ ε) (hm : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i) (s : ℕ) :
    ∀ y ∈ dblFlag ε W s, uMat m *ᵥ y ∈ dblFlag ε W s := by
  intro y hy
  by_cases hs : s ≤ a
  · rw [dblFlag_le hs] at hy ⊢
    exact hm _ y hy
  · have e : dblFlag ε W s = perpJ ε (natFlag W (2 * a + 1 - s)) := by rw [dblFlag, if_neg hs]
    rw [e, mem_perpJ] at hy ⊢
    intro x hx
    have h1 := GlobalTheory.FlagLeviGroup.form_inv m⁻¹ x y
    rw [inv_inv] at h1
    rw [h1]
    exact hy _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (natFlag W (2 * a + 1 - s)) (hm _) x hx)

/- English proof (translation)
Establish `hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s` using `hX`. Use `show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (Jm ε * Xᴴ * Jm ε) *ᵥ y ∈ dblFlag ε W s`. Introduce `s hs y hy`. Establish `e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s))`. Establish `h` using `dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)`.

Rewrite `h` using `[show 2 * a + 1 - (2 * a + 1 - s) = s by omega]`. Then use the resulting hypothesis. Establish `e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s))`. Establish `h` using `dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)`. Rewrite `h` using `[show 2 * a + 1 - (2 * a - s) = s + 1 by omega]`. Then use the resulting hypothesis. Rewrite using `[e1, mem_perpJ]`.

Rewrite `hy` using `[e2, mem_perpJ]`. Introduce `x hx`. Rewrite using `[form_adj]`. Establish `hx' : x ∈ dblFlag ε W (2 * a - s + 1)` using `by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]`. Conclude with `hy _ (hX' (2 * a - s) (by omega) x hx')`.
-/
theorem adj_mem_lower {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lower (dblFlag ε W) (2 * a + 1)) :
    Jm ε * Xᴴ * Jm ε ∈ lower (dblFlag ε W) (2 * a + 1) := by
  have hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
  show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (Jm ε * Xᴴ * Jm ε) *ᵥ y ∈ dblFlag ε W s
  intro s hs y hy
  have e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s)) := by
    have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)
    rwa [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at h
  have e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s)) := by
    have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)
    rwa [show 2 * a + 1 - (2 * a - s) = s + 1 by omega] at h
  rw [e1, mem_perpJ]
  rw [e2, mem_perpJ] at hy
  intro x hx
  rw [form_adj]
  have hx' : x ∈ dblFlag ε W (2 * a - s + 1) := by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]
  exact hy _ (hX' (2 * a - s) (by omega) x hx')

/- English proof (translation)
Establish `ea1 : dblFlag ε W (a + 1) = perpJ ε (W (Fin.last a))`. Establish `h` using `dblFlag_sub (ε := ε) (W := W) (le_refl a)`. Rewrite `h` using `[show 2 * a + 1 - a = a + 1 by omega, dblFlag_last]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `hX`.

Establish `hX' : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s` using `hX`. Use `⟨fun i y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h` using `hX' i (by omega) y (by rw [dblFlag_succ]; exact hy)`. Rewrite `h` using `[dblFlag_castSucc]`. Then use the resulting hypothesis. Establish `h` using `hX' a (by omega) y (by rw [ea1, mem_perpJ]; exact hy)`.

Rewrite `h` using `[dblFlag_last]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩ show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s`. Introduce `s hs y hy`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl` into its components or cases. Establish `e1 : dblFlag ε W (s + 1) = W ⟨s + 1, by omega⟩` using `dblFlag_succ (ε := ε) (W := W) ⟨s, hs⟩`.

Establish `e2 : dblFlag ε W s = W ⟨s, by omega⟩` using `dblFlag_castSucc (ε := ε) (W := W) ⟨s, hs⟩`. Rewrite `hy` using `[e1]`. Rewrite using `[e2]`. Conclude with `h1 ⟨s, hs⟩ y hy`. Rewrite `hy` using `[ea1, mem_perpJ]`.

Rewrite using `[dblFlag_last]`. Conclude with `h2 y hy`.
-/
theorem mem_lower_half {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lower (dblFlag ε W) (a + 1) ↔
    (∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y, (∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Jm ε *ᵥ y) = 0) → X *ᵥ y ∈ W (Fin.last a) := by
  have ea1 : dblFlag ε W (a + 1) = perpJ ε (W (Fin.last a)) := by
    have h := dblFlag_sub (ε := ε) (W := W) (le_refl a)
    rwa [show 2 * a + 1 - a = a + 1 by omega, dblFlag_last] at h
  constructor
  · intro hX
    have hX' : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · have h := hX' i (by omega) y (by rw [dblFlag_succ]; exact hy)
      rwa [dblFlag_castSucc] at h
    · have h := hX' a (by omega) y (by rw [ea1, mem_perpJ]; exact hy)
      rwa [dblFlag_last] at h
  · rintro ⟨h1, h2⟩
    show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s
    intro s hs y hy
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · have e1 : dblFlag ε W (s + 1) = W ⟨s + 1, by omega⟩ := dblFlag_succ (ε := ε) (W := W) ⟨s, hs⟩
      have e2 : dblFlag ε W s = W ⟨s, by omega⟩ := dblFlag_castSucc (ε := ε) (W := W) ⟨s, hs⟩
      rw [e1] at hy
      rw [e2]
      exact h1 ⟨s, hs⟩ y hy
    · rw [ea1, mem_perpJ] at hy
      rw [dblFlag_last]
      exact h2 y hy

/- English proof (translation)
Establish `hX' : ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s` using `hX`. Use `show ∀ s, s < r → ∀ y ∈ F (s + 1), (uMat m * X * uMat m⁻¹) *ᵥ y ∈ F s`. Introduce `s hs y hy`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `hm s _ (hX' s hs _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (F (s + 1)) (hm (s + 1)) y hy))`.
-/
theorem conj_mem_lower {F : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ} (m : UJ ε)
    (hm : ∀ s, ∀ y ∈ F s, uMat m *ᵥ y ∈ F s) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lower F r) :
    uMat m * X * uMat m⁻¹ ∈ lower F r := by
  have hX' : ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s := hX
  show ∀ s, s < r → ∀ y ∈ F (s + 1), (uMat m * X * uMat m⁻¹) *ᵥ y ∈ F s
  intro s hs y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hm s _ (hX' s hs _ (GlobalTheory.FlagMeas.UnipRad.inv_keeps m (F (s + 1)) (hm (s + 1)) y hy))

/- English proof (translation)
Introduce `n ε a j W hj hW μ hμ m hm`. Take `⟨⟨N, hN⟩, hNc, -⟩` from `GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW`. Take `⟨⟨M, hM⟩, -, -, -, hconj⟩` from `GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W`. Establish `hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i` using `fun i y hy => (hm i y hy).1`. Establish `hkeep : ∀ s, ∀ y ∈ dblFlag ε W s, uMat m *ᵥ y ∈ dblFlag ε W s` using `dblFlag_keeps m hmk`.

Establish `hmi : m⁻¹ ∈ flagM ε W`. Rewrite using `[← hM]`. Conclude with `M.inv_mem (by rw [← SetLike.mem_coe, hM]; exact hm)`. Establish `hS : ∀ g, g ∈ N ↔ m * g * m⁻¹ ∈ N`. Introduce `g`.

Rewrite using `[← SetLike.mem_coe, ← SetLike.mem_coe, hN]`. Use `⟨hconj m hm g, fun h => ?_⟩` and prove the remaining obligations. Establish `h2` using `hconj m⁻¹ hmi _ h`. Establish `e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g` using `by group`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.

Establish `hNinv : ∀ g, g ∈ flagN ε W → g⁻¹ ∈ flagN ε W`. Introduce `g hg`. Rewrite `hg`, the goal using `[← hN]`. Conclude with `N.inv_mem hg`. Establish `half : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (a + 1)`.

Introduce `g`. Rewrite using `[mem_lower_half]`. Simplify using `only [Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `Iff.rfl`. Establish `hNA : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (2 * a + 1)`.

Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `h1 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s` using `(half g).1 hg`. Establish `h2 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g⁻¹ - 1) *ᵥ y ∈ dblFlag ε W s` using `(half g⁻¹).1 (hNinv g hg)`.

Use `show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s`. Introduce `s hs y hy`. Distinguish the cases in `hsa : s < a + 1`. Conclude with `h1 s hsa y hy`. Establish `e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s))`.

Establish `h` using `dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)`. Rewrite `h` using `[show 2 * a + 1 - (2 * a + 1 - s) = s by omega]`. Then use the resulting hypothesis. Establish `e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s))`. Establish `h` using `dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)`. Rewrite `h` using `[show 2 * a + 1 - (2 * a - s) = s + 1 by omega]`. Then use the resulting hypothesis.

Rewrite using `[e1, mem_perpJ]`. Rewrite `hy` using `[e2, mem_perpJ]`. Introduce `x hx`. Establish `h3` using `GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y`. Rewrite `h3` using `[inv_inv]`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub, h3, ← sub_dotProduct, ← star_sub]`. Establish `e3 : uMat g⁻¹ *ᵥ x - x = (uMat g⁻¹ - 1) *ᵥ x` using `by rw [Matrix.sub_mulVec, Matrix.one_mulVec]`. Rewrite using `[e3]`. Conclude with `hy _ (h2 (2 * a - s) (by omega) x (by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]))`. Introduce `h`.

Apply `(half g).2` to reduce the goal to its premises. Establish `h' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s` using `h`. Use `show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s`. Conclude with `fun s hs => h' s (by omega)`. Establish `hAmul : ∀ X ∈ lower (dblFlag ε W) (2 * a + 1), ∀ Y ∈ lower (dblFlag ε W) (2 * a + 1), X * Y ∈ lower (dblFlag ε W) (2 * a + 1)`.

Introduce `X hX Y hY`. Establish `hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s` using `hX`. Establish `hY' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), Y *ᵥ y ∈ dblFlag ε W s` using `hY`. Use `show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (X * Y) *ᵥ y ∈ dblFlag ε W s`. Introduce `s hs y hy`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Break down `s with _ | s` into its components or cases. Establish `h0 : Y *ᵥ y ∈ dblFlag ε W 0` using `hY' 0 hs y hy`. Rewrite `h0` using `[dblFlag_zero hW, Submodule.mem_bot]`. Rewrite using `[h0, Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Conclude with `dblFlag_mono hW (Nat.le_succ s) (hX' s (by omega) _ (hY' (s + 1) hs y hy))`. Take `⟨d, E, hEo, hEli, hEspan⟩` from `GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' n ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ ⊓ lieSub ε)`. Establish `hE : ∀ X, (X ∈ lower (dblFlag ε W) (2 * a + 1) ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)`. Introduce `X`.

Rewrite using `[← hEspan]`. Conclude with `Iff.rfl`. Establish `h55` using `GlobalTheory.T.finrank_and_det_of_real_basis_skew_part n ε (lower (dblFlag ε W) (2 * a + 1)) d E (fun X hX => adj_mem_lower hX) hEli hE`. Establish `hdet1 : ‖(uMat m).det‖ = 1` using `((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε ⊥ (perpJ ε ⊥) (fun y => mem_perpJ)).2.2 m).1`. Establish `h38` using `GlobalTheory.T.flagNilradical_finrank_and_abs_det_conj n (uMat m) (uMat m⁻¹) (2 * a + 1) (dblFlag ε W) (lower (dblFlag ε W) (2 * a + 1)) (GlobalTheory.FlagLeviGroup.uMat_mul_inv m) hdet1 (dblFlag_mono hW) (dblFlag_zero hW) (dblFlag_top hW) hkeep (fun X => Iff.rfl)`.

Establish `hDpos : ∀ s, 0 < detOn (uMat m) (dblFlag ε W s)` using `fun s => (((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)).2.2 m).2 (hkeep s)).2.2`. Establish `hD0 : detOn (uMat m) (dblFlag ε W 0) = 1`. Rewrite using `[dblFlag_zero hW]`. Establish `hb : ∀ y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)), Matrix.toLin' (uMat m) y ∈ (⊥ : Submodule ℂ (Fin n → ℂ))`. Introduce `y hy`.

Rewrite using `[(Submodule.mem_bot ℂ).1 hy, map_zero]`. Conclude with `zero_mem _`. Unfold `detOn`. Rewrite using `[dif_pos hb, LinearMap.det_eq_one_of_subsingleton, norm_one]`. Establish `hν0 : Module.finrank ℂ (dblFlag ε W 0) = 0` using `by rw [dblFlag_zero hW, finrank_bot]`.

Establish `hνs : ∀ i : Fin a, Module.finrank ℂ (dblFlag ε W (i + 1)) = Module.finrank ℂ (dblFlag ε W i) + j i`. Introduce `i`. Rewrite using `[dblFlag_succ, dblFlag_castSucc]`. Conclude with `hW.2.2.1 i`. Establish `h2ν : 2 * Module.finrank ℂ (dblFlag ε W a) ≤ n`.

Establish `h40` using `(GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W a) (perpJ ε (dblFlag ε W a)) (fun y => mem_perpJ)).1`. Establish `hle : dblFlag ε W a ≤ perpJ ε (dblFlag ε W a)`. Rewrite using `[dblFlag_last]`. Introduce `x hx`. Rewrite using `[mem_perpJ]`.

Introduce `x' hx'`. Conclude with `hW.2.2.2 x' hx' x hx`. Establish `h3` using `Submodule.finrank_mono hle`. Use linear arithmetic over natural numbers and integers. Establish `hsym : ∀ s, s ≤ a → detOn (uMat m) (dblFlag ε W (2 * a + 1 - s)) = detOn (uMat m) (dblFlag ε W s) ∧ Module.finrank ℂ (dblFlag ε W (2 * a + 1 - s)) + Module.finrank ℂ (dblFlag ε W s) = n`.

Introduce `s hs`. Establish `h40` using `GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)`. Rewrite using `[dblFlag_sub hs]`. Conclude with `⟨((h40.2.2 m).2 (hkeep s)).2.1, h40.1⟩`. Establish `h56` using `GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd n a j (fun s => detOn (uMat m) (dblFlag ε W s)) (fun s => Module.finrank ℂ (dblFlag ε W s)) hj hDpos hD0 hν0 hνs h2ν hsym`.

Establish `hconjE : ∀ k, uMat m * E k * uMat m⁻¹ ∈ Submodule.span ℝ (Set.range E)`. Introduce `k`. Establish `hk` using `(hE (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)`. Conclude with `(hE _).1 ⟨conj_mem_lower m hkeep hk.1, inG_conj m hk.2⟩`. Use `choose z hz using fun k => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hconjE k)`.

Set `L : Matrix (Fin d) (Fin d) ℝ` to `Matrix.of fun i k => z k i`. Establish `hL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i` using `fun k => (hz k).symm`. Set `φ : lower (dblFlag ε W) (2 * a + 1) →ₗ[ℂ] lower (dblFlag ε W) (2 * a + 1)` to `{ toFun := fun X => ⟨uMat m * X * uMat m⁻¹, conj_mem_lower m hkeep X.2⟩ map_add' := fun X Y => by ext1`. Simplify using `[Matrix.mul_add, Matrix.add_mul]`. Use the proof step `map_smul' := fun c X => by ext1`.

Simplify using `}`. Establish `hφ : ∀ X : lower (dblFlag ε W) (2 * a + 1), ((φ X : lower (dblFlag ε W) (2 * a + 1)) : Matrix (Fin n) (Fin n) ℂ) = uMat m * X * uMat m⁻¹` using `fun X => rfl`. Establish `hdetφ : LinearMap.det φ = ((L.det : ℝ) : ℂ)` using `h55.2 φ L (fun k _ => hL k)`. Establish `hnorm` using `h38.2 φ hφ`. Establish `habs : |L.det| = ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^ Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^ Module.finrank ℂ (dblFlag ε W s)`.

Rewrite using `[← hnorm, hdetφ, Complex.norm_real, Real.norm_eq_abs]`. Establish `hP : 0 < ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^ Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^ Module.finrank ℂ (dblFlag ε W s)` using `Finset.prod_pos fun s _ => div_pos (pow_pos (hDpos s) _) (pow_pos (hDpos (s + 1)) _)`. Establish `hLne : L.det ≠ 0` using `abs_pos.1 (by rw [habs]; exact hP)`. Establish `hd : d = dimN n j`. Rewrite using `[← h55.1, h38.1]`.

Conclude with `h56.1`. Establish `hNA' : ∀ g, g ∈ N ↔ uMat g - 1 ∈ (lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ`. Introduce `g`. Rewrite using `[← SetLike.mem_coe, hN]`. Conclude with `hNA g`.

Establish `h28` using `GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul n ε ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ) d E N hAmul hEo hE hNA' (by rw [hN]; exact hNc) μ (by rw [hN, hd]; exact hμ) m L hS hL hLne`. Establish `hloc : locSize j W (uMat m) = fun i : Fin a => (detOn (uMat m) (dblFlag ε W (i + 1)) / detOn (uMat m) (dblFlag ε W i)) ^ (-(1 : ℝ) / j i)`. Use function extensionality and compare the values at `i`. Rewrite using `[dblFlag_succ, dblFlag_castSucc]`. Both sides reduce to the same expression.

Establish `hfin : layerProd n 1 j (locSize j W (uMat m)) id = |L.det|⁻¹`. Rewrite using `[hloc, habs]`. Conclude with `h56.2`. Rewrite using `[h28, hfin]`.
-/
theorem modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → ∀ μ, IsGaugeSub (flagN ε W) (dimN n j) μ → ∀ m ∈ flagM ε W, μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) • μ := by
  intro n ε a j W hj hW μ hμ m hm
  obtain ⟨⟨N, hN⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hM⟩, -, -, -, hconj⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  have hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i := fun i y hy => (hm i y hy).1
  have hkeep : ∀ s, ∀ y ∈ dblFlag ε W s, uMat m *ᵥ y ∈ dblFlag ε W s := dblFlag_keeps m hmk
  have hmi : m⁻¹ ∈ flagM ε W := by
    rw [← hM]
    exact M.inv_mem (by rw [← SetLike.mem_coe, hM]; exact hm)
  have hS : ∀ g, g ∈ N ↔ m * g * m⁻¹ ∈ N := by
    intro g
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, hN]
    refine ⟨hconj m hm g, fun h => ?_⟩
    have h2 := hconj m⁻¹ hmi _ h
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rwa [e] at h2
  have hNinv : ∀ g, g ∈ flagN ε W → g⁻¹ ∈ flagN ε W := by
    intro g hg
    rw [← hN] at hg ⊢
    exact N.inv_mem hg
  have half : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (a + 1) := by
    intro g
    rw [mem_lower_half]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Iff.rfl
  have hNA : ∀ g : UJ ε, g ∈ flagN ε W ↔ uMat g - 1 ∈ lower (dblFlag ε W) (2 * a + 1) := by
    intro g
    constructor
    · intro hg
      have h1 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s :=
        (half g).1 hg
      have h2 : ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g⁻¹ - 1) *ᵥ y ∈ dblFlag ε W s :=
        (half g⁻¹).1 (hNinv g hg)
      show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s
      intro s hs y hy
      by_cases hsa : s < a + 1
      · exact h1 s hsa y hy
      · have e1 : dblFlag ε W s = perpJ ε (dblFlag ε W (2 * a + 1 - s)) := by
          have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a + 1 - s) (by omega)
          rwa [show 2 * a + 1 - (2 * a + 1 - s) = s by omega] at h
        have e2 : dblFlag ε W (s + 1) = perpJ ε (dblFlag ε W (2 * a - s)) := by
          have h := dblFlag_dual (ε := ε) (W := W) (s := 2 * a - s) (by omega)
          rwa [show 2 * a + 1 - (2 * a - s) = s + 1 by omega] at h
        rw [e1, mem_perpJ]
        rw [e2, mem_perpJ] at hy
        intro x hx
        have h3 := GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y
        rw [inv_inv] at h3
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub, h3, ← sub_dotProduct,
          ← star_sub]
        have e3 : uMat g⁻¹ *ᵥ x - x = (uMat g⁻¹ - 1) *ᵥ x := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        rw [e3]
        exact hy _ (h2 (2 * a - s) (by omega) x (by rwa [show 2 * a - s + 1 = 2 * a + 1 - s by omega]))
    · intro h
      apply (half g).2
      have h' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s := h
      show ∀ s, s < a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (uMat g - 1) *ᵥ y ∈ dblFlag ε W s
      exact fun s hs => h' s (by omega)
  have hAmul : ∀ X ∈ lower (dblFlag ε W) (2 * a + 1), ∀ Y ∈ lower (dblFlag ε W) (2 * a + 1),
      X * Y ∈ lower (dblFlag ε W) (2 * a + 1) := by
    intro X hX Y hY
    have hX' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), X *ᵥ y ∈ dblFlag ε W s := hX
    have hY' : ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), Y *ᵥ y ∈ dblFlag ε W s := hY
    show ∀ s, s < 2 * a + 1 → ∀ y ∈ dblFlag ε W (s + 1), (X * Y) *ᵥ y ∈ dblFlag ε W s
    intro s hs y hy
    rw [← Matrix.mulVec_mulVec]
    rcases s with _ | s
    · have h0 : Y *ᵥ y ∈ dblFlag ε W 0 := hY' 0 hs y hy
      rw [dblFlag_zero hW, Submodule.mem_bot] at h0
      rw [h0, Matrix.mulVec_zero]
      exact zero_mem _
    · exact dblFlag_mono hW (Nat.le_succ s) (hX' s (by omega) _ (hY' (s + 1) hs y hy))
  obtain ⟨d, E, hEo, hEli, hEspan⟩ :=
    GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' n ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ ⊓ lieSub ε)
  have hE : ∀ X, (X ∈ lower (dblFlag ε W) (2 * a + 1) ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := by
    intro X
    rw [← hEspan]
    exact Iff.rfl
  have h55 := GlobalTheory.T.finrank_and_det_of_real_basis_skew_part n ε (lower (dblFlag ε W) (2 * a + 1)) d E (fun X hX => adj_mem_lower hX) hEli hE
  have hdet1 : ‖(uMat m).det‖ = 1 :=
    ((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε ⊥ (perpJ ε ⊥) (fun y => mem_perpJ)).2.2 m).1
  have h38 := GlobalTheory.T.flagNilradical_finrank_and_abs_det_conj n (uMat m) (uMat m⁻¹) (2 * a + 1) (dblFlag ε W) (lower (dblFlag ε W) (2 * a + 1))
    (GlobalTheory.FlagLeviGroup.uMat_mul_inv m) hdet1 (dblFlag_mono hW) (dblFlag_zero hW) (dblFlag_top hW) hkeep
    (fun X => Iff.rfl)
  have hDpos : ∀ s, 0 < detOn (uMat m) (dblFlag ε W s) := fun s =>
    (((GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)).2.2 m).2 (hkeep s)).2.2
  have hD0 : detOn (uMat m) (dblFlag ε W 0) = 1 := by
    rw [dblFlag_zero hW]
    have hb : ∀ y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)), Matrix.toLin' (uMat m) y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := by
      intro y hy
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact zero_mem _
    unfold detOn
    rw [dif_pos hb, LinearMap.det_eq_one_of_subsingleton, norm_one]
  have hν0 : Module.finrank ℂ (dblFlag ε W 0) = 0 := by rw [dblFlag_zero hW, finrank_bot]
  have hνs : ∀ i : Fin a, Module.finrank ℂ (dblFlag ε W (i + 1)) = Module.finrank ℂ (dblFlag ε W i) + j i := by
    intro i
    rw [dblFlag_succ, dblFlag_castSucc]
    exact hW.2.2.1 i
  have h2ν : 2 * Module.finrank ℂ (dblFlag ε W a) ≤ n := by
    have h40 := (GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W a) (perpJ ε (dblFlag ε W a)) (fun y => mem_perpJ)).1
    have hle : dblFlag ε W a ≤ perpJ ε (dblFlag ε W a) := by
      rw [dblFlag_last]
      intro x hx
      rw [mem_perpJ]
      intro x' hx'
      exact hW.2.2.2 x' hx' x hx
    have h3 := Submodule.finrank_mono hle
    omega
  have hsym : ∀ s, s ≤ a → detOn (uMat m) (dblFlag ε W (2 * a + 1 - s)) = detOn (uMat m) (dblFlag ε W s) ∧
      Module.finrank ℂ (dblFlag ε W (2 * a + 1 - s)) + Module.finrank ℂ (dblFlag ε W s) = n := by
    intro s hs
    have h40 := GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary n ε (dblFlag ε W s) (perpJ ε (dblFlag ε W s)) (fun y => mem_perpJ)
    rw [dblFlag_sub hs]
    exact ⟨((h40.2.2 m).2 (hkeep s)).2.1, h40.1⟩
  have h56 := GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd n a j (fun s => detOn (uMat m) (dblFlag ε W s))
    (fun s => Module.finrank ℂ (dblFlag ε W s)) hj hDpos hD0 hν0 hνs h2ν hsym
  have hconjE : ∀ k, uMat m * E k * uMat m⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    intro k
    have hk := (hE (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
    exact (hE _).1 ⟨conj_mem_lower m hkeep hk.1, inG_conj m hk.2⟩
  choose z hz using fun k => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hconjE k)
  let L : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => z k i
  have hL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i := fun k => (hz k).symm
  let φ : lower (dblFlag ε W) (2 * a + 1) →ₗ[ℂ] lower (dblFlag ε W) (2 * a + 1) :=
    { toFun := fun X => ⟨uMat m * X * uMat m⁻¹, conj_mem_lower m hkeep X.2⟩
      map_add' := fun X Y => by
        ext1
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        ext1
        simp }
  have hφ : ∀ X : lower (dblFlag ε W) (2 * a + 1),
      ((φ X : lower (dblFlag ε W) (2 * a + 1)) : Matrix (Fin n) (Fin n) ℂ) = uMat m * X * uMat m⁻¹ :=
    fun X => rfl
  have hdetφ : LinearMap.det φ = ((L.det : ℝ) : ℂ) := h55.2 φ L (fun k _ => hL k)
  have hnorm := h38.2 φ hφ
  have habs : |L.det| = ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^
      Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^
      Module.finrank ℂ (dblFlag ε W s) := by
    rw [← hnorm, hdetφ, Complex.norm_real, Real.norm_eq_abs]
  have hP : 0 < ∏ s ∈ Finset.range (2 * a + 1), detOn (uMat m) (dblFlag ε W s) ^
      Module.finrank ℂ (dblFlag ε W (s + 1)) / detOn (uMat m) (dblFlag ε W (s + 1)) ^
      Module.finrank ℂ (dblFlag ε W s) :=
    Finset.prod_pos fun s _ => div_pos (pow_pos (hDpos s) _) (pow_pos (hDpos (s + 1)) _)
  have hLne : L.det ≠ 0 := abs_pos.1 (by rw [habs]; exact hP)
  have hd : d = dimN n j := by
    rw [← h55.1, h38.1]
    exact h56.1
  have hNA' : ∀ g, g ∈ N ↔ uMat g - 1 ∈ (lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ := by
    intro g
    rw [← SetLike.mem_coe, hN]
    exact hNA g
  have h28 := GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul n ε ((lower (dblFlag ε W) (2 * a + 1)).restrictScalars ℝ) d E N hAmul hEo hE hNA'
    (by rw [hN]; exact hNc) μ (by rw [hN, hd]; exact hμ) m L hS hL hLne
  have hloc : locSize j W (uMat m) = fun i : Fin a =>
      (detOn (uMat m) (dblFlag ε W (i + 1)) / detOn (uMat m) (dblFlag ε W i)) ^ (-(1 : ℝ) / j i) := by
    funext i
    rw [dblFlag_succ, dblFlag_castSucc]
    rfl
  have hfin : layerProd n 1 j (locSize j W (uMat m)) id = |L.det|⁻¹ := by
    rw [hloc, habs]
    exact h56.2
  rw [h28, hfin]

end GlobalTheory.FlagModulus
