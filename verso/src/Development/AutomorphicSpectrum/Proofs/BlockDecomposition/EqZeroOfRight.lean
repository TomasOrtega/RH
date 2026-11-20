import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag

noncomputable section

open NumberField Matrix
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.CompanionTheory.NonEll

variable {n : ℕ}

def formB (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)

def nrmC (D : GL (Fin n) ℂ) : GL (Fin n) ℂ := D * thetaR (starRingEnd ℂ) n D

/- English proof (translation)
Establish `hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1` using `by simp`. Establish `hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1` using `by simp`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `hy x hx`. Take `⟨u, hu, rfl⟩` from `Submodule.mem_map.1 hy`.

Use `hu x hx` as an intermediate fact. Simplify `this` using `[formB, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hiD, dotProduct]`. Introduce `h`. Use `Submodule.mem_map.2 ⟨(D⁻¹ : GL (Fin n) ℂ).val *ᵥ y, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Simplify `h x hx` using `[formB, dotProduct]`.

Simplify using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDi]`.
-/
theorem mem_perpD_iff (D : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perpD (starRingEnd ℂ) D W ↔ ∀ x ∈ W, formB D x y = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  constructor
  · rintro hy x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
    have := hu x hx
    simpa [formB, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hiD, dotProduct] using this
  · intro h
    refine Submodule.mem_map.2 ⟨(D⁻¹ : GL (Fin n) ℂ).val *ᵥ y, fun x hx => ?_, ?_⟩
    · simpa [formB, dotProduct] using h x hx
    · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDi]

/- English proof (translation)
Establish `hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1` using `by simp`. Establish `hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1` using `by simp`. Establish `hG : (nrmC D).val = D.val * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ`. Simplify using `only [nrmC, Units.val_mul, thetaR_val]`. Both sides reduce to the same expression.

Establish `hH : ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ * (D.val)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]`. Establish `hK : (nrmC D).valᴴ * (D⁻¹ : GL (Fin n) ℂ).val * (nrmC D).val = (D⁻¹ : GL (Fin n) ℂ).val`. Rewrite using `[hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hiD, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[← Matrix.conjTranspose_mul, hiD, Matrix.conjTranspose_one, Matrix.mul_one]`. Unfold `formB`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hK]`.
-/
theorem formB_nrm (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) :
    formB D ((nrmC D).val *ᵥ x) ((nrmC D).val *ᵥ y) = formB D x y := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  have hG : (nrmC D).val = D.val * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
    simp only [nrmC, Units.val_mul, thetaR_val]
    rfl
  have hH : ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ * (D.val)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hK : (nrmC D).valᴴ * (D⁻¹ : GL (Fin n) ℂ).val * (nrmC D).val = (D⁻¹ : GL (Fin n) ℂ).val := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = (D⁻¹ : GL (Fin n) ℂ).val * (D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val * D.val) *
          ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (D⁻¹ : GL (Fin n) ℂ).val * ((D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ) := by
          rw [hiD, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [← Matrix.conjTranspose_mul, hiD, Matrix.conjTranspose_one, Matrix.mul_one]
  unfold formB
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hK]

/- English proof (translation)
Simplify using `[formB, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem formB_smul_left (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D (c • x) y = conj c * formB D x y := by
  simp [formB, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[formB, Matrix.mulVec_smul, dotProduct_smul]`.
-/
theorem formB_smul_right (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D x (c • y) = c * formB D x y := by
  simp [formB, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[formB, star_add, add_dotProduct]`.
-/
theorem formB_add_left (D : GL (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    formB D (x + x') y = formB D x y + formB D x' y := by
  simp [formB, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `[formB, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem formB_add_right (D : GL (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    formB D x (y + y') = formB D x y + formB D x y' := by
  simp [formB, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[formB]`.
-/
theorem formB_zero_left (D : GL (Fin n) ℂ) (y : Fin n → ℂ) : formB D 0 y = 0 := by simp [formB]

/- English proof (translation)
Simplify using `[formB]`.
-/
theorem formB_zero_right (D : GL (Fin n) ℂ) (x : Fin n → ℂ) : formB D x 0 = 0 := by simp [formB]

/- English proof (translation)
Establish `hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1` using `by simp`. Establish `h1` using `h (D.val *ᵥ x)`. Simplify using `only [formB, Matrix.mulVec_mulVec] at h1`. Rewrite `h1` using `[show (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 by simp, Matrix.one_mulVec]`. Conclude with `dotProduct_star_self_eq_zero.1 h1`.
-/
theorem eq_zero_of_left (D : GL (Fin n) ℂ) (x : Fin n → ℂ) (h : ∀ y, formB D x y = 0) : x = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have h1 := h (D.val *ᵥ x)
  simp only [formB, Matrix.mulVec_mulVec] at h1
  rw [show (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 by simp, Matrix.one_mulVec] at h1
  exact dotProduct_star_self_eq_zero.1 h1

/- English proof (translation)
Establish `h1` using `h ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)`. Establish `h2 : (D⁻¹ : GL (Fin n) ℂ).val *ᵥ y = 0` using `dotProduct_star_self_eq_zero.1 h1`. Establish `h3` using `congrArg (fun w => D.val *ᵥ w) h2`. Simplify `h3` using `[Matrix.mulVec_mulVec]`.
-/
theorem eq_zero_of_right (D : GL (Fin n) ℂ) (y : Fin n → ℂ) (h : ∀ x, formB D x y = 0) : y = 0 := by
  have h1 := h ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)
  have h2 : (D⁻¹ : GL (Fin n) ℂ).val *ᵥ y = 0 := dotProduct_star_self_eq_zero.1 h1
  have h3 := congrArg (fun w => D.val *ᵥ w) h2
  simpa [Matrix.mulVec_mulVec] using h3

abbrev endN (D : GL (Fin n) ℂ) : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' (nrmC D).val

/- English proof (translation)
Establish `e1 : (nrmC D).val *ᵥ x = μ • x` using `by simpa using Module.End.mem_eigenspace_iff.1 hx`. Establish `e2 : (nrmC D).val *ᵥ y = ν • y` using `by simpa using Module.End.mem_eigenspace_iff.1 hy`. Use `formB_nrm D x y` as an intermediate fact. Rewrite `this` using `[e1, e2, formB_smul_left, formB_smul_right, ← mul_assoc]`. Assume the negation of the conclusion as `h0`.

Conclude with `h (mul_right_cancel₀ h0 (by rw [this, one_mul]))`.
-/
theorem eigen_pair (D : GL (Fin n) ℂ) {μ ν : ℂ} {x y : Fin n → ℂ} (hx : x ∈ (endN D).eigenspace μ)
    (hy : y ∈ (endN D).eigenspace ν) (h : conj μ * ν ≠ 1) : formB D x y = 0 := by
  have e1 : (nrmC D).val *ᵥ x = μ • x := by simpa using Module.End.mem_eigenspace_iff.1 hx
  have e2 : (nrmC D).val *ᵥ y = ν • y := by simpa using Module.End.mem_eigenspace_iff.1 hy
  have := formB_nrm D x y
  rw [e1, e2, formB_smul_left, formB_smul_right, ← mul_assoc] at this
  by_contra h0
  exact h (mul_right_cancel₀ h0 (by rw [this, one_mul]))

def eigSum (D : GL (Fin n) ℂ) (P : ℂ → Prop) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ μ : {μ : ℂ // P μ}, (endN D).eigenspace μ

/- English proof (translation)
The claim follows from `le_iSup (fun μ : {μ : ℂ // P μ} => (endN D).eigenspace μ) ⟨μ, h⟩`.
-/
theorem eigen_le (D : GL (Fin n) ℂ) {P : ℂ → Prop} {μ : ℂ} (h : P μ) :
    (endN D).eigenspace μ ≤ eigSum D P :=
  le_iSup (fun μ : {μ : ℂ // P μ} => (endN D).eigenspace μ) ⟨μ, h⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.iSup_induction' with`. Consider the case `mem μ x hx`. Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem ν y hy => exact eigen_pair D hx hy (h _ _ μ.2 ν.2)`. Consider the case `zero => exact formB_zero_right D x`.

Consider the case `add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]`. Consider the case `zero => exact formB_zero_left D y`. Consider the case `add a b _ _ ha hb => rw [formB_add_left, ha, hb, add_zero]`.
-/
theorem eigSum_orth (D : GL (Fin n) ℂ) {P Q : ℂ → Prop} (h : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1)
    {x y : Fin n → ℂ} (hx : x ∈ eigSum D P) (hy : y ∈ eigSum D Q) : formB D x y = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem ν y hy => exact eigen_pair D hx hy (h _ _ μ.2 ν.2)
    | zero => exact formB_zero_right D x
    | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
  | zero => exact formB_zero_left D y
  | add a b _ _ ha hb => rw [formB_add_left, ha, hb, add_zero]

/- English proof (translation)
Establish `hss : (endN D).IsSemisimple`. Use `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree ?_` and prove the remaining obligations. Rewrite using `[← Matrix.charpoly_toLin']`. Conclude with `LinearMap.aeval_self_charpoly _`. Establish `h1` using `Module.End.iSup_maxGenEigenspace_eq_top (endN D)`.

Simplify `h1` using `only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]`.
-/
theorem iSup_eigen (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) :
    ⨆ μ, (endN D).eigenspace μ = ⊤ := by
  have hss : (endN D).IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree ?_
    rw [← Matrix.charpoly_toLin']
    exact LinearMap.aeval_self_charpoly _
  have h1 := Module.End.iSup_maxGenEigenspace_eq_top (endN D)
  simpa only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1

/- English proof (translation)
Rewrite using `[eq_top_iff, ← iSup_eigen D hs]`. Use `iSup_le fun μ => ?_` and prove the remaining obligations. Break down `h μ with h | h` into its components or cases. Conclude with `(eigen_le D h).trans le_sup_left`. Conclude with `(eigen_le D h).trans le_sup_right`.
-/
theorem eigSum_sup (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q : ℂ → Prop}
    (h : ∀ μ, P μ ∨ Q μ) : eigSum D P ⊔ eigSum D Q = ⊤ := by
  rw [eq_top_iff, ← iSup_eigen D hs]
  refine iSup_le fun μ => ?_
  rcases h μ with h | h
  · exact (eigen_le D h).trans le_sup_left
  · exact (eigen_le D h).trans le_sup_right

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[mem_perpD_iff]`. Establish `hy' : y ∈ eigSum D Q ⊔ eigSum D R` using `by rw [eigSum_sup D hs hQR]; trivial`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy'`.

Establish `hb0 : b = 0`. Use `eq_zero_of_right D b fun x => ?_` and prove the remaining obligations. Establish `hx : x ∈ eigSum D P ⊔ eigSum D P'` using `by rw [eigSum_sup D hs hPP]; trivial`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `h1 : formB D p b = 0`.

Use `hy p hp` as an intermediate fact. Rewrite `this` using `[formB_add_right, eigSum_orth D hPQ hp ha, zero_add]`. Then use the resulting hypothesis. Rewrite using `[formB_add_left, h1, eigSum_orth D hPR hq hb, add_zero]`. Rewrite using `[hb0, add_zero]`. Conclude with `ha`.

Introduce `y hy`. Rewrite using `[mem_perpD_iff]`. Conclude with `fun x hx => eigSum_orth D hPQ hx hy`.
-/
theorem perpD_eigSum (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q R P' : ℂ → Prop}
    (hPQ : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1) (hQR : ∀ μ, Q μ ∨ R μ) (hPP : ∀ μ, P μ ∨ P' μ)
    (hPR : ∀ μ ν, P' μ → R ν → conj μ * ν ≠ 1) :
    perpD (starRingEnd ℂ) D (eigSum D P) = eigSum D Q := by
  apply le_antisymm
  · intro y hy
    rw [mem_perpD_iff] at hy
    have hy' : y ∈ eigSum D Q ⊔ eigSum D R := by rw [eigSum_sup D hs hQR]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
    have hb0 : b = 0 := by
      refine eq_zero_of_right D b fun x => ?_
      have hx : x ∈ eigSum D P ⊔ eigSum D P' := by rw [eigSum_sup D hs hPP]; trivial
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : formB D p b = 0 := by
        have := hy p hp
        rwa [formB_add_right, eigSum_orth D hPQ hp ha, zero_add] at this
      rw [formB_add_left, h1, eigSum_orth D hPR hq hb, add_zero]
    rw [hb0, add_zero]
    exact ha
  · intro y hy
    rw [mem_perpD_iff]
    exact fun x hx => eigSum_orth D hPQ hx hy

/- English proof (translation)
Introduce `e`. Use `congrArg norm e` as an intermediate fact. Rewrite `this` using `[norm_mul, Complex.norm_conj, norm_one]`. Conclude with `h this`.
-/
theorem conj_mul_ne {μ ν : ℂ} (h : ‖μ‖ * ‖ν‖ ≠ 1) : conj μ * ν ≠ 1 := by
  intro e
  have := congrArg norm e
  rw [norm_mul, Complex.norm_conj, norm_one] at this
  exact h this

/- English proof (translation)
Establish `n1 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 1 < a → 1 ≤ b → a * b ≠ 1` using `fun {a b} _ _ ha hb => by nlinarith`. Establish `n2 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a < 1 → b ≤ 1 → a * b ≠ 1` using `fun {a b} h0 h1 ha hb => by nlinarith`. Establish `p1 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 < ‖μ‖)) = eigSum D (fun μ => 1 ≤ ‖μ‖)` using `perpD_eigSum D hs (R := fun μ => ‖μ‖ < 1) (P' := fun μ => ‖μ‖ ≤ 1) (fun μ ν hμ hν => conj_mul_ne (n1 (norm_nonneg _) (norm_nonneg _) hμ hν)) (fun μ => le_or_gt 1 ‖μ‖) (fun μ => (lt_or_ge 1 ‖μ‖)) (fun μ ν hμ hν => conj_mul_ne (by`. Rewrite using `[mul_comm]`. Conclude with `n2 (norm_nonneg _) (norm_nonneg _) hν hμ))`.

Establish `p2 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 ≤ ‖μ‖)) = eigSum D (fun μ => 1 < ‖μ‖)` using `perpD_eigSum D hs (R := fun μ => ‖μ‖ ≤ 1) (P' := fun μ => ‖μ‖ < 1) (fun μ ν hμ hν => conj_mul_ne (by`. Rewrite using `[mul_comm]`. Conclude with `n1 (norm_nonneg _) (norm_nonneg _) hν hμ))`. Use the proof step `(fun μ => lt_or_ge 1 ‖μ‖) (fun μ => le_or_gt 1 ‖μ‖)`. Use the proof step `(fun μ ν hμ hν => conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hμ hν))`.

Use `⟨_, _, ?_, ?_, p1, p2⟩` and prove the remaining obligations. Introduce `hbot`. Establish `hev : (endN D).HasEigenvalue z`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']`. Conclude with `hz`.

Take `⟨e, hee⟩` from `hev.exists_hasEigenvector`. Establish `he` using `hee.1`. Establish `he0` using `hee.2`. Break down `lt_or_gt_of_ne hz1 with hlt | hgt` into its components or cases. Use `he0 (eq_zero_of_left D e fun y => ?_)` and prove the remaining obligations.

Establish `hy : y ∈ ⨆ μ, (endN D).eigenspace μ` using `by rw [iSup_eigen D hs]; trivial`. Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem ν y hy`. Distinguish the cases in `hν : 1 < ‖ν‖`. Establish `: y ∈ (⊥ : Submodule ℂ (Fin n → ℂ))` using `hbot ▸ eigen_le D hν hy`.

Rewrite using `[(Submodule.mem_bot ℂ).1 this]`. Conclude with `formB_zero_right D e`. Conclude with `eigen_pair D he hy (conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hlt (not_lt.1 hν)))`. Consider the case `zero => exact formB_zero_right D e`. Consider the case `add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]`.

Establish `: e ∈ (⊥ : Submodule ℂ (Fin n → ℂ))` using `hbot ▸ eigen_le D hgt he`. Conclude with `he0 ((Submodule.mem_bot ℂ).1 this)`. Conclude with `iSup_le fun μ => eigen_le D (le_of_lt μ.2)`.
-/
theorem locFlag (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {z : ℂ}
    (hz : (nrmC D).val.charpoly.IsRoot z) (hz1 : ‖z‖ ≠ 1) :
    ∃ W₁ W₂ : Submodule ℂ (Fin n → ℂ), W₁ ≠ ⊥ ∧ W₁ ≤ W₂ ∧ perpD (starRingEnd ℂ) D W₁ = W₂ ∧
      perpD (starRingEnd ℂ) D W₂ = W₁ := by
  have n1 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 1 < a → 1 ≤ b → a * b ≠ 1 := fun {a b} _ _ ha hb => by nlinarith
  have n2 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a < 1 → b ≤ 1 → a * b ≠ 1 := fun {a b} h0 h1 ha hb => by nlinarith
  have p1 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 < ‖μ‖)) = eigSum D (fun μ => 1 ≤ ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ < 1) (P' := fun μ => ‖μ‖ ≤ 1)
      (fun μ ν hμ hν => conj_mul_ne (n1 (norm_nonneg _) (norm_nonneg _) hμ hν))
      (fun μ => le_or_gt 1 ‖μ‖) (fun μ => (lt_or_ge 1 ‖μ‖))
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n2 (norm_nonneg _) (norm_nonneg _) hν hμ))
  have p2 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 ≤ ‖μ‖)) = eigSum D (fun μ => 1 < ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ ≤ 1) (P' := fun μ => ‖μ‖ < 1)
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n1 (norm_nonneg _) (norm_nonneg _) hν hμ))
      (fun μ => lt_or_ge 1 ‖μ‖) (fun μ => le_or_gt 1 ‖μ‖)
      (fun μ ν hμ hν => conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hμ hν))
  refine ⟨_, _, ?_, ?_, p1, p2⟩
  · intro hbot
    have hev : (endN D).HasEigenvalue z := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hz
    obtain ⟨e, hee⟩ := hev.exists_hasEigenvector
    have he := hee.1
    have he0 := hee.2
    rcases lt_or_gt_of_ne hz1 with hlt | hgt
    · refine he0 (eq_zero_of_left D e fun y => ?_)
      have hy : y ∈ ⨆ μ, (endN D).eigenspace μ := by rw [iSup_eigen D hs]; trivial
      induction hy using Submodule.iSup_induction' with
      | mem ν y hy =>
        by_cases hν : 1 < ‖ν‖
        · have : y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hν hy
          rw [(Submodule.mem_bot ℂ).1 this]
          exact formB_zero_right D e
        · exact eigen_pair D he hy (conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hlt (not_lt.1 hν)))
      | zero => exact formB_zero_right D e
      | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
    · have : e ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hgt he
      exact he0 ((Submodule.mem_bot ℂ).1 this)
  · exact iSup_le fun μ => eigen_le D (le_of_lt μ.2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `IsCMField.complexEmbedding_complexConj E σ x`.
-/
theorem conjE_emb (σ : E →+* ℂ) (x : E) : σ (conjE E x) = conj (σ x) :=
  IsCMField.complexEmbedding_complexConj E σ x

/- English proof (translation)
Establish `h1 : ((locGL v d)⁻¹ : GL (Fin n) ℂ).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Simplify using `only [nrmC, nrm, Units.val_mul, thetaR_val, Matrix.map_mul]`. Rewrite using `[h1]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[conjE_emb]`.
-/
theorem nrmC_locGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    (nrmC (locGL v d)).val = (nrm d).val.map v.embedding := by
  have h1 : ((locGL v d)⁻¹ : GL (Fin n) ℂ).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := by
    rw [← map_inv]; rfl
  simp only [nrmC, nrm, Units.val_mul, thetaR_val, Matrix.map_mul]
  rw [h1]
  congr 1
  ext i j
  simp [conjE_emb]

/- English proof (translation)
Introduce `E _ _ _ n d hreg hell`. Establish `hnot : ∃ (τ : E →+* ℂ) (z : ℂ), ((nrm d).val.charpoly.map τ).IsRoot z ∧ ‖z‖ ≠ 1`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hell ⟨hreg, fun τ z hz => hno τ z hz⟩`.

Take `⟨τ, z, hz, hz1⟩` from `hnot`. Use `⟨InfinitePlace.mk τ, ?_⟩` and prove the remaining obligations. Use `set v := InfinitePlace.mk τ with hv`. Establish `hcp : (nrmC (locGL v d)).val.charpoly = (nrm d).val.charpoly.map v.embedding`. Rewrite using `[nrmC_locGL, Matrix.charpoly_map]`.

Establish `hs : (nrmC (locGL v d)).val.charpoly.Separable`. Rewrite using `[hcp]`. Conclude with `Polynomial.Separable.map hreg`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases. Conclude with `locFlag (locGL v d) hs (z := z) (by rw [hcp, hv, h]; exact hz) hz1`.

Use `locFlag (locGL v d) hs (z := conj z) ?_ (by rwa [Complex.norm_conj])` and prove the remaining obligations. Rewrite using `[hcp, hv, h]`. Establish `e : (nrm d).val.charpoly.map (ComplexEmbedding.conjugate τ) = ((nrm d).val.charpoly.map τ).map (starRingEnd ℂ)`. Rewrite using `[Polynomial.map_map]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `Polynomial.IsRoot.map hz`.
-/
theorem nonEllFlag : PositivityTheory.Rg.BcB.D4.NonEllFlag := by
  intro E _ _ _ n d hreg hell
  have hnot : ∃ (τ : E →+* ℂ) (z : ℂ), ((nrm d).val.charpoly.map τ).IsRoot z ∧ ‖z‖ ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hell ⟨hreg, fun τ z hz => hno τ z hz⟩
  obtain ⟨τ, z, hz, hz1⟩ := hnot
  refine ⟨InfinitePlace.mk τ, ?_⟩
  set v := InfinitePlace.mk τ with hv
  have hcp : (nrmC (locGL v d)).val.charpoly = (nrm d).val.charpoly.map v.embedding := by
    rw [nrmC_locGL, Matrix.charpoly_map]
  have hs : (nrmC (locGL v d)).val.charpoly.Separable := by
    rw [hcp]; exact Polynomial.Separable.map hreg
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact locFlag (locGL v d) hs (z := z) (by rw [hcp, hv, h]; exact hz) hz1
  · refine locFlag (locGL v d) hs (z := conj z) ?_ (by rwa [Complex.norm_conj])
    rw [hcp, hv, h]
    have e : (nrm d).val.charpoly.map (ComplexEmbedding.conjugate τ) =
        ((nrm d).val.charpoly.map τ).map (starRingEnd ℂ) := by
      rw [Polynomial.map_map]; rfl
    rw [e]
    exact Polynomial.IsRoot.map hz

end GlobalTheory.CompanionTheory.NonEll

end
