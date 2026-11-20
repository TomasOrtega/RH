import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development

noncomputable section

open NumberField Matrix Formalism.UG PI.InHHClassFin

namespace PI.UnitaryGroupMassFormula.InHHClassFin

variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

/- English proof (translation)
The claim follows from `RingHom.ext fun _ => rfl`.
-/
theorem sig_eq (I : Formalism.MainNotions.S.AutInst) : (I.cm.sig : I.E →+* I.E) = starRingEnd I.E :=
  RingHom.ext fun _ => rfl

def Frame.Jt (fr : Frame I S) : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E :=
  cT (starRingEnd I.E) fr.B * I.J * fr.B

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Frame.J'_eq (fr : Frame I S) : fr.J' = fr.Jt.toBlocks₂₂ := rfl

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) : hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_smul_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (c : A) (x y : n → A) : hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `[hform]`.
-/
theorem hform_zero_left {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (y : n → A) : hform σ J 0 y = 0 := by
  simp [hform]

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (c : A) (x y : n → A) : hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[hform]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]`.
-/
theorem hform_sum_right {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x : n → A) (s : Finset ι) (y : ι → n → A) :
    hform σ J x (∑ i ∈ s, y i) = ∑ i ∈ s, hform σ J x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hform]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx => exact hw x hx`. Consider the case `zero => exact hform_zero_left _ _ _`. Consider the case `add x y _ _ hx hy => rw [hform_add_left, hx, hy, add_zero]`.

Consider the case `smul a x _ hx => rw [hform_smul_left, hx, mul_zero]`.
-/
theorem hform_span_left (σ : I.E →+* I.E) (w : Fin I.n → I.E)
    (hw : ∀ s ∈ S, hform σ I.J s w = 0) :
    ∀ u ∈ Submodule.span I.E S, hform σ I.J u w = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact hw x hx
  | zero => exact hform_zero_left _ _ _
  | add x y _ _ hx hy => rw [hform_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [hform_smul_left, hx, mul_zero]

/- English proof (translation)
Establish `hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i`. Introduce `i j`. Establish `h` using `congrFun (congrFun I.J_herm j) i`. Simplify `h` using `[Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Simplify using `only [hform, map_sum, map_mul, starRingEnd_self_apply, hJ]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_swap (x y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J y x = starRingEnd I.E (hform (starRingEnd I.E) I.J x y) := by
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have h := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] using h
  simp only [hform, map_sum, map_mul, starRingEnd_self_apply, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [Frame.Jt, hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem Frame.Jt_apply (fr : Frame I S) (p q : Fin fr.m ⊕ Fin fr.k) :
    fr.Jt p q = hform (starRingEnd I.E) I.J (fun a => fr.B a p) (fun a => fr.B a q) := by
  simp only [Frame.Jt, hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use extensionality with `p q`. Use `show fr.Jt (Sum.inl p) (Sum.inr q) = 0`. Rewrite using `[Frame.Jt_apply]`. Conclude with `hform_span_left _ _ (fun s hs => fr.orth s hs q) _ (fr.col_span p)`.
-/
theorem Frame.Jt_12 (fr : Frame I S) : fr.Jt.toBlocks₁₂ = 0 := by
  ext p q
  show fr.Jt (Sum.inl p) (Sum.inr q) = 0
  rw [Frame.Jt_apply]
  exact hform_span_left _ _ (fun s hs => fr.orth s hs q) _ (fr.col_span p)

/- English proof (translation)
Use extensionality with `p q`. Use `show fr.Jt (Sum.inr p) (Sum.inl q) = 0`. Rewrite using `[Frame.Jt_apply, hform_swap, hform_span_left _ _ (fun s hs => fr.orth s hs p) _ (fr.col_span q), map_zero]`.
-/
theorem Frame.Jt_21 (fr : Frame I S) : fr.Jt.toBlocks₂₁ = 0 := by
  ext p q
  show fr.Jt (Sum.inr p) (Sum.inl q) = 0
  rw [Frame.Jt_apply, hform_swap, hform_span_left _ _ (fun s hs => fr.orth s hs p) _ (fr.col_span q), map_zero]

/- English proof (translation)
Establish `h` using `(Matrix.fromBlocks_toBlocks fr.Jt).symm`. Rewrite `h` using `[Frame.Jt_12, Frame.Jt_21, ← Frame.J'_eq]`. Conclude with `h`.
-/
theorem Frame.Jt_blocks (fr : Frame I S) : fr.Jt = Matrix.fromBlocks fr.Jt.toBlocks₁₁ 0 0 fr.J' := by
  have h := (Matrix.fromBlocks_toBlocks fr.Jt).symm
  rw [Frame.Jt_12, Frame.Jt_21, ← Frame.J'_eq] at h
  exact h

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_cT (M : Matrix (Fin I.n) (Fin I.n) I.E) : cT (starRingEnd I.E) (cT (starRingEnd I.E) M) = M := by
  ext i j
  simp [Formalism.UG.cT]

/- English proof (translation)
Simplify using `only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem cT_mul' {m p q : Type} [Fintype p] (M : Matrix m p I.E) (N : Matrix p q I.E) :
    cT (starRingEnd I.E) (M * N) = cT (starRingEnd I.E) N * cT (starRingEnd I.E) M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Establish `hJ : I.J * I.J⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)`. Establish `h1 : cT (starRingEnd I.E) (1 : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E) = 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[Formalism.UG.cT]`. Simplify using `[Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]`. Establish `hc : cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi = 1`. Rewrite using `[← cT_mul', fr.inv_mul, h1]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Frame.Jt, Matrix.mul_assoc]`. Use `_ = cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi := by`. Rewrite using `[fr.mul_inv, Matrix.mul_one, Matrix.mul_assoc (cT _ fr.B), hJ, Matrix.mul_one]`. Use `_ = 1 := hc`.
-/
theorem Frame.Jt_inv (fr : Frame I S) :
    fr.Jt * (fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi) = 1 := by
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have h1 : cT (starRingEnd I.E) (1 : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  have hc : cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi = 1 := by
    rw [← cT_mul', fr.inv_mul, h1]
  calc fr.Jt * (fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi)
      = cT (starRingEnd I.E) fr.B * I.J * (fr.B * fr.Bi) * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi := by
        simp only [Frame.Jt, Matrix.mul_assoc]
    _ = cT (starRingEnd I.E) fr.B * cT (starRingEnd I.E) fr.Bi := by
        rw [fr.mul_inv, Matrix.mul_one, Matrix.mul_assoc (cT _ fr.B), hJ, Matrix.mul_one]
    _ = 1 := hc

/- English proof (translation)
Establish `h1 : fr.Jt.det ≠ 0`. Introduce `h`. Establish `h2` using `congrArg Matrix.det (Frame.Jt_inv fr)`. Rewrite `h2` using `[Matrix.det_mul, h, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one h2`.

Rewrite `h1` using `[Frame.Jt_blocks, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩`.
-/
theorem Frame.det_blocks (fr : Frame I S) : fr.Jt.toBlocks₁₁.det ≠ 0 ∧ fr.J'.det ≠ 0 := by
  have h1 : fr.Jt.det ≠ 0 := by
    intro h
    have h2 := congrArg Matrix.det (Frame.Jt_inv fr)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  rw [Frame.Jt_blocks, Matrix.det_fromBlocks_zero₂₁] at h1
  exact ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩

/- English proof (translation)
Rewrite using `[Formalism.UG.IsHerm, sig_eq]`. Use extensionality with `p q`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Frame.J'_eq]`. Use `show starRingEnd I.E (fr.Jt (Sum.inr q) (Sum.inr p)) = fr.Jt (Sum.inr p) (Sum.inr q)`.

Rewrite using `[Frame.Jt_apply, Frame.Jt_apply, hform_swap (fun a => fr.B a (Sum.inr q)) (fun a => fr.B a (Sum.inr p))]`.
-/
theorem Frame.J'_herm (fr : Frame I S) : IsHerm (I.cm.sig : I.E →+* I.E) fr.J' := by
  rw [Formalism.UG.IsHerm, sig_eq]
  ext p q
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [Frame.J'_eq]
  show starRingEnd I.E (fr.Jt (Sum.inr q) (Sum.inr p)) = fr.Jt (Sum.inr p) (Sum.inr q)
  rw [Frame.Jt_apply, Frame.Jt_apply,
    hform_swap (fun a => fr.B a (Sum.inr q)) (fun a => fr.B a (Sum.inr p))]

/- English proof (translation)
Simplify using `only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.UG.cT, vecMul, mulVec, dotProduct, map_sum, mul_comm]`.
-/
theorem hform_cT {p : Type} [Fintype p] (B : Matrix (Fin I.n) p I.E) (u v : p → I.E) :
    hform (starRingEnd I.E) (cT (starRingEnd I.E) B * I.J * B) u v =
      hform (starRingEnd I.E) I.J (B *ᵥ u) (B *ᵥ v) := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  congr 1
  funext i
  simp [Formalism.UG.cT, vecMul, mulVec, dotProduct, map_sum, mul_comm]

/- English proof (translation)
Rewrite using `[← hform_cT]`. Simplify using `only [hform, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]`. Both sides reduce to the same expression.
-/
theorem Frame.hform_J' (fr : Frame I S) (x y : Fin fr.k → I.E) :
    hform (starRingEnd I.E) fr.J' x y =
      hform (starRingEnd I.E) I.J (fr.B *ᵥ Sum.elim 0 x) (fr.B *ᵥ Sum.elim 0 y) := by
  rw [← hform_cT]
  simp only [hform, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rfl

/- English proof (translation)
Introduce `s hs`. Establish `e : fr.B *ᵥ Sum.elim 0 x = ∑ b, x b • (fun i => fr.B i (Sum.inr b))`. Use extensionality with `i`. Simplify using `[mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]`. Rewrite using `[e, hform_sum_right]`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hform_smul_right, fr.orth s hs b, mul_zero]`.
-/
theorem Frame.orth_vec (fr : Frame I S) (x : Fin fr.k → I.E) :
    ∀ s ∈ S, hform (starRingEnd I.E) I.J s (fr.B *ᵥ Sum.elim 0 x) = 0 := by
  intro s hs
  have e : fr.B *ᵥ Sum.elim 0 x = ∑ b, x b • (fun i => fr.B i (Sum.inr b)) := by
    ext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]
  rw [e, hform_sum_right]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hform_smul_right, fr.orth s hs b, mul_zero]

/- English proof (translation)
Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `hw : Sum.elim (0 : Fin fr.m → I.E) x = 0`. Establish `h2` using `congrArg (fun v => fr.Bi *ᵥ v) h`. Simplify `h2` using `[Matrix.mulVec_mulVec, fr.inv_mul]`.

Use function extensionality and compare the values at `b`. Establish `h3` using `congrFun hw (Sum.inr b)`. Simplify using `using h3`.
-/
theorem Frame.vec_ne_zero (fr : Frame I S) (x : Fin fr.k → I.E) (hx : x ≠ 0) :
    fr.B *ᵥ Sum.elim 0 x ≠ 0 := by
  intro h
  apply hx
  have hw : Sum.elim (0 : Fin fr.m → I.E) x = 0 := by
    have h2 := congrArg (fun v => fr.Bi *ᵥ v) h
    simpa [Matrix.mulVec_mulVec, fr.inv_mul] using h2
  funext b
  have h3 := congrFun hw (Sum.inr b)
  simpa using h3

/- English proof (translation)
Introduce `I S fr hS`. Use `⟨Frame.J'_herm fr, isUnit_iff_ne_zero.mpr (Frame.det_blocks fr).2, I.cm.totReal, fun ι => ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.IsDefiniteAt`. Simplify using `only [sig_eq]`. Break down `hS ι with hpos | hneg` into its components or cases.

Use `left`. Introduce `x hx`. Rewrite using `[Frame.hform_J']`. Conclude with `hpos _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)`. Use `right`.

Introduce `x hx`. Rewrite using `[Frame.hform_J']`. Conclude with `hneg _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)`.
-/
theorem frameGram : FrameGram := by
  intro I S fr hS
  refine ⟨Frame.J'_herm fr, isUnit_iff_ne_zero.mpr (Frame.det_blocks fr).2, I.cm.totReal, fun ι => ?_⟩
  unfold Formalism.UG.IsDefiniteAt
  simp only [sig_eq]
  rcases hS ι with hpos | hneg
  · left
    intro x hx
    rw [Frame.hform_J']
    exact hpos _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)
  · right
    intro x hx
    rw [Frame.hform_J']
    exact hneg _ (Frame.vec_ne_zero fr x hx) (Frame.orth_vec fr x)

end PI.UnitaryGroupMassFormula.InHHClassFin
