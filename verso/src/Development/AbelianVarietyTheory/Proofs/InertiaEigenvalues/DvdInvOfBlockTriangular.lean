import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UdlApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwahoriFactorisation

open Polynomial

namespace GlobalTheory.IwahoriFactor

section General

variable {O : Type} [CommRing O] {n : ℕ}

def Shape (α β : O) (g : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)

def UpperUnip (α : O) (u : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)

def LowerUnip (β : O) (l : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)

/- English proof (translation)
Introduce `i j`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.one_apply_ne h.ne]`. Conclude with `dvd_zero _`. Rewrite using `[Matrix.one_apply_ne h.ne']`.

Conclude with `dvd_zero _`.
-/
theorem Shape.one (α β : O) : Shape α β (1 : Matrix (Fin n) (Fin n) O) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.one_apply_ne h.ne]; exact dvd_zero _
  · rw [Matrix.one_apply_ne h.ne']; exact dvd_zero _

/- English proof (translation)
Introduce `i j`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.dvd_sum fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i k with hk | hk` into its components or cases.

Conclude with `((hx i k).1 hk).mul_right _`. Conclude with `((hy k j).1 (hk.trans_lt h)).mul_left _`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.dvd_sum fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k i with hk | hk` into its components or cases.

Conclude with `((hx i k).2 hk).mul_right _`. Conclude with `((hy k j).2 (h.trans_le hk)).mul_left _`.
-/
theorem Shape.mul {α β : O} {x y : Matrix (Fin n) (Fin n) O} (hx : Shape α β x)
    (hy : Shape α β y) : Shape α β (x * y) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · exact ((hx i k).1 hk).mul_right _
    · exact ((hy k j).1 (hk.trans_lt h)).mul_left _
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · exact ((hx i k).2 hk).mul_right _
    · exact ((hy k j).2 (h.trans_le hk)).mul_left _

/- English proof (translation)
Set `f` to `Ideal.Quotient.mk (Ideal.span {γ})`. Establish `hf : ∀ x, f x = 0 ↔ γ ∣ x` using `fun x => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `h1 : ((g : Matrix (Fin n) (Fin n) O).map f) * (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map f) = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]`.

Use `letI := invertibleOfRightInverse _ _ h1`. Establish `h2 : ((g : Matrix (Fin n) (Fin n) O).map f).BlockTriangular b` using `fun i j h => (hf _).2 (hg i j h)`. Establish `h3` using `Matrix.blockTriangular_inv_of_blockTriangular h2`. Rewrite `h3` using `[Matrix.inv_eq_right_inv h1]`. Introduce `i j h`.

Conclude with `(hf _).1 (h3 h)`.
-/
theorem dvd_inv_of_blockTriangular {ι : Type} [LinearOrder ι] (b : Fin n → ι) (γ : O)
    (g : GL (Fin n) O) (hg : ∀ i j, b j < b i → γ ∣ (g : Matrix (Fin n) (Fin n) O) i j) :
    ∀ i j, b j < b i → γ ∣ ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i j := by
  let f := Ideal.Quotient.mk (Ideal.span {γ})
  have hf : ∀ x, f x = 0 ↔ γ ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have h1 : ((g : Matrix (Fin n) (Fin n) O).map f) *
      (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map f) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero f) (map_one f)]
  letI := invertibleOfRightInverse _ _ h1
  have h2 : ((g : Matrix (Fin n) (Fin n) O).map f).BlockTriangular b :=
    fun i j h => (hf _).2 (hg i j h)
  have h3 := Matrix.blockTriangular_inv_of_blockTriangular h2
  rw [Matrix.inv_eq_right_inv h1] at h3
  intro i j h
  exact (hf _).1 (h3 h)

/- English proof (translation)
Introduce `i j`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `dvd_inv_of_blockTriangular (ι := (Fin n)ᵒᵈ) OrderDual.toDual α g (fun i j h => (hg i j).1 h) i j h`. Conclude with `dvd_inv_of_blockTriangular id β g (fun i j h => (hg i j).2 h) i j h`.
-/
theorem Shape.inv {α β : O} {g : GL (Fin n) O} (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    Shape α β ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact dvd_inv_of_blockTriangular (ι := (Fin n)ᵒᵈ) OrderDual.toDual α g
      (fun i j h => (hg i j).1 h) i j h
  · exact dvd_inv_of_blockTriangular id β g (fun i j h => (hg i j).2 h) i j h

def shapeGroup (n : ℕ) (α β : O) : Subgroup (GL (Fin n) O) where
  carrier := {g | Shape α β (g : Matrix (Fin n) (Fin n) O)}
  one_mem' := Shape.one α β
  mul_mem' hx hy := Shape.mul hx hy
  inv_mem' hx := Shape.inv hx

/- English proof (translation)
Introduce `i j` and use `⟨(hu i j).2.2, fun h => by rw [(hu i j).1 h]; exact dvd_zero _⟩`.
-/
theorem UpperUnip.shape {α : O} (β : O) {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    Shape α β u := fun i j =>
  ⟨(hu i j).2.2, fun h => by rw [(hu i j).1 h]; exact dvd_zero _⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun h => by rw [(hl i j).1 h]; exact dvd_zero _, (hl i j).2.2⟩`.
-/
theorem LowerUnip.shape (α : O) {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    Shape α β l := fun i j =>
  ⟨fun h => by rw [(hl i j).1 h]; exact dvd_zero _, (hl i j).2.2⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun h => by rw [Matrix.diagonal_apply_ne _ h.ne]; exact dvd_zero _, fun h => by rw [Matrix.diagonal_apply_ne _ h.ne']; exact dvd_zero _⟩`.
-/
theorem Shape.diagonal (α β : O) (d : Fin n → O) : Shape α β (Matrix.diagonal d) := fun i j =>
  ⟨fun h => by rw [Matrix.diagonal_apply_ne _ h.ne]; exact dvd_zero _,
    fun h => by rw [Matrix.diagonal_apply_ne _ h.ne']; exact dvd_zero _⟩

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j h => (hu i j).1 h)]`. Conclude with `Finset.prod_eq_one fun i _ => (hu i i).2.1 rfl`.
-/
theorem UpperUnip.det {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hu i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2.1 rfl

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular l (fun i j h => (hl i j).1 h)]`. Conclude with `Finset.prod_eq_one fun i _ => (hl i i).2.1 rfl`.
-/
theorem LowerUnip.det {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => (hl i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hl i i).2.1 rfl

/- English proof (translation)
Establish `iu' : IsUnit u'.det` using `by rw [hu'.det]; exact isUnit_one`. Establish `il : IsUnit l.det` using `by rw [hl.det]; exact isUnit_one`. Use `letI := u'.invertibleOfIsUnitDet iu'`. Use `letI := l.invertibleOfIsUnitDet il`. Establish `tu : u.BlockTriangular id` using `fun i j h => (hu i j).1 h`.

Establish `tu' : u'.BlockTriangular id` using `fun i j h => (hu' i j).1 h`. Establish `tl : l.BlockTriangular OrderDual.toDual` using `fun i j h => (hl i j).1 h`. Establish `tl' : l'.BlockTriangular OrderDual.toDual` using `fun i j h => (hl' i j).1 h`. Use `set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX`. Establish `e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O))`.

Rewrite using `[hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']`. Establish `e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l'`. Rewrite using `[hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']`. Establish `e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹`. Rewrite using `[← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]`.

Establish `tX : X.BlockTriangular id` using `(Matrix.blockTriangular_inv_of_blockTriangular tu').mul (tu.mul (Matrix.blockTriangular_diagonal _))`. Establish `tX' : X.BlockTriangular OrderDual.toDual`. Rewrite using `[e3]`. Conclude with `((Matrix.blockTriangular_diagonal _).mul tl').mul (Matrix.blockTriangular_inv_of_blockTriangular tl)`. Establish `hd : X = Matrix.diagonal (fun i => X i i)`.

Use extensionality with `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[Matrix.diagonal_apply_ne _ h.ne]`. Conclude with `tX' h`. Rewrite using `[Matrix.diagonal_apply_eq]`.

Rewrite using `[Matrix.diagonal_apply_ne _ h.ne']`. Conclude with `tX h`. Rewrite `e1`, `e2` using `[hd]`. Establish `f1 : ∀ i j, u' i j * X j j = u i j * d j` using `fun i j => by`. Simplify `congrFun (congrFun e1 i) j` using `[Matrix.mul_diagonal]`.

Establish `f2 : ∀ i j, X i i * l i j = d' i * l' i j` using `fun i j => by`. Simplify `congrFun (congrFun e2 i) j` using `[Matrix.diagonal_mul]`. Establish `g1 : ∀ i, X i i = d i` using `fun i => by`. Simplify `f1 i i` using `[(hu i i).2.1 rfl, (hu' i i).2.1 rfl]`. Establish `g2 : ∀ i, X i i = d' i` using `fun i => by`.

Simplify `f2 i i` using `[(hl i i).2.1 rfl, (hl' i i).2.1 rfl]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `f1 i j` as an intermediate fact. Rewrite `this` using `[g1]`.

Conclude with `((Units.mul_left_inj _).1 this).symm`. Use function extensionality and compare the values at `i`. Conclude with `Units.ext ((g1 i).symm.trans (g2 i))`. Use extensionality with `i j`. Use `f2 i j` as an intermediate fact.

Rewrite `this` using `[g2]`. Conclude with `(Units.mul_right_inj _).1 this`.
-/
theorem factor_unique {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by
  have iu' : IsUnit u'.det := by rw [hu'.det]; exact isUnit_one
  have il : IsUnit l.det := by rw [hl.det]; exact isUnit_one
  letI := u'.invertibleOfIsUnitDet iu'
  letI := l.invertibleOfIsUnitDet il
  have tu : u.BlockTriangular id := fun i j h => (hu i j).1 h
  have tu' : u'.BlockTriangular id := fun i j h => (hu' i j).1 h
  have tl : l.BlockTriangular OrderDual.toDual := fun i j h => (hl i j).1 h
  have tl' : l'.BlockTriangular OrderDual.toDual := fun i j h => (hl' i j).1 h
  set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX
  have e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O)) := by
    rw [hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']
  have e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l' := by
    rw [hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']
  have e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹ := by
    rw [← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]
  have tX : X.BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular tu').mul
      (tu.mul (Matrix.blockTriangular_diagonal _))
  have tX' : X.BlockTriangular OrderDual.toDual := by
    rw [e3]
    exact ((Matrix.blockTriangular_diagonal _).mul tl').mul
      (Matrix.blockTriangular_inv_of_blockTriangular tl)
  have hd : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.diagonal_apply_ne _ h.ne]; exact tX' h
    · rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne']; exact tX h
  rw [hd] at e1 e2
  have f1 : ∀ i j, u' i j * X j j = u i j * d j := fun i j => by
    simpa [Matrix.mul_diagonal] using congrFun (congrFun e1 i) j
  have f2 : ∀ i j, X i i * l i j = d' i * l' i j := fun i j => by
    simpa [Matrix.diagonal_mul] using congrFun (congrFun e2 i) j
  have g1 : ∀ i, X i i = d i := fun i => by
    simpa [(hu i i).2.1 rfl, (hu' i i).2.1 rfl] using f1 i i
  have g2 : ∀ i, X i i = d' i := fun i => by
    simpa [(hl i i).2.1 rfl, (hl' i i).2.1 rfl] using f2 i i
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := f1 i j
    rw [g1] at this
    exact ((Units.mul_left_inj _).1 this).symm
  · funext i
    exact Units.ext ((g1 i).symm.trans (g2 i))
  · ext i j
    have := f2 i j
    rw [g2] at this
    exact (Units.mul_right_inj _).1 this

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UnipotentDecomposition.main`. Consider the case `exact _root_.GlobalTheory.UnipotentDecomposition.main`. Consider the case `(apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UnipotentDecomposition.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnipotentDecomposition.main ..)`.
-/
theorem exists_factor [IsLocalRing O] {α β : O} (hαβ : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), Shape α β g → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        UpperUnip α u ∧ LowerUnip β l ∧ g = u * Matrix.diagonal (fun i => (d i : O)) * l ∧
          ∀ i, α * β ∣ (d i : O) - g i i := by
  first
  | exact @_root_.GlobalTheory.UnipotentDecomposition.main
  | exact _root_.GlobalTheory.UnipotentDecomposition.main
  | (apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentDecomposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentDecomposition.main ..)

/- English proof (translation)
Set `f` to `IsLocalRing.residue O`. Establish `h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x` using `fun x => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `h1 : (g.map f).BlockTriangular id` using `fun i j h => (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)`. Establish `h2 : f g.det = ∏ k, f (g k k)`.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hi`. Establish `h3 : f g.det = 0`. Rewrite using `[h2]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)`. Conclude with `(h0 _).1 h3 hdet`.
-/
theorem isUnit_diag [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) {g : Matrix (Fin n) (Fin n) O}
    (hdet : IsUnit g.det) (hg : Shape α β g) (i : Fin n) : IsUnit (g i i) := by
  let f := IsLocalRing.residue O
  have h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h1 : (g.map f).BlockTriangular id := fun i j h =>
    (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)
  have h2 : f g.det = ∏ k, f (g k k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]
    rfl
  by_contra hi
  have h3 : f g.det = 0 := by
    rw [h2]; exact Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)
  exact (h0 _).1 h3 hdet

def flip (g : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) O :=
  g.submatrix Fin.revPerm Fin.revPerm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flip_apply (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[flip_apply]`.
-/
theorem flip_flip (g : Matrix (Fin n) (Fin n) O) : flip (flip g) = g := by
  ext i j; simp [flip_apply]

/- English proof (translation)
Unfold `flip`. Rewrite using `[← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression.
-/
theorem flip_triple (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
    Matrix.submatrix_diagonal_equiv]
  rfl

/- English proof (translation)
Introduce `i j` and use `⟨fun h => (hg _ _).2 (Fin.rev_lt_rev.2 h), fun h => (hg _ _).1 (Fin.rev_lt_rev.2 h)⟩`.
-/
theorem Shape.flip {α β : O} {g : Matrix (Fin n) (Fin n) O} (hg : Shape α β g) :
    Shape β α (flip g) := fun i j =>
  ⟨fun h => (hg _ _).2 (Fin.rev_lt_rev.2 h), fun h => (hg _ _).1 (Fin.rev_lt_rev.2 h)⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun h => (hu _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hu _ _).2.1 (congrArg Fin.rev h), fun h => (hu _ _).2.2 (Fin.rev_lt_rev.2 h)⟩`.
-/
theorem UpperUnip.flip {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    LowerUnip α (flip u) := fun i j =>
  ⟨fun h => (hu _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hu _ _).2.1 (congrArg Fin.rev h),
    fun h => (hu _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h), fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩`.
-/
theorem LowerUnip.flip {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    UpperUnip β (flip l) := fun i j =>
  ⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h),
    fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

/- English proof (translation)
Introduce `h` and use `hβ (isUnit_of_mul_isUnit_right h)`.
-/
theorem not_isUnit_mul {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) :=
  fun h => hβ (isUnit_of_mul_isUnit_right h)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation`. Consider the case `exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation`. Consider the case `(apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation ..)`.
-/
theorem existsUnique_factor [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      UpperUnip α p.1 ∧ LowerUnip β p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  first
  | exact @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | (apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation ..)

/- English proof (translation)
Take `⟨u, d, l, hu, hl, hfac, -⟩` from `exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)`. Establish `hfac2` using `congrArg flip hfac`. Rewrite `hfac2` using `[flip_flip, flip_triple]`. Use `⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩`.

Establish `hfac3` using `congrArg flip hfac'`. Rewrite `hfac3` using `[flip_triple]`. Take `⟨h1, h2, h3⟩` from `factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip (hfac.symm.trans hfac3)`. Substitute `h1 h2 h3` using the available equality. Simplify using `[flip_flip]`.
-/
theorem existsUnique_factor_opp [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      LowerUnip β p.1 ∧ UpperUnip α p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  obtain ⟨u, d, l, hu, hl, hfac, -⟩ :=
    exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip
      (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)
  have hfac2 := congrArg flip hfac
  rw [flip_flip, flip_triple] at hfac2
  refine ⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩
  rintro ⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩
  have hfac3 := congrArg flip hfac'
  rw [flip_triple] at hfac3
  obtain ⟨h1, h2, h3⟩ := factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip
    (hfac.symm.trans hfac3)
  subst h1 h2 h3
  simp [flip_flip]

end General

/- English proof (translation)
Introduce `h` and use `hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 h)`.
-/
theorem not_isUnit_pow {O : Type} [CommRing O] {ϖ : O} (hϖ : Irreducible ϖ) {s : ℕ} (hs : 1 ≤ s) :
    ¬ IsUnit (ϖ ^ s) := fun h =>
  hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 h)

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ n r s hs g hg`. Conclude with `existsUnique_factor (not_isUnit_pow hϖ hs) g hg`.
-/
theorem iwahori_factorisation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (n r s : ℕ), 1 ≤ s → ∀ g : GL (Fin n) O, (∀ i j, (i < j → ϖ ^ r ∣ (g : Matrix (Fin n) (Fin n) O) i j) ∧ (j < i → ϖ ^ s ∣ (g : Matrix (Fin n) (Fin n) O) i j)) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, (∀ i j, (j < i → p.1 i j = 0) ∧ (i = j → p.1 i j = 1) ∧ (i < j → ϖ ^ r ∣ p.1 i j)) ∧ (∀ i j, (i < j → p.2.2 i j = 0) ∧ (i = j → p.2.2 i j = 1) ∧ (j < i → ϖ ^ s ∣ p.2.2 i j)) ∧ (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  intro O _ _ _ ϖ hϖ n r s hs g hg
  exact existsUnique_factor (not_isUnit_pow hϖ hs) g hg

end GlobalTheory.IwahoriFactor
