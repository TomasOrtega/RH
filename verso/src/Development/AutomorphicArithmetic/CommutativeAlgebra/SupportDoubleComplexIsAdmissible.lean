import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

/- English proof (translation)
Unfold `Sx.face`. Rewrite using `[← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app, SimplicialObject.δ_comp_δ E h]`.
-/
private theorem sx_face_face {E : Spc} {p : ℕ} {U : Scheme} (y : Sx E (p+2) U) {a b : Fin (p+2)}
    (h : a ≤ b) : (y.face b.succ).face a = (y.face a.castSucc).face b := by
  unfold Sx.face
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app,
    SimplicialObject.δ_comp_δ E h]

/- English proof (translation)
Establish `ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b` using `fun h => sx_face_face y h`. Rewrite using `[← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]`. Set `g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2)` to `fun ji => if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega)) else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))`. Establish `gg : ∀ ji, g (g ji) = ji`. Introduce and unpack `⟨j, i⟩`.

Distinguish the cases in `h : (j : ℕ) ≤ i`. Establish `h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2))` using `by simp; omega`. Simplify using `only [g, dif_pos h, dif_neg h1]`. Apply the tactic sequence `ext <;> simp`. Establish `h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2))` using `by simp; omega`.

Simplify using `only [g, dif_neg h, dif_pos h1]`. Apply the tactic sequence `ext <;> simp`. Use `Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)` and prove the remaining obligations. Introduce and unpack `⟨j, i⟩ _`. Distinguish the cases in `h : (j : ℕ) ≤ i`.

Simplify using `only [g, dif_pos h]`. Establish `hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc` using `by ext; simp`. Establish `hle : j.castLT (by omega) ≤ i` using `by rw [Fin.le_def]; simpa using h`. Rewrite using `[ff hle, ← hj]`. Simplify using `only [Fin.val_succ, Fin.coe_castLT]`.

Rewrite using `[← add_smul]`. Use `zero_smul ℤ _` and compare the differences between its conclusion and the goal. Rewrite using `[show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring`. Simplify using `only [g, dif_neg h]`. Establish `hj0 : j ≠ 0` using `by intro h0; simp [h0] at h`.

Establish `hle : i ≤ j.pred hj0` using `by rw [Fin.le_def]; simp; omega`. Establish `key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0)`. Use `ff hle` as an intermediate fact. Rewrite `this` using `[Fin.succ_pred]`. Then use the resulting hypothesis. Rewrite using `[key]`.

Simplify using `only [Fin.coe_castSucc, Fin.coe_pred]`. Rewrite using `[← add_smul]`. Use `zero_smul ℤ _` and compare the differences between its conclusion and the goal. Establish `: (j : ℕ) = (j : ℕ) - 1 + 1` using `by omega`. Rewrite using `[this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring`.

Introduce and unpack `⟨j, i⟩ _ _ heq`. Distinguish the cases in `h : (j : ℕ) ≤ i`. Simplify using `only [g, dif_pos h, Prod.mk.injEq] at heq`. Use `congrArg Fin.val heq.1` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [g, dif_neg h, Prod.mk.injEq] at heq`. Use `congrArg Fin.val heq.1` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_neg_one_pow_face_face_eq_zero {A : Type*} [AddCommGroup A] {E : Spc} {p : ℕ} {U : Scheme}
    (f : Sx E p U → A) (y : Sx E (p+2) U) :
    ∑ j : Fin (p+3), ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i) = 0 := by
  have ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b :=
    fun h => sx_face_face y h
  rw [← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]
  let g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2) := fun ji =>
    if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega))
    else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))
  have gg : ∀ ji, g (g ji) = ji := by
    rintro ⟨j, i⟩
    by_cases h : (j : ℕ) ≤ i
    · have h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2)) := by simp; omega
      simp only [g, dif_pos h, dif_neg h1]
      ext <;> simp
    · have h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2)) := by simp; omega
      simp only [g, dif_neg h, dif_pos h1]
      ext <;> simp
  refine Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)
  · rintro ⟨j, i⟩ _
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h]
      have hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc := by ext; simp
      have hle : j.castLT (by omega) ≤ i := by rw [Fin.le_def]; simpa using h
      rw [ff hle, ← hj]
      simp only [Fin.val_succ, Fin.coe_castLT]
      rw [← add_smul]
      convert zero_smul ℤ _
      rw [show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring
    · simp only [g, dif_neg h]
      have hj0 : j ≠ 0 := by intro h0; simp [h0] at h
      have hle : i ≤ j.pred hj0 := by rw [Fin.le_def]; simp; omega
      have key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0) := by
        have := ff hle
        rwa [Fin.succ_pred] at this
      rw [key]
      simp only [Fin.coe_castSucc, Fin.coe_pred]
      rw [← add_smul]
      convert zero_smul ℤ _
      have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      rw [this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring
  · rintro ⟨j, i⟩ _ _ heq
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega
    · simp only [g, dif_neg h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega

/- English proof (translation)
Introduce `R _ E Z K m`. Unfold `famDC`. Prove the components needed by the constructor for the conclusion. Introduce `p s t u x`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `U y`. Express the relevant statement in the definitionally equal form `Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0`. Rewrite using `[HomologicalComplex.d_comp_d]`. Both sides reduce to the same expression. Introduce `p s x`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U y`. Simplify using `[Fam.δ]`. Establish `hz` using `sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y`. Establish `hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) • (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) = m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • (x : (V : Scheme) → Sx E p V → Sec (K.X (s …`.

Introduce `j`. Rewrite using `[smul_comm, Finset.smul_sum]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[smul_smul, pow_add]`. Repeatedly rewrite using `[hj, ← Finset.smul_sum]`. Rewrite using `[hz, smul_zero, smul_zero]`. Introduce `p s t x`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `U y`. Simplify using `[Fam.map, Fam.δ]`.
-/
theorem UpperTheory.supportDoubleComplex_isAdmissible :
    ∀ (R : Type) [CommRing R] (E : Spc) (Z : Sub E) (K : Cx R) (m : ℤ), (famDC Z K m).Ok := by
  intro R _ E Z K m
  unfold famDC
  constructor
  · intro p s t u x
    apply Subtype.ext
    funext U y
    change Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0
    rw [HomologicalComplex.d_comp_d]
    rfl
  · intro p s x
    apply Subtype.ext
    funext U y
    simp [Fam.δ]
    have hz := sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y
    have hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) =
        m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) := by
      intro j
      rw [smul_comm, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, pow_add]
    simp_rw [hj, ← Finset.smul_sum]
    rw [hz, smul_zero, smul_zero]
  · intro p s t x
    apply Subtype.ext
    funext U y
    simp [Fam.map, Fam.δ]
