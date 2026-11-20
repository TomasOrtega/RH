import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

/- English proof (translation)
Introduce `q R _ f g h`. Establish `hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C`. Apply `IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))` to reduce the goal to its premises. Conclude with `RingHom.ext_int _ _`. Establish `hCa : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a)` using `fun a => RingHom.congr_fun hC a`.

Establish `hmul : ∀ m n : ℤ, (LaurentPolynomial.T m : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q) * LaurentPolynomial.T n = LaurentPolynomial.T (m + n)` using `fun m n => (LaurentPolynomial.T_add m n).symm`. Establish `h1 : f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1)) = 1`. Rewrite using `[← map_mul, hmul]`. Simplify using the standard rewrite rules. Establish `h2 : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1`.

Rewrite using `[← map_mul, hmul]`. Simplify using the standard rewrite rules. Establish `hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, mul_one]`.

Use `_ = (f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1))) * g (LaurentPolynomial.T (-1)) := by`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = g (LaurentPolynomial.T (-1)) := by rw [h1, one_mul]`. Establish `hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n)`.

Introduce `n`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [← hmul, map_mul, map_mul, ih, h]`. Consider the case `pred i ih => rw [sub_eq_add_neg, ← hmul, map_mul, map_mul, ih, hinv]`.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `p`. Proceed by induction on `p using LaurentPolynomial.induction_on' with`. Consider the case `add p r hp hr => rw [map_add, map_add, hp, hr]`. Consider the case `C_mul_T n a`.

Rewrite using `[map_mul, map_mul, hCa, hT]`.
-/
theorem UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext :
    ∀ (q : ℕ) {R : Type} [inst : CommRing R] {f g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q →+* R},
      (f : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) =
          (g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) →
        f = g := by
  intro q R _ f g h
  have hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))
    exact RingHom.ext_int _ _
  have hCa : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a) :=
    fun a => RingHom.congr_fun hC a
  have hmul : ∀ m n : ℤ, (LaurentPolynomial.T m : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q) * LaurentPolynomial.T n
      = LaurentPolynomial.T (m + n) := fun m n => (LaurentPolynomial.T_add m n).symm
  have h1 : f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have h2 : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    calc f (LaurentPolynomial.T (-1))
        = f (LaurentPolynomial.T (-1)) * (g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1))) := by
          rw [h2, mul_one]
      _ = (f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1))) * g (LaurentPolynomial.T (-1)) := by
          rw [← h]; ring
      _ = g (LaurentPolynomial.T (-1)) := by rw [h1, one_mul]
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [← hmul, map_mul, map_mul, ih, h]
    | pred i ih => rw [sub_eq_add_neg, ← hmul, map_mul, map_mul, ih, hinv]
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | C_mul_T n a =>
    rw [map_mul, map_mul, hCa, hT]
