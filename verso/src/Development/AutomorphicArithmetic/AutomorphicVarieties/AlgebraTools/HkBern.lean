import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Set `φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R` to `aeval fun j => if j = a then X a + X c else X j`. Set `ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R` to `aeval fun j => if j = a then X a - X c else X j`. Establish `hψ : ψ.comp φ = AlgHom.id R _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`.

Distinguish the cases in `hj : j = a`. Simplify using `[φ, ψ, hj, hac.symm]`. Simplify using `[φ, ψ, hj]`. Establish `h1 : φ (X a - X c) = X a` using `by simp [φ, hac.symm]`. Establish `h2 : X a * φ y = X a * 0` using `by rw [mul_zero, ← h1, ← map_mul, h, map_zero]`.

Establish `h3 : φ y = 0` using `(MvPolynomial.isRegular_X (R := R) (n := a)).left h2`. Establish `h4` using `AlgHom.congr_fun hψ y`. Rewrite `h4` using `[AlgHom.comp_apply, h3, map_zero, AlgHom.id_apply]`. Conclude with `h4.symm`.
-/
private theorem UpperTheory.V.AlgebraTools.hkBern_reg {R : Type} [CommRing R] {n : ℕ} {a c : Fin n} (hac : a ≠ c)
    (y : MvPolynomial (Fin n) R) (h : (X a - X c) * y = 0) : y = 0 := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a + X c else X j
  let ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a - X c else X j
  have hψ : ψ.comp φ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = a
    · simp [φ, ψ, hj, hac.symm]
    · simp [φ, ψ, hj]
  have h1 : φ (X a - X c) = X a := by simp [φ, hac.symm]
  have h2 : X a * φ y = X a * 0 := by rw [mul_zero, ← h1, ← map_mul, h, map_zero]
  have h3 : φ y = 0 := (MvPolynomial.isRegular_X (R := R) (n := a)).left h2
  have h4 := AlgHom.congr_fun hψ y
  rw [AlgHom.comp_apply, h3, map_zero, AlgHom.id_apply] at h4
  exact h4.symm

/- English proof (translation)
Introduce `R _ n q H _ _ b`. Establish `main : ∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = x - rename (swap a c) x ∧ b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y)`. Introduce `a c hac`. Establish `hX : ∀ j : Fin n, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = X j - rename (swap a c) (X j) ∧ b.T (swap a c) * b.th (X j) = b.th (rename (swap a c) (X j)) * b.T (swap a c) + (q - 1) • b.th (X a * y)`. Introduce `j`.

Distinguish the cases in `ha : j = a`. Substitute `ha` using the available equality. Use `⟨1, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_X, swap_apply_left, mul_one]`. Conclude with `b.relA j c hac`.

Distinguish the cases in `hc : j = c`. Substitute `hc` using the available equality. Use `⟨-1, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_X, swap_apply_right, mul_neg, mul_one, map_neg, smul_neg, ← sub_eq_add_neg]`. Conclude with `b.relB a j hac`.

Use `⟨0, by simp [swap_apply_of_ne_of_ne ha hc], ?_⟩` and prove the remaining obligations. Rewrite using `[rename_X, swap_apply_of_ne_of_ne ha hc, mul_zero, map_zero, smul_zero, add_zero]`. Conclude with `b.comm a c hac j ha hc`. Introduce `x`. Proceed by induction on `x using MvPolynomial.induction_on with`.

Consider the case `C r`. Use `⟨0, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_C, mul_zero, map_zero, smul_zero, add_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.commutes]`. Consider the case `add p p' hp hp'`. Take `⟨y, h1, h2⟩` from `hp`.

Take `⟨y', h1', h2'⟩` from `hp'`. Use `⟨y + y', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, h1, h1', map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, map_add, map_add, mul_add, h2, h2', mul_add, map_add, add_mul, smul_add]`.

Normalize the expressions using the abelian group laws. Consider the case `mul_X p j hp`. Take `⟨y, h1, h2⟩` from `hp`. Take `⟨y', h1', h2'⟩` from `hX j`. Use `⟨y * X j + rename (swap a c) p * y', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Take the linear combination `(X j) * h1 + rename (swap a c) p * h1'`. Establish `e : X a * (y * X j + rename (swap a c) p * y') = (X a * y) * X j + rename (swap a c) p * (X a * y')` using `by ring`. Rewrite using `[e, map_add, map_mul b.th (X a * y), map_mul b.th _ (X a * y'), map_mul (rename _), map_mul b.th p, map_mul b.th (rename _ p), ← mul_assoc, h2, add_mul, mul_assoc, h2', mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Normalize the expressions using the abelian group laws.

Use `⟨main, fun z hz => ?_⟩` and prove the remaining obligations. Use `UpperTheory.V.AlgebraTools.hkInd n (fun w => b.T w * b.th z = b.th z * b.T w) ?_ ?_` and prove the remaining obligations. Simplify using `only [b.T_one, one_mul, mul_one]`. Introduce `a c hac w hw ih`. Take `⟨y, h1, h2⟩` from `main a c hac z`.

Establish `hne : a ≠ c`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Rewrite `h1`, `h2` using `[hz (swap a c)]`. Rewrite `h1` using `[sub_self]`.

Rewrite `h2` using `[UpperTheory.V.AlgebraTools.hkBern_reg hne y h1, mul_zero, map_zero, smul_zero, add_zero]`. Rewrite using `[b.T_mul a c hac w hw, mul_assoc, ih, ← mul_assoc, h2, mul_assoc]`.
-/
theorem UpperTheory.V.AlgebraTools.hkBern :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y)) ∧
      ∀ z : MvPolynomial (Fin n) R, z.IsSymmetric → ∀ w, b.T w * b.th z = b.th z * b.T w := by
  intro R _ n q H _ _ b
  have main : ∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
    intro a c hac
    have hX : ∀ j : Fin n, ∃ y : MvPolynomial (Fin n) R,
        (X a - X c) * y = X j - rename (swap a c) (X j) ∧
        b.T (swap a c) * b.th (X j) = b.th (rename (swap a c) (X j)) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
      intro j
      by_cases ha : j = a
      · subst ha
        refine ⟨1, by simp, ?_⟩
        rw [rename_X, swap_apply_left, mul_one]
        exact b.relA j c hac
      · by_cases hc : j = c
        · subst hc
          refine ⟨-1, by simp, ?_⟩
          rw [rename_X, swap_apply_right, mul_neg, mul_one, map_neg, smul_neg, ← sub_eq_add_neg]
          exact b.relB a j hac
        · refine ⟨0, by simp [swap_apply_of_ne_of_ne ha hc], ?_⟩
          rw [rename_X, swap_apply_of_ne_of_ne ha hc, mul_zero, map_zero, smul_zero, add_zero]
          exact b.comm a c hac j ha hc
    intro x
    induction x using MvPolynomial.induction_on with
    | C r =>
      refine ⟨0, by simp, ?_⟩
      rw [rename_C, mul_zero, map_zero, smul_zero, add_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        Algebra.commutes]
    | add p p' hp hp' =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hp'
      refine ⟨y + y', ?_, ?_⟩
      · rw [mul_add, h1, h1', map_add]; ring
      · rw [map_add, map_add, map_add, mul_add, h2, h2', mul_add, map_add, add_mul, smul_add]; abel
    | mul_X p j hp =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hX j
      refine ⟨y * X j + rename (swap a c) p * y', ?_, ?_⟩
      · rw [map_mul]
        linear_combination (X j) * h1 + rename (swap a c) p * h1'
      · have e : X a * (y * X j + rename (swap a c) p * y') =
            (X a * y) * X j + rename (swap a c) p * (X a * y') := by ring
        rw [e, map_add, map_mul b.th (X a * y), map_mul b.th _ (X a * y'), map_mul (rename _), map_mul b.th p,
          map_mul b.th (rename _ p), ← mul_assoc, h2, add_mul, mul_assoc, h2', mul_add, smul_add, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel
  refine ⟨main, fun z hz => ?_⟩
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => b.T w * b.th z = b.th z * b.T w) ?_ ?_
  · simp only [b.T_one, one_mul, mul_one]
  · intro a c hac w hw ih
    obtain ⟨y, h1, h2⟩ := main a c hac z
    have hne : a ≠ c := by
      rintro rfl
      omega
    rw [hz (swap a c)] at h1 h2
    rw [sub_self] at h1
    rw [UpperTheory.V.AlgebraTools.hkBern_reg hne y h1, mul_zero, map_zero, smul_zero, add_zero] at h2
    rw [b.T_mul a c hac w hw, mul_assoc, ih, ← mul_assoc, h2, mul_assoc]
