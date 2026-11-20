import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Introduce `R _ n q H _ _ b`. Set `S : Submodule R H` to `{ carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u} add_mem' := by`. Introduce and unpack `_ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩`. Conclude with `⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `r _ ⟨c₁, rfl⟩`. Conclude with `⟨r • c₁, by simp [Finset.smul_sum]⟩ }`. Establish `hone : ∀ x u, b.th x * b.T u ∈ S`. Introduce `x u`.

Use `⟨Pi.single u x, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single u]`. Simplify using the standard rewrite rules. Introduce `v _ hv`. Simplify using `[Pi.single_eq_of_ne hv]`.

Simplify using the standard rewrite rules. Establish `hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S`. Introduce `a c hac x u`. Distinguish the cases in `hlt : u⁻¹ a < u⁻¹ c`. Rewrite using `[← b.T_mul a c hac u hlt]`.

Conclude with `hone _ _`. Establish `hne : u⁻¹ c ≠ u⁻¹ a`. Introduce `e`. Use `(u⁻¹).injective e` as an intermediate fact. Rewrite `hac` using `[this]`.

Use linear arithmetic over natural numbers and integers. Establish `hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c`. Rewrite using `[mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]`. Conclude with `lt_of_le_of_ne (not_lt.mp hlt) hne`. Establish `e` using `b.T_mul a c hac _ hw'`.

Rewrite `e` using `[swap_mul_self_mul]`. Establish `e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← e]`. Use `_ = (q - 1) • b.T u + q • b.T (swap a c * u) := by`.

Rewrite using `[b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]`. Rewrite using `[e2, mul_add, mul_smul_comm, mul_smul_comm]`. Conclude with `S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))`. Establish `hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S`. Introduce and unpack `a c hac _ ⟨c₁, rfl⟩`.

Rewrite using `[Finset.mul_sum]`. Use `S.sum_mem fun u _ => ?_` and prove the remaining obligations. Take `⟨y, -, hy⟩` from `(UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)`. Rewrite using `[← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]`. Conclude with `S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))`.

Establish `key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S`. Use `UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_` and prove the remaining obligations. Introduce `h hh`. Rewrite using `[b.T_one, one_mul]` and apply the resulting hypothesis. Introduce `a c hac w hw ih h hh`.

Rewrite using `[b.T_mul a c hac w hw, mul_assoc]`. Conclude with `hs a c hac _ (ih h hh)`. Introduce `w c`. Conclude with `key w _ ⟨c, rfl⟩`.
-/
theorem UpperTheory.V.AlgebraTools.hkSpan :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (w : Perm (Fin n)) (c : Perm (Fin n) → MvPolynomial (Fin n) R),
      ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, b.T w * ∑ u, b.th (c u) * b.T u = ∑ u, b.th (c' u) * b.T u := by
  intro R _ n q H _ _ b
  classical
  let S : Submodule R H :=
    { carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u}
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c₁, rfl⟩
        exact ⟨r • c₁, by simp [Finset.smul_sum]⟩ }
  have hone : ∀ x u, b.th x * b.T u ∈ S := by
    intro x u
    refine ⟨Pi.single u x, ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S := by
    intro a c hac x u
    by_cases hlt : u⁻¹ a < u⁻¹ c
    · rw [← b.T_mul a c hac u hlt]
      exact hone _ _
    · have hne : u⁻¹ c ≠ u⁻¹ a := by
        intro e
        have := (u⁻¹).injective e
        rw [this] at hac
        omega
      have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have e := b.T_mul a c hac _ hw'
      rw [swap_mul_self_mul] at e
      have e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u) := by
        calc b.T (swap a c) * b.T u = (b.T (swap a c) * b.T (swap a c)) * b.T (swap a c * u) := by
              rw [mul_assoc, ← e]
          _ = (q - 1) • b.T u + q • b.T (swap a c * u) := by
              rw [b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]
      rw [e2, mul_add, mul_smul_comm, mul_smul_comm]
      exact S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S := by
    rintro a c hac _ ⟨c₁, rfl⟩
    rw [Finset.mul_sum]
    refine S.sum_mem fun u _ => ?_
    obtain ⟨y, -, hy⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)
    rw [← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]
    exact S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))
  have key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · intro h hh
      rwa [b.T_one, one_mul]
    · intro a c hac w hw ih h hh
      rw [b.T_mul a c hac w hw, mul_assoc]
      exact hs a c hac _ (ih h hh)
  intro w c
  exact key w _ ⟨c, rfl⟩
