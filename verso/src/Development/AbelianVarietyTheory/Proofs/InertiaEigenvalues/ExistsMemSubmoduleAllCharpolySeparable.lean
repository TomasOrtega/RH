import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Polynomial

namespace GlobalTheory.SepGeneric

/- English proof (translation)
Establish `hle : (derivative f).natDegree ≤ t` using `(natDegree_derivative_le f).trans (by omega)`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Establish `h1 : resultant f (derivative f) t t = resultant f (derivative f) f.natDegree (derivative f).natDegree`. Use `resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl` as an intermediate fact. Rewrite `this` using `[← hk]`.

Rewrite using `[this, ← ht, hf.coeff_natDegree]`. Simplify using the standard rewrite rules. Rewrite using `[h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]`. Both sides reduce to the same expression.
-/
theorem separable_iff_resultant {K : Type} [Field K] {f : K[X]} (hf : f.Monic) {t : ℕ}
    (ht : f.natDegree = t) : f.Separable ↔ resultant f (derivative f) t t ≠ 0 := by
  have hle : (derivative f).natDegree ≤ t :=
    (natDegree_derivative_le f).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have h1 : resultant f (derivative f) t t
      = resultant f (derivative f) f.natDegree (derivative f).natDegree := by
    have := resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl
    rw [← hk] at this
    rw [this, ← ht, hf.coeff_natDegree]
    simp
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

/- English proof (translation)
Set `N : Matrix (Fin t) (Fin t) K[X]` to `B.map C + (X : K[X]) • A.map C`. Set `D : K[X]` to `resultant N.charpoly (derivative N.charpoly) t t`. Establish `hN : ∀ l : K, N.map (evalRingHom l) = B + l • A`. Introduce `l`. Use extensionality with `i j`.

Simplify using `[N]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0`. Introduce `l`. Rewrite using `[separable_iff_resultant (Matrix.charpoly_monic _) (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]`.

Both sides reduce to the same expression. Establish `hD0 : D ≠ 0`. Introduce `h`. Use `(hD 0).1 (by simpa using hB)` as an intermediate fact. Simplify using `[h] at this`.

Use `(D.roots.toFinset.finite_toSet).subset ?_` and prove the remaining obligations. Introduce `l hl`. Simplify using `only [Set.mem_setOf_eq, hD, not_not] at hl`. Simplify using `[hD0, hl]`.
-/
theorem finite_bad_base {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K)
    (hB : B.charpoly.Separable) : {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  classical
  let N : Matrix (Fin t) (Fin t) K[X] := B.map C + (X : K[X]) • A.map C
  let D : K[X] := resultant N.charpoly (derivative N.charpoly) t t
  have hN : ∀ l : K, N.map (evalRingHom l) = B + l • A := by
    intro l
    ext i j
    simp [N]
    ring
  have hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0 := by
    intro l
    rw [separable_iff_resultant (Matrix.charpoly_monic _)
      (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]
    rfl
  have hD0 : D ≠ 0 := by
    intro h
    have := (hD 0).1 (by simpa using hB)
    simp [h] at this
  refine (D.roots.toFinset.finite_toSet).subset ?_
  intro l hl
  simp only [Set.mem_setOf_eq, hD, not_not] at hl
  simp [hD0, hl]

/- English proof (translation)
Establish `h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X)`. Establish `: (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X)))` using `by ext1 i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Establish `h3 : (C c : K[X]) * (C c⁻¹ * X) = X`.

Rewrite using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]`. Simplify using `[mul_sub, h3]`. Simplify using `[Matrix.charmatrix_apply_ne _ _ _ h]`. Rewrite using `[Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]`. Use `congr 1`.

Conclude with `((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm`. Establish `h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable`. Rewrite using `[separable_def, derivative_comp]`. Establish `hu : IsUnit (derivative (C c⁻¹ * X : K[X]))`. Simplify using `using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))`.

Rewrite using `[isCoprime_mul_unit_left_right hu]`. Conclude with `((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))`. Rewrite using `[h1, mul_comm]`. Conclude with `h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)`.
-/
theorem separable_smul {K : Type} [Field K] {t : ℕ} (A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : A.charpoly.Separable) : (c • A).charpoly.Separable := by
  classical
  have h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X) := by
    have : (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X))) := by
      ext1 i j
      by_cases h : i = j
      · subst h
        have h3 : (C c : K[X]) * (C c⁻¹ * X) = X := by
          rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
        simp [mul_sub, h3]
      · simp [Matrix.charmatrix_apply_ne _ _ _ h]
    rw [Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]
    congr 1
    exact ((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm
  have h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable := by
    rw [separable_def, derivative_comp]
    have hu : IsUnit (derivative (C c⁻¹ * X : K[X])) := by
      simpa using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))
    rw [isCoprime_mul_unit_left_right hu]
    exact ((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))
  rw [h1, mul_comm]
  exact h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)

/- English proof (translation)
Establish `hA' : A.charpoly.Separable`. Use `separable_smul _ (inv_ne_zero hc) hA` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Establish `hf` using `(finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn`. Use `(hf.insert 0).subset ?_` and prove the remaining obligations.

Introduce `l hl`. Distinguish the cases in `h0 : l = 0`. Conclude with `Or.inl h0`. Use `Or.inr ?_` and prove the remaining obligations. Introduce `h`.

Apply `hl` to reduce the goal to its premises. Use `separable_smul _ h0 h` as an intermediate fact. Rewrite `this` using `[smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm]`. Then use the resulting hypothesis.
-/
theorem finite_bad_dir {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : (c • A).charpoly.Separable) :
    {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  have hA' : A.charpoly.Separable := by
    have := separable_smul _ (inv_ne_zero hc) hA
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hf := (finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn
  refine (hf.insert 0).subset ?_
  intro l hl
  by_cases h0 : l = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro h
    apply hl
    have := separable_smul _ h0 h
    rwa [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm] at this

/- English proof (translation)
Establish `key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable`. Introduce `Y`. Proceed by induction on `Y using Finset.induction_on with`. Consider the case `empty => exact ⟨0, M.zero_mem, by simp⟩`. Consider the case `insert x Y hx ih`.

Take `⟨s, hs, hY⟩` from `ih`. Establish `h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite`. Break down `h x with h | ⟨s', hs', c, hc, h⟩` into its components or cases. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `hf` using `(finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l) (add_right_injective 1).injOn`.

Use `hf.subset ?_` and prove the remaining obligations. Introduce `l hl`. Simplify `hl` using `[add_smul, add_assoc]`. Conclude with `⟨s', hs', finite_bad_dir _ _ hc h⟩`. Take `⟨s', hs', h1⟩` from `h1`.

Establish `h2 : (⋃ y ∈ insert x Y, {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite`. Use `(insert x Y).finite_toSet.biUnion ?_` and prove the remaining obligations. Introduce `y hy`. Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Conclude with `h1`.

Conclude with `finite_bad_base _ _ (hY y hy)`. Establish `h3` using `h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn`. Take `⟨l, hl⟩` from `h3.exists_notMem`. Use `⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Simplify using `only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl`. Use `hl y hy` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, add_assoc]`. Then use the resulting hypothesis. Use `Fintype.ofFinite X` as an intermediate fact. Take `⟨s, hs, h⟩` from `key Finset.univ`.

Conclude with `⟨s, hs, fun x => h x (Finset.mem_univ x)⟩`.
-/
theorem exists_separable {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ)
    (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K)
    (h : ∀ x, (a x).charpoly.Separable ∨
      ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) :
    ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  classical
  have key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, M.zero_mem, by simp⟩
    | insert x Y hx ih =>
      obtain ⟨s, hs, hY⟩ := ih
      have h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite := by
        rcases h x with h | ⟨s', hs', c, hc, h⟩
        · refine ⟨s, hs, ?_⟩
          have hf := (finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l)
            (add_right_injective 1).injOn
          refine hf.subset ?_
          intro l hl
          simpa [add_smul, add_assoc] using hl
        · exact ⟨s', hs', finite_bad_dir _ _ hc h⟩
      obtain ⟨s', hs', h1⟩ := h1
      have h2 : (⋃ y ∈ insert x Y,
          {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite := by
        refine (insert x Y).finite_toSet.biUnion ?_
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h1
        · exact finite_bad_base _ _ (hY y hy)
      have h3 := h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn
      obtain ⟨l, hl⟩ := h3.exists_notMem
      refine ⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩
      intro y hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hl y hy
      rwa [algebraMap_smul, add_assoc] at this
  have := Fintype.ofFinite X
  obtain ⟨s, hs, h⟩ := key Finset.univ
  exact ⟨s, hs, fun x => h x (Finset.mem_univ x)⟩

end GlobalTheory.SepGeneric
