import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, hj, rfl⟩` from `hy`.

Use `⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩` and prove the remaining obligations. Establish `: j' ≠ j` using `by rintro rfl; omega`. Simplify using `[this]`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨c, hc, rfl⟩` from `hy`. Take `⟨d, hd, rfl⟩` from `hz`. Conclude with `⟨c + d, fun j hj => by simp [hc j hj, hd j hj], by rw [Matrix.mulVec_add]⟩`.

Consider the case `smul a y _ hy`. Take `⟨c, hc, rfl⟩` from `hy`. Conclude with `⟨a • c, fun j hj => by simp [hc j hj], by rw [Matrix.mulVec_smul]⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Establish `: M *ᵥ c = ∑ j, c j • (fun i => M i j)`.

Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) < k`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Rewrite using `[hc j (not_lt.mp hj), zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_span_first_columns_iff {R : Type} [CommRing R] {n r : ℕ}
    (M : Matrix (Fin n) (Fin r) R) (k : ℕ) (x : Fin n → R) :
    x ∈ Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => M i j} ↔
      ∃ c : Fin r → R, (∀ j : Fin r, k ≤ (j : ℕ) → c j = 0) ∧ x = M *ᵥ c := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
      · have : j' ≠ j := by rintro rfl; omega
        simp [this]
      · ext i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      exact ⟨c + d, fun j hj => by simp [hc j hj, hd j hj], by rw [Matrix.mulVec_add]⟩
    | smul a y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨a • c, fun j hj => by simp [hc j hj], by rw [Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    have : M *ᵥ c = ∑ j, c j • (fun i => M i j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hc j (not_lt.mp hj), zero_smul]
      exact Submodule.zero_mem _

/- English proof (translation)
Establish `key : ∀ j : Fin r, ∃ c : Fin r → R, (∀ j' : Fin r, (j : ℕ) + 1 ≤ (j' : ℕ) → c j' = 0) ∧ (fun i => u' i j) = u *ᵥ c` using `fun j => (mem_span_first_columns_iff u _ _).mp (h (j + 1) (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩))`. Use `choose c hc hc' using key`. Use `⟨Matrix.of fun i j => c j i, fun i j hij => hc j i hij, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (hc' j) i` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem exists_triangular_of_span_first_columns_le {R : Type} [CommRing R] {n r : ℕ}
    (u u' : Matrix (Fin n) (Fin r) R)
    (h : ∀ k : ℕ,
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} ≤
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) :
    ∃ b : Matrix (Fin r) (Fin r) R, b.BlockTriangular id ∧ u' = u * b := by
  have key : ∀ j : Fin r, ∃ c : Fin r → R, (∀ j' : Fin r, (j : ℕ) + 1 ≤ (j' : ℕ) → c j' = 0) ∧
      (fun i => u' i j) = u *ᵥ c := fun j =>
    (mem_span_first_columns_iff u _ _).mp
      (h (j + 1) (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩))
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, fun i j hij => hc j i hij, ?_⟩
  ext i j
  have := congrFun (hc' j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/- English proof (translation)
Introduce `V L _ _ _ _ _ n r ι u ⟨h0, h1⟩`. Use `set A : Matrix (Fin r) (Fin r) V := u.submatrix ι id with hA`. Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular A (fun i j hij => h0 i j hij)]`. Simplify using `[hA, h1]`.

Establish `hAu : IsUnit A.det` using `hdet ▸ isUnit_one`. Establish `hinj : Function.Injective (algebraMap V L)` using `IsFractionRing.injective V L`. Establish `hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin r) V) (c : Fin r → V) (i : Fin m), algebraMap V L ((M *ᵥ c) i) = ((M.map (algebraMap V L)) *ᵥ (fun j => algebraMap V L (c j))) i`. Introduce `m M c i`. Simplify using `[Matrix.mulVec, dotProduct]`.

Use `⟨fun k x => ?_, fun u' hu' => ?_⟩` and prove the remaining obligations. Establish `e` using `mem_span_first_columns_iff (u.map (algebraMap V L)) k (fun i => algebraMap V L (x i))`. Simplify using `only [Matrix.map_apply] at e`. Rewrite using `[e, mem_span_first_columns_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, hx⟩ set c₀ : Fin r → V := A⁻¹ *ᵥ (fun i => x (ι i)) with hc₀`. Establish `hAc : A *ᵥ c₀ = fun i => x (ι i)`. Rewrite using `[hc₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]`. Establish `hAL : IsUnit (A.map (algebraMap V L))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`.

Use `(algebraMap V L).map_det A` as an intermediate fact. Rewrite `this` using `[hdet, map_one]`. Conclude with `(show (1 : L) = (A.map (algebraMap V L)).det from this) ▸ isUnit_one`. Establish `hcc : (fun j => algebraMap V L (c₀ j)) = c`. Apply `Matrix.mulVec_injective_iff_isUnit.mpr hAL` to reduce the goal to its premises.

Use extensionality with `i`. Rewrite using `[← hmap, hAc]`. Conclude with `congrFun hx (ι i)`. Use `⟨c₀, fun j hj => hinj ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← hc j hj, ← hcc]`.

Use extensionality with `i`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hmap, hcc]`. Conclude with `congrFun hx i`. Introduce and unpack `⟨c, hc, rfl⟩`.

Use `⟨fun j => algebraMap V L (c j), fun j hj => by simp [hc j hj], ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Conclude with `hmap u c i`. Take `⟨b, hb, hub⟩` from `exists_triangular_of_span_first_columns_le u u' fun k => (hu' k).le`. Take `⟨b', hb', hub'⟩` from `exists_triangular_of_span_first_columns_le u' u fun k => (hu' k).ge`.

Establish `h2 : u = u * (b * b')` using `by rw [← Matrix.mul_assoc, ← hub, ← hub']`. Establish `h3 : A = A * (b * b')`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h2 (ι i)) j`. Establish `h4 : b * b' = 1`.

Use `congrArg (fun M => A⁻¹ * M) h3` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul] at this`. Conclude with `this.symm`. Use `⟨b, hb, fun i => ?_, hub⟩` and prove the remaining obligations. Establish `h5 : (b * b') i i = b i i * b' i i`.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hb h, zero_mul]`. Rewrite using `[hb' h, mul_zero]`.

Rewrite `h5` using `[h4, Matrix.one_apply_eq]`. Conclude with `IsUnit.of_mul_eq_one _ h5.symm`.
-/
theorem cell_columns_saturated_and_triangular :
    ∀ (V L : Type) [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] (n r : ℕ) (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ (k : ℕ) (x : Fin n → V), (fun i => algebraMap V L (x i)) ∈ Submodule.span L {y : Fin n → L | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => algebraMap V L (u i j)} ↔ x ∈ Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) ∧ ∀ u' : Matrix (Fin n) (Fin r) V, (∀ k : ℕ, Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} = Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) → ∃ b : Matrix (Fin r) (Fin r) V, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ u' = u * b := by
  intro V L _ _ _ _ _ n r ι u ⟨h0, h1⟩
  set A : Matrix (Fin r) (Fin r) V := u.submatrix ι id with hA
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A (fun i j hij => h0 i j hij)]
    simp [hA, h1]
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin r) V) (c : Fin r → V) (i : Fin m),
      algebraMap V L ((M *ᵥ c) i) =
        ((M.map (algebraMap V L)) *ᵥ (fun j => algebraMap V L (c j))) i := by
    intro m M c i
    simp [Matrix.mulVec, dotProduct]
  refine ⟨fun k x => ?_, fun u' hu' => ?_⟩
  · have e := mem_span_first_columns_iff (u.map (algebraMap V L)) k
      (fun i => algebraMap V L (x i))
    simp only [Matrix.map_apply] at e
    rw [e, mem_span_first_columns_iff]
    constructor
    · rintro ⟨c, hc, hx⟩
      set c₀ : Fin r → V := A⁻¹ *ᵥ (fun i => x (ι i)) with hc₀
      have hAc : A *ᵥ c₀ = fun i => x (ι i) := by
        rw [hc₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
      have hAL : IsUnit (A.map (algebraMap V L)) := by
        rw [Matrix.isUnit_iff_isUnit_det]
        have := (algebraMap V L).map_det A
        rw [hdet, map_one] at this
        exact (show (1 : L) = (A.map (algebraMap V L)).det from this) ▸ isUnit_one
      have hcc : (fun j => algebraMap V L (c₀ j)) = c := by
        apply Matrix.mulVec_injective_iff_isUnit.mpr hAL
        ext i
        rw [← hmap, hAc]
        exact congrFun hx (ι i)
      refine ⟨c₀, fun j hj => hinj ?_, ?_⟩
      · rw [map_zero, ← hc j hj, ← hcc]
      · ext i
        apply hinj
        rw [hmap, hcc]
        exact congrFun hx i
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun j => algebraMap V L (c j), fun j hj => by simp [hc j hj], ?_⟩
      ext i
      exact hmap u c i
  · obtain ⟨b, hb, hub⟩ := exists_triangular_of_span_first_columns_le u u' fun k => (hu' k).le
    obtain ⟨b', hb', hub'⟩ := exists_triangular_of_span_first_columns_le u' u fun k => (hu' k).ge
    have h2 : u = u * (b * b') := by rw [← Matrix.mul_assoc, ← hub, ← hub']
    have h3 : A = A * (b * b') := by
      ext i j
      exact congrFun (congrFun h2 (ι i)) j
    have h4 : b * b' = 1 := by
      have := congrArg (fun M => A⁻¹ * M) h3
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul] at this
      exact this.symm
    refine ⟨b, hb, fun i => ?_, hub⟩
    have h5 : (b * b') i i = b i i * b' i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hb h, zero_mul]
      · rw [hb' h, mul_zero]
    rw [h4, Matrix.one_apply_eq] at h5
    exact IsUnit.of_mul_eq_one _ h5.symm

end GlobalTheory
