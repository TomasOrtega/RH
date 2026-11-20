import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `main : ∀ k, k ≤ n → ∀ i j : Fin n, (j : ℕ) < k → ((List.ofFn M).take k).prod i j = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ i j hj`. Conclude with `absurd hj (Nat.not_lt_zero _)`.

Consider the case `succ k ih`. Introduce `hk i j hj`. Establish `htake : (List.ofFn M).take (k + 1) = (List.ofFn M).take k ++ [M ⟨k, hk⟩]`. Rewrite using `[List.take_succ]`. Simplify using `[show k < n by omega]`.

Rewrite using `[htake, List.prod_append, List.prod_singleton, mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `m _`. Distinguish the cases in `hm : (m : ℕ) < k`. Rewrite using `[ih (Nat.le_of_succ_le hk) i m hm, zero_mul]`.

Distinguish the cases in `hmj : j < m`. Rewrite using `[h1 ⟨k, hk⟩ m j hmj, mul_zero]`. Establish `e1 : m = ⟨k, hk⟩` using `Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)`. Establish `e2 : j = ⟨k, hk⟩` using `Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)`. Rewrite using `[e1, e2, h2, mul_zero]`.

Establish `hall : (List.ofFn M).take n = List.ofFn M` using `List.take_of_length_le (by simp)`. Use extensionality with `i j`. Rewrite using `[← hall]`. Conclude with `main n le_rfl i j j.2`.
-/
private theorem prod_tri {C : Type} [CommRing C] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) C)
    (h1 : ∀ k i j, j < i → M k i j = 0) (h2 : ∀ k, M k k k = 0) : (List.ofFn M).prod = 0 := by
  have main : ∀ k, k ≤ n → ∀ i j : Fin n, (j : ℕ) < k → ((List.ofFn M).take k).prod i j = 0 := by
    intro k
    induction k with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk i j hj
      have htake : (List.ofFn M).take (k + 1) = (List.ofFn M).take k ++ [M ⟨k, hk⟩] := by
        rw [List.take_succ]
        simp [show k < n by omega]
      rw [htake, List.prod_append, List.prod_singleton, mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : (m : ℕ) < k
      · rw [ih (Nat.le_of_succ_le hk) i m hm, zero_mul]
      · by_cases hmj : j < m
        · rw [h1 ⟨k, hk⟩ m j hmj, mul_zero]
        · have e1 : m = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          have e2 : j = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          rw [e1, e2, h2, mul_zero]
  have hall : (List.ofFn M).take n = List.ofFn M := List.take_of_length_le (by simp)
  ext i j
  rw [← hall]
  exact main n le_rfl i j j.2

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Rewrite using `[List.map_cons, List.prod_cons, ih, List.prod_cons]`. Simplify using `[mul_assoc]`.
-/
private theorem prod_conj {R : Type} [Monoid R] (g : Rˣ) (L : List R) :
    (L.map fun x => (g : R) * x * ((g⁻¹ : Rˣ) : R)).prod = g * L.prod * ((g⁻¹ : Rˣ) : R) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp [mul_assoc]

/- English proof (translation)
Introduce `H C _ _ n r ψ hf`. Take `⟨g, hg⟩` from `hf`. Establish `hconj : ∀ s, ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = (g : Matrix (Fin n) (Fin n) C) * r s * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)`. Introduce `s`. Simplify using `[Units.val_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `gs show (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod = 0`. Set `M : Fin n → Matrix (Fin n) (Fin n) C` to `fun i => (g : Matrix (Fin n) (Fin n) C) * (r (gs i) - (ψ i (gs i) : C) • 1) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)`. Establish `hM : ∀ i, M i = ((g * r.toHomUnits (gs i) * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - (ψ i (gs i) : C) • 1`. Introduce `i`.

Rewrite using `[hconj]`. Simplify using `only [M]`. Rewrite using `[mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]`. Establish `h0 : (List.ofFn M).prod = 0`. Use `prod_tri M (fun k i j hij => ?_) (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]`. Conclude with `(hg (gs k)).1 i j hij`. Rewrite using `[hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, (hg (gs k)).2 k, sub_self]`. Establish `hmap : List.ofFn M = (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).map (fun x => (g : Matrix (Fin n) (Fin n) C) * x * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))`. Rewrite using `[List.map_ofFn]`.

Both sides reduce to the same expression. Rewrite `h0` using `[hmap, prod_conj g]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[mul_assoc]`. Use `_ = 0 := by rw [h0, mul_zero, zero_mul]`.

Introduce `s`. Rewrite using `[← Matrix.charpoly_units_conj g (r s), ← Matrix.coe_units_inv, ← hconj, Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]`.
-/
theorem UpperTheory.V.Fr.ord_of_flag :
    ∀ {H C : Type} [Group H] [CommRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ), UpperTheory.V.W.HasFlag r.toHomUnits ψ → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) ∧ ∀ g, (r g).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ψ i g : C)) := by
  intro H C _ _ n r ψ hf
  obtain ⟨g, hg⟩ := hf
  have hconj : ∀ s, ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      (g : Matrix (Fin n) (Fin n) C) * r s * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
    intro s
    simp [Units.val_mul]
  constructor
  · intro gs
    show (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod = 0
    let M : Fin n → Matrix (Fin n) (Fin n) C := fun i =>
      (g : Matrix (Fin n) (Fin n) C) * (r (gs i) - (ψ i (gs i) : C) • 1) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)
    have hM : ∀ i, M i = ((g * r.toHomUnits (gs i) * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) -
        (ψ i (gs i) : C) • 1 := by
      intro i
      rw [hconj]
      simp only [M]
      rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]
    have h0 : (List.ofFn M).prod = 0 := by
      refine prod_tri M (fun k i j hij => ?_) (fun k => ?_)
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
        exact (hg (gs k)).1 i j hij
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, (hg (gs k)).2 k, sub_self]
    have hmap : List.ofFn M = (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).map
        (fun x => (g : Matrix (Fin n) (Fin n) C) * x * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, prod_conj g] at h0
    calc (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod
        = ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) *
          ((g : Matrix (Fin n) (Fin n) C) *
            (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod *
            ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) * (g : Matrix (Fin n) (Fin n) C) := by
          simp [mul_assoc]
      _ = 0 := by rw [h0, mul_zero, zero_mul]
  · intro s
    rw [← Matrix.charpoly_units_conj g (r s), ← Matrix.coe_units_inv, ← hconj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
