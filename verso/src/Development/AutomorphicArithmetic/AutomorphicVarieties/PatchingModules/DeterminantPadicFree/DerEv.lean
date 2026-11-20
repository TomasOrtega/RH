import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `i j`. Use `⟨fun _ => Submodule.mem_top, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_bot, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hij h`.
-/
private theorem single_mem_ev_of_same_block {F : Type} [CommRing F] {n a : ℕ} (p q : Fin n) (c : F)
    (h : ((p : ℕ) < a ↔ (q : ℕ) < a)) : Matrix.single p q c ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

/- English proof (translation)
Introduce `F _ n a d hd`. Set `β : Fin n → Fin n` to `fun i => if h : (i : ℕ) < a then ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ else ⟨a, lt_of_le_of_lt (not_lt.mp h) i.isLt⟩`. Establish `hβ : ∀ i : Fin n, ((i : ℕ) < a ↔ (β i : ℕ) < a)`. Introduce `i`. Distinguish the cases in `h : (i : ℕ) < a`.

Simplify using `only [β, dif_pos h]`. Conclude with `⟨fun _ => Nat.zero_lt_of_lt h, fun _ => h⟩`. Simplify using `only [β, dif_neg h]`. Conclude with `⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩`. Establish `hβeq : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → β i = β j`.

Introduce `i j h`. Distinguish the cases in `hi : (i : ℕ) < a`. Establish `hj` using `h.mp hi`. Simplify using `only [β, dif_pos hi, dif_pos hj]`. Establish `hj : ¬ (j : ℕ) < a` using `fun hj => hi (h.mpr hj)`.

Simplify using `only [β, dif_neg hi, dif_neg hj]`. Set `E : Fin n → Fin n → Matrix (Fin n) (Fin n) F` to `fun i j => Matrix.single i j 1`. Set `u : Fin n → Matrix (Fin n) (Fin n) F` to `fun k => E k (β k)`. Set `v : Fin n → Matrix (Fin n) (Fin n) F` to `fun k => E (β k) k`. Establish `hu : ∀ k, u k ∈ Ev F F n a` using `fun k => single_mem_ev_of_same_block _ _ _ (hβ k)`.

Set `Y` to `∑ k, d (u k) * v k`. Establish `hsum : ∑ k, u k * v k = 1`. Simplify using `only [u, v, E, Matrix.single_mul_single_same, mul_one]`. Conclude with `Matrix.sum_single_one`. Establish `key : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → d (E i j) = Y * E i j - E i j * Y`.

Introduce `i j hij`. Establish `hE : E i j ∈ Ev F F n a` using `single_mem_ev_of_same_block i j 1 hij`. Establish `h1 : Y * E i j = d (u i) * v j`. Simplify using `only [Y, Finset.sum_mul, mul_assoc]`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using `only [v, E, u]`. Rewrite using `[Matrix.single_mul_single_same, mul_one, hβeq i j hij]`. Introduce `k _ hk`. Simplify using `only [v, E]`. Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ hk _, mul_zero]`.

Simplify using the standard rewrite rules. Establish `hk : ∀ k, E i j * d (u k) = d (E i j * u k) - d (E i j) * u k`. Introduce `k`. Rewrite using `[hd _ hE _ (hu k)]`. Normalize the expressions using the abelian group laws.

Establish `hEu : ∀ k, E i j * u k = if j = k then u i else 0`. Introduce `k`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [E, u]`.

Rewrite using `[Matrix.single_mul_single_same, mul_one, hβeq i j hij]`. Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ h _`. Establish `h2 : E i j * Y = d (u i) * v j - d (E i j)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Y, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hk, sub_mul, mul_assoc]`. Use `_ = d (u i) * v j - d (E i j) := by`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]`. Use `congr 1`.

Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[hEu, if_pos rfl]`. Introduce `k _ hk`. Rewrite using `[hEu, if_neg (Ne.symm hk), map_zero, zero_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[h1, h2]`. Normalize the expressions using the abelian group laws. Use `⟨Y, fun x hx => ?_⟩` and prove the remaining obligations. Set `D' : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F` to `d - (LinearMap.mulLeft F Y - LinearMap.mulRight F Y)`. Establish `hD : D' x = 0`.

Rewrite using `[Matrix.matrix_eq_sum_single x, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hij : ((i : ℕ) < a ↔ (j : ℕ) < a)`.

Establish `hs : Matrix.single i j (x i j) = x i j • E i j`. Simplify using `only [E, Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hs, map_smul]`. Simplify using `only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, key i j hij, sub_self, smul_zero]`. Establish `h0 : x i j = 0` using `(Submodule.mem_bot F).mp ((hx i j).2 hij)`.

Rewrite using `[h0, Matrix.single_zero, map_zero]`. Simplify using `only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at hD`. Conclude with `hD`.
-/
theorem UpperTheory.V.Pa.Det.derEv :
    ∀ {F : Type} [CommRing F] {n a : ℕ} (d : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F), (∀ x ∈ Ev F F n a, ∀ y ∈ Ev F F n a, d (x * y) = d x * y + x * d y) → ∃ Y, ∀ x ∈ Ev F F n a, d x = Y * x - x * Y := by
  intro F _ n a d hd
  let β : Fin n → Fin n := fun i =>
    if h : (i : ℕ) < a then ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
    else ⟨a, lt_of_le_of_lt (not_lt.mp h) i.isLt⟩
  have hβ : ∀ i : Fin n, ((i : ℕ) < a ↔ (β i : ℕ) < a) := by
    intro i
    by_cases h : (i : ℕ) < a
    · simp only [β, dif_pos h]
      exact ⟨fun _ => Nat.zero_lt_of_lt h, fun _ => h⟩
    · simp only [β, dif_neg h]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
  have hβeq : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → β i = β j := by
    intro i j h
    by_cases hi : (i : ℕ) < a
    · have hj := h.mp hi
      simp only [β, dif_pos hi, dif_pos hj]
    · have hj : ¬ (j : ℕ) < a := fun hj => hi (h.mpr hj)
      simp only [β, dif_neg hi, dif_neg hj]
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) F := fun i j => Matrix.single i j 1
  let u : Fin n → Matrix (Fin n) (Fin n) F := fun k => E k (β k)
  let v : Fin n → Matrix (Fin n) (Fin n) F := fun k => E (β k) k
  have hu : ∀ k, u k ∈ Ev F F n a := fun k => single_mem_ev_of_same_block _ _ _ (hβ k)
  let Y := ∑ k, d (u k) * v k
  have hsum : ∑ k, u k * v k = 1 := by
    simp only [u, v, E, Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have key : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) →
      d (E i j) = Y * E i j - E i j * Y := by
    intro i j hij
    have hE : E i j ∈ Ev F F n a := single_mem_ev_of_same_block i j 1 hij
    have h1 : Y * E i j = d (u i) * v j := by
      simp only [Y, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_eq_single i]
      · simp only [v, E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · intro k _ hk
        simp only [v, E]
        rw [Matrix.single_mul_single_of_ne _ _ _ _ hk _, mul_zero]
      · simp
    have hk : ∀ k, E i j * d (u k) = d (E i j * u k) - d (E i j) * u k := by
      intro k
      rw [hd _ hE _ (hu k)]
      abel
    have hEu : ∀ k, E i j * u k = if j = k then u i else 0 := by
      intro k
      split_ifs with h
      · subst h
        simp only [E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
    have h2 : E i j * Y = d (u i) * v j - d (E i j) := by
      calc E i j * Y = ∑ k, (d (E i j * u k) * v k - d (E i j) * (u k * v k)) := by
            simp only [Y, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mul_assoc, hk, sub_mul, mul_assoc]
        _ = d (u i) * v j - d (E i j) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
            congr 1
            rw [Finset.sum_eq_single j]
            · rw [hEu, if_pos rfl]
            · intro k _ hk
              rw [hEu, if_neg (Ne.symm hk), map_zero, zero_mul]
            · simp
    rw [h1, h2]
    abel
  refine ⟨Y, fun x hx => ?_⟩
  let D' : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F :=
    d - (LinearMap.mulLeft F Y - LinearMap.mulRight F Y)
  have hD : D' x = 0 := by
    rw [Matrix.matrix_eq_sum_single x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : ((i : ℕ) < a ↔ (j : ℕ) < a)
    · have hs : Matrix.single i j (x i j) = x i j • E i j := by
        simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]
      simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        key i j hij, sub_self, smul_zero]
    · have h0 : x i j = 0 := (Submodule.mem_bot F).mp ((hx i j).2 hij)
      rw [h0, Matrix.single_zero, map_zero]
  simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    sub_eq_zero] at hD
  exact hD
