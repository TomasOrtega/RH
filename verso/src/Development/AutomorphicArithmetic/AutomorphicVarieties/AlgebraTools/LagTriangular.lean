import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨1, isUnit_one, by simp⟩`. Consider the case `cons x L ih`. Take `⟨u, hu, e⟩` from `h x (by simp)`. Take `⟨v, hv, e'⟩` from `ih (fun y hy => h y (by simp [hy]))`.

Conclude with `⟨u * v, hu.mul hv, by`. Rewrite using `[List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩`.
-/
private theorem left_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ f * x = u • f) :
    ∃ u : R, IsUnit u ∧ f * L.prod = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨u * v, hu.mul hv, by
      rw [List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨1, isUnit_one, by simp⟩`. Consider the case `cons x L ih`. Take `⟨u, hu, e⟩` from `h x (by simp)`. Take `⟨v, hv, e'⟩` from `ih (fun y hy => h y (by simp [hy]))`.

Conclude with `⟨v * u, hv.mul hu, by`. Rewrite using `[List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩`.
-/
private theorem right_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ x * f = u • f) :
    ∃ u : R, IsUnit u ∧ L.prod * f = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨v * u, hv.mul hu, by
      rw [List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩

/- English proof (translation)
Establish `hlen : (List.ofFn F).length = n` using `List.length_ofFn`. Establish `hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1)` using `by conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]`. Use `congr 1`. Rewrite using `[List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]`. Simplify using the standard rewrite rules.

Establish `hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f`. Introduce `x hx`. Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.1 hx`. Simplify using `only [List.length_take, hlen] at hk`. Rewrite using `[List.getElem_take, List.getElem_ofFn]`.

Conclude with `hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)`. Establish `hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g`. Introduce `x hx`. Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.1 hx`. Simplify using `only [List.length_drop, hlen] at hk`.

Rewrite using `[List.getElem_drop, List.getElem_ofFn]`. Conclude with `hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)`. Take `⟨u, hu, hA⟩` from `left_unit (R := R) f _ hT`. Take `⟨v, hv, hB⟩` from `right_unit (R := R) g _ hD`. Establish `key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g)`.

Rewrite using `[hsplit, List.prod_append, List.prod_cons]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (u • f) * F i * (v • g) := by rw [hA, hB]`. Use `_ = (u * v) • (f * F i * g) := by`.

Rewrite using `[smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]`. Rewrite `key` using `[h0, mul_zero, zero_mul]`. Conclude with `((hu.mul hv).smul_eq_zero).1 key.symm`.
-/
private theorem mid_zero {R E : Type} [CommRing R] [Ring E] [Algebra R E] {n : ℕ} (f g : E)
    (F : Fin n → E) (i : Fin n)
    (hf : ∀ j, j < i → ∃ u : R, IsUnit u ∧ f * F j = u • f)
    (hg : ∀ j, i < j → ∃ u : R, IsUnit u ∧ F j * g = u • g)
    (h0 : (List.ofFn F).prod = 0) : f * F i * g = 0 := by
  have hlen : (List.ofFn F).length = n := List.length_ofFn
  have hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]
    congr 1
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]
    simp
  have hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, hlen] at hk
    rw [List.getElem_take, List.getElem_ofFn]
    exact hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop, hlen] at hk
    rw [List.getElem_drop, List.getElem_ofFn]
    exact hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  obtain ⟨u, hu, hA⟩ := left_unit (R := R) f _ hT
  obtain ⟨v, hv, hB⟩ := right_unit (R := R) g _ hD
  have key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g) := by
    rw [hsplit, List.prod_append, List.prod_cons]
    calc f * (((List.ofFn F).take i).prod * (F i * ((List.ofFn F).drop (i + 1)).prod)) * g
        = (f * ((List.ofFn F).take i).prod) * F i * (((List.ofFn F).drop (i + 1)).prod * g) := by
          simp only [mul_assoc]
      _ = (u • f) * F i * (v • g) := by rw [hA, hB]
      _ = (u * v) • (f * F i * g) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h0, mul_zero, zero_mul] at key
  exact ((hu.mul hv).smul_eq_zero).1 key.symm

/- English proof (translation)
Introduce `R Λ E _ _ _ _ _ n ρ χ z hprod hu`. Establish `hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0`. Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Simplify `hprod (fun _ => z)` using `[Function.comp_def]`. Take `⟨hcoi, hP, -, hcomm⟩` from `lag_coi (fun i => χ i z) (ρ z) hu hzero`.

Establish `hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) = (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c`. Introduce `c j`. Rewrite using `[mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes, ← Algebra.smul_def, sub_smul]`. Establish `hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c = (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c`. Introduce `c j`.

Rewrite using `[sub_mul, hP, ← Algebra.smul_def, sub_smul]`. Establish `key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) → lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) * lag (fun i => χ i z) (ρ z) d = 0`. Introduce `y c d i h1 h2`. Establish `h` using `mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d) (fun j => ρ (Function.update (fun _ => z) i y j) - algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)`. Simplify using `using h`.

Introduce `j hj`. Use `⟨_, hu c j (h1 j hj).symm, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.update_apply, if_neg (ne_of_lt hj)]`. Conclude with `hl c j`. Introduce `j hj`.

Use `⟨_, hu d j (h2 j hj).symm, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.update_apply, if_neg (ne_of_gt hj)]`. Conclude with `hr d j`. Establish `hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r * lag (fun i => χ i z) (ρ z) d = r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d)`. Introduce `r c d`.

Rewrite using `[← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]`. Use `⟨hcoi, ?_, ?_⟩` and prove the remaining obligations. Introduce `y a b hba`. Establish `h` using `key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))`. Rewrite `h` using `[mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero]`.

Conclude with `h`. Introduce `y i`. Establish `h` using `key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)`. Rewrite `h` using `[mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero]`. Conclude with `h`.
-/
theorem UpperTheory.V.AlgebraTools.lag_triangular :
    ∀ {R Λ E : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Ring E] [Algebra R E] {n : ℕ} (ρ : Λ →ₐ[R] E) (χ : Fin n → Λ →ₐ[R] R) (z : Λ), (∀ y : Fin n → Λ, (List.ofFn fun i => ρ (y i) - algebraMap R E (χ i (y i))).prod = 0) → (∀ i j, i ≠ j → IsUnit (χ i z - χ j z)) → CompleteOrthogonalIdempotents (lag (fun i => χ i z) (ρ z)) ∧ (∀ (y : Λ) (a b : Fin n), b < a → lag (fun i => χ i z) (ρ z) a * ρ y * lag (fun i => χ i z) (ρ z) b = 0) ∧ ∀ (y : Λ) (i : Fin n), lag (fun i => χ i z) (ρ z) i * ρ y * lag (fun i => χ i z) (ρ z) i = χ i y • lag (fun i => χ i z) (ρ z) i := by
  intro R Λ E _ _ _ _ _ n ρ χ z hprod hu
  have hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hprod (fun _ => z)
  obtain ⟨hcoi, hP, -, hcomm⟩ := lag_coi (fun i => χ i z) (ρ z) hu hzero
  have hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes,
      ← Algebra.smul_def, sub_smul]
  have hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [sub_mul, hP, ← Algebra.smul_def, sub_smul]
  have key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) →
      lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) *
        lag (fun i => χ i z) (ρ z) d = 0 := by
    intro y c d i h1 h2
    have h := mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d)
      (fun j => ρ (Function.update (fun _ => z) i y j) -
        algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)
    · simpa using h
    · intro j hj
      refine ⟨_, hu c j (h1 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_lt hj)]
      exact hl c j
    · intro j hj
      refine ⟨_, hu d j (h2 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_gt hj)]
      exact hr d j
  have hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r *
      lag (fun i => χ i z) (ρ z) d =
        r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d) := by
    intro r c d
    rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]
  refine ⟨hcoi, ?_, ?_⟩
  · intro y a b hba
    have h := key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))
    rw [mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero] at h
    exact h
  · intro y i
    have h := key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)
    rw [mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero] at h
    exact h
