import Mathlib

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce a local definition for the expression. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Equip the data with the indicated structure. Equip the data with the indicated structure.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem exists_orthonormal_expansion_of_sesq {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by
  let cd : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip y x
      conj_inner_symm := fun x y => by simp [hsym y x]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        change ip x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup C := @InnerProductSpace.Core.toNormedAddCommGroup ℂ C _ _ _ cd
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ C
  refine ⟨_, b, fun i j => ?_, fun x => ?_⟩
  · have h := orthonormal_iff_ite.mp b.orthonormal j i
    have e : ⟪b j, b i⟫_ℂ = ip (b i) (b j) := rfl
    rw [e] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have h := b.sum_repr' x
    exact h.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem value_of_adjoint_of_mem_span : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  intro X W C _ _ _ _ _ ev K ipD ip pet hD hDpos hsym hpos hpet x F l hF hl hF0
  obtain ⟨n, b, hb, hexp⟩ := exists_orthonormal_expansion_of_sesq ip hsym hpos
  let Φ : (Fin n → W) →ₗ[ℂ] (X → ℂ) := ∑ j, (ev (b j)).comp (LinearMap.proj j)
  have hΦ : ∀ u, Φ u = ∑ j, ev (b j) (u j) := by
    intro u; simp [Φ, LinearMap.sum_apply]
  have hspan : Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} ≤
      (Submodule.pi Set.univ (fun _ : Fin n => K)).map Φ := by
    rw [Submodule.span_le]
    rintro G ⟨y, w, hw, rfl⟩
    refine ⟨fun j => ip y (b j) • w, fun j _ => K.smul_mem _ hw, ?_⟩
    rw [hΦ]
    conv_rhs => rw [hexp y]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_smul, LinearMap.smul_apply]
  obtain ⟨u, hu, hFu⟩ := hspan hF
  have huK : ∀ j, u j ∈ K := fun j => hu j (Set.mem_univ j)
  rw [hΦ] at hFu
  have key : ∀ k, ∀ w ∈ K, ipD w (u k) = ip (b k) x * l w := by
    intro k w hw
    have h1 := hl (b k) w hw
    rw [← hFu, hpet] at h1
    simpa only [hb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h1
  have hex : ∃ k, u k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF0
    rw [← hFu]
    simp [h]
  obtain ⟨k, hk⟩ := hex
  have hkpos := hDpos (u k) hk
  rw [key k (u k) (huK k)] at hkpos
  have ha : ip (b k) x ≠ 0 := by
    intro h; rw [h, zero_mul] at hkpos; simp at hkpos
  have hx : x ≠ 0 := by
    rintro rfl; exact ha (by simp)
  refine ⟨hx, ?_⟩
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = (conj (ip (b k) x))⁻¹ • u k := ⟨_, rfl⟩
  have hw₀K : w₀ ∈ K := hw₀def ▸ K.smul_mem _ (huK k)
  have hw₀ : ∀ w ∈ K, ipD w w₀ = l w := by
    intro w hw
    rw [hw₀def, LinearMap.map_smulₛₗ, key k w hw, map_inv₀, Complex.conj_conj, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hu_eq : ∀ j, u j = conj (ip (b j) x) • w₀ := by
    intro j
    have hdK : u j - conj (ip (b j) x) • w₀ ∈ K := K.sub_mem (huK j) (K.smul_mem _ hw₀K)
    have hd0 : ∀ w ∈ K, ipD w (u j - conj (ip (b j) x) • w₀) = 0 := by
      intro w hw
      rw [map_sub, LinearMap.map_smulₛₗ, key j w hw, hw₀ w hw, Complex.conj_conj, smul_eq_mul, sub_self]
    by_contra hne
    have := hDpos _ (sub_ne_zero.mpr hne)
    rw [hd0 _ hdK] at this
    simp at this
  refine ⟨w₀, hw₀K, ?_⟩
  rw [← hFu]
  have hsum : ∑ j, ev (b j) (u j) = ∑ j, ev (b j) (conj (ip (b j) x) • w₀) :=
    Finset.sum_congr rfl (fun j _ => by rw [hu_eq j])
  rw [hsum]
  conv_rhs => rw [hexp x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [map_smul, LinearMap.smul_apply]
  rw [hsym x (b j)]

end GlobalTheory.ChainOnto
