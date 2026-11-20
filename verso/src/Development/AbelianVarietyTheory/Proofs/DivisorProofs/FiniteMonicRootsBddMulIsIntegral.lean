import Mathlib
open NumberField Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Multiset.esymm, ← Multiset.sum_map_mul_left]`. Use `(integralClosure ℤ ℂ).multiset_sum_mem ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `Multiset.mem_map.mp hx`. Rewrite `ht` using `[Multiset.mem_powersetCard]`.

Establish `: c ^ m * t.prod = (t.map (fun w => c * w)).prod`. Rewrite using `[Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]`. Rewrite using `[this]`. Use `(integralClosure ℤ ℂ).multiset_prod_mem ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨w, hw, rfl⟩` from `Multiset.mem_map.mp hy`. Conclude with `h w (Multiset.mem_of_le ht.1 hw)`.
-/
theorem isIntegral_pow_mul_esymm (s : Multiset ℂ) (c : ℂ) (m : ℕ)
    (h : ∀ w ∈ s, IsIntegral ℤ (c * w)) : IsIntegral ℤ (c ^ m * s.esymm m) := by
  rw [Multiset.esymm, ← Multiset.sum_map_mul_left]
  refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  have : c ^ m * t.prod = (t.map (fun w => c * w)).prod := by
    rw [Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_id', ht.2]
  rw [this]
  refine (integralClosure ℤ ℂ).multiset_prod_mem ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
  exact h w (Multiset.mem_of_le ht.1 hw)

/- English proof (translation)
Introduce `F _ _ n N B hN`. Set `φ₀ : F →+* ℂ` to `(Classical.arbitrary (InfinitePlace F)).embedding`. Set `B₁ : ℝ` to `max |B| 1`. Set `C : ℝ` to `(N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)`. Establish `hT` using `Embeddings.finite_of_norm_le F ℂ C`.

Set `f : F[X] → Fin (n + 1) → F` to `fun P k => (N : F) ^ n * P.coeff k`. Use `Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -`. Establish `hk : (k : ℕ) ≤ n` using `Nat.lt_succ_iff.mp k.2`. Use `⟨?_, fun φ => ?_⟩` and prove the remaining obligations.

Establish `hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree` using `IsAlgClosed.card_roots_eq_natDegree`. Establish `hdeg : (P.map φ₀).natDegree = n` using `by rw [hm.natDegree_map, hd]`. Establish `hc` using `coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)`. Rewrite `hc` using `[(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map]`. Rewrite using `[← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]`.

Use `show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))`. Rewrite using `[map_mul, map_pow, map_natCast, hc]`. Establish `hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) = ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) * ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k))`. Establish `: (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hk]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Use `IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _) ((isIntegral_one.neg).pow _)) ?_` and prove the remaining obligations. Conclude with `GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)`.

Use `show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C`. Rewrite using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]`. Establish `hb` using `coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _) (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))`. Rewrite `hb` using `[coeff_map, hd]`. Establish `hB₁ : (1 : ℝ) ≤ B₁` using `le_max_right _ _`.

Establish `h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n` using `mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _)) (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)`. Conclude with `mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)`. Introduce and unpack `P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ`. Use extensionality with `i`. Distinguish the cases in `hi : i ≤ n`.

Establish `h` using `congrFun hPQ ⟨i, by omega⟩`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]`.
-/
theorem finite_monic_roots_bdd_mul_isIntegral :
    ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  intro F _ _ n N B hN
  let φ₀ : F →+* ℂ := (Classical.arbitrary (InfinitePlace F)).embedding
  let B₁ : ℝ := max |B| 1
  let C : ℝ := (N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)
  have hT := Embeddings.finite_of_norm_le F ℂ C
  let f : F[X] → Fin (n + 1) → F := fun P k => (N : F) ^ n * P.coeff k
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_
  · rintro _ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
    refine ⟨?_, fun φ => ?_⟩
    · have hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hdeg : (P.map φ₀).natDegree = n := by rw [hm.natDegree_map, hd]
      have hc := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
      rw [(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map] at hc
      rw [← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]
      show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))
      rw [map_mul, map_pow, map_natCast, hc]
      have hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) =
          ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) *
            ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) := by
        have : (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [this]; ring
      rw [hsplit]
      refine IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _)
        ((isIntegral_one.neg).pow _)) ?_
      exact GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)
    · show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
      have hb := coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _)
        (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))
      rw [coeff_map, hd] at hb
      have hB₁ : (1 : ℝ) ≤ B₁ := le_max_right _ _
      have h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n :=
        mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _))
          (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
  · rintro P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ
    ext i
    by_cases hi : i ≤ n
    · have h := congrFun hPQ ⟨i, by omega⟩
      exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end GlobalTheory
