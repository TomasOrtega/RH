import Mathlib
open scoped Matrix

namespace GlobalTheory.UniformCoboundary

/- English proof (translation)
Set `W : Finset Γ → Submodule K (Fin 2 → K)` to `fun T => ⨅ t ∈ T, LinearMap.ker (Matrix.toLin' (M t) - LinearMap.id)`. Establish `hW : ∀ (T : Finset Γ) (v : Fin 2 → K), v ∈ W T ↔ ∀ t ∈ T, M t *ᵥ v = v`. Introduce `T v`. Simplify using `only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]`. Take `⟨_, ⟨T, hTS, rfl⟩, hmin⟩` from `(wellFounded_lt (α := Submodule K (Fin 2 → K))).has_min {P | ∃ T : Finset Γ, ↑T ⊆ S ∧ W T = P} ⟨_, ∅, by simp, rfl⟩`.

Use `⟨T, hTS, fun v hv s hs => ?_⟩` and prove the remaining obligations. Establish `hle : W (insert s T) ≤ W T`. Introduce `w hw`. Rewrite `hw`, the goal using `[hW]`. Conclude with `fun t ht => hw t (Finset.mem_insert_of_mem ht)`.

Establish `hnlt : ¬ W (insert s T) < W T` using `hmin _ ⟨insert s T, by rw [Finset.coe_insert]; exact Set.insert_subset hs hTS, rfl⟩`. Establish `heq : W (insert s T) = W T` using `(hle.lt_or_eq).resolve_left hnlt`. Establish `hv' : v ∈ W (insert s T)` using `by rw [heq, hW]; exact hv`. Conclude with `(hW _ _).1 hv' s (Finset.mem_insert_self s T)`.
-/
theorem exists_finset_fixed {K : Type} [Field K] {Γ : Type} (S : Set Γ)
    (M : Γ → Matrix (Fin 2) (Fin 2) K) :
    ∃ T : Finset Γ, (↑T ⊆ S) ∧
      ∀ v : Fin 2 → K, (∀ t ∈ T, M t *ᵥ v = v) → ∀ s ∈ S, M s *ᵥ v = v := by
  classical
  let W : Finset Γ → Submodule K (Fin 2 → K) :=
    fun T => ⨅ t ∈ T, LinearMap.ker (Matrix.toLin' (M t) - LinearMap.id)
  have hW : ∀ (T : Finset Γ) (v : Fin 2 → K), v ∈ W T ↔ ∀ t ∈ T, M t *ᵥ v = v := by
    intro T v
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]
  obtain ⟨_, ⟨T, hTS, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K (Fin 2 → K))).has_min
      {P | ∃ T : Finset Γ, ↑T ⊆ S ∧ W T = P} ⟨_, ∅, by simp, rfl⟩
  refine ⟨T, hTS, fun v hv s hs => ?_⟩
  have hle : W (insert s T) ≤ W T := by
    intro w hw
    rw [hW] at hw ⊢
    exact fun t ht => hw t (Finset.mem_insert_of_mem ht)
  have hnlt : ¬ W (insert s T) < W T :=
    hmin _ ⟨insert s T, by rw [Finset.coe_insert]; exact Set.insert_subset hs hTS, rfl⟩
  have heq : W (insert s T) = W T := (hle.lt_or_eq).resolve_left hnlt
  have hv' : v ∈ W (insert s T) := by rw [heq, hW]; exact hv
  exact (hW _ _).1 hv' s (Finset.mem_insert_self s T)

/- English proof (translation)
Use `⟨∑ k, ∑ p, ‖L (Pi.single p 1) k‖, by positivity, fun w ε hε hw k => ?_⟩` and prove the remaining obligations. Establish `h1 : w = ∑ p, w p • (Pi.single p 1 : ι → K)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h2 : L w k = ∑ p, w p * L (Pi.single p 1) k` using `by conv_lhs => rw [h1]`.

Simplify using `[map_sum, Finset.sum_apply]`. Establish `h3 : ‖L w k‖ ≤ (∑ p, ‖L (Pi.single p 1) k‖) * ε`. Rewrite using `[h2, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, mul_comm]`.

Conclude with `mul_le_mul_of_nonneg_left (hw p) (norm_nonneg _)`. Use `h3.trans (mul_le_mul_of_nonneg_right ?_ hε)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun k => ∑ p, ‖L (Pi.single p 1) k‖) (fun k _ => by positivity) (Finset.mem_univ k)`.
-/
theorem exists_bound {K : Type} [NormedField K] {ι : Type} [Fintype ι]
    (L : (ι → K) →ₗ[K] (Fin 2 → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ι → K) (ε : ℝ), 0 ≤ ε → (∀ p, ‖w p‖ ≤ ε) → ∀ k, ‖L w k‖ ≤ C * ε := by
  classical
  refine ⟨∑ k, ∑ p, ‖L (Pi.single p 1) k‖, by positivity, fun w ε hε hw k => ?_⟩
  have h1 : w = ∑ p, w p • (Pi.single p 1 : ι → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : L w k = ∑ p, w p * L (Pi.single p 1) k := by
    conv_lhs => rw [h1]
    simp [map_sum, Finset.sum_apply]
  have h3 : ‖L w k‖ ≤ (∑ p, ‖L (Pi.single p 1) k‖) * ε := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hw p) (norm_nonneg _)
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ hε)
  exact Finset.single_le_sum (f := fun k => ∑ p, ‖L (Pi.single p 1) k‖)
    (fun k _ => by positivity) (Finset.mem_univ k)

/- English proof (translation)
Take `⟨T, hTS, hT⟩` from `exists_finset_fixed S M`. Set `e : (Fin 2 → K) →ₗ[K] (T × Fin 2 → K)` to `LinearMap.pi fun p => (LinearMap.proj p.2).comp (Matrix.toLin' (M p.1) - LinearMap.id)`. Establish `he : ∀ v (p : T × Fin 2), e v p = (M p.1 *ᵥ v - v) p.2`. Introduce `v p`. Simplify using `[e, Matrix.toLin'_apply]`.

Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective e.rangeRestrict (LinearMap.range_rangeRestrict e)`. Take `⟨L, hL⟩` from `LinearMap.exists_extend g`. Establish `heL : ∀ v, e (L (e v)) = e v`. Introduce `v`. Establish `h1 : L (e v) = g (e.rangeRestrict v)` using `LinearMap.congr_fun hL (e.rangeRestrict v)`.

Establish `h2 : e.rangeRestrict (g (e.rangeRestrict v)) = e.rangeRestrict v` using `LinearMap.congr_fun hg (e.rangeRestrict v)`. Rewrite using `[h1]`. Conclude with `congrArg Subtype.val h2`. Establish `hSL : ∀ v, ∀ s ∈ S, M s *ᵥ (L (e v)) - L (e v) = M s *ᵥ v - v`. Introduce `v s hs`.

Establish `h0 : e (L (e v) - v) = 0` using `by rw [map_sub, heL, sub_self]`. Establish `h1 : ∀ t ∈ T, M t *ᵥ (L (e v) - v) = L (e v) - v`. Introduce `t ht`. Rewrite using `[← sub_eq_zero]`. Use function extensionality and compare the values at `i`.

Use `congrFun h0 (⟨t, ht⟩, i)` as an intermediate fact. Rewrite `this` using `[he]`. Conclude with `this`. Establish `h2` using `hT _ h1 s hs`. Rewrite `h2` using `[Matrix.mulVec_sub]`.

Rewrite using `[sub_eq_sub_iff_sub_eq_sub]`. Conclude with `h2`. Take `⟨C, hC, hCb⟩` from `exists_bound L`. Set `Y : T × Fin 2 → K` to `fun p => y p.1 p.2`. Use `⟨L Y, fun s hs => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero, ← norm_le_zero_iff]`. Establish `key : ∀ r : ℕ, ‖y s i - (M s *ᵥ L Y - L Y) i‖ ≤ (1 + 3 * C) * ‖q‖ ^ r`. Introduce `r`. Take `⟨vr, hvr⟩` from `hf r`.

Establish `hε : 0 ≤ ‖q‖ ^ r` using `by positivity`. Establish `hu : ∀ k, ‖L (Y - e vr) k‖ ≤ C * ‖q‖ ^ r`. Use `hCb _ _ hε fun p => ?_` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, he, ← hvr p.1 (hTS p.1.2), ← norm_pow]`. Conclude with `hy r p.1 p.2`.

Establish `hv : L Y = L (e vr) + L (Y - e vr)` using `by simp [map_sub]`. Generalize the expression as in `L (Y - e vr) = u at hu hv`. Establish `hid : M s *ᵥ L Y - L Y = f r s + (M s *ᵥ u - u)`. Rewrite using `[hvr s hs, ← hSL vr s hs, hv, Matrix.mulVec_add]`. Normalize the expressions using the abelian group laws.

Establish `hMu : ‖(M s *ᵥ u) i‖ ≤ 2 * (C * ‖q‖ ^ r)`. Establish `: (M s *ᵥ u) i = M s i 0 * u 0 + M s i 1 * u 1`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Rewrite using `[this]`. Establish `hb : ∀ k, ‖M s i k * u k‖ ≤ C * ‖q‖ ^ r` using `fun k => by`.

Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hM s i k)).trans (hu k)`. Use `norm_add_le (M s i 0 * u 0) (M s i 1 * u 1)` as an intermediate fact. Combine the linear relations using `[hb 0, hb 1]`. Establish `h1 : y s i - (M s *ᵥ L Y - L Y) i = (y s i - f r s i) - ((M s *ᵥ u) i - u i)`.

Rewrite using `[hid]`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hy r s i`. Rewrite `h2` using `[norm_pow]`.

Rewrite using `[h1]`. Establish `h3` using `norm_sub_le (y s i - f r s i) ((M s *ᵥ u) i - u i)`. Establish `h4` using `norm_sub_le ((M s *ᵥ u) i) (u i)`. Establish `h5` using `hu i`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlim : Filter.Tendsto (fun r : ℕ => (1 + 3 * C) * ‖q‖ ^ r) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (1 + 3 * C)`. Conclude with `ge_of_tendsto' hlim key`.
-/
theorem coboundary_of_approx {K : Type} [NormedField K] (q : K) (hq : ‖q‖ < 1) (Γ : Type)
    (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) K) (f : ℕ → Γ → Fin 2 → K) (y : Γ → Fin 2 → K)
    (hM : ∀ s i j, ‖M s i j‖ ≤ 1)
    (hf : ∀ r, ∃ v : Fin 2 → K, ∀ s ∈ S, f r s = M s *ᵥ v - v)
    (hy : ∀ r s i, ‖y s i - f r s i‖ ≤ ‖q ^ r‖) :
    ∃ v : Fin 2 → K, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_finset_fixed S M
  let e : (Fin 2 → K) →ₗ[K] (T × Fin 2 → K) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Matrix.toLin' (M p.1) - LinearMap.id)
  have he : ∀ v (p : T × Fin 2), e v p = (M p.1 *ᵥ v - v) p.2 := by
    intro v p
    simp [e, Matrix.toLin'_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective e.rangeRestrict
    (LinearMap.range_rangeRestrict e)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend g
  have heL : ∀ v, e (L (e v)) = e v := by
    intro v
    have h1 : L (e v) = g (e.rangeRestrict v) := LinearMap.congr_fun hL (e.rangeRestrict v)
    have h2 : e.rangeRestrict (g (e.rangeRestrict v)) = e.rangeRestrict v :=
      LinearMap.congr_fun hg (e.rangeRestrict v)
    rw [h1]
    exact congrArg Subtype.val h2
  have hSL : ∀ v, ∀ s ∈ S, M s *ᵥ (L (e v)) - L (e v) = M s *ᵥ v - v := by
    intro v s hs
    have h0 : e (L (e v) - v) = 0 := by rw [map_sub, heL, sub_self]
    have h1 : ∀ t ∈ T, M t *ᵥ (L (e v) - v) = L (e v) - v := by
      intro t ht
      rw [← sub_eq_zero]
      funext i
      have := congrFun h0 (⟨t, ht⟩, i)
      rw [he] at this
      exact this
    have h2 := hT _ h1 s hs
    rw [Matrix.mulVec_sub] at h2
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2
  obtain ⟨C, hC, hCb⟩ := exists_bound L
  let Y : T × Fin 2 → K := fun p => y p.1 p.2
  refine ⟨L Y, fun s hs => ?_⟩
  funext i
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have key : ∀ r : ℕ, ‖y s i - (M s *ᵥ L Y - L Y) i‖ ≤ (1 + 3 * C) * ‖q‖ ^ r := by
    intro r
    obtain ⟨vr, hvr⟩ := hf r
    have hε : 0 ≤ ‖q‖ ^ r := by positivity
    have hu : ∀ k, ‖L (Y - e vr) k‖ ≤ C * ‖q‖ ^ r := by
      refine hCb _ _ hε fun p => ?_
      rw [Pi.sub_apply, he, ← hvr p.1 (hTS p.1.2), ← norm_pow]
      exact hy r p.1 p.2
    have hv : L Y = L (e vr) + L (Y - e vr) := by simp [map_sub]
    generalize L (Y - e vr) = u at hu hv
    have hid : M s *ᵥ L Y - L Y = f r s + (M s *ᵥ u - u) := by
      rw [hvr s hs, ← hSL vr s hs, hv, Matrix.mulVec_add]
      abel
    have hMu : ‖(M s *ᵥ u) i‖ ≤ 2 * (C * ‖q‖ ^ r) := by
      have : (M s *ᵥ u) i = M s i 0 * u 0 + M s i 1 * u 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [this]
      have hb : ∀ k, ‖M s i k * u k‖ ≤ C * ‖q‖ ^ r := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hM s i k)).trans (hu k)
      have := norm_add_le (M s i 0 * u 0) (M s i 1 * u 1)
      linarith [hb 0, hb 1]
    have h1 : y s i - (M s *ᵥ L Y - L Y) i = (y s i - f r s i) - ((M s *ᵥ u) i - u i) := by
      rw [hid]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h2 := hy r s i
    rw [norm_pow] at h2
    rw [h1]
    have h3 := norm_sub_le (y s i - f r s i) ((M s *ᵥ u) i - u i)
    have h4 := norm_sub_le ((M s *ᵥ u) i) (u i)
    have h5 := hu i
    linarith
  have hlim : Filter.Tendsto (fun r : ℕ => (1 + 3 * C) * ‖q‖ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (1 + 3 * C)
  exact ge_of_tendsto' hlim key

/- English proof (translation)
Introduce `l _ Γ S M f y hM hf hy`. Use `coboundary_of_approx ((l : ℕ) : PadicAlgCl l) ?_ Γ S M f y hM hf hy` and prove the remaining obligations. Establish `h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])`. Rewrite using `[map_natCast]`. Establish `h0 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖` using `PadicAlgCl.norm_extends l _`.

Rewrite using `[h, h0]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem coboundary_of_padic_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  intro l _ Γ S M f y hM hf hy
  refine coboundary_of_approx ((l : ℕ) : PadicAlgCl l) ?_ Γ S M f y hM hf hy
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  have h0 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [h, h0]
  exact Padic.norm_p_lt_one

end GlobalTheory.UniformCoboundary
