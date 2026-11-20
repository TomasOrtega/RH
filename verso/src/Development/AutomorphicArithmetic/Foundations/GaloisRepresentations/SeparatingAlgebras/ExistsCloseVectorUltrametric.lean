import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

noncomputable section

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `P v hn h`. Distinguish the cases in `hP : P = ⊥`.

Substitute `hP` using the available equality. Use `⟨0, Submodule.zero_mem _, fun i => ?_⟩` and prove the remaining obligations. Establish `key` using `h (Pi.single i 1) ?_ ?_`. Simplify `key` using `[Pi.single_apply]`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Introduce `c hc`.

Establish `hc0 : c = 0` using `by simpa using hc`. Simplify using `[hc0]`. Take `⟨p0, hp0, hp0ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Establish `hex : ∃ i, p0 i ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hp0ne (funext hcon)`. Take `⟨j, hj⟩` from `hex`. Use `haveI : Nonempty X := ⟨j⟩`. Take `⟨i0, hi0⟩` from `Finite.exists_max (fun i => ‖p0 i‖)`.

Establish `hne : p0 i0 ≠ 0`. Introduce `h0`. Establish `h1` using `hi0 j`. Rewrite `h1` using `[h0, norm_zero]`. Conclude with `hj (norm_le_zero_iff.mp h1)`.

Take `⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0` from `⟨_, rfl⟩`. Establish `hpP : p ∈ P` using `hp ▸ P.smul_mem _ hp0`. Establish `hpi0 : p i0 = 1` using `by simp [hp, hne]`. Establish `hple : ∀ i, ‖p i‖ ≤ 1`. Introduce `i`.

Simplify using `only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]`. Rewrite using `[inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]`. Simplify using `using hi0 i`. Take `⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k)` from `⟨_, rfl⟩`. Establish `hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0`.

Introduce `c`. Simplify using `[hP', Submodule.mem_inf, LinearMap.mem_ker]`. Establish `hlt : P' < P`. Use `lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_` and prove the remaining obligations. Introduce `heq`.

Establish `h1 : p ∈ P'` using `heq ▸ hpP`. Establish `h2` using `((hmem p).1 h1).2`. Rewrite `h2` using `[hpi0]`. Conclude with `one_ne_zero h2`. Establish `hfr` using `Submodule.finrank_lt_finrank_of_lt hlt`.

Take `⟨c', hc', hb⟩` from `ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by`. Introduce `a ha hperp`. Take `⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i` from `⟨_, rfl⟩`. Establish `hsn : ‖s‖ ≤ 1`. Rewrite using `[hs]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (ha i) (norm_nonneg _) (hple i)`. Establish `hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0`. Introduce `w`.

Simplify using `[Pi.single_apply, ite_mul]`. Establish `key` using `h (a - Pi.single i0 s : X → k) ?_ ?_`. Establish `e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub, Finset.sum_sub_distrib, hsingle]`. Use `congr 1`.

Rewrite using `[hs, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`. Rewrite `key` using `[e]`. Then use the resulting hypothesis. Introduce `i`. Distinguish the cases in `hi : i = i0`.

Substitute `hi` using the available equality. Simplify using `only [Pi.sub_apply, Pi.single_eq_same]`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]` and apply the resulting hypothesis.

Simplify `ha i` using `[Pi.single_apply, hi]`. Introduce `c hc`. Establish `hd : c - c i0 • p ∈ P'`. Use `(hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩` and prove the remaining obligations. Simplify using `[hpi0]`.

Establish `h0` using `hperp _ hd`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0`. Simplify using `only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]`. Establish `h1 : ∑ i, a i * (c i0 * p i) = c i0 * s`. Rewrite using `[hs, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`. Rewrite `h0` using `[h1]`. Rewrite using `[mul_comm s]`. Conclude with `h0)`. Use `⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩` and prove the remaining obligations.

Establish `e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i`. Simplify using `[sub_sub]`. Rewrite using `[e]`. Conclude with `hb i`.
-/
private theorem exists_close_vector_ultrametric (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (r : ℝ) :
    ∀ (n : ℕ) (P : Submodule k (X → k)) (v : X → k), Module.finrank k P = n →
      (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) →
      ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P v hn h
  by_cases hP : P = ⊥
  · subst hP
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    have key := h (Pi.single i 1) ?_ ?_
    · simpa [Pi.single_apply] using key
    · intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · intro c hc
      have hc0 : c = 0 := by simpa using hc
      simp [hc0]
  · obtain ⟨p0, hp0, hp0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ i, p0 i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp0ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty X := ⟨j⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖p0 i‖)
    have hne : p0 i0 ≠ 0 := by
      intro h0
      have h1 := hi0 j
      rw [h0, norm_zero] at h1
      exact hj (norm_le_zero_iff.mp h1)
    obtain ⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0 := ⟨_, rfl⟩
    have hpP : p ∈ P := hp ▸ P.smul_mem _ hp0
    have hpi0 : p i0 = 1 := by simp [hp, hne]
    have hple : ∀ i, ‖p i‖ ≤ 1 := by
      intro i
      simp only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
      simpa using hi0 i
    obtain ⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k) := ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0 := by
      intro c
      simp [hP', Submodule.mem_inf, LinearMap.mem_ker]
    have hlt : P' < P := by
      refine lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_
      intro heq
      have h1 : p ∈ P' := heq ▸ hpP
      have h2 := ((hmem p).1 h1).2
      rw [hpi0] at h2
      exact one_ne_zero h2
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨c', hc', hb⟩ := ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by
      intro a ha hperp
      obtain ⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i := ⟨_, rfl⟩
      have hsn : ‖s‖ ≤ 1 := by
        rw [hs]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_one₀ (ha i) (norm_nonneg _) (hple i)
      have hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0 := by
        intro w
        simp [Pi.single_apply, ite_mul]
      have key := h (a - Pi.single i0 s : X → k) ?_ ?_
      · have e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
            Finset.sum_sub_distrib, hsingle]
          congr 1
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rwa [e] at key
      · intro i
        by_cases hi : i = i0
        · subst hi
          simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)
          rwa [norm_neg]
        · simpa [Pi.single_apply, hi] using ha i
      · intro c hc
        have hd : c - c i0 • p ∈ P' := by
          refine (hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩
          simp [hpi0]
        have h0 := hperp _ hd
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]
        have h1 : ∑ i, a i * (c i0 * p i) = c i0 * s := by
          rw [hs, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [h1] at h0
        rw [mul_comm s]
        exact h0)
    refine ⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩
    have e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i := by
      simp [sub_sub]
    rw [e]
    exact hb i

/- English proof (translation)
Introduce `k _ _ X _ P v r h`. Conclude with `exists_close_vector_ultrametric k X r _ P v rfl h`.
-/
theorem hB_pf : HB := by
  intro k _ _ X _ P v r h
  exact exists_close_vector_ultrametric k X r _ P v rfl h

end UpperTheory.Gal.Gen

end
