import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace NoncommutativeSwapSum

/- English proof (translation)
Apply the tactic sequence `refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;> simp [nc, ne_comm]`.
-/
lemma nc_swap {n : ℕ} {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p.swap = ∑ p ∈ nc ε, f p := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;> simp [nc, ne_comm]

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `using hS w`.
-/
lemma sumS {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1 = κ • (1 : Module.End ℂ V) - casimirK ε E := by
  ext w
  rw [LinearMap.sum_apply]
  simpa using hS w

/- English proof (translation)
Establish `h1` using `sumS ε E κ hS`. Establish `hc : casimirK ε E * (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) - (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) * casimirK ε E = 0`. Rewrite using `[h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Rewrite `hc` using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`.

Establish `h2 : ∀ p ∈ nc ε, casimirK ε E * (E p.1 p.2 * E p.2 p.1) - E p.1 p.2 * E p.2 p.1 * casimirK ε E = Z ε E p.1 p.2 * E p.2 p.1 + E p.1 p.2 * Z ε E p.2 p.1`. Introduce `p _`. Simplify using `only [Z]`. Use `noncomm_ring`. Rewrite `hc` using `[Finset.sum_congr rfl h2, Finset.sum_add_distrib]`.

Establish `h3 : ∑ p ∈ nc ε, E p.1 p.2 * Z ε E p.2 p.1 = ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2` using `nc_swap ε (fun p => E p.2 p.1 * Z ε E p.1 p.2)`. Rewrite `hc` using `[h3]`. Conclude with `eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hc)`.
-/
lemma key {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 = -∑ p ∈ nc ε, Z ε E p.1 p.2 * E p.2 p.1 := by
  have h1 := sumS ε E κ hS
  have hc : casimirK ε E * (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1)
      - (∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1) * casimirK ε E = 0 := by
    rw [h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at hc
  have h2 : ∀ p ∈ nc ε, casimirK ε E * (E p.1 p.2 * E p.2 p.1) - E p.1 p.2 * E p.2 p.1 * casimirK ε E
      = Z ε E p.1 p.2 * E p.2 p.1 + E p.1 p.2 * Z ε E p.2 p.1 := by
    intro p _
    simp only [Z]
    noncomm_ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib] at hc
  have h3 : ∑ p ∈ nc ε, E p.1 p.2 * Z ε E p.2 p.1 = ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 :=
    nc_swap ε (fun p => E p.2 p.1 * Z ε E p.1 p.2)
  rw [h3] at hc
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hc)

end NoncommutativeSwapSum

/- English proof (translation)
Introduce `h0 h1 h3 h6 n ε V _ _ E hM`. Take `⟨_, _, _, h0c⟩` from `h0 n ε V E hM`. Take `⟨_, _, hE1, _, hcomm, hL2, hZ2⟩` from `h1 n ε V E hM`. Take `⟨κ, hκ⟩` from `h3 n ε V E hM`. Establish `hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w` using `fun w => (h0c κ hκ w).2.2`.

Establish `hWU : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) ∈ U E 2` using `Submodule.sum_mem _ fun p _ => hcomm 1 2 _ (hE1 _ _) _ (hZ2 _ _)`. Take `⟨C1, hC1, hW1⟩` from `h6 n ε V E hM 2 _ hWU`. Establish `hZZ : ∀ p : Fin n × Fin n, casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E ∈ U E 3` using `fun p => hcomm 2 2 _ hL2 _ (hZ2 _ _)`. Use `choose Cp hCp0 hCp using fun p => h6 n ε V E hM 3 _ (hZZ p)`. Establish `hCs : 0 ≤ ∑ p ∈ nc ε, Cp p ^ 2` using `Finset.sum_nonneg fun p _ => sq_nonneg _`.

Use `⟨C1 + ∑ p ∈ nc ε, Cp p ^ 2, by positivity, fun μ v hμ hv => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hT : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) = (2 : ℂ) • ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2`. Rewrite using `[Finset.sum_sub_distrib, NoncommutativeSwapSum.key ε E (κ : ℂ) hS, two_smul]`. Normalize the expressions using the abelian group laws. Establish `hWv` using `hW1 μ v hμ hv`.

Rewrite `hWv` using `[Real.sq_sqrt (by linarith), hT, LinearMap.smul_apply, norm_smul]`. Establish `h2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite `hWv` using `[h2]`. Establish `hTsum : ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v) = -inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)`. Rewrite using `[LinearMap.sum_apply, inner_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hne : ε p.1 ≠ ε p.2` using `(Finset.mem_filter.mp hp).2`. Rewrite using `[hM.uni, adjSign, if_neg hne]`. Simplify using the standard rewrite rules. Establish `hv0` using `norm_nonneg v`.

Establish `hTv0` using `norm_nonneg ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)`. Rewrite using `[hTsum, norm_neg]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hv0` to reduce the goal to its premises. Establish `: 0 ≤ C1 * (1 + μ) * ‖v‖`.

Apply `mul_nonneg (mul_nonneg hC1 (by linarith)) hv0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = C1 * (1 + μ) * ‖v‖ ^ 2 := by ring`. Use `_ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) * ‖v‖ ^ 2 := by`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises.

Apply `mul_le_mul_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : Real.sqrt (1 + μ) ^ 2 = 1 + μ` using `Real.sq_sqrt (by linarith)`. Establish `hp : ∀ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2 ≤ Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2`. Introduce `p _`.

Establish `h` using `hCp p μ v hμ hv`. Establish `hm` using `mul_self_le_mul_self (norm_nonneg _) h`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`.

Use `_ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem a9_of_a0_a1_eigenbasis_a6 : A0 → A1 → CasimirIsRealScalar → A6 → A9 := by
  intro h0 h1 h3 h6 n ε V _ _ E hM
  obtain ⟨_, _, _, h0c⟩ := h0 n ε V E hM
  obtain ⟨_, _, hE1, _, hcomm, hL2, hZ2⟩ := h1 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3 n ε V E hM
  have hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w :=
    fun w => (h0c κ hκ w).2.2
  have hWU : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) ∈ U E 2 :=
    Submodule.sum_mem _ fun p _ => hcomm 1 2 _ (hE1 _ _) _ (hZ2 _ _)
  obtain ⟨C1, hC1, hW1⟩ := h6 n ε V E hM 2 _ hWU
  have hZZ : ∀ p : Fin n × Fin n,
      casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E ∈ U E 3 :=
    fun p => hcomm 2 2 _ hL2 _ (hZ2 _ _)
  choose Cp hCp0 hCp using fun p => h6 n ε V E hM 3 _ (hZZ p)
  have hCs : 0 ≤ ∑ p ∈ nc ε, Cp p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  refine ⟨C1 + ∑ p ∈ nc ε, Cp p ^ 2, by positivity, fun μ v hμ hv => ⟨?_, ?_⟩⟩
  · have hT : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1))
        = (2 : ℂ) • ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 := by
      rw [Finset.sum_sub_distrib, NoncommutativeSwapSum.key ε E (κ : ℂ) hS, two_smul]
      abel
    have hWv := hW1 μ v hμ hv
    rw [Real.sq_sqrt (by linarith), hT, LinearMap.smul_apply, norm_smul] at hWv
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hWv
    have hTsum : ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)
        = -inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v) := by
      rw [LinearMap.sum_apply, inner_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hne : ε p.1 ≠ ε p.2 := (Finset.mem_filter.mp hp).2
      rw [hM.uni, adjSign, if_neg hne]
      simp
    have hv0 := norm_nonneg v
    have hTv0 := norm_nonneg ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)
    rw [hTsum, norm_neg]
    calc ‖inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)‖
        ≤ ‖v‖ * ‖(∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (C1 * (1 + μ) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_left _ hv0
          have : 0 ≤ C1 * (1 + μ) * ‖v‖ := by
            apply mul_nonneg (mul_nonneg hC1 (by linarith)) hv0
          linarith
      _ = C1 * (1 + μ) * ‖v‖ ^ 2 := by ring
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
  · have hs : Real.sqrt (1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
    have hp : ∀ p ∈ nc ε,
        ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          ≤ Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
      intro p _
      have h := hCp p μ v hμ hv
      have hm := mul_self_le_mul_self (norm_nonneg _) h
      calc ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          = ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖
            * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ := sq _
        _ ≤ (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) * (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) := hm
        _ = Cp p ^ 2 * (Real.sqrt (1 + μ) ^ 2) ^ 3 * ‖v‖ ^ 2 := by ring
        _ = Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by rw [hs]
    calc ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
        ≤ ∑ p ∈ nc ε, Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := Finset.sum_le_sum hp
      _ = (∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          linarith

end PositivityTheory.CW

end
