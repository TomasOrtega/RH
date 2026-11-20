import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open Filter Topology Set

/- English proof (translation)
Introduce `hs`. Use `set f : (Fin 2 → ℤ) → ℝ := fun x => ‖x‖ ^ (-(2 * (1 : ℝ))) with hf`. Establish `hnn : ∀ x, 0 ≤ f x` using `fun x => Real.rpow_nonneg (norm_nonneg _) _`. Set `g : ℕ × ℕ → (Fin 2 → ℤ)` to `fun p => ![(p.1 : ℤ) + 1, (p.2 : ℤ)]`. Establish `hg : Function.Injective g`.

Introduce `p q h`. Establish `h0` using `congrFun h 0`. Establish `h1` using `congrFun h 1`. Simplify using `[g] at h0 h1`. Conclude with `Prod.ext (by omega) (by omega)`.

Establish `hsg : Summable (f ∘ g)` using `hs.comp_injective hg`. Establish `hprod : Summable fun a : ℕ => ∑' b : ℕ, (f ∘ g) (a, b)` using `hsg.prod`. Establish `key : ∀ a : ℕ, (1 : ℝ) / ((a : ℝ) + 1) ≤ ∑' b : ℕ, (f ∘ g) (a, b)`. Introduce `a`. Establish `hrow : Summable fun b : ℕ => (f ∘ g) (a, b)` using `hsg.prod_factor a`.

Establish `hterm : ∀ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) = 1 / ((a : ℝ) + 1) ^ 2`. Introduce `b hb`. Establish `hb' : b ≤ a` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)`. Establish `hn : ‖g (a, b)‖ = (a : ℝ) + 1`. Apply `le_antisymm` to reduce the goal to its premises.

Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 ?_` and prove the remaining obligations. Introduce `i`. Use `fin_cases i`. Simplify using `[g, Int.norm_eq_abs]`. Rewrite using `[abs_of_nonneg (by positivity)]`.

Simplify using `[g, Int.norm_eq_abs]`. Establish `: (b : ℝ) ≤ a` using `by exact_mod_cast hb'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `norm_le_pi_norm (g (a, b)) 0`. Establish `h2 : ‖g (a, b) 0‖ = (a : ℝ) + 1`.

Simplify using `[g, Int.norm_eq_abs]`. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Function.comp, hf, hn]`. Rewrite using `[show (-(2 * (1 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `_ = ∑ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) := Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)`.

Use `_ ≤ ∑' b, (f ∘ g) (a, b) := hrow.sum_le_tsum _ (fun b _ => hnn _)`. Establish `hsum : Summable fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1)` using `Summable.of_nonneg_of_le (fun a => by positivity) key hprod`. Establish `hsum' : Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ)`. Simplify `hsum` using `[Nat.cast_add, Nat.cast_one]`. Conclude with `Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum')`.
-/
private lemma not_summable_two : ¬ Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * (1 : ℝ))) := by
  intro hs
  set f : (Fin 2 → ℤ) → ℝ := fun x => ‖x‖ ^ (-(2 * (1 : ℝ))) with hf
  have hnn : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  let g : ℕ × ℕ → (Fin 2 → ℤ) := fun p => ![(p.1 : ℤ) + 1, (p.2 : ℤ)]
  have hg : Function.Injective g := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [g] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hsg : Summable (f ∘ g) := hs.comp_injective hg
  have hprod : Summable fun a : ℕ => ∑' b : ℕ, (f ∘ g) (a, b) := hsg.prod
  have key : ∀ a : ℕ, (1 : ℝ) / ((a : ℝ) + 1) ≤ ∑' b : ℕ, (f ∘ g) (a, b) := by
    intro a
    have hrow : Summable fun b : ℕ => (f ∘ g) (a, b) := hsg.prod_factor a
    have hterm : ∀ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) = 1 / ((a : ℝ) + 1) ^ 2 := by
      intro b hb
      have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hn : ‖g (a, b)‖ = (a : ℝ) + 1 := by
        apply le_antisymm
        · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
          intro i
          fin_cases i
          · simp [g, Int.norm_eq_abs]
            rw [abs_of_nonneg (by positivity)]
          · simp [g, Int.norm_eq_abs]
            have : (b : ℝ) ≤ a := by exact_mod_cast hb'
            linarith
        · have h := norm_le_pi_norm (g (a, b)) 0
          have h2 : ‖g (a, b) 0‖ = (a : ℝ) + 1 := by
            simp [g, Int.norm_eq_abs]
            positivity
          linarith
      simp only [Function.comp, hf, hn]
      rw [show (-(2 * (1 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, one_div]
    calc (1 : ℝ) / ((a : ℝ) + 1)
        = ∑ b ∈ Finset.range (a + 1), 1 / ((a : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
      _ = ∑ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) :=
          Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)
      _ ≤ ∑' b, (f ∘ g) (a, b) := hrow.sum_le_tsum _ (fun b _ => hnn _)
  have hsum : Summable fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun a => by positivity) key hprod
  have hsum' : Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum')

/- English proof (translation)
Unfold `UpperTheory.V.Af.Rs.WTop`. Use `⟨fun t ht => EisensteinSeries.summable_one_div_norm_rpow ht, fun M => ?_⟩` and prove the remaining obligations. Establish `hnn : ∀ (s : ℝ) (x : Fin 2 → ℤ), 0 ≤ ‖x‖ ^ (-(2 * s))` using `fun s x => Real.rpow_nonneg (norm_nonneg _) _`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F : Finset (Fin 2 → ℤ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))) := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `not_summable_two (summable_of_sum_le (hnn 1) h)`. Establish `ht : Tendsto (fun s : ℝ => ∑ x ∈ F, ‖x‖ ^ (-(2 * s))) (𝓝 1) (𝓝 (∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ)))))`. Apply `tendsto_finset_sum` to reduce the goal to its premises. Introduce `x _`.

Establish `hc : ContinuousAt (fun s : ℝ => ‖x‖ ^ (-(2 * s))) 1`. Apply `ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) (g := fun y : ℝ => ‖x‖ ^ y)` to reduce the goal to its premises. Conclude with `Real.continuousAt_const_rpow' (by norm_num)`. Use `fun_prop`. Conclude with `hc`.

Establish `hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * s)) ∧ s ∈ Ioc 1 2`. Use `((ht.eventually (lt_mem_nhds hF)).filter_mono nhdsWithin_le_nhds).and ?_` and prove the remaining obligations. Establish `hI : Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ)` using `Ioo_mem_nhdsGT (by norm_num)`. Use `filter_upwards [hI] with s hs using ⟨hs.1, hs.2.le⟩`. Take `⟨s, hsM, hs⟩` from `hev.exists`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s))` using `EisensteinSeries.summable_one_div_norm_rpow (by linarith [hs.1])`. Conclude with `hsM.le.trans (hsum.sum_le_tsum F (fun x _ => hnn s x))`.
-/
theorem UpperTheory.V.Af.Rs.wTop :
    UpperTheory.V.Af.Rs.WTop := by
  unfold UpperTheory.V.Af.Rs.WTop
  refine ⟨fun t ht => EisensteinSeries.summable_one_div_norm_rpow ht, fun M => ?_⟩
  have hnn : ∀ (s : ℝ) (x : Fin 2 → ℤ), 0 ≤ ‖x‖ ^ (-(2 * s)) :=
    fun s x => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 2 → ℤ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))) := by
    by_contra h
    push_neg at h
    exact not_summable_two (summable_of_sum_le (hnn 1) h)
  have ht : Tendsto (fun s : ℝ => ∑ x ∈ F, ‖x‖ ^ (-(2 * s))) (𝓝 1)
      (𝓝 (∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))))) := by
    apply tendsto_finset_sum
    intro x _
    have hc : ContinuousAt (fun s : ℝ => ‖x‖ ^ (-(2 * s))) 1 := by
      apply ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) (g := fun y : ℝ => ‖x‖ ^ y)
      · exact Real.continuousAt_const_rpow' (by norm_num)
      · fun_prop
    exact hc
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * s)) ∧ s ∈ Ioc 1 2 := by
    refine ((ht.eventually (lt_mem_nhds hF)).filter_mono nhdsWithin_le_nhds).and ?_
    have hI : Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with s hs using ⟨hs.1, hs.2.le⟩
  obtain ⟨s, hsM, hs⟩ := hev.exists
  refine ⟨s, hs, ?_⟩
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith [hs.1])
  exact hsM.le.trans (hsum.sum_le_tsum F (fun x _ => hnn s x))
