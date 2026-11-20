import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

/- English proof (translation)
Unfold `CVXStatement`. Introduce `K hanti hne hcl hmid hb`. Take `⟨R, hR⟩` from `isBounded_iff_forall_norm_le.1 hb`. Establish `hbdd : ∀ n, BddBelow ((fun w : H => ‖w‖) '' K n)` using `fun n => ⟨0, by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w⟩`. Establish `hSne : ∀ n, ((fun w : H => ‖w‖) '' K n).Nonempty` using `fun n => (hne n).image _`.

Take `⟨d, hd⟩ : ∃ d : ℕ → ℝ, d = fun n => sInf ((fun w : H => ‖w‖) '' K n)` from `⟨_, rfl⟩`. Establish `hdle : ∀ n, ∀ w ∈ K n, d n ≤ ‖w‖`. Introduce `n w hw`. Rewrite using `[hd]`. Conclude with `csInf_le (hbdd n) ⟨w, hw, rfl⟩`.

Establish `hd0 : ∀ n, 0 ≤ d n`. Introduce `n`. Rewrite using `[hd]`. Conclude with `le_csInf (hSne n) (by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w)`. Establish `hdmono : Monotone d`.

Introduce `n m hnm`. Rewrite using `[hd]`. Conclude with `csInf_le_csInf (hbdd n) (hSne m) (Set.image_mono (hanti hnm))`. Establish `hdR : ∀ n, d n ≤ R`. Introduce `n`.

Take `⟨w, hw⟩` from `hne n`. Conclude with `(hdle n w hw).trans (hR w (hanti (Nat.zero_le n) hw))`. Establish `happrox : ∀ n, ∃ w ∈ K n, ‖w‖ < d n + 1 / ((n : ℝ) + 1)`. Introduce `n`. Establish `hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1)` using `by positivity`.

Establish `hlt : sInf ((fun w : H => ‖w‖) '' K n) < d n + 1 / ((n : ℝ) + 1)`. Rewrite using `[hd]`. Conclude with `lt_add_of_pos_right _ hpos`. Take `⟨_, ⟨w, hw, rfl⟩, hw2⟩` from `exists_lt_of_csInf_lt (hSne n) hlt`. Conclude with `⟨w, hw, hw2⟩`.

Use `choose x hxK hxn using happrox`. Establish `hbddA : BddAbove (Set.range d)` using `⟨R, by rintro _ ⟨n, rfl⟩; exact hdR n⟩`. Take `⟨L, hL⟩ : ∃ L, L = ⨆ n, d n` from `⟨_, rfl⟩`. Establish `hdL : ∀ n, d n ≤ L` using `fun n => by rw [hL]; exact le_ciSup hbddA n`. Establish `hL0 : 0 ≤ L` using `(hd0 0).trans (hdL 0)`.

Establish `hkey : ∀ n m, n ≤ m → ‖x m - x n‖ ^ 2 ≤ 2 * ‖x m‖ ^ 2 + 2 * ‖x n‖ ^ 2 - 4 * d n ^ 2`. Introduce `n m hnm`. Establish `hmK : x m ∈ K n` using `hanti hnm (hxK m)`. Establish `h1` using `hdle n _ (hmid n (x m) hmK (x n) (hxK n))`. Establish `h2 : ‖x m + x n‖ = 2 * ‖(2 : ℂ)⁻¹ • (x m + x n)‖` using `by first`.

Consider the case `(rw [norm_smul, norm_inv, Complex.norm_two]; ring)`. Consider the case `(rw [norm_smul]; norm_num)`. Consider the case `(simp [norm_smul]; ring)`. Establish `h3 : 4 * d n ^ 2 ≤ ‖x m + x n‖ ^ 2`. Rewrite using `[h2]`.

Use polynomial arithmetic with `[h1, hd0 n]`. Establish `hpar` using `parallelogram_law_with_norm ℂ (x m) (x n)`. Use polynomial arithmetic with `[hpar, h3]`. Establish `hcauchy : CauchySeq x`. Rewrite using `[Metric.cauchySeq_iff']`.

Introduce `ε hε`. Take `⟨η, hηdef⟩ : ∃ η, η = min 1 (ε ^ 2 / (16 * (L + 1)))` from `⟨_, rfl⟩`. Establish `hη0 : 0 < η` using `by rw [hηdef]; exact lt_min one_pos (by positivity)`. Establish `hη1 : η ≤ 1` using `by rw [hηdef]; exact min_le_left _ _`. Establish `hηε : η ≤ ε ^ 2 / (16 * (L + 1))` using `by rw [hηdef]; exact min_le_right _ _`.

Take `⟨N₁, hN₁⟩` from `exists_lt_of_lt_ciSup (f := d) (by rw [← hL]; linarith : L - η < ⨆ n, d n)`. Take `⟨N₂, hN₂⟩` from `exists_nat_one_div_lt hη0`. Use `⟨max N₁ N₂, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hdN : L - η < d (max N₁ N₂)` using `hN₁.trans_le (hdmono (le_max_left _ _))`. Establish `heN : 1 / (((max N₁ N₂ : ℕ) : ℝ) + 1) < η`.

Use `lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂` and prove the remaining obligations. Establish `: (N₂ : ℝ) ≤ ((max N₁ N₂ : ℕ) : ℝ)` using `by exact_mod_cast le_max_right N₁ N₂`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hem : 1 / ((m : ℝ) + 1) < η`. Use `lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂` and prove the remaining obligations.

Establish `: (N₂ : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast (le_max_right N₁ N₂).trans hm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `hkey (max N₁ N₂) m hm`. Establish `hxm` using `hxn m`. Establish `hxN` using `hxn (max N₁ N₂)`.

Establish `hdm` using `hdL m`. Establish `hdNL` using `hdL (max N₁ N₂)`. Establish `hd0N` using `hd0 (max N₁ N₂)`. Establish `a1 : ‖x m‖ < L + η` using `by linarith`. Establish `a2 : ‖x (max N₁ N₂)‖ < d (max N₁ N₂) + η` using `by linarith`.

Establish `b1 : ‖x m‖ ^ 2 ≤ (L + η) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) a1.le 2`. Establish `b2 : ‖x (max N₁ N₂)‖ ^ 2 ≤ (d (max N₁ N₂) + η) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) a2.le 2`. Establish `c0 : 0 ≤ (d (max N₁ N₂) - L + η) * (d (max N₁ N₂) + L)` using `mul_nonneg (by linarith) (by linarith)`. Establish `c1 : d (max N₁ N₂) * η ≤ L * η` using `mul_le_mul_of_nonneg_right hdNL hη0.le`. Establish `c2 : η * η ≤ η * 1` using `mul_le_mul_of_nonneg_left hη1 hη0.le`.

Establish `c3 : 0 ≤ L * η` using `mul_nonneg hL0 hη0.le`. Establish `b3 : L ^ 2 - 2 * L * η ≤ d (max N₁ N₂) ^ 2` using `by nlinarith`. Establish `b4 : η * (16 * (L + 1)) ≤ ε ^ 2` using `(le_div_iff₀ (by positivity)).1 hηε`. Establish `hsq : ‖x m - x (max N₁ N₂)‖ ^ 2 < ε ^ 2` using `by nlinarith`. Rewrite using `[dist_eq_norm]`.

Use polynomial arithmetic with `[norm_nonneg (x m - x (max N₁ N₂))]`. Take `⟨y, hy⟩` from `cauchySeq_tendsto_of_complete hcauchy`. Use `⟨y, fun n => ?_⟩` and prove the remaining obligations. Apply `(hcl n).mem_of_tendsto hy` to reduce the goal to its premises. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm`.

Conclude with `hanti hm (hxK m)`.
-/
theorem cvx (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CVXStatement H := by
  unfold CVXStatement
  intro K hanti hne hcl hmid hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hbdd : ∀ n, BddBelow ((fun w : H => ‖w‖) '' K n) :=
    fun n => ⟨0, by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w⟩
  have hSne : ∀ n, ((fun w : H => ‖w‖) '' K n).Nonempty := fun n => (hne n).image _
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, d = fun n => sInf ((fun w : H => ‖w‖) '' K n) := ⟨_, rfl⟩
  have hdle : ∀ n, ∀ w ∈ K n, d n ≤ ‖w‖ := by
    intro n w hw; rw [hd]; exact csInf_le (hbdd n) ⟨w, hw, rfl⟩
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n; rw [hd]
    exact le_csInf (hSne n) (by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w)
  have hdmono : Monotone d := by
    intro n m hnm; rw [hd]
    exact csInf_le_csInf (hbdd n) (hSne m) (Set.image_mono (hanti hnm))
  have hdR : ∀ n, d n ≤ R := by
    intro n
    obtain ⟨w, hw⟩ := hne n
    exact (hdle n w hw).trans (hR w (hanti (Nat.zero_le n) hw))
  have happrox : ∀ n, ∃ w ∈ K n, ‖w‖ < d n + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf ((fun w : H => ‖w‖) '' K n) < d n + 1 / ((n : ℝ) + 1) := by
      rw [hd]; exact lt_add_of_pos_right _ hpos
    obtain ⟨_, ⟨w, hw, rfl⟩, hw2⟩ := exists_lt_of_csInf_lt (hSne n) hlt
    exact ⟨w, hw, hw2⟩
  choose x hxK hxn using happrox
  have hbddA : BddAbove (Set.range d) := ⟨R, by rintro _ ⟨n, rfl⟩; exact hdR n⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ⨆ n, d n := ⟨_, rfl⟩
  have hdL : ∀ n, d n ≤ L := fun n => by rw [hL]; exact le_ciSup hbddA n
  have hL0 : 0 ≤ L := (hd0 0).trans (hdL 0)
  have hkey : ∀ n m, n ≤ m → ‖x m - x n‖ ^ 2 ≤ 2 * ‖x m‖ ^ 2 + 2 * ‖x n‖ ^ 2 - 4 * d n ^ 2 := by
    intro n m hnm
    have hmK : x m ∈ K n := hanti hnm (hxK m)
    have h1 := hdle n _ (hmid n (x m) hmK (x n) (hxK n))
    have h2 : ‖x m + x n‖ = 2 * ‖(2 : ℂ)⁻¹ • (x m + x n)‖ := by
      first
        | (rw [norm_smul, norm_inv, Complex.norm_two]; ring)
        | (rw [norm_smul]; norm_num)
        | (simp [norm_smul]; ring)
    have h3 : 4 * d n ^ 2 ≤ ‖x m + x n‖ ^ 2 := by
      rw [h2]; nlinarith [h1, hd0 n]
    have hpar := parallelogram_law_with_norm ℂ (x m) (x n)
    nlinarith [hpar, h3]
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨η, hηdef⟩ : ∃ η, η = min 1 (ε ^ 2 / (16 * (L + 1))) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hηdef]; exact lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
    have hηε : η ≤ ε ^ 2 / (16 * (L + 1)) := by rw [hηdef]; exact min_le_right _ _
    obtain ⟨N₁, hN₁⟩ := exists_lt_of_lt_ciSup (f := d) (by rw [← hL]; linarith : L - η < ⨆ n, d n)
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hη0
    refine ⟨max N₁ N₂, fun m hm => ?_⟩
    have hdN : L - η < d (max N₁ N₂) := hN₁.trans_le (hdmono (le_max_left _ _))
    have heN : 1 / (((max N₁ N₂ : ℕ) : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ ((max N₁ N₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right N₁ N₂
      linarith
    have hem : 1 / ((m : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N₁ N₂).trans hm
      linarith
    have hk := hkey (max N₁ N₂) m hm
    have hxm := hxn m
    have hxN := hxn (max N₁ N₂)
    have hdm := hdL m
    have hdNL := hdL (max N₁ N₂)
    have hd0N := hd0 (max N₁ N₂)
    have a1 : ‖x m‖ < L + η := by linarith
    have a2 : ‖x (max N₁ N₂)‖ < d (max N₁ N₂) + η := by linarith
    have b1 : ‖x m‖ ^ 2 ≤ (L + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1.le 2
    have b2 : ‖x (max N₁ N₂)‖ ^ 2 ≤ (d (max N₁ N₂) + η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) a2.le 2
    have c0 : 0 ≤ (d (max N₁ N₂) - L + η) * (d (max N₁ N₂) + L) :=
      mul_nonneg (by linarith) (by linarith)
    have c1 : d (max N₁ N₂) * η ≤ L * η := mul_le_mul_of_nonneg_right hdNL hη0.le
    have c2 : η * η ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
    have c3 : 0 ≤ L * η := mul_nonneg hL0 hη0.le
    have b3 : L ^ 2 - 2 * L * η ≤ d (max N₁ N₂) ^ 2 := by nlinarith
    have b4 : η * (16 * (L + 1)) ≤ ε ^ 2 := (le_div_iff₀ (by positivity)).1 hηε
    have hsq : ‖x m - x (max N₁ N₂)‖ ^ 2 < ε ^ 2 := by nlinarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x m - x (max N₁ N₂))]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, fun n => ?_⟩
  apply (hcl n).mem_of_tendsto hy
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact hanti hm (hxK m)

end ReciprocityTheory.L2DbarEstimates
