import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SegCone

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `t ht hn`. Use `set S := Finset.univ.filter (fun i => t i ≠ 0) with hS`. Establish `hSt : ∀ i, i ∉ S → t i = 0` using `fun i hi => by simpa [hS] using hi`.

Distinguish the cases in `hli : LinearIndepOn ℝ v (S : Set ι)`. Conclude with `⟨S, t, hli, ht, hSt, rfl⟩`. Rewrite `hli` using `[linearIndepOn_finset_iff]`. Use `push_neg at hli`. Take `⟨f, hf0, i₀, hi₀, hfi₀⟩` from `hli`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg0, hgS, hgpos⟩ : ∃ g : ι → ℝ, (∑ i, g i • v i = 0) ∧ (∀ i, i ∉ S → g i = 0) ∧ 0 < g i₀ := by`. Use `⟨fun i => if i ∈ S then f i * f i₀ else 0, ?_, fun i hi => by simp [hi], ?_⟩` and prove the remaining obligations. Establish `: ∑ i, (if i ∈ S then f i * f i₀ else 0) • v i = ∑ i ∈ S, (f i * f i₀) • v i`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]`. Conclude with `Finset.sum_congr rfl fun i hi => by simp [hi]`.

Rewrite using `[this]`. Establish `h2 : ∑ i ∈ S, (f i * f i₀) • v i = f i₀ • ∑ i ∈ S, f i • v i`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]`. Rewrite using `[h2, hf0, smul_zero]`.

Simplify using `only [hi₀, if_true]`. Conclude with `mul_self_pos.mpr hfi₀`. Establish `hP : (S.filter (fun i => 0 < g i)).Nonempty` using `⟨i₀, by simp [hi₀, hgpos]⟩`. Take `⟨j, hjP, hjmin⟩` from `Finset.exists_min_image _ (fun i => t i / g i) hP`. Establish `hjS : j ∈ S` using `(Finset.mem_filter.mp hjP).1`.

Establish `hgj : 0 < g j` using `(Finset.mem_filter.mp hjP).2`. Use `set l := t j / g j with hl`. Establish `hl0 : 0 ≤ l` using `div_nonneg (ht j) hgj.le`. Establish `ht' : ∀ i, 0 ≤ t i - l * g i` using `fun i => by`. Distinguish the cases in `hgi : 0 < g i`.

Establish `hiS : i ∈ S`. Assume the negation of the conclusion as `hi`. Rewrite `hgi` using `[hgS i hi]`. Conclude with `lt_irrefl _ hgi`. Use `hjmin i (Finset.mem_filter.mpr ⟨hiS, hgi⟩)` as an intermediate fact.

Establish `h3 : l * g i ≤ t i` using `(le_div_iff₀ hgi).mp this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: l * g i ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hl0 (not_lt.mp hgi)`. Combine the linear relations using `[ht i]`. Establish `hlt : (Finset.univ.filter (fun i => t i - l * g i ≠ 0)).card < n`.

Rewrite using `[← hn]`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨j, hjS, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]`.

Rewrite using `[hl, div_mul_cancel₀ _ hgj.ne', sub_self]`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi`. Assume the negation of the conclusion as `hiS`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[hSt i hiS, hgS i hiS]`. Simplify using the standard rewrite rules. Take `⟨S', s, h1, h2, h3, h4⟩` from `ih _ hlt (fun i => t i - l * g i) ht' (by congr)`. Use `⟨S', s, h1, h2, h3, h4.trans ?_⟩` and prove the remaining obligations. Establish `: ∑ i, (t i - l * g i) • v i = ∑ i, t i • v i - l • ∑ i, g i • v i`.

Rewrite using `[Finset.smul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [sub_smul, mul_smul]`. Rewrite using `[this, hg0, smul_zero, sub_zero]`.
-/
theorem exists_indep_rep (v : ι → V) (n : ℕ) : ∀ (t : ι → ℝ), (∀ i, 0 ≤ t i) →
    (by classical exact (Finset.univ.filter (fun i => t i ≠ 0)).card) = n →
    ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
      ∑ i, s i • v i = ∑ i, t i • v i := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ht hn
  set S := Finset.univ.filter (fun i => t i ≠ 0) with hS
  have hSt : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  by_cases hli : LinearIndepOn ℝ v (S : Set ι)
  · exact ⟨S, t, hli, ht, hSt, rfl⟩
  rw [linearIndepOn_finset_iff] at hli
  push_neg at hli
  obtain ⟨f, hf0, i₀, hi₀, hfi₀⟩ := hli
  obtain ⟨g, hg0, hgS, hgpos⟩ : ∃ g : ι → ℝ, (∑ i, g i • v i = 0) ∧ (∀ i, i ∉ S → g i = 0) ∧ 0 < g i₀ := by
    refine ⟨fun i => if i ∈ S then f i * f i₀ else 0, ?_, fun i hi => by simp [hi], ?_⟩
    · have : ∑ i, (if i ∈ S then f i * f i₀ else 0) • v i = ∑ i ∈ S, (f i * f i₀) • v i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi => by simp [hi])]
        exact Finset.sum_congr rfl fun i hi => by simp [hi]
      rw [this]
      have h2 : ∑ i ∈ S, (f i * f i₀) • v i = f i₀ • ∑ i ∈ S, f i • v i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
      rw [h2, hf0, smul_zero]
    · simp only [hi₀, if_true]
      exact mul_self_pos.mpr hfi₀
  have hP : (S.filter (fun i => 0 < g i)).Nonempty := ⟨i₀, by simp [hi₀, hgpos]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image _ (fun i => t i / g i) hP
  have hjS : j ∈ S := (Finset.mem_filter.mp hjP).1
  have hgj : 0 < g j := (Finset.mem_filter.mp hjP).2
  set l := t j / g j with hl
  have hl0 : 0 ≤ l := div_nonneg (ht j) hgj.le
  have ht' : ∀ i, 0 ≤ t i - l * g i := fun i => by
    by_cases hgi : 0 < g i
    · have hiS : i ∈ S := by
        by_contra hi
        rw [hgS i hi] at hgi
        exact lt_irrefl _ hgi
      have := hjmin i (Finset.mem_filter.mpr ⟨hiS, hgi⟩)
      have h3 : l * g i ≤ t i := (le_div_iff₀ hgi).mp this
      linarith
    · have : l * g i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0 (not_lt.mp hgi)
      linarith [ht i]
  have hlt : (Finset.univ.filter (fun i => t i - l * g i ≠ 0)).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, hjS, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [hl, div_mul_cancel₀ _ hgj.ne', sub_self]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiS
      apply hi
      rw [hSt i hiS, hgS i hiS]
      simp
  obtain ⟨S', s, h1, h2, h3, h4⟩ := ih _ hlt (fun i => t i - l * g i) ht' (by congr)
  refine ⟨S', s, h1, h2, h3, h4.trans ?_⟩
  have : ∑ i, (t i - l * g i) • v i = ∑ i, t i • v i - l • ∑ i, g i • v i := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul, mul_smul]
  rw [this, hg0, smul_zero, sub_zero]

/- English proof (translation)
Establish `hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1)` using `fun k => by positivity`. Establish `h' : ∀ k : ℕ, ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧ B + (1 / ((k : ℝ) + 1)) • B₀ = ∑ i, s i • v i` using `fun k => by`. Take `⟨t, ht, hx⟩` from `h _ (hpos k)`. Take `⟨S, s, h1, h2, h3, h4⟩` from `exists_indep_rep v _ t ht rfl`. Conclude with `⟨S, s, h1, h2, h3, hx.trans h4.symm⟩`.

Use `choose S s hli hs hS hx using h'`. Take `⟨S₀, hinf⟩` from `Finite.exists_infinite_fiber S`. Establish `hI : (S ⁻¹' {S₀}).Infinite` using `Set.infinite_coe_iff.mp hinf`. Take `⟨k₁, hk₁, k₂, hk₂, hne⟩` from `hI.nontrivial`. Establish `hk₁' : S k₁ = S₀` using `hk₁`.

Establish `hk₂' : S k₂ = S₀` using `hk₂`. Use `set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε`. Establish `hd : ε k₁ - ε k₂ ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `h1 : ε k₁ = ε k₂` using `sub_eq_zero.mp h0`. Simplify using `only [hε] at h1`. Establish `h2 : (k₁ : ℝ) + 1 ≠ 0` using `by positivity`. Establish `h3 : (k₂ : ℝ) + 1 ≠ 0` using `by positivity`. Clear denominators, using `at h1` for the nonvanishing conditions.

Establish `: (k₂ : ℝ) = k₁` using `by linarith`. Conclude with `this.symm` after adjusting the coercions. Use `set b : ι → ℝ := fun i => (s k₁ i - s k₂ i) / (ε k₁ - ε k₂) with hb`. Use `set a : ι → ℝ := fun i => s k₁ i - ε k₁ * b i with ha`. Establish `hB₀ : B₀ = ∑ i, b i • v i`.

Establish `h1 : (ε k₁ - ε k₂) • B₀ = ∑ i, (s k₁ i - s k₂ i) • v i`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, ← hx k₁, ← hx k₂]`. Simplify using `only [hε]`. Normalize the expressions using the abelian group laws. Establish `h2 : B₀ = (ε k₁ - ε k₂)⁻¹ • ∑ i, (s k₁ i - s k₂ i) • v i`.

Rewrite using `[← h1, smul_smul, inv_mul_cancel₀ hd, one_smul]`. Rewrite using `[h2, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, hb]`. Use `congr 1`.

Simplify using `only`. Rewrite using `[div_eq_mul_inv, mul_comm]`. Establish `hB : B = ∑ i, a i • v i`. Establish `h1 : ∑ i, a i • v i = ∑ i, s k₁ i • v i - ε k₁ • ∑ i, b i • v i`. Rewrite using `[Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [ha]; simp only; rw [sub_smul, mul_smul]`. Rewrite using `[h1, ← hB₀, ← hx k₁]`. Simplify using `only [hε]`. Normalize the expressions using the abelian group laws. Establish `hb0 : ∀ i, i ∉ S₀ → b i = 0` using `fun i hi => by`.

Simplify using `only [hb]`. Rewrite using `[hS k₁ i (hk₁' ▸ hi), hS k₂ i (hk₂' ▸ hi)]`. Simplify using the standard rewrite rules. Establish `ha0 : ∀ i, i ∉ S₀ → a i = 0` using `fun i hi => by`. Simplify using `only [ha]`.

Rewrite using `[hb0 i hi, hS k₁ i (hk₁' ▸ hi)]`. Simplify using the standard rewrite rules. Establish `hcoord : ∀ k, S k = S₀ → ∀ i ∈ S₀, 0 ≤ a i + ε k * b i` using `fun k hk i hi => by`. Establish `hz : ∑ j ∈ S₀, (a j + ε k * b j - s k j) • v j = 0`. Rewrite using `[Finset.sum_subset (Finset.subset_univ S₀) (fun j _ hj => by`.

Rewrite using `[ha0 j hj, hb0 j hj, hS k j (hk ▸ hj)]`. Use the proof step `simp)]`. Establish `h1 : ∑ j, (a j + ε k * b j - s k j) • v j = ∑ j, a j • v j + ε k • ∑ j, b j • v j - ∑ j, s k j • v j`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [sub_smul, add_smul, mul_smul]`.

Rewrite using `[h1, ← hB, ← hB₀, ← hx k]`. Simplify using `only [hε]`. Normalize the expressions using the abelian group laws. Establish `hl` using `hli k`. Rewrite `hl` using `[hk, linearIndepOn_finset_iff]`.

Use `hl _ hz i hi` as an intermediate fact. Establish `h0` using `hs k i`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨a, fun i => ?_, hB⟩` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ S₀`.

Assume the negation of the conclusion as `hneg`. Establish `hai : a i < 0` using `not_le.mp hneg`. Take `⟨N, hN⟩` from `exists_nat_gt (|b i| / (-a i))`. Take `⟨k, hk, hNk⟩` from `hI.exists_gt N`. Establish `hc` using `hcoord k hk i hi`.

Establish `hna : 0 < -a i` using `by linarith`. Establish `h1 : |b i| < N * (-a i)` using `(div_lt_iff₀ hna).mp hN`. Establish `h2 : (N : ℝ) < (k : ℝ) + 1`. Establish `: (N : ℝ) < k` using `by exact_mod_cast hNk`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hk1 : (0 : ℝ) < (k : ℝ) + 1` using `by positivity`. Establish `h3 : |b i| < ((k : ℝ) + 1) * (-a i)` using `lt_trans h1 (mul_lt_mul_of_pos_right h2 hna)`. Establish `h4 : ε k * b i < -a i`. Simplify using `only [hε]`. Rewrite using `[one_div, inv_mul_lt_iff₀ hk1]`.

Conclude with `lt_of_le_of_lt (le_abs_self _) h3`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[ha0 i hi]`.
-/
theorem seg_mem_cone (v : ι → V) (B B₀ : V)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B + ε • B₀ = ∑ i, t i • v i) :
    ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • v i := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have h' : ∀ k : ℕ, ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧
      (∀ i, i ∉ S → s i = 0) ∧ B + (1 / ((k : ℝ) + 1)) • B₀ = ∑ i, s i • v i := fun k => by
    obtain ⟨t, ht, hx⟩ := h _ (hpos k)
    obtain ⟨S, s, h1, h2, h3, h4⟩ := exists_indep_rep v _ t ht rfl
    exact ⟨S, s, h1, h2, h3, hx.trans h4.symm⟩
  choose S s hli hs hS hx using h'
  obtain ⟨S₀, hinf⟩ := Finite.exists_infinite_fiber S
  have hI : (S ⁻¹' {S₀}).Infinite := Set.infinite_coe_iff.mp hinf
  obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hI.nontrivial
  have hk₁' : S k₁ = S₀ := hk₁
  have hk₂' : S k₂ = S₀ := hk₂
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hd : ε k₁ - ε k₂ ≠ 0 := by
    intro h0
    apply hne
    have h1 : ε k₁ = ε k₂ := sub_eq_zero.mp h0
    simp only [hε] at h1
    have h2 : (k₁ : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (k₂ : ℝ) + 1 ≠ 0 := by positivity
    field_simp at h1
    have : (k₂ : ℝ) = k₁ := by linarith
    exact_mod_cast this.symm
  set b : ι → ℝ := fun i => (s k₁ i - s k₂ i) / (ε k₁ - ε k₂) with hb
  set a : ι → ℝ := fun i => s k₁ i - ε k₁ * b i with ha
  have hB₀ : B₀ = ∑ i, b i • v i := by
    have h1 : (ε k₁ - ε k₂) • B₀ = ∑ i, (s k₁ i - s k₂ i) • v i := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hx k₁, ← hx k₂]
      simp only [hε]
      abel
    have h2 : B₀ = (ε k₁ - ε k₂)⁻¹ • ∑ i, (s k₁ i - s k₂ i) • v i := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hb]
    congr 1
    simp only
    rw [div_eq_mul_inv, mul_comm]
  have hB : B = ∑ i, a i • v i := by
    have h1 : ∑ i, a i • v i = ∑ i, s k₁ i • v i - ε k₁ • ∑ i, b i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; simp only; rw [sub_smul, mul_smul]
    rw [h1, ← hB₀, ← hx k₁]
    simp only [hε]
    abel
  have hb0 : ∀ i, i ∉ S₀ → b i = 0 := fun i hi => by
    simp only [hb]
    rw [hS k₁ i (hk₁' ▸ hi), hS k₂ i (hk₂' ▸ hi)]
    simp
  have ha0 : ∀ i, i ∉ S₀ → a i = 0 := fun i hi => by
    simp only [ha]
    rw [hb0 i hi, hS k₁ i (hk₁' ▸ hi)]
    simp
  have hcoord : ∀ k, S k = S₀ → ∀ i ∈ S₀, 0 ≤ a i + ε k * b i := fun k hk i hi => by
    have hz : ∑ j ∈ S₀, (a j + ε k * b j - s k j) • v j = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ S₀) (fun j _ hj => by
        rw [ha0 j hj, hb0 j hj, hS k j (hk ▸ hj)]; simp)]
      have h1 : ∑ j, (a j + ε k * b j - s k j) • v j =
          ∑ j, a j • v j + ε k • ∑ j, b j • v j - ∑ j, s k j • v j := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [sub_smul, add_smul, mul_smul]
      rw [h1, ← hB, ← hB₀, ← hx k]
      simp only [hε]
      abel
    have hl := hli k
    rw [hk, linearIndepOn_finset_iff] at hl
    have := hl _ hz i hi
    have h0 := hs k i
    linarith
  refine ⟨a, fun i => ?_, hB⟩
  by_cases hi : i ∈ S₀
  · by_contra hneg
    have hai : a i < 0 := not_le.mp hneg
    obtain ⟨N, hN⟩ := exists_nat_gt (|b i| / (-a i))
    obtain ⟨k, hk, hNk⟩ := hI.exists_gt N
    have hc := hcoord k hk i hi
    have hna : 0 < -a i := by linarith
    have h1 : |b i| < N * (-a i) := (div_lt_iff₀ hna).mp hN
    have h2 : (N : ℝ) < (k : ℝ) + 1 := by
      have : (N : ℝ) < k := by exact_mod_cast hNk
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : |b i| < ((k : ℝ) + 1) * (-a i) := lt_trans h1 (mul_lt_mul_of_pos_right h2 hna)
    have h4 : ε k * b i < -a i := by
      simp only [hε]
      rw [one_div, inv_mul_lt_iff₀ hk1]
      exact lt_of_le_of_lt (le_abs_self _) h3
    linarith
  · rw [ha0 i hi]

end SegCone

/- English proof (translation)
The claim follows from `seg_mem_cone (fun i => toReal (γ i)) B B₀ h`.
-/
theorem rcone_closed_seg (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (h : ∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) : B ∈ rcone γ :=
  seg_mem_cone (fun i => toReal (γ i)) B B₀ h

end GlobalTheory.CompanionTheory.Ar.Fan
