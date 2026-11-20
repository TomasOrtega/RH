import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

section Norm

variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)

/- English proof (translation)
Introduce `z`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨y, hy1, hy⟩` from `h x (mem_normInteger.1 x.2)`. Use `⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_pow]`.

Rewrite using `[Ideal.Quotient.eq]`. Establish `hmem` using `(mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F)) (x := (⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x) 1).2`. Establish `hle : ‖(((⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x : normInteger F) : F)‖ ≤ ‖((p : normInteger F) : F)‖ ^ 1`. Rewrite using `[pow_one, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, norm_sub_rev]`. Simplify using `using hy`.

Use `hmem hle` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem surjective_pow_of_norm
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖) :
    Function.Surjective (fun x : ModP (normInteger F) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy1, hy⟩ := h x (mem_normInteger.1 x.2)
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  rw [Ideal.Quotient.eq]
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := (⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x) 1).2
  have hle : ‖(((⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x : normInteger F) : F)‖ ≤
      ‖((p : normInteger F) : F)‖ ^ 1 := by
    rw [pow_one, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, norm_sub_rev]
    simpa using hy
  have := hmem hle
  rwa [pow_one] at this

end Norm

section Perfectoid

/- English proof (translation)
Simplify `IsUltrametricDist.norm_add_le_max a (-b)` using `[sub_eq_add_neg]`.
-/
private theorem norm_sub_le_max_of_ultrametric_field {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]

/- English proof (translation)
Take `⟨z, hz⟩` from `IsPerfectoidField.surjective_pow (K := F) (p := p) (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Use `⟨y, mem_normInteger.1 y.2, ?_⟩` and prove the remaining obligations. Establish `hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger F)}) (⟨x, mem_normInteger.2 hx⟩ - y ^ p) = 0`. Rewrite using `[map_sub, map_pow]`.

Conclude with `sub_eq_zero.2 hz.symm`. Rewrite `hz'` using `[Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmem` using `(mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F)) (x := ⟨x, mem_normInteger.2 hx⟩ - y ^ p) 1).1 (by rwa [pow_one])`. Simplify using `using hmem`.
-/
theorem exists_norm_sub_pow_le [IsPerfectoidField F p] {x : F} (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
  obtain ⟨z, hz⟩ := IsPerfectoidField.surjective_pow (K := F) (p := p)
    (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, mem_normInteger.1 y.2, ?_⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger F)}) (⟨x, mem_normInteger.2 hx⟩ - y ^ p)
      = 0 := by
    rw [map_sub, map_pow]
    exact sub_eq_zero.2 hz.symm
  rw [Ideal.Quotient.eq_zero_iff_mem] at hz'
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := ⟨x, mem_normInteger.2 hx⟩ - y ^ p) 1).1 (by rwa [pow_one])
  simpa using hmem

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Distinguish the cases in `h0 : π ^ (p * k) = 0`. Use `⟨z, hz, by simp [pow_nonneg (norm_nonneg π)], ?_⟩` and prove the remaining obligations. Establish `: ‖x - z ^ p‖ ≤ 0` using `by rwa [← norm_pow, h0, norm_zero] at hxz`. Conclude with `this.trans (le_max_of_le_left (pow_nonneg (norm_nonneg _) _))`.

Use `set w := (x - z ^ p) / π ^ (p * k) with hw`. Establish `hw1 : ‖w‖ ≤ 1`. Rewrite using `[hw, norm_div, norm_pow]`. Conclude with `div_le_one_of_le₀ hxz (pow_nonneg (norm_nonneg _) _)`. Take `⟨u, hu1, hu⟩` from `h w hw1`.

Establish `hπk : ‖π ^ k‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ`. Establish `hb1 : ‖π ^ k * u‖ ≤ 1`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hπk (norm_nonneg _) hu1`. Use `⟨z + π ^ k * u, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz hb1)`. Rewrite using `[add_sub_cancel_left, norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hu1`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp (⟨z, mem_normInteger.2 hz⟩ : normInteger F) ⟨π ^ k * u, mem_normInteger.2 hb1⟩`. Establish `hr'` using `congrArg (fun t : normInteger F => (t : F)) hr`.

Simplify using `only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul, SubringClass.coe_natCast] at hr'`. Establish `hr1 : ‖(r : F)‖ ≤ 1` using `mem_normInteger.1 r.2`. Establish `hxw : x - z ^ p = π ^ (p * k) * w`. Rewrite using `[hw, mul_div_cancel₀ _ h0]`. Establish `key : x - (z + π ^ k * u) ^ p = π ^ (p * k) * (w - u ^ p) - (p : F) * z * (π ^ k * u) * r`.

Rewrite using `[hr']`. Establish `: (π ^ k * u) ^ p = π ^ (p * k) * u ^ p`. Rewrite using `[mul_pow, ← pow_mul, mul_comm k p]`. Rewrite using `[this]`. Take the linear combination `hxw`.

Rewrite using `[key]`. Use `(norm_sub_le_max_of_ultrametric_field _ _).trans (max_le_max ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, mul_add, mul_one, pow_add]`. Conclude with `mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]`.

Establish `h1 : ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ ‖π‖ ^ k`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_norm_sub_pow_step {π : F} (hπ : ‖π‖ ≤ 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p)
    {x z : F} (hz : ‖z‖ ≤ 1) {k : ℕ} (hxz : ‖x - z ^ p‖ ≤ ‖π‖ ^ (p * k)) :
    ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ ‖π‖ ^ k ∧
      ‖x - z' ^ p‖ ≤ max (‖π‖ ^ (p * (k + 1))) (‖(p : F)‖ * ‖π‖ ^ k) := by
  have hp : p.Prime := Fact.out
  by_cases h0 : π ^ (p * k) = 0
  · refine ⟨z, hz, by simp [pow_nonneg (norm_nonneg π)], ?_⟩
    have : ‖x - z ^ p‖ ≤ 0 := by rwa [← norm_pow, h0, norm_zero] at hxz
    exact this.trans (le_max_of_le_left (pow_nonneg (norm_nonneg _) _))
  set w := (x - z ^ p) / π ^ (p * k) with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_div, norm_pow]
    exact div_le_one_of_le₀ hxz (pow_nonneg (norm_nonneg _) _)
  obtain ⟨u, hu1, hu⟩ := h w hw1
  have hπk : ‖π ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ
  have hb1 : ‖π ^ k * u‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hπk (norm_nonneg _) hu1
  refine ⟨z + π ^ k * u, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz hb1)
  · rw [add_sub_cancel_left, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hu1
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨z, mem_normInteger.2 hz⟩ : normInteger F)
      ⟨π ^ k * u, mem_normInteger.2 hb1⟩
    have hr' := congrArg (fun t : normInteger F => (t : F)) hr
    simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul,
      SubringClass.coe_natCast] at hr'
    have hr1 : ‖(r : F)‖ ≤ 1 := mem_normInteger.1 r.2
    have hxw : x - z ^ p = π ^ (p * k) * w := by
      rw [hw, mul_div_cancel₀ _ h0]
    have key : x - (z + π ^ k * u) ^ p =
        π ^ (p * k) * (w - u ^ p) - (p : F) * z * (π ^ k * u) * r := by
      rw [hr']
      have : (π ^ k * u) ^ p = π ^ (p * k) * u ^ p := by
        rw [mul_pow, ← pow_mul, mul_comm k p]
      rw [this]
      linear_combination hxw
    rw [key]
    refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul, norm_pow, mul_add, mul_one, pow_add]
      exact mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
      have h1 : ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ ‖π‖ ^ k := by
        calc ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ 1 * (‖π‖ ^ k * 1) * 1 := by
              gcongr
          _ = ‖π‖ ^ k := by ring
      calc ‖(p : F)‖ * ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖
          = ‖(p : F)‖ * (‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖) := by ring
        _ ≤ ‖(p : F)‖ * ‖π‖ ^ k := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Use `set c := ‖π‖ with hc`. Establish `hc0 : 0 ≤ c` using `norm_nonneg _`. Establish `key : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖`. Introduce `x hx`.

Distinguish the cases in `hpz : (p : F) = 0`. Establish `hstep : ∀ (k : ℕ) (z : F), ‖z‖ ≤ 1 → ‖x - z ^ p‖ ≤ c ^ (p * k) → ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ c ^ k ∧ ‖x - z' ^ p‖ ≤ c ^ (p * (k + 1))`. Introduce `k z hz hxz`. Take `⟨z', h1, h2, h3⟩` from `exists_norm_sub_pow_step p hπ.le h hz hxz`. Use `⟨z', h1, h2, h3.trans (max_le le_rfl ?_)⟩` and prove the remaining obligations.

Rewrite using `[hpz, norm_zero, zero_mul]`. Conclude with `pow_nonneg hc0 _`. Set `S : ℕ → Type _` to `fun k => {z : F // ‖z‖ ≤ 1 ∧ ‖x - z ^ p‖ ≤ c ^ (p * k)}`. Set `next : (k : ℕ) → S k → S (k + 1)` to `fun k z => ⟨Classical.choose (hstep k z.1 z.2.1 z.2.2), (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).1, (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.2⟩`. Establish `hnext : ∀ (k : ℕ) (z : S k), ‖(next k z).1 - z.1‖ ≤ c ^ k` using `fun k z => (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.1`.

Establish `base : ‖x - (0 : F) ^ p‖ ≤ c ^ (p * 0)`. Rewrite using `[mul_zero, pow_zero, zero_pow hp0, sub_zero]`. Conclude with `hx`. Set `s : (k : ℕ) → S k` to `fun k => Nat.rec ⟨0, by simp, base⟩ next k`. Set `z : ℕ → F` to `fun k => (s k).1`.

Establish `hdist : ∀ k, dist (z k) (z (k + 1)) ≤ 1 * c ^ k`. Introduce `k`. Rewrite using `[one_mul, dist_comm, dist_eq_norm]`. Conclude with `hnext k (s k)`. Establish `hcau : CauchySeq z` using `cauchySeq_of_le_geometric c 1 hπ hdist`.

Take `⟨L, hL⟩` from `cauchySeq_tendsto_of_complete hcau`. Establish `hL1 : ‖L‖ ≤ 1` using `le_of_tendsto' hL.norm fun k => (s k).2.1`. Use `⟨L, hL1, ?_⟩` and prove the remaining obligations. Establish `ht0 : Filter.Tendsto (fun k => c ^ (p * k)) Filter.atTop (nhds 0)`. Repeatedly rewrite using `[pow_mul]`.

Conclude with `tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hc0 _) (pow_lt_one₀ hc0 hπ hp0)`. Establish `h1 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds 0)` using `squeeze_zero (fun _ => norm_nonneg _) (fun k => (s k).2.2) ht0`. Establish `h2 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds ‖x - L ^ p‖)` using `(tendsto_const_nhds.sub (hL.pow p)).norm`. Rewrite using `[tendsto_nhds_unique h2 h1]`. Conclude with `norm_nonneg _`.

Establish `hpos : 0 < ‖(p : F)‖` using `norm_pos_iff.2 hpz`. Establish `hind : ∀ k : ℕ, ∃ z : F, ‖z‖ ≤ 1 ∧ (‖x - z ^ p‖ ≤ ‖(p : F)‖ ∨ ‖x - z ^ p‖ ≤ c ^ (p * k))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Use `⟨0, by simp, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, pow_zero, zero_pow hp0, sub_zero]`. Conclude with `hx`. Consider the case `succ k ih`. Take `⟨z, hz, hz'⟩` from `ih`.

Break down `hz' with hz' | hz'` into its components or cases. Conclude with `⟨z, hz, Or.inl hz'⟩`. Take `⟨z', h1, -, h3⟩` from `exists_norm_sub_pow_step p hπ.le h hz hz'`. Use `⟨z', h1, ?_⟩` and prove the remaining obligations. Break down `le_total (c ^ (p * (k + 1))) (‖(p : F)‖ * c ^ k) with hle | hle` into its components or cases.

Use `left`. Use `h3.trans ((max_eq_right hle).le.trans ?_)` and prove the remaining obligations. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hc0 hπ.le)`. Use `right`. Conclude with `h3.trans (max_eq_left hle).le`.

Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hpos hπ`. Take `⟨z, hz, hz'⟩` from `hind n`. Use `⟨z, hz, hz'.elim id fun h' => h'.trans ?_⟩` and prove the remaining obligations. Use `le_trans ?_ hn.le` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one hc0 hπ.le (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hp0))`.

Conclude with `{ complete := inferInstance norm_natCast_lt_one := hp exists_norm_mem_Ioo := hnd surjective_pow := surjective_pow_of_norm p key }`.
-/
theorem of_norm_sub_pow_le {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (hnd : ∀ r : ℝ, r < 1 → ∃ x : F, r < ‖x‖ ∧ ‖x‖ < 1) {π : F} (hπ : ‖π‖ < 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p) : IsPerfectoidField F p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set c := ‖π‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _

  have key : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
    intro x hx
    by_cases hpz : (p : F) = 0
    ·
      have hstep : ∀ (k : ℕ) (z : F), ‖z‖ ≤ 1 → ‖x - z ^ p‖ ≤ c ^ (p * k) →
          ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ c ^ k ∧ ‖x - z' ^ p‖ ≤ c ^ (p * (k + 1)) := by
        intro k z hz hxz
        obtain ⟨z', h1, h2, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hxz
        refine ⟨z', h1, h2, h3.trans (max_le le_rfl ?_)⟩
        rw [hpz, norm_zero, zero_mul]
        exact pow_nonneg hc0 _
      let S : ℕ → Type _ := fun k => {z : F // ‖z‖ ≤ 1 ∧ ‖x - z ^ p‖ ≤ c ^ (p * k)}
      let next : (k : ℕ) → S k → S (k + 1) := fun k z =>
        ⟨Classical.choose (hstep k z.1 z.2.1 z.2.2),
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).1,
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.2⟩
      have hnext : ∀ (k : ℕ) (z : S k), ‖(next k z).1 - z.1‖ ≤ c ^ k := fun k z =>
        (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.1
      have base : ‖x - (0 : F) ^ p‖ ≤ c ^ (p * 0) := by
        rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
      let s : (k : ℕ) → S k := fun k => Nat.rec ⟨0, by simp, base⟩ next k
      let z : ℕ → F := fun k => (s k).1
      have hdist : ∀ k, dist (z k) (z (k + 1)) ≤ 1 * c ^ k := by
        intro k
        rw [one_mul, dist_comm, dist_eq_norm]
        exact hnext k (s k)
      have hcau : CauchySeq z := cauchySeq_of_le_geometric c 1 hπ hdist
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
      have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun k => (s k).2.1
      refine ⟨L, hL1, ?_⟩
      have ht0 : Filter.Tendsto (fun k => c ^ (p * k)) Filter.atTop (nhds 0) := by
        simp_rw [pow_mul]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hc0 _)
          (pow_lt_one₀ hc0 hπ hp0)
      have h1 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun k => (s k).2.2) ht0
      have h2 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds ‖x - L ^ p‖) :=
        (tendsto_const_nhds.sub (hL.pow p)).norm
      rw [tendsto_nhds_unique h2 h1]
      exact norm_nonneg _
    ·
      have hpos : 0 < ‖(p : F)‖ := norm_pos_iff.2 hpz
      have hind : ∀ k : ℕ, ∃ z : F, ‖z‖ ≤ 1 ∧
          (‖x - z ^ p‖ ≤ ‖(p : F)‖ ∨ ‖x - z ^ p‖ ≤ c ^ (p * k)) := by
        intro k
        induction k with
        | zero =>
          refine ⟨0, by simp, Or.inr ?_⟩
          rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
        | succ k ih =>
          obtain ⟨z, hz, hz'⟩ := ih
          rcases hz' with hz' | hz'
          · exact ⟨z, hz, Or.inl hz'⟩
          · obtain ⟨z', h1, -, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hz'
            refine ⟨z', h1, ?_⟩
            rcases le_total (c ^ (p * (k + 1))) (‖(p : F)‖ * c ^ k) with hle | hle
            · left
              refine h3.trans ((max_eq_right hle).le.trans ?_)
              exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hc0 hπ.le)
            · right
              exact h3.trans (max_eq_left hle).le
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hπ
      obtain ⟨z, hz, hz'⟩ := hind n
      refine ⟨z, hz, hz'.elim id fun h' => h'.trans ?_⟩
      refine le_trans ?_ hn.le
      exact pow_le_pow_of_le_one hc0 hπ.le (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hp0))
  exact
    { complete := inferInstance
      norm_natCast_lt_one := hp
      exists_norm_mem_Ioo := hnd
      surjective_pow := surjective_pow_of_norm p key }

/- English proof (translation)
Use `completeSpace (K := F) p` as an intermediate fact. Apply the tactic sequence `have hiso : Isometry e := Isometry.of_dist_eq fun x y => by`. Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, he]`. Set `ie : F ≃ᵢ F'` to `{ e.toEquiv with isometry_toFun := hiso }`. Establish `he' : ∀ y, ‖e.symm y‖ = ‖y‖` using `fun y => by conv_rhs => rw [← e.apply_symm_apply y]`.

Rewrite using `[he]`. Establish `hpF : ‖(p : F')‖ = ‖(p : F)‖` using `by rw [← map_natCast e p, he]`. Conclude with `{ complete := ie.symm.completeSpace norm_natCast_lt_one := hpF ▸ norm_natCast_lt_one (K := F) (p := p) exists_norm_mem_Ioo := fun r hr => by`. Take `⟨x, h1, h2⟩` from `exists_norm_mem_Ioo (K := F) (p := p) r hr`. Conclude with `⟨e x, by rwa [he], by rwa [he]⟩`.

Use `surjective_pow := surjective_pow_of_norm p fun y hy => by`. Take `⟨x, hx1, hx⟩` from `exists_norm_sub_pow_le p (x := e.symm y) (by rwa [he'])`. Use `⟨e x, by rwa [he], ?_⟩` and prove the remaining obligations. Establish `hyx : y - e x ^ p = e (e.symm y - x ^ p)`. Rewrite using `[map_sub, map_pow, e.apply_symm_apply]`.

Rewrite using `[hpF, hyx, he]`. Conclude with `hx }`.
-/
theorem of_ringEquiv {F F' : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField F'] [IsUltrametricDist F'] (p : ℕ) [Fact p.Prime]
    [IsPerfectoidField F p] (e : F ≃+* F') (he : ∀ x, ‖e x‖ = ‖x‖) : IsPerfectoidField F' p := by
  have := completeSpace (K := F) p
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, he]
  let ie : F ≃ᵢ F' := { e.toEquiv with isometry_toFun := hiso }
  have he' : ∀ y, ‖e.symm y‖ = ‖y‖ := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [he]
  have hpF : ‖(p : F')‖ = ‖(p : F)‖ := by rw [← map_natCast e p, he]
  exact
    { complete := ie.symm.completeSpace
      norm_natCast_lt_one := hpF ▸ norm_natCast_lt_one (K := F) (p := p)
      exists_norm_mem_Ioo := fun r hr => by
        obtain ⟨x, h1, h2⟩ := exists_norm_mem_Ioo (K := F) (p := p) r hr
        exact ⟨e x, by rwa [he], by rwa [he]⟩
      surjective_pow := surjective_pow_of_norm p fun y hy => by
        obtain ⟨x, hx1, hx⟩ := exists_norm_sub_pow_le p (x := e.symm y) (by rwa [he'])
        refine ⟨e x, by rwa [he], ?_⟩
        have hyx : y - e x ^ p = e (e.symm y - x ^ p) := by
          rw [map_sub, map_pow, e.apply_symm_apply]
        rw [hpF, hyx, he]
        exact hx }

end Perfectoid

end IsPerfectoidField

end GroundTheory.PAdicHodge
