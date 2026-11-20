import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

/- English proof (translation)
Rewrite using `[tendsto_order]`. Prove the components needed by the constructor for the conclusion. Introduce `a ha filter_upwards [h.eventually (lt_mem_nhds ha), self_mem_nhdsWithin] with t ht ht0`. Conclude with `ht.trans_le (ENNReal.div_le_div_right (hFF t (t + 1) ht0 (by linarith)).1 _)`. Introduce `b hb`.

Establish `h1 : Tendsto (fun l : ℝ => C * ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 C)`. Establish `h2 : Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 1)`. Establish `: Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝 1) (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ k)))` using `(ENNReal.continuous_ofReal.comp (continuous_pow k)).tendsto 1`. Simplify using `using this.mono_left nhdsWithin_le_nhds`. Simplify using `using ENNReal.Tendsto.const_mul h2 (Or.inr hC)`.

Take `⟨l, hl, hl1⟩` from `((h1.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists`. Establish `hl1 : 1 < l` using `hl1`. Establish `hl0 : 0 < l` using `by linarith`. Establish `h3 : Tendsto (fun t : ℝ => l * t) (𝓝[>] 0) (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Establish `: Tendsto (fun t : ℝ => l * t) (𝓝 0) (𝓝 (l * 0))` using `(continuous_const.mul continuous_id).tendsto 0`. Simplify using `using this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Conclude with `mul_pos hl0 ht`. Establish `h4` using `ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (l ^ k)) (h.comp h3) (Or.inr ENNReal.ofReal_ne_top)`.

Use `filter_upwards [h4.eventually (gt_mem_nhds hl), self_mem_nhdsWithin] with t ht ht0`. Establish `ht0 : 0 < t` using `ht0`. Use `lt_of_le_of_lt ?_ ht` and prove the remaining obligations. Establish `hlk : ENNReal.ofReal (l ^ k) ≠ 0`. Simplify using `using pow_pos hl0 k`.

Establish `e : F (l * t) / ENNReal.ofReal ((l * t) ^ k) * ENNReal.ofReal (l ^ k) = F (l * t) / ENNReal.ofReal (t ^ k)`. Rewrite using `[mul_pow, ENNReal.ofReal_mul (pow_pos hl0 k).le, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hlk) (Or.inl ENNReal.ofReal_ne_top), mul_assoc, mul_right_comm, ENNReal.inv_mul_cancel hlk ENNReal.ofReal_ne_top, one_mul]`. Simplify using `only [Function.comp]`. Rewrite using `[e]`. Conclude with `ENNReal.div_le_div_right (hFF t (l * t) ht0 (by nlinarith)).2 _`.
-/
theorem tendsto_div_pow_of_sandwich (k : ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) (F F' : ℝ → ℝ≥0∞)
    (hFF : ∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s)
    (h : Tendsto (fun t : ℝ => F t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 C) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [h.eventually (lt_mem_nhds ha), self_mem_nhdsWithin] with t ht ht0
    exact ht.trans_le (ENNReal.div_le_div_right (hFF t (t + 1) ht0 (by linarith)).1 _)
  · intro b hb
    have h1 : Tendsto (fun l : ℝ => C * ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 C) := by
      have h2 : Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 1) := by
        have : Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝 1)
            (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ k))) :=
          (ENNReal.continuous_ofReal.comp (continuous_pow k)).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hC)
    obtain ⟨l, hl, hl1⟩ := ((h1.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have hl1 : 1 < l := hl1
    have hl0 : 0 < l := by linarith
    have h3 : Tendsto (fun t : ℝ => l * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => l * t) (𝓝 0) (𝓝 (l * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos hl0 ht
    have h4 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (l ^ k)) (h.comp h3)
      (Or.inr ENNReal.ofReal_ne_top)
    filter_upwards [h4.eventually (gt_mem_nhds hl), self_mem_nhdsWithin] with t ht ht0
    have ht0 : 0 < t := ht0
    refine lt_of_le_of_lt ?_ ht
    have hlk : ENNReal.ofReal (l ^ k) ≠ 0 := by
      simpa using pow_pos hl0 k
    have e : F (l * t) / ENNReal.ofReal ((l * t) ^ k) * ENNReal.ofReal (l ^ k)
        = F (l * t) / ENNReal.ofReal (t ^ k) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_pos hl0 k).le, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hlk) (Or.inl ENNReal.ofReal_ne_top), mul_assoc, mul_right_comm,
        ENNReal.inv_mul_cancel hlk ENNReal.ofReal_ne_top, one_mul]
    simp only [Function.comp]
    rw [e]
    exact ENNReal.div_le_div_right (hFF t (l * t) ht0 (by nlinarith)).2 _

/- English proof (translation)
Introduce `k c c₀ F F' M V hc hc₀ hFF hV hMV hQ`. Use `tendsto_div_pow_of_sandwich k _ ENNReal.ofReal_ne_top F F' hFF ?_` and prove the remaining obligations. Establish `hpi` using `Real.pi_pos`. Establish `hk : (0 : ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`. Use `set K : ℝ := (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ) with hK`.

Establish `hKpos : 0 < K` using `by positivity`. Establish `hc0' : ENNReal.ofReal c₀ ≠ 0` using `by simpa using hc₀`. Establish `hc' : ENNReal.ofReal c ≠ 0` using `by simpa using hc`. Establish `h1` using `ENNReal.Tendsto.mul_const (b := ENNReal.ofReal K) (ENNReal.Tendsto.div hQ (Or.inl hc') hMV (Or.inr ENNReal.ofReal_ne_top)) (Or.inr ENNReal.ofReal_ne_top)`. Establish `e0 : ENNReal.ofReal c / ENNReal.ofReal c₀ * ENNReal.ofReal K = ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ))`.

Rewrite using `[← ENNReal.ofReal_div_of_pos hc₀, ← ENNReal.ofReal_mul (by positivity), hK, mul_div_assoc]`. Rewrite `h1` using `[e0]`. Establish `h2 : Tendsto (fun ρ : ℝ => F (ρ ^ 2 / 2) / ENNReal.ofReal ((ρ ^ 2 / 2) ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ))))`. Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hMV.eventually (isOpen_ne.mem_nhds hc0'), hMV.eventually (isOpen_ne.mem_nhds ENNReal.ofReal_ne_top), self_mem_nhdsWithin] with ρ hm0 hmt hρ`.

Establish `hρ : 0 < ρ` using `hρ`. Take `⟨hv0, hvt⟩` from `hV ρ hρ`. Rewrite using `[ENNReal.mul_div_mul_comm (Or.inl hv0.ne') (Or.inl hvt.ne), mul_comm (M ρ / V ρ), mul_div_assoc (_ / _), ENNReal.div_self hm0 hmt, mul_one, mul_div_assoc, mul_assoc, ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv (F _), ← ENNReal …`. Use `congr 2`. Rewrite using `[hK, div_pow, ← pow_mul, mul_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝[>] 0) (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝 0) (𝓝 (Real.sqrt (2 * 0)))` using `(by fun_prop : Continuous fun t : ℝ => Real.sqrt (2 * t)).tendsto 0`.

Simplify using `using this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Establish `ht : 0 < t` using `ht`. Conclude with `Real.sqrt_pos.2 (by linarith)`. Use `(h2.comp h3).congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Establish `ht : 0 < t` using `ht`. Establish `: Real.sqrt (2 * t) ^ 2 / 2 = t`. Rewrite using `[Real.sq_sqrt (by linarith)]; ring`. Simplify using `only [Function.comp, this]`.
-/
theorem thin_tube_limit_arith : ∀ (k : ℕ) (c c₀ : ℝ) (F F' M V : ℝ → ℝ≥0∞), 0 < c → 0 < c₀ → (∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s) → (∀ ρ : ℝ, 0 < ρ → 0 < V ρ ∧ V ρ < ⊤) → Tendsto (fun ρ : ℝ => M ρ / V ρ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c₀)) → Tendsto (fun ρ : ℝ => M ρ * (F (ρ ^ 2 / 2) * ENNReal.ofReal (ρ / Real.pi)) / (V ρ * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c)) → Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  intro k c c₀ F F' M V hc hc₀ hFF hV hMV hQ
  refine tendsto_div_pow_of_sandwich k _ ENNReal.ofReal_ne_top F F' hFF ?_
  have hpi := Real.pi_pos
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  set K : ℝ := (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hc0' : ENNReal.ofReal c₀ ≠ 0 := by simpa using hc₀
  have hc' : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have h1 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal K)
    (ENNReal.Tendsto.div hQ (Or.inl hc') hMV (Or.inr ENNReal.ofReal_ne_top))
    (Or.inr ENNReal.ofReal_ne_top)
  have e0 : ENNReal.ofReal c / ENNReal.ofReal c₀ * ENNReal.ofReal K
      = ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)) := by
    rw [← ENNReal.ofReal_div_of_pos hc₀, ← ENNReal.ofReal_mul (by positivity), hK, mul_div_assoc]
  rw [e0] at h1
  have h2 : Tendsto (fun ρ : ℝ => F (ρ ^ 2 / 2) / ENNReal.ofReal ((ρ ^ 2 / 2) ^ k)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
    refine h1.congr' ?_
    filter_upwards [hMV.eventually (isOpen_ne.mem_nhds hc0'),
      hMV.eventually (isOpen_ne.mem_nhds ENNReal.ofReal_ne_top), self_mem_nhdsWithin]
      with ρ hm0 hmt hρ
    have hρ : 0 < ρ := hρ
    obtain ⟨hv0, hvt⟩ := hV ρ hρ
    rw [ENNReal.mul_div_mul_comm (Or.inl hv0.ne') (Or.inl hvt.ne), mul_comm (M ρ / V ρ),
      mul_div_assoc (_ / _), ENNReal.div_self hm0 hmt, mul_one, mul_div_assoc, mul_assoc,
      ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      div_eq_mul_inv (F _), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 2
    rw [hK, div_pow, ← pow_mul, mul_pow]
    field_simp
    ring
  have h3 : Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝 0) (𝓝 (Real.sqrt (2 * 0))) :=
        (by fun_prop : Continuous fun t : ℝ => Real.sqrt (2 * t)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : 0 < t := ht
      exact Real.sqrt_pos.2 (by linarith)
  refine (h2.comp h3).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have : Real.sqrt (2 * t) ^ 2 / 2 = t := by
    rw [Real.sq_sqrt (by linarith)]; ring
  simp only [Function.comp, this]

end GlobalTheory.Tube
