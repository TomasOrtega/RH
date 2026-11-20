import Mathlib

namespace GlobalTheory

open IsDedekindDomain in

/- English proof (translation)
Introduce `A _ _ m a₀ b₀ hm`. Choose the witnesses or unpack the hypotheses as in `⟨b, hbm, hb0⟩ : ∃ b, b - b₀ ∈ m ∧ b ≠ 0 := by`. Distinguish the cases in `h : b₀ = 0`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`. Conclude with `⟨x, by simpa [h] using hx, hx0⟩`.

Conclude with `⟨b₀, by simp, h⟩`. Establish `hspan : Ideal.span {b} ≠ (0 : Ideal A)`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`. Establish `hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {b}}.Finite` using `Ideal.finite_factors hspan`.

Set `S` to `hfin.toFinset.filter (fun v => ¬ m ≤ v.asIdeal)`. Set `K : Ideal A` to `⨅ v ∈ S, v.asIdeal`. Establish `hK : m ⊔ K = ⊤`. Apply `Ideal.sup_iInf_eq_top` to reduce the goal to its premises. Introduce `v hv`.

Establish `hv' : ¬ m ≤ v.asIdeal` using `(Finset.mem_filter.mp hv).2`. Establish `hmax : v.asIdeal.IsMaximal` using `v.isMaximal`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[sup_comm]`. Establish `heq` using `hmax.eq_of_le hne le_sup_left`.

Conclude with `hv' (heq ▸ le_sup_right)`. Establish `h1 : (1 : A) ∈ m ⊔ K` using `by rw [hK]; exact Submodule.mem_top`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.mp h1`. Use `⟨a₀ * y + x, b, ?_, hbm, hb0, ?_⟩` and prove the remaining obligations. Establish `: a₀ * y + x - a₀ = x - a₀ * x`.

Establish `hy' : y = 1 - x` using `by rw [← hxy]; ring`. Rewrite using `[hy']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `m.sub_mem hx (m.mul_mem_left a₀ hx)`.

Introduce and unpack `p hp hmp ⟨hap, hbp⟩`. Establish `hp0 : p ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hb0 ((Submodule.mem_bot A).mp hbp)`. Set `v : HeightOneSpectrum A` to `⟨p, hp.isPrime, hp0⟩`.

Establish `hvS : v ∈ S`. Use `Finset.mem_filter.mpr ⟨?_, hmp⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Use `show p ∣ Ideal.span {b}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hbp`. Establish `hKp : K ≤ p` using `iInf₂_le v hvS`. Establish `hyp : y ∈ p` using `hKp hy`. Establish `hxp : x ∈ p`. Use `p.sub_mem hap (p.mul_mem_left a₀ hyp)` as an intermediate fact.

Simplify using `using this`. Conclude with `hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hxy ▸ p.add_mem hxp hyp))`.
-/
theorem exists_reps_coprime_outside_modulus : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (m : Ideal A) (a₀ b₀ : A), m ≠ ⊥ → ∃ a b : A, a - a₀ ∈ m ∧ b - b₀ ∈ m ∧ b ≠ 0 ∧ ∀ p : Ideal A, p.IsMaximal → ¬ m ≤ p → ¬ (a ∈ p ∧ b ∈ p) := by
  classical
  intro A _ _ m a₀ b₀ hm
  obtain ⟨b, hbm, hb0⟩ : ∃ b, b - b₀ ∈ m ∧ b ≠ 0 := by
    by_cases h : b₀ = 0
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      exact ⟨x, by simpa [h] using hx, hx0⟩
    · exact ⟨b₀, by simp, h⟩
  have hspan : Ideal.span {b} ≠ (0 : Ideal A) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  have hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors hspan
  let S := hfin.toFinset.filter (fun v => ¬ m ≤ v.asIdeal)
  let K : Ideal A := ⨅ v ∈ S, v.asIdeal
  have hK : m ⊔ K = ⊤ := by
    apply Ideal.sup_iInf_eq_top
    intro v hv
    have hv' : ¬ m ≤ v.asIdeal := (Finset.mem_filter.mp hv).2
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    by_contra hne
    rw [sup_comm] at hne
    have heq := hmax.eq_of_le hne le_sup_left
    exact hv' (heq ▸ le_sup_right)
  have h1 : (1 : A) ∈ m ⊔ K := by rw [hK]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  refine ⟨a₀ * y + x, b, ?_, hbm, hb0, ?_⟩
  · have : a₀ * y + x - a₀ = x - a₀ * x := by
      have hy' : y = 1 - x := by rw [← hxy]; ring
      rw [hy']; ring
    rw [this]
    exact m.sub_mem hx (m.mul_mem_left a₀ hx)
  · rintro p hp hmp ⟨hap, hbp⟩
    have hp0 : p ≠ ⊥ := by
      rintro rfl
      exact hb0 ((Submodule.mem_bot A).mp hbp)
    let v : HeightOneSpectrum A := ⟨p, hp.isPrime, hp0⟩
    have hvS : v ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hmp⟩
      rw [Set.Finite.mem_toFinset]
      show p ∣ Ideal.span {b}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hbp
    have hKp : K ≤ p := iInf₂_le v hvS
    have hyp : y ∈ p := hKp hy
    have hxp : x ∈ p := by
      have := p.sub_mem hap (p.mul_mem_left a₀ hyp)
      simpa using this
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hxy ▸ p.add_mem hxp hyp))

end GlobalTheory
