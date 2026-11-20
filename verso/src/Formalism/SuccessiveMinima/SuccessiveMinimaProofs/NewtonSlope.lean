import Formalism.SuccessiveMinima.StatementNP

namespace Formalism.FN
open Filter Topology

variable {K : Type*} [NormedField K]

/- English proof (translation)
The claim follows from `h.bddAbove_range`.
-/
lemma gNorm_bdd_of_conv (a : ℕ → K) (r : ℝ) (h : ConvOn a r) :
    BddAbove (Set.range fun k : ℕ => ‖a k‖ * r ^ k) := h.bddAbove_range

/- English proof (translation)
Use `set f : ℕ → ℝ := fun k => ‖a k‖ * r ^ k with hf`. Choose the witnesses or unpack the hypotheses as in `⟨k0, hk0⟩ : ∃ k0, a k0 ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `ha (funext hc)`.

Establish `fpos : 0 < f k0` using `by simp only [hf]; positivity`. Establish `ev : ∀ᶠ k in atTop, f k < f k0` using `(h : Tendsto f atTop (𝓝 0)).eventually (gt_mem_nhds fpos)`. Take `⟨M0, hM0⟩` from `eventually_atTop.1 ev`. Use `set M := max M0 (k0 + 1)`. Establish `hM : ∀ k ≥ M, f k < f k0` using `fun k hk => hM0 k (le_trans (le_max_left _ _) hk)`.

Take `⟨k1, hk1m, hk1⟩` from `Finset.exists_max_image (Finset.range M) f ⟨k0, by simp [M]⟩`. Establish `hall : ∀ k, f k ≤ f k1`. Introduce `k`. Distinguish the cases in `hk : k < M`. Conclude with `hk1 k (by simpa using hk)`.

Conclude with `(hM k (by omega)).le.trans (hk1 k0 (by simp [M]))`. Establish `hg : gNorm a r = f k1` using `le_antisymm (ciSup_le hall) (le_ciSup (gNorm_bdd_of_conv a r h) k1)`. Establish `hS : {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}.Nonempty` using `⟨k1, by simp [hg, f]⟩`. Establish `hB : BddAbove {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}`. Use `⟨M, fun k hk => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hM k hc.le` as an intermediate fact. Establish `e : f k = f k1` using `by simpa [hg, f] using hk`. Combine the linear relations using `[hall k0]`.

Use `⟨Nat.sSup_mem hS hB, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `fpos.trans_le (hall k0)`.
-/
lemma wdeg_spec (a : ℕ → K) (r : ℝ) (hr : 0 < r) (h : ConvOn a r) (ha : a ≠ 0) :
    ‖a (wdeg a r)‖ * r ^ (wdeg a r) = gNorm a r ∧ 0 < gNorm a r := by
  set f : ℕ → ℝ := fun k => ‖a k‖ * r ^ k with hf
  obtain ⟨k0, hk0⟩ : ∃ k0, a k0 ≠ 0 := by
    by_contra hc; push Not at hc; exact ha (funext hc)
  have fpos : 0 < f k0 := by simp only [hf]; positivity
  have ev : ∀ᶠ k in atTop, f k < f k0 := (h : Tendsto f atTop (𝓝 0)).eventually (gt_mem_nhds fpos)
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 ev
  set M := max M0 (k0 + 1)
  have hM : ∀ k ≥ M, f k < f k0 := fun k hk => hM0 k (le_trans (le_max_left _ _) hk)
  obtain ⟨k1, hk1m, hk1⟩ := Finset.exists_max_image (Finset.range M) f ⟨k0, by simp [M]⟩
  have hall : ∀ k, f k ≤ f k1 := by
    intro k
    by_cases hk : k < M
    · exact hk1 k (by simpa using hk)
    · exact (hM k (by omega)).le.trans (hk1 k0 (by simp [M]))
  have hg : gNorm a r = f k1 :=
    le_antisymm (ciSup_le hall) (le_ciSup (gNorm_bdd_of_conv a r h) k1)
  have hS : {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}.Nonempty := ⟨k1, by simp [hg, f]⟩
  have hB : BddAbove {k : ℕ | ‖a k‖ * r ^ k = gNorm a r} := by
    refine ⟨M, fun k hk => ?_⟩
    by_contra hc; push Not at hc
    have := hM k hc.le
    have e : f k = f k1 := by simpa [hg, f] using hk
    linarith [hall k0]
  refine ⟨Nat.sSup_mem hS hB, ?_⟩
  rw [hg]; exact fpos.trans_le (hall k0)

end Formalism.FN
