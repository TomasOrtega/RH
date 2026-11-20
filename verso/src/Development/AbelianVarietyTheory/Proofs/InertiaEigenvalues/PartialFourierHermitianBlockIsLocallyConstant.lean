import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩`. Use `haveI : IsUltrametricDist E := Unram.ultraE (F := F)`. Establish `htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1`. Introduce `d hd`. Apply `hψ.1` to reduce the goal to its premises.

Establish `h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1`. Rewrite using `[htr]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)` and prove the remaining obligations. Rewrite using `[Unram.norm_star (F := F)]`. Conclude with `hd`.

Rewrite `h1` using `[norm_algebraMap']`. Then use the resulting hypothesis. Take `⟨R, hR⟩` from `(Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1 ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)`. Use `set R' : ℝ := max R 1 with hR'`. Establish `hR'pos : 0 < R'` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `X₀`. Establish `hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E)` using `(continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk ((continuous_snd.comp continuous_snd).sub continuous_const))`. Establish `hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U`. Establish `: ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0`. Apply the tactic sequence `ext <;> simp`.

Conclude with `hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)`. Establish `hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R')` using `(continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by positivity))`. Use `filter_upwards [hV1, hV2] with X hX1 hX2`. Unfold `fourU`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Establish `hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2)`. Use `hUf (X₀.1, c, X₀.2.2) _ hX1` as an intermediate fact. Apply the tactic sequence `rw [← this]; congr 1; ext <;> simp`. Rewrite using `[hfe]`.

Distinguish the cases in `h0 : f (X₀.1, c, X₀.2.2) = 0`. Rewrite using `[h0, zero_mul, zero_mul]`. Use `congr 1`. Establish `hc : ‖c‖ ≤ R`. Establish `hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f` using `⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩`.

Simplify using `using hR hmem`. Establish `hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1`. Establish `hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R'` using `by rw [← dist_eq_norm]; exact hX2`. Unfold `dotProduct`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, Pi.star_apply, Unram.norm_star (F := F)]`. Establish `h1 : ‖c i‖ ≤ R'` using `(norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))`. Establish `h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R'` using `(norm_le_pi_norm _ i).trans hd`. Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1)`.

Rewrite using `[dotProduct_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, map_add, AddChar.map_add_eq_mul, htr1 _ hs, mul_one]`.
-/
theorem fourU_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f →
    (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)

  have htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1 := by
    intro d hd
    apply hψ.1
    have h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1 := by
      rw [htr]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)
      rw [Unram.norm_star (F := F)]; exact hd
    rwa [norm_algebraMap'] at h1

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1
    ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀
  have hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) :=
    (continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk
      ((continuous_snd.comp continuous_snd).sub continuous_const))
  have hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U := by
    have : ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0 := by
      ext <;> simp
    exact hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)
  have hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R') :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))
  filter_upwards [hV1, hV2] with X hX1 hX2
  unfold fourU
  congr 1
  funext c
  have hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2) := by
    have := hUf (X₀.1, c, X₀.2.2) _ hX1
    rw [← this]; congr 1; ext <;> simp
  rw [hfe]
  by_cases h0 : f (X₀.1, c, X₀.2.2) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hc : ‖c‖ ≤ R := by
    have hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f :=
      ⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩
    simpa using hR hmem
  have hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1 := by
    have hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R' := by rw [← dist_eq_norm]; exact hX2
    unfold dotProduct
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
    have h1 : ‖c i‖ ≤ R' := (norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))
    have h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R' := (norm_le_pi_norm _ i).trans hd
    calc ‖c i‖ * ‖(X.2.1 - X₀.2.1) i‖ ≤ R' * (1 / R') :=
          mul_le_mul h1 h2 (norm_nonneg _) hR'pos.le
      _ = 1 := by field_simp
  have hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1) := by
    rw [dotProduct_sub]; ring
  rw [hsplit, map_add, AddChar.map_add_eq_mul, htr1 _ hs, mul_one]

end GlobalTheory
