import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Sheets
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `n M _ z U u w₀ N hcov hw₀ hfin hvan k`. Take `⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩` from `sheets n M z U u hcov w₀ hw₀ hfin`. Establish `hWn : W ∈ 𝓝 w₀` using `hW.mem_nhds hwW`. Establish `hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N`. Introduce `i`.

Establish `hx : z (s i w₀) = w₀` using `hzs i w₀ hwW`. Establish `h1` using `IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)`. Use `h1.congr' (Eventually.of_forall fun v => rfl) ?_` and prove the remaining obligations. Use `filter_upwards [hWn] with v hv`. Simplify using `only [Function.comp_apply, hzs i v hv, hx]`.

Establish `hprod : ∀ t : Finset (Fin d), (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))`. Consider the case `insert a t ha ih`.

Establish `hc : (insert a t).card = t.card + 1`. Conclude with `Finset.card_insert_of_notMem ha`. Simplify using `only [Finset.prod_insert ha]`. Rewrite using `[hc]`. Conclude with `((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl) (Eventually.of_forall fun v => by show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use the proof step `ring)`. Establish `heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v)) =ᶠ[𝓝 w₀] fiberSymm n z u k` using `by filter_upwards [hWn] with v hv`. Rewrite using `[fiberSymm, hvals v hv, Finset.esymm_map_val]`.

Use `IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)` and prove the remaining obligations. Use `IsBigO.fun_sum fun t ht => ?_` and prove the remaining obligations. Use `hprod t` as an intermediate fact. Rewrite `this` using `[(Finset.mem_powersetCard.mp ht).2]`. Then use the resulting hypothesis.
-/
theorem symmVanish : symmVanishStatement.{u} := by
  intro n M _ z U u w₀ N hcov hw₀ hfin hvan k
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w₀ hw₀ hfin
  have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hwW
  have hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N := by
    intro i
    have hx : z (s i w₀) = w₀ := hzs i w₀ hwW
    have h1 := IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)
    refine h1.congr' (Eventually.of_forall fun v => rfl) ?_
    filter_upwards [hWn] with v hv
    simp only [Function.comp_apply, hzs i v hv, hx]
  have hprod : ∀ t : Finset (Fin d),
      (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))
    | insert a t ha ih =>
      have hc : (insert a t).card = t.card + 1 := by
        exact Finset.card_insert_of_notMem ha
      simp only [Finset.prod_insert ha]
      rw [hc]
      exact ((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl)
        (Eventually.of_forall fun v => by
          show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)
          rw [← pow_add]; congr 1; ring)
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w₀] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)
  refine IsBigO.fun_sum fun t ht => ?_
  have := hprod t
  rwa [(Finset.mem_powersetCard.mp ht).2] at this

end ReciprocityTheory.L2DbarEstimates.Norm
