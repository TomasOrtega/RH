import Mathlib

namespace GlobalTheory

open Module

/- English proof (translation)
Use `set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef`. Use `haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F`. Establish `hWV : W ≤ V` using `Submodule.span_le.mpr (fun u hu => hF u hu)`. Set `ev : X → Module.Dual ℂ W` to `fun x => (LinearMap.proj x).comp W.subtype`. Establish `hev : ∀ x (w : W), ev x w = (w : X → ℂ) x` using `fun x w => rfl`.

Use `set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef`. Establish `hcoan : S.dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Rewrite `hw` using `[Submodule.mem_dualCoannihilator]`.

Establish `h0 : (w : X → ℂ) = 0`. Use function extensionality and compare the values at `x`. Use `hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)` as an intermediate fact. Simplify `this` using `[hev]`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `Subtype.ext h0`. Establish `hS : S = ⊤`. Use `Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)` as an intermediate fact. Rewrite using `[← this, hcoan, Submodule.dualAnnihilator_bot]`. Set `b` to `Module.finBasis ℂ W`.

Establish `hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i`. Introduce `i`. Establish `: b.coord i ∈ S` using `by rw [hS]; trivial`. Conclude with `Finsupp.mem_span_range_iff_exists_finsupp.mp this`. Use `choose μ hμ using hμ`.

Use `set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef`. Establish `hsub : ∀ i, (μ i).support ⊆ s` using `fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩`. Use `⟨s, fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))`.

Introduce `u hu`. Set `w : W` to `⟨u, Submodule.subset_span hu⟩`. Establish `hw : (w : X → ℂ) = u` using `rfl`. Establish `hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x`. Introduce `i`.

Establish `h1 : b.repr w i = b.coord i w` using `rfl`. Rewrite using `[h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]`. Simplify using `[LinearMap.sum_apply, hev, hw]`. Introduce `x _`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Use `_ = _ := by`. Repeatedly rewrite using `[hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem finset_functions_recovered_from_values {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ))
    (hF : ∀ u ∈ F, u ∈ V) :
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  classical
  set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F
  have hWV : W ≤ V := Submodule.span_le.mpr (fun u hu => hF u hu)
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef
  have hcoan : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : X → ℂ) = 0 := by
      funext x
      have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [← this, hcoan, Submodule.dualAnnihilator_bot]
  let b := Module.finBasis ℂ W
  have hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i := by
    intro i
    have : b.coord i ∈ S := by rw [hS]; trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp this
  choose μ hμ using hμ
  set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef
  have hsub : ∀ i, (μ i).support ⊆ s := fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  refine ⟨s,
    fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))
  · intro u hu
    let w : W := ⟨u, Submodule.subset_span hu⟩
    have hw : (w : X → ℂ) = u := rfl
    have hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x := by
      intro i
      have h1 : b.repr w i = b.coord i w := rfl
      rw [h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]
      · simp [LinearMap.sum_apply, hev, hw]
      · intro x _; simp
    calc u = ((∑ i, b.repr w i • b i : W) : X → ℂ) := by rw [b.sum_repr w]
      _ = ∑ i, b.repr w i • ((b i : W) : X → ℂ) := by
          rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      _ = _ := by
        simp_rw [hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [mul_comm]

end GlobalTheory
