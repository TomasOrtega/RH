import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound

open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

/- English proof (translation)
Set `K : Finset Y → Submodule ℂ (Y → ℂ)` to `fun t => { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0} add_mem' := fun {a b} ha hb => ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩ zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩ smul_mem' := fun c a ha => ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }`. Establish `hKle : ∀ t, K t ≤ Ψ` using `fun t _ h => h.1`. Use `haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)`. Set `f : Finset Y → ℕ` to `fun t => Module.finrank ℂ (K t)`. Use `⟨Function.argmin f, fun ψ hψ h0 => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hne (funext hall)`.

Use `set t := Function.argmin f with ht`. Establish `hlt : K (insert y t) < K t`. Use `lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_` and prove the remaining obligations. Introduce `heq`. Establish `hmem : ψ ∈ K t` using `⟨hψ, h0⟩`.

Rewrite `hmem` using `[← heq]`. Conclude with `hy (hmem.2 y (Finset.mem_insert_self y t))`. Establish `h1 : f (insert y t) < f t` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `h2 : f t ≤ f (insert y t)` using `Function.argmin_le f _`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

/- English proof (translation)
Set `T : Ψ →ₗ[ℂ] Lp ℂ 2 μ` to `{ toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1 map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2) map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }`. Establish `hker : LinearMap.ker T = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `ψ hψ`. Establish `h0 : ψ.1 =ᵐ[μ] 0` using `(MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by`.

Rewrite using `[MemLp.toLp_zero]`. Conclude with `hψ)`. Conclude with `Subtype.ext (hinj ψ.1 ψ.2 h0)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective T hker`. Set `ev : Ψ →ₗ[ℂ] ℂ` to `{ toFun := fun ψ => ψ.1 y₀ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Set `ℓ : LinearMap.range T →ₗ[ℂ] ℂ` to `(ev ∘ₗ g).domRestrict (LinearMap.range T)`. Set `L : LinearMap.range T →L[ℂ] ℂ` to `⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩`. Use `⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩` and prove the remaining obligations. Set `p : Ψ` to `⟨ψ, hψ⟩`. Establish `hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀`.

Express the relevant statement in the definitionally equal form `ev (g (T p)) = ψ y₀`. Establish `: g (T p) = p` using `LinearMap.congr_fun hg p`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊`.

Rewrite using `[← hL]`. Conclude with `L.le_opNNNorm _`. Establish `hen : ‖T p‖ₑ = eLpNorm ψ 2 μ` using `Lp.enorm_toLp (hm ψ hψ)`. Establish `hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ`. Rewrite using `[← hen]`.

Simplify using `only [enorm_eq_nnnorm]`. Conclude with `hb` after adjusting the coercions. Establish `hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ`. Use `eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)` as an intermediate fact. Simplify using `using this`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, hsq]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

/- English proof (translation)
Introduce `X Y _ _ _ _ _ ν _ _ F hF hfin`. Use `set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ`. Use `haveI : FiniteDimensional ℂ Ψ := hfin`. Establish `hc : ∀ ψ ∈ Ψ, Continuous ψ`. Introduce `ψ hψ`.

Proceed by induction on `hψ using Submodule.span_induction with`. Consider the case `mem x h => obtain ⟨i, rfl⟩ := h`. Conclude with `hF i`. Consider the case `zero => exact continuous_const`. Consider the case `add a b _ _ ha hb => exact ha.add hb`.

Consider the case `smul c a _ ha => exact ha.const_smul c`. Take `⟨t, ht⟩` from `exists_finset_separating Ψ`. Use `choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y`. Establish `hΩ : IsCompact (⋃ y ∈ t, N y)` using `t.isCompact_biUnion fun y _ => hNc y`. Use `set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef`.

Use `⟨Ω, hΩ, fun y₀ => ?_⟩` and prove the remaining obligations. Use `haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩`. Establish `hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω)`. Introduce `ψ hψ`. Take `⟨B, hB⟩` from `hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn`.

Use `MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_` and prove the remaining obligations. Establish `hmeas : MeasurableSet Ω` using `hΩ.measurableSet`. Conclude with `(ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)`. Establish `hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0`. Introduce `ψ hψ h0`.

Use `ht ψ hψ fun y hy => ?_` and prove the remaining obligations. Establish `hsub : interior (N y) ⊆ Ω` using `interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)`. Establish `h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0` using `ae_mono (Measure.restrict_mono hsub le_rfl) h0`. Establish `h2` using `Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn continuousOn_const`. Conclude with `h2 (mem_interior_iff_mem_nhds.2 (hNn y))`.

Take `⟨C, hC⟩` from `bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀`. Conclude with `⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩`.
-/
theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
