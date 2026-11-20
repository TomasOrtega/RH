import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicCoordSB

/- English proof (translation)
Introduce `F _ _ κ _ φ hSB hae`. Use `⟨?_, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hae⟩` and prove the remaining obligations. Set `L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → v.adicCompletion F)` to `fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}`. Set `S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))` to `{v | ¬ φ v = Set.indicator (L v) 1}`. Establish `hS : S.Finite` using `Filter.eventually_cofinite.1 hae`.

Set `ev : (κ → FiniteAdeleRing (𝓞 F) F) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F)` to `fun y v i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)`. Establish `hev : ∀ y v i, ev y v i = (y i).1 v` using `fun _ _ _ => rfl`. Establish `hcont : ∀ v, Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => ev y v` using `fun v => continuous_pi fun i => (RestrictedProduct.continuous_eval (R := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (A := fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp (continuous_apply i)`. Establish `hfin : ∀ y, (Function.mulSupport fun v => φ v (ev y v)).Finite`. Introduce `y`.

Establish `hint : ∀ᶠ v in Filter.cofinite, ev y v ∈ L v` using `Filter.eventually_all.2 fun i => (y i).2`. Use `(Filter.eventually_cofinite.1 (hae.and hint)).subset ?_` and prove the remaining obligations. Introduce `w hw h'`. Apply `hw` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[h'.1, Set.indicator_of_mem h'.2]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `IsLocallyConstant fun y => ∏ᶠ v, φ v (ev y v)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `y`.

Distinguish the cases in `hy : ∀ v ∉ S, ev y v ∈ L v`. Set `G : Set (κ → FiniteAdeleRing (𝓞 F) F)` to `{z | ∀ v ∉ S, ev z v ∈ L v}`. Establish `hGe : G = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F => z i) ⁻¹' {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x.1 v ∈ v.adicCompletionIntegers F}`. Use extensionality with `z`. Simplify using `only [G, L, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, hev]`.

Conclude with `⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩`. Establish `hGo : IsOpen G`. Rewrite using `[hGe]`. Conclude with `isOpen_iInter_of_finite fun i => (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)).preimage (continuous_apply i)`. Establish `heq : ∀ z ∈ G, ∏ᶠ v, φ v (ev z v) = ∏ v ∈ hS.toFinset, φ v (ev z v)`.

Introduce `z hz`. Use `finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset]`. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises.

Establish `hφ : φ v = Set.indicator (L v) 1` using `not_not.1 hvS`. Simplify using `only`. Rewrite using `[hφ, Set.indicator_of_mem (hz v hvS)]`. Both sides reduce to the same expression. Establish `hlc : IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => ∏ v ∈ hS.toFinset, φ v (ev z v)`.

Establish `: ∀ v, IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => φ v (ev z v)` using `fun v => (hSB v).1.comp_continuous (hcont v)`. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun z => ?_` and prove the remaining obligations. Establish `h2 : ∀ᶠ w in nhds z, ∀ v ∈ hS.toFinset, φ v (ev w v) = φ v (ev z v)` using `(Filter.eventually_all_finset _).2 fun v _ => (IsLocallyConstant.iff_eventually_eq _).1 (this v) z`. Use `filter_upwards [h2] with w hw`. Conclude with `Finset.prod_congr rfl hw`.

Use `filter_upwards [hGo.mem_nhds hy, (IsLocallyConstant.iff_eventually_eq _).1 hlc y] with z hz hz'`. Rewrite using `[heq z hz, heq y hy]`. Conclude with `hz'`. Use `push_neg at hy`. Take `⟨v, hvS, hvL⟩` from `hy`.

Establish `hφ : φ v = Set.indicator (L v) 1` using `not_not.1 hvS`. Set `U : Set (κ → FiniteAdeleRing (𝓞 F) F)` to `{z | ev z v ∉ L v}`. Establish `hLc : IsClosed (L v)`. Establish `e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Use extensionality with `x`.

Simplify using `[L]`. Rewrite using `[e]`. Conclude with `isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed`. Establish `hUo : IsOpen U` using `hLc.isOpen_compl.preimage (hcont v)`. Establish `h0 : ∀ z ∈ U, ∏ᶠ w, φ w (ev z w) = 0` using `fun z hz => finprod_eq_zero _ v (by show φ v (ev z v) = 0; rw [hφ, Set.indicator_of_notMem hz]) (hfin z)`.

Use `filter_upwards [hUo.mem_nhds hvL] with z hz`. Rewrite using `[h0 z hz, h0 y hvL]`.
-/
theorem finprod_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ φ hSB hae
  classical
  refine ⟨?_, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hae⟩
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → v.adicCompletion F) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  let S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := {v | ¬ φ v = Set.indicator (L v) 1}
  have hS : S.Finite := Filter.eventually_cofinite.1 hae
  let ev : (κ → FiniteAdeleRing (𝓞 F) F) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) :=
    fun y v i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)
  have hev : ∀ y v i, ev y v i = (y i).1 v := fun _ _ _ => rfl
  have hcont : ∀ v, Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => ev y v := fun v =>
    continuous_pi fun i => (RestrictedProduct.continuous_eval (R := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      w.adicCompletion F) (A := fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
      (continuous_apply i)
  have hfin : ∀ y, (Function.mulSupport fun v => φ v (ev y v)).Finite := by
    intro y
    have hint : ∀ᶠ v in Filter.cofinite, ev y v ∈ L v :=
      Filter.eventually_all.2 fun i => (y i).2
    refine (Filter.eventually_cofinite.1 (hae.and hint)).subset ?_
    intro w hw h'
    apply hw
    simp only
    rw [h'.1, Set.indicator_of_mem h'.2]
    rfl
  change IsLocallyConstant fun y => ∏ᶠ v, φ v (ev y v)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  by_cases hy : ∀ v ∉ S, ev y v ∈ L v
  ·
    let G : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ∀ v ∉ S, ev z v ∈ L v}
    have hGe : G = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F => z i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x.1 v ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [G, L, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, hev]
      exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
    have hGo : IsOpen G := by
      rw [hGe]
      exact isOpen_iInter_of_finite fun i =>
        (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)).preimage
          (continuous_apply i)
    have heq : ∀ z ∈ G, ∏ᶠ v, φ v (ev z v) = ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      intro z hz
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      by_contra hvS
      apply hv
      have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
      simp only
      rw [hφ, Set.indicator_of_mem (hz v hvS)]
      rfl
    have hlc : IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      have : ∀ v, IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => φ v (ev z v) := fun v =>
        (hSB v).1.comp_continuous (hcont v)
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun z => ?_
      have h2 : ∀ᶠ w in nhds z, ∀ v ∈ hS.toFinset, φ v (ev w v) = φ v (ev z v) :=
        (Filter.eventually_all_finset _).2 fun v _ => (IsLocallyConstant.iff_eventually_eq _).1 (this v) z
      filter_upwards [h2] with w hw
      exact Finset.prod_congr rfl hw
    filter_upwards [hGo.mem_nhds hy, (IsLocallyConstant.iff_eventually_eq _).1 hlc y] with z hz hz'
    rw [heq z hz, heq y hy]
    exact hz'
  ·
    push_neg at hy
    obtain ⟨v, hvS, hvL⟩ := hy
    have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
    let U : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ev z v ∉ L v}
    have hLc : IsClosed (L v) := by
      have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        ext x; simp [L]
      rw [e]
      exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
    have hUo : IsOpen U := hLc.isOpen_compl.preimage (hcont v)
    have h0 : ∀ z ∈ U, ∏ᶠ w, φ w (ev z w) = 0 := fun z hz =>
      finprod_eq_zero _ v (by show φ v (ev z v) = 0; rw [hφ, Set.indicator_of_notMem hz]) (hfin z)
    filter_upwards [hUo.mem_nhds hvL] with z hz
    rw [h0 z hz, h0 y hvL]

end GlobalTheory.AdelicCoordSB
