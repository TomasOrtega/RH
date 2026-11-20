import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

namespace PositivityTheory.ThKG

open IsDedekindDomain NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `y`. Establish `hy : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv`. Use `set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧ ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT`. Establish `hTfin : T.Finite` using `hcof.and hy`.

Establish `hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`. Establish `hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F`. Use `Filter.eventually_all.2 fun i => ?_` and prove the remaining obligations. Establish `hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i` using `(continuous_apply i).sub continuous_const`. Establish `hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈ {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F}`.

Introduce `v`. Simplify using `only [sub_self]`. Conclude with `zero_mem _`. Conclude with `hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)`. Establish `hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) = φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)`.

Use `(Filter.eventually_all_finite hTfin).2 fun v _ => ?_` and prove the remaining obligations. Establish `hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)` using `continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)`. Conclude with `((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y`. Use `filter_upwards [hU, hS] with y' hU' hS'`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ T`. Conclude with `hS' v hv`. Establish `hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧ ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F`. Simplify `hv` using `[hT]`. Take `⟨h1, h2⟩` from `hv'`.

Establish `h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F`. Introduce `i`. Establish `h4` using `add_mem (hU' i v) (h2 i)`. Establish `h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)` using `by show (y' i) v - (y i) v + (y i) v = (y' i) v`. Conclude with `sub_add_cancel _ _`.

Rewrite `h4` using `[h5]`. Then use the resulting hypothesis. Rewrite using `[h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3), Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ( …`. Both sides reduce to the same expression.
-/
theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hy : ∀ᶠ v in Filter.cofinite, ∀ i,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT
  have hTfin : T.Finite := hcof.and hy
  have hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i :=
      (continuous_apply i).sub continuous_const
    have hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈
        {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} := by
      intro v
      simp only [sub_self]
      exact zero_mem _
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
  have hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) =
      φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
    refine (Filter.eventually_all_finite hTfin).2 fun v _ => ?_
    have hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F =>
        fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    exact ((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y
  filter_upwards [hU, hS] with y' hU' hS'
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ T
  · exact hS' v hv
  · have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      simpa [hT] using hv
    obtain ⟨h1, h2⟩ := hv'
    have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F := by
      intro i
      have h4 := add_mem (hU' i v) (h2 i)
      have h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) := by
        show (y' i) v - (y i) v + (y i) v = (y' i) v
        exact sub_add_cancel _ _
      rwa [h5] at h4
    rw [h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3),
      Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl

/- English proof (translation)
Introduce `F _ _ κ _ φ hSB hae`. Set `L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → Fv F v)` to `fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}`. Establish `hLc : ∀ v, IsClosed (L v)` using `fun v => by`. Establish `e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `x`.

Simplify using `[L]`. Rewrite using `[e]`. Conclude with `isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed`. Establish `hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite, (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ L v` using `fun y => Filter.eventually_all.2 fun i => (y i).2`. Establish `hfac : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, (∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 → ∀ v, φ v (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0`.

Introduce `y h v`. Establish `hfin : (Function.mulSupport fun v => φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)).Finite`. Use `(Filter.eventually_cofinite.1 (hae.and (hint y))).subset ?_` and prove the remaining obligations. Introduce `w hw h'`. Apply `hw` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[h'.1, Set.indicator_of_mem h'.2]`. Both sides reduce to the same expression. Rewrite `h` using `[finprod_eq_prod _ hfin]`. Distinguish the cases in `hv : v ∈ hfin.toFinset`.

Conclude with `Finset.prod_ne_zero_iff.1 h v hv`. Rewrite `hv` using `[Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not]`. Rewrite using `[hv]`. Conclude with `one_ne_zero`. Set `D : κ → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (Fv F v)` to `fun i v => ((fun Z : κ → Fv F v => Z i) '' tsupport (φ v)) ∪ (v.adicCompletionIntegers F : Set (Fv F v))`.

Establish `hD : ∀ i v, IsCompact (D i v)` using `fun i v => ((hSB v).2.isCompact.image (continuous_apply i)).union (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)`. Establish `hDe : ∀ i, ∀ᶠ v in Filter.cofinite, D i v = (v.adicCompletionIntegers F : Set (Fv F v))`. Introduce `i`. Use `filter_upwards [hae] with v hv`. Use `Set.union_eq_right.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨Z, hZ, rfl⟩`. Establish `hsub : tsupport (φ v) ⊆ L v`. Rewrite using `[hv]`. Conclude with `closure_minimal Set.support_indicator_subset (hLc v)`. Conclude with `hsub hZ i`.

Set `Box : Set (κ → FiniteAdeleRing (𝓞 F) F)` to `Set.pi Set.univ fun i => {x | ∀ v, x v ∈ D i v}`. Establish `hbox : IsCompact Box` using `isCompact_univ_pi fun i => PI.VolStabS.AdmissibleCompactSupport.isCompact_finBox (hD i) (hDe i)`. Use `HasCompactSupport.intro hbox fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Apply `hy` to reduce the goal to its premises.

Introduce `i _ v`. Conclude with `Or.inl ⟨_, subset_tsupport _ (hfac y h v), rfl⟩`.
-/
theorem hasCompactSupport_finprod : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ φ hSB hae
  classical
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → Fv F v) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  have hLc : ∀ v, IsClosed (L v) := fun v => by
    have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [L]
    rw [e]
    exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ L v := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  have hfac : ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      (∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 →
      ∀ v, φ v (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 := by
    intro y h v
    have hfin : (Function.mulSupport fun v => φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)).Finite := by
      refine (Filter.eventually_cofinite.1 (hae.and (hint y))).subset ?_
      intro w hw h'
      apply hw
      simp only
      rw [h'.1, Set.indicator_of_mem h'.2]
      rfl
    rw [finprod_eq_prod _ hfin] at h
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 h v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  let D : κ → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun i v =>
    ((fun Z : κ → Fv F v => Z i) '' tsupport (φ v)) ∪ (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i v, IsCompact (D i v) := fun i v =>
    ((hSB v).2.isCompact.image (continuous_apply i)).union (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i, ∀ᶠ v in Filter.cofinite,
      D i v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (φ v) ⊆ L v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (hLc v)
    exact hsub hZ i
  let Box : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
    Set.pi Set.univ fun i => {x | ∀ v, x v ∈ D i v}
  have hbox : IsCompact Box :=
    isCompact_univ_pi fun i => PI.VolStabS.AdmissibleCompactSupport.isCompact_finBox (hD i) (hDe i)
  refine HasCompactSupport.intro hbox fun y hy => ?_
  by_contra h
  apply hy
  intro i _ v
  exact Or.inl ⟨_, subset_tsupport _ (hfac y h v), rfl⟩

end PositivityTheory.ThKG
