import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import GroundTheory.GlobalFields.TateThesis.Chebotarev

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.F.Inert

namespace InertPlacesInfinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev inertSet (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :=
  GroundTheory.Global.chebotarevSet (K := maximalRealSubfield E) (L := E) {IsCMField.complexConj E}

/- English proof (translation)
Introduce `hfin`. Establish `hZ` using `GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop K`. Establish `hlim : Filter.Tendsto (fun s => NumberField.Set.primeIdealZetaSum S s / NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)`. Establish `hup : Filter.Tendsto (fun s => (S.ncard : ℝ) / NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)` using `tendsto_const_nhds.div_atTop hZ`. Apply `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup` to reduce the goal to its premises.

Use `filter_upwards with s`. Conclude with `div_nonneg (NumberField.Set.primeIdealZetaSum_nonneg _ _) (NumberField.Set.primeIdealZetaSum_nonneg _ _)`. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Establish `hs' : (0 : ℝ) ≤ s` using `le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hs))`. Conclude with `div_le_div_of_nonneg_right (NumberField.Set.primeIdealZetaSum_le_card_of_finite hfin hs') (NumberField.Set.primeIdealZetaSum_nonneg _ _)`.

Establish `h0` using `tendsto_nhds_unique h hlim`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem infinite_of_hasDirichletDensity_pos {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : NumberField.Set.HasDirichletDensity S δ) (hδ : 0 < δ) : S.Infinite := by
  intro hfin
  have hZ := GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop K
  have hlim : Filter.Tendsto (fun s => NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hup : Filter.Tendsto (fun s => (S.ncard : ℝ) / NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := tendsto_const_nhds.div_atTop hZ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards with s
      exact div_nonneg (NumberField.Set.primeIdealZetaSum_nonneg _ _)
        (NumberField.Set.primeIdealZetaSum_nonneg _ _)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (0 : ℝ) ≤ s := le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hs))
      exact div_le_div_of_nonneg_right
        (NumberField.Set.primeIdealZetaSum_le_card_of_finite hfin hs')
        (NumberField.Set.primeIdealZetaSum_nonneg _ _)
  have h0 := tendsto_nhds_unique h hlim
  linarith

/- English proof (translation)
Establish `hσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj E)`. Rewrite using `[IsCMField.zpowers_complexConj_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hσ`. Rewrite using `[← zpow_mod_orderOf, IsCMField.orderOf_complexConj]`.

Use `push_cast`. Apply the tactic sequence `rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]`.
-/
private theorem eq_one_or_eq_complexConj_of_maximalRealSubfield (E : Type) [Field E] [NumberField E] [IsCMField E]
    (σ : Gal(E/↥(maximalRealSubfield E))) : σ = 1 ∨ σ = IsCMField.complexConj E := by
  have hσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj E) := by
    rw [IsCMField.zpowers_complexConj_eq_top]
    trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  rw [← zpow_mod_orderOf, IsCMField.orderOf_complexConj]
  push_cast
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]

/- English proof (translation)
Establish `hcl : ∀ σ ∈ ({IsCMField.complexConj E} : Set Gal(E/↥(maximalRealSubfield E))), ∀ τ : Gal(E/↥(maximalRealSubfield E)), τ * σ * τ⁻¹ ∈ ({IsCMField.complexConj E} : Set Gal(E/↥(maximalRealSubfield E)))`. Introduce `σ hσ τ`. Rewrite `hσ`, the goal using `[Set.mem_singleton_iff]`. Substitute `hσ` using the available equality. Apply the tactic sequence `rcases eq_one_or_eq_complexConj_of_maximalRealSubfield E τ with h | h <;> subst h <;> group`.

Establish `hd` using `GroundTheory.Global.hasDirichletDensity_chebotarevSet (K := ↥(maximalRealSubfield E)) (L := E) _ hcl`. Apply `infinite_of_hasDirichletDensity_pos hd` to reduce the goal to its premises. Establish `h2 : Nat.card Gal(E/↥(maximalRealSubfield E)) = 2`. Rewrite using `[IsGalois.card_aut_eq_finrank]`. Use `haveI := IsCMField.isQuadraticExtension E`.

Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
theorem inertSet_infinite : (inertSet E).Infinite := by
  have hcl : ∀ σ ∈ ({IsCMField.complexConj E} : Set Gal(E/↥(maximalRealSubfield E))),
      ∀ τ : Gal(E/↥(maximalRealSubfield E)), τ * σ * τ⁻¹ ∈
        ({IsCMField.complexConj E} : Set Gal(E/↥(maximalRealSubfield E))) := by
    intro σ hσ τ
    rw [Set.mem_singleton_iff] at hσ ⊢
    subst hσ
    rcases eq_one_or_eq_complexConj_of_maximalRealSubfield E τ with h | h <;> subst h <;> group
  have hd := GroundTheory.Global.hasDirichletDensity_chebotarevSet
    (K := ↥(maximalRealSubfield E)) (L := E) _ hcl
  apply infinite_of_hasDirichletDensity_pos hd
  have h2 : Nat.card Gal(E/↥(maximalRealSubfield E)) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    haveI := IsCMField.isQuadraticExtension E
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2]
  simp

/- English proof (translation)
Use `haveI := hw`. Use `haveI := hu`. Take `⟨σ, hσ⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal u.asIdeal Gal(E/↥(maximalRealSubfield E))`. Apply `IsDedekindDomain.HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[← hσ]`.

Break down `eq_one_or_eq_complexConj_of_maximalRealSubfield E σ with h | h` into its components or cases. Rewrite using `[h, one_smul]`. Establish `hfrob` using `(hv w hw).2`. Rewrite `hfrob` using `[Set.mem_singleton_iff]`. Establish `hst` using `(IsArithFrobAt.arithFrobAt (𝓞 ↥(maximalRealSubfield E)) Gal(E/↥(maximalRealSubfield E)) w.asIdeal).mem_stabilizer`.

Rewrite `hst` using `[hfrob, ← h]`. Conclude with `MulAction.mem_stabilizer_iff.mp hst`.
-/
theorem eq_of_liesOver {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} (hv : v ∈ inertSet E)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : w.asIdeal.LiesOver v.asIdeal) (hu : u.asIdeal.LiesOver v.asIdeal) :
    u = w := by
  haveI := hw
  haveI := hu
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal u.asIdeal
    Gal(E/↥(maximalRealSubfield E))
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [← hσ]
  rcases eq_one_or_eq_complexConj_of_maximalRealSubfield E σ with h | h
  · rw [h, one_smul]
  · have hfrob := (hv w hw).2
    rw [Set.mem_singleton_iff] at hfrob
    have hst := (IsArithFrobAt.arithFrobAt (𝓞 ↥(maximalRealSubfield E))
      Gal(E/↥(maximalRealSubfield E)) w.asIdeal).mem_stabilizer
    rw [hfrob, ← h] at hst
    exact MulAction.mem_stabilizer_iff.mp hst

end InertPlacesInfinite

/- English proof (translation)
Introduce `E _ _ _ _ n π hπ Sec hSec X`. Establish `hB : {w : HeightOneSpectrum (𝓞 E) | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}.Finite` using `Filter.eventually_cofinite.mp (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)`. Use `set T : Set (HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) := (fun w : HeightOneSpectrum (𝓞 E) => HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w) '' ((X : Set (GlobalTheory.BCT.Pl E)) ∪ {w | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}) with hT`. Establish `hTf : T.Finite` using `(X.finite_toSet.union hB).image _`. Take `⟨v, hv, hvT⟩` from `(InertPlacesInfinite.inertSet_infinite (E := E)).exists_notMem_finite hTf`.

Take `⟨⟨Q, hQp, hQo⟩⟩` from `Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal`. Establish `hQb : Q ≠ ⊥`. Introduce `h0`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[hQo.over, h0]`.

Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Set `w0 : HeightOneSpectrum (𝓞 E)` to `⟨Q, hQp, hQb⟩`. Establish `hw0 : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w0 = v` using `HeightOneSpectrum.ext hQo.over.symm`. Take `⟨u, ⟨huSec, huw⟩, -⟩` from `hSec w0`. Establish `huv : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) u = v` using `huw.trans hw0`.

Use `⟨u, huSec, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `huX`. Conclude with `hvT ⟨u, Or.inl huX, huv⟩`. Introduce and unpack `⟨u', hne, hu'⟩`. Apply `hne` to reduce the goal to its premises.

Establish `h1 : u.asIdeal.LiesOver v.asIdeal` using `⟨(congrArg HeightOneSpectrum.asIdeal huv).symm⟩`. Establish `h2 : u'.asIdeal.LiesOver v.asIdeal` using `⟨(congrArg HeightOneSpectrum.asIdeal (hu'.trans huv)).symm⟩`. Conclude with `InertPlacesInfinite.eq_of_liesOver hv h1 h2`. Assume the negation of the conclusion as `hun`. Conclude with `hvT ⟨u, Or.inr hun, huv⟩`.
-/
theorem inertPlaceEx : InertPlaceEx := by
  intro E _ _ _ _ n π hπ Sec hSec X
  have hB : {w : HeightOneSpectrum (𝓞 E) | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}.Finite :=
    Filter.eventually_cofinite.mp (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)
  set T : Set (HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) :=
    (fun w : HeightOneSpectrum (𝓞 E) => HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w) ''
      ((X : Set (GlobalTheory.BCT.Pl E)) ∪ {w | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}) with hT
  have hTf : T.Finite := (X.finite_toSet.union hB).image _
  obtain ⟨v, hv, hvT⟩ := (InertPlacesInfinite.inertSet_infinite (E := E)).exists_notMem_finite hTf
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  have hQb : Q ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [hQo.over, h0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  let w0 : HeightOneSpectrum (𝓞 E) := ⟨Q, hQp, hQb⟩
  have hw0 : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w0 = v :=
    HeightOneSpectrum.ext hQo.over.symm
  obtain ⟨u, ⟨huSec, huw⟩, -⟩ := hSec w0
  have huv : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) u = v := huw.trans hw0
  refine ⟨u, huSec, ?_, ?_, ?_⟩
  · intro huX
    exact hvT ⟨u, Or.inl huX, huv⟩
  · rintro ⟨u', hne, hu'⟩
    apply hne
    have h1 : u.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal huv).symm⟩
    have h2 : u'.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal (hu'.trans huv)).symm⟩
    exact InertPlacesInfinite.eq_of_liesOver hv h1 h2
  · by_contra hun
    exact hvT ⟨u, Or.inr hun, huv⟩

end PositivityTheory.Rg.BcB.F.Inert

end
