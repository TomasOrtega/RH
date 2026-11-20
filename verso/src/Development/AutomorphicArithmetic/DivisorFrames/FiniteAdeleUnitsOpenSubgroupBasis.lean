import Mathlib
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
open NumberField IsDedekindDomain Filter Topology
open scoped RestrictedProduct

/- English proof (translation)
Use `⟨fun s _ hs => ?_⟩` and prove the remaining obligations. Establish `h` using `(hs.image f hf.continuousOn).subsingleton`. Conclude with `fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))`.
-/
private theorem td_of_inj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_zero]`. Use `Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0` using `(Valuation.zero_iff _).not.mpr hne`. Establish `hc` using `Valued.isClopen_ball (R := v.adicCompletion F) ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)`.

Establish `h0 : (0 : v.adicCompletion F) ∈ {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y < (Valued.v : Valuation (v.adicCompletion F) _).restrict x}`. Simplify using `only [Set.mem_ofPred_eq, map_zero]`. Conclude with `pos_iff_ne_zero.mpr hr`. Establish `h1` using `hc.connectedComponent_subset h0 hx`. Conclude with `(lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1`.
-/
private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

/- English proof (translation)
Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v`. Use `haveI : TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) := td_of_inj (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v) fun x y h => Subtype.ext (funext fun v => congrFun h v)`. Conclude with `inferInstanceAs (TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))`.
-/
private theorem td_finiteAdele (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v
  haveI : TotallyDisconnectedSpace
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) :=
    td_of_inj (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

/- English proof (translation)
The claim follows from `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc haveI : NonarchimedeanGroup K := ⟨fun U hU => by obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U)) (mem_interior_iff_mem_nhds.2 hU) exact ⟨N.toOpenSubgroup, hN.trans in …`.
-/
private theorem nonarch_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

/- English proof (translation)
Introduce `E _ _ W hW`. Use `haveI := td_finiteAdele E`. Use `haveI : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 E) E)ˣ := td_of_inj Units.val Units.continuous_val Units.val_injective`. Use `haveI := nonarch_of_isCompact_isOpen (GroundTheory.Global.isCompact_finiteIntegralUnits E) (GroundTheory.Global.isOpen_finiteIntegralUnits E)`. Conclude with `NonarchimedeanGroup.is_nonarchimedean W hW`.
-/
theorem UpperTheory.finiteAdele_units_open_subgroup_basis :
    ∀ (E : Type) [Field E] [NumberField E], ∀ W ∈ nhds (1 : (FiniteAdeleRing (𝓞 E) E)ˣ), ∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 E) E)ˣ, (U : Set (FiniteAdeleRing (𝓞 E) E)ˣ) ⊆ W := by
  intro E _ _ W hW
  haveI := td_finiteAdele E
  haveI : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 E) E)ˣ :=
    td_of_inj Units.val Units.continuous_val Units.val_injective
  haveI := nonarch_of_isCompact_isOpen (GroundTheory.Global.isCompact_finiteIntegralUnits E)
    (GroundTheory.Global.isOpen_finiteIntegralUnits E)
  exact NonarchimedeanGroup.is_nonarchimedean W hW
