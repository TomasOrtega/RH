import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMaps

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.SpreadFromGeneric

/- English proof (translation)
Set `η : Spec (T.presheaf.stalk p)` to `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (T.presheaf.stalk p))`. Establish `h1 : T.fromSpecStalk p η = p` using `hp _ (by`. Establish `: T.fromSpecStalk p η ∈ Set.range (T.fromSpecStalk p)` using `⟨η, rfl⟩`. Rewrite using `[Scheme.range_fromSpecStalk] at this)` and apply the resulting hypothesis. Establish `h2 : T.fromSpecStalk p η = T.fromSpecStalk p (closedPoint _)` using `h1.trans Scheme.fromSpecStalk_closedPoint.symm`.

Establish `h3` using `(T.fromSpecStalk p).isEmbedding.injective h2`. Conclude with `(congrArg PrimeSpectrum.asIdeal h3).symm`.
-/
theorem maximalIdeal_stalk_eq_bot {T : Scheme.{0}} (p : T) [IsDomain (T.presheaf.stalk p)]
    (hp : ∀ q : T, q ⤳ p → q = p) : maximalIdeal (T.presheaf.stalk p) = ⊥ := by
  let η : Spec (T.presheaf.stalk p) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (T.presheaf.stalk p))
  have h1 : T.fromSpecStalk p η = p := hp _ (by
    have : T.fromSpecStalk p η ∈ Set.range (T.fromSpecStalk p) := ⟨η, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this)
  have h2 : T.fromSpecStalk p η = T.fromSpecStalk p (closedPoint _) :=
    h1.trans Scheme.fromSpecStalk_closedPoint.symm
  have h3 := (T.fromSpecStalk p).isEmbedding.injective h2
  exact (congrArg PrimeSpectrum.asIdeal h3).symm

/- English proof (translation)
Establish `surj` using `SurjectiveOnStalks.stalkMap_surjective j q`. Establish `inj : Function.Injective (ConcreteCategory.hom (j.stalkMap q))`. Rewrite using `[RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← h]`. Conclude with `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)`. Conclude with `(ConcreteCategory.isIso_iff_bijective _).2 ⟨inj, surj⟩`.
-/
theorem isIso_stalkMap {U T : Scheme.{0}} (j : U ⟶ T) [SurjectiveOnStalks j] (q : U)
    (h : maximalIdeal (T.presheaf.stalk (j q)) = ⊥) : IsIso (j.stalkMap q) := by
  have surj := SurjectiveOnStalks.stalkMap_surjective j q
  have inj : Function.Injective (ConcreteCategory.hom (j.stalkMap q)) := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← h]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨inj, surj⟩

/- English proof (translation)
Introduce `S T U Y t s j g _ _ _ hn _ _ _ hgs p hp hgen`. Establish `: GlobalTheory.IsNormalScheme T` using `GlobalTheory.IsNormalScheme.of_pred hn`. Take `⟨q, rfl⟩` from `hp`. Establish `: IsIso (j.stalkMap q)` using `isIso_stalkMap j q (maximalIdeal_stalk_eq_bot (j q) hgen)`. Set `v : Spec (T.presheaf.stalk (j q)) ⟶ U` to `Spec.map (inv (j.stalkMap q)) ≫ U.fromSpecStalk q`.

Establish `hv : v ≫ j = T.fromSpecStalk (j q)`. Simplify using `only [v, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]`. Establish `hvinv : Spec.map (j.stalkMap q) ≫ v = U.fromSpecStalk q`. Simplify using `only [v]`.

Rewrite using `[← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]`. Establish `hsp : (v ≫ g) ≫ s = T.fromSpecStalk (j q) ≫ t`. Rewrite using `[Category.assoc, hgs, ← Category.assoc, hv]`. Take `⟨W₀, hW₀, f₀, h₁, h₂⟩` from `spread_out_of_isGermInjective' t s (v ≫ g) hsp`. Set `Z : irreducibleComponents T` to `⟨_, irreducibleComponent_mem_irreducibleComponents (j q)⟩`.

Set `W : T.Opens` to `W₀ ⊓ GlobalTheory.IsNormalScheme.component Z`. Establish `hpW : j q ∈ W` using `⟨hW₀, GlobalTheory.IsNormalScheme.mem_component.2 mem_irreducibleComponent⟩`. Establish `hgenW : ∀ y ∈ W, j q ⤳ y`. Introduce `y hy`. Take `⟨η, hη⟩` from `QuasiSober.sober (isIrreducible_irreducibleComponent (x := j q)) isClosed_irreducibleComponent`.

Establish `h1 : η ⤳ j q` using `(isGenericPoint_iff_specializes.1 hη _).2 mem_irreducibleComponent`. Rewrite `hη` using `[hgen η h1]`. Conclude with `(isGenericPoint_iff_specializes.1 hη y).2 (GlobalTheory.IsNormalScheme.mem_component.1 hy.2)`. Establish `hq : q ∈ j ⁻¹ᵁ W` using `hpW`. Establish `e1 : (j ⁻¹ᵁ W).ι ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _)) = q`.

Establish `h` using `Scheme.Hom.comp_apply ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) (j ⁻¹ᵁ W).ι (closedPoint _)`. Rewrite `h` using `[Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]`. Conclude with `h.symm`. Establish `hd : IsDominant ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq)`. Use `⟨?_⟩` and prove the remaining obligations.

Introduce `x`. Establish `hs : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _) ⤳ x`. Rewrite using `[← ((j ⁻¹ᵁ W).ι ≫ j).isEmbedding.isInducing.specializes_iff, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]`. Conclude with `hgenW _ x.2`. Conclude with `closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (closedPoint _))) (specializes_iff_mem_closure.1 hs)`.

Establish `e2 : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq ≫ j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) = Spec.map (j.stalkMap q) ≫ W₀.fromSpecStalkOfMem (j q) hW₀`. Rewrite using `[← cancel_mono W₀.ι]`. Simplify using `only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.Opens.fromSpecStalkOfMem_ι_assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]`. Establish `key : j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) ≫ f₀ = (j ⁻¹ᵁ W).ι ≫ g`. Use `ext_of_isDominant_of_isSeparated s ?_ ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc, h₂, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc, hgs]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Category.assoc]`. Use `_ = Spec.map (j.stalkMap q) ≫ v ≫ g := by rw [e2, Category.assoc, ← h₁]`. Use `_ = U.fromSpecStalk q ≫ g := by rw [← Category.assoc, hvinv]`.

Use `_ = _ := by rw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]`. Use `⟨W, T.homOfLE inf_le_left ≫ f₀, v, hpW, hv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h₂, Scheme.homOfLE_ι_assoc]`. Introduce `T' u w huw`. Establish `hr : Set.range w ⊆ Set.range (j ⁻¹ᵁ W).ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Express the relevant statement in the definitionally equal form `j (w x) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply, ← huw, Scheme.Hom.comp_apply]`. Conclude with `(u x).2`.

Set `w'` to `IsOpenImmersion.lift (j ⁻¹ᵁ W).ι w hr`. Establish `hw' : w' ≫ (j ⁻¹ᵁ W).ι = w` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hu : u = w' ≫ j ∣_ W`. Rewrite using `[← cancel_mono W.ι, huw, Category.assoc, morphismRestrict_ι, ← Category.assoc, hw']`. Rewrite using `[hu, Category.assoc, key, ← Category.assoc, hw']`.
-/
theorem exists_spread : ∀ (S T U Y : Scheme.{0}) (t : T ⟶ S) (s : Y ⟶ S) (j : U ⟶ T) (g : U ⟶ Y), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsReduced U → IsPreimmersion j → Flat j → g ≫ s = j ≫ t → ∀ p : T, p ∈ Set.range j → (∀ q : T, q ⤳ p → q = p) → ∃ (W : T.Opens) (f : W.toScheme ⟶ Y) (v : Spec (T.presheaf.stalk p) ⟶ U), p ∈ W ∧ v ≫ j = T.fromSpecStalk p ∧ f ≫ s = W.ι ≫ t ∧ ∀ (T' : Scheme.{0}) (u : T' ⟶ W.toScheme) (w : T' ⟶ U), u ≫ W.ι = w ≫ j → u ≫ f = w ≫ g := by
  intro S T U Y t s j g _ _ _ hn _ _ _ hgs p hp hgen
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  obtain ⟨q, rfl⟩ := hp
  have : IsIso (j.stalkMap q) := isIso_stalkMap j q (maximalIdeal_stalk_eq_bot (j q) hgen)
  let v : Spec (T.presheaf.stalk (j q)) ⟶ U := Spec.map (inv (j.stalkMap q)) ≫ U.fromSpecStalk q
  have hv : v ≫ j = T.fromSpecStalk (j q) := by
    simp only [v, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hvinv : Spec.map (j.stalkMap q) ≫ v = U.fromSpecStalk q := by
    simp only [v]
    rw [← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]
  have hsp : (v ≫ g) ≫ s = T.fromSpecStalk (j q) ≫ t := by
    rw [Category.assoc, hgs, ← Category.assoc, hv]
  obtain ⟨W₀, hW₀, f₀, h₁, h₂⟩ := spread_out_of_isGermInjective' t s (v ≫ g) hsp
  let Z : irreducibleComponents T := ⟨_, irreducibleComponent_mem_irreducibleComponents (j q)⟩
  let W : T.Opens := W₀ ⊓ GlobalTheory.IsNormalScheme.component Z
  have hpW : j q ∈ W := ⟨hW₀, GlobalTheory.IsNormalScheme.mem_component.2 mem_irreducibleComponent⟩
  have hgenW : ∀ y ∈ W, j q ⤳ y := by
    intro y hy
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := j q))
      isClosed_irreducibleComponent
    have h1 : η ⤳ j q := (isGenericPoint_iff_specializes.1 hη _).2 mem_irreducibleComponent
    rw [hgen η h1] at hη
    exact (isGenericPoint_iff_specializes.1 hη y).2 (GlobalTheory.IsNormalScheme.mem_component.1 hy.2)
  have hq : q ∈ j ⁻¹ᵁ W := hpW
  have e1 : (j ⁻¹ᵁ W).ι ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _)) = q := by
    have h := Scheme.Hom.comp_apply ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) (j ⁻¹ᵁ W).ι (closedPoint _)
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint] at h
    exact h.symm
  have hd : IsDominant ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) := by
    refine ⟨?_⟩
    intro x
    have hs : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _) ⤳ x := by
      rw [← ((j ⁻¹ᵁ W).ι ≫ j).isEmbedding.isInducing.specializes_iff, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, e1]
      exact hgenW _ x.2
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (closedPoint _))) (specializes_iff_mem_closure.1 hs)
  have e2 : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq ≫ j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) =
      Spec.map (j.stalkMap q) ≫ W₀.fromSpecStalkOfMem (j q) hW₀ := by
    rw [← cancel_mono W₀.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.Opens.fromSpecStalkOfMem_ι_assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have key : j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) ≫ f₀ = (j ⁻¹ᵁ W).ι ≫ g := by
    refine ext_of_isDominant_of_isSeparated s ?_ ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) ?_
    · simp only [Category.assoc, h₂, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc, hgs]
    · calc _ = ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq ≫ j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀)) ≫ f₀ := by
            simp only [Category.assoc]
        _ = Spec.map (j.stalkMap q) ≫ v ≫ g := by rw [e2, Category.assoc, ← h₁]
        _ = U.fromSpecStalk q ≫ g := by rw [← Category.assoc, hvinv]
        _ = _ := by rw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
  refine ⟨W, T.homOfLE inf_le_left ≫ f₀, v, hpW, hv, ?_, ?_⟩
  · rw [Category.assoc, h₂, Scheme.homOfLE_ι_assoc]
  · intro T' u w huw
    have hr : Set.range w ⊆ Set.range (j ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change j (w x) ∈ W
      rw [← Scheme.Hom.comp_apply, ← huw, Scheme.Hom.comp_apply]
      exact (u x).2
    let w' := IsOpenImmersion.lift (j ⁻¹ᵁ W).ι w hr
    have hw' : w' ≫ (j ⁻¹ᵁ W).ι = w := IsOpenImmersion.lift_fac _ _ _
    have hu : u = w' ≫ j ∣_ W := by
      rw [← cancel_mono W.ι, huw, Category.assoc, morphismRestrict_ι, ← Category.assoc, hw']
    rw [hu, Category.assoc, key, ← Category.assoc, hw']

end GlobalTheory.SpreadFromGeneric
