import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `e' : gp ⁻¹ᵁ W = gp ⁻¹ᵁ V` using `le_antisymm (gp.preimage_mono h) e`. Establish `hh : homOfLE (gp.preimage_mono h) = eqToHom e'` using `Subsingleton.elim _ _`. Use `show Function.Bijective ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom`. Rewrite using `[hh]`. Conclude with `ConcreteCategory.bijective_of_isIso ((Sp K).presheaf.map (eqToHom e').op)`.
-/
theorem resK_bijective {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V)
    (e : gp ⁻¹ᵁ V ≤ gp ⁻¹ᵁ W) : Function.Bijective (resK gp h) := by
  have e' : gp ⁻¹ᵁ W = gp ⁻¹ᵁ V := le_antisymm (gp.preimage_mono h) e
  have hh : homOfLE (gp.preimage_mono h) = eqToHom e' := Subsingleton.elim _ _
  show Function.Bijective ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom
  rw [hh]
  exact ConcreteCategory.bijective_of_isIso ((Sp K).presheaf.map (eqToHom e').op)

/- English proof (translation)
Take `⟨p, hp, hy⟩` from `h`. Use `⟨p, hp, hg ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.hom_eval₂, hy, map_zero]`.
-/
theorem isIntegralElem_of_comp_injective {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Injective g) {y : A}
    (h : (g.comp f).IsIntegralElem (g y)) : f.IsIntegralElem y := by
  obtain ⟨p, hp, hy⟩ := h
  refine ⟨p, hp, hg ?_⟩
  rw [Polynomial.hom_eval₂, hy, map_zero]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Distinguish the cases in `h : O = ⊥`. Conclude with `Or.inl h`. Use `right`. Take `⟨x, hx⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp h`. Use `top_unique fun z _ => ?_` and prove the remaining obligations.

Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Rewrite using `[Subsingleton.elim z x]` and apply the resulting hypothesis.
-/
theorem eq_bot_or_eq_top_of_sp (K : Type) [Field K] (O : (Sp K).Opens) : O = ⊥ ∨ O = ⊤ := by
  by_cases h : O = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp h
    refine top_unique fun z _ => ?_
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim z x]
end GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `S K _ gp V W hWV hV hW b hb`. Set `C : Finset Γ(Sp K, gp ⁻¹ᵁ V) → Subring Γ(Sp K, gp ⁻¹ᵁ W)` to `fun s => Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _))`. Establish `Cmono : ∀ s t : Finset Γ(Sp K, gp ⁻¹ᵁ V), s ⊆ t → C s ≤ C t`. Introduce `s t hst`. Use `Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono ?_))` and prove the remaining obligations.

Conclude with `hst` after adjusting the coercions. Set `J : Ideal Γ(S, W)` to `{ carrier := {c | ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧ (gp.app W).hom c * b ∈ C s} zero_mem' := ⟨∅, by simp, by rw [map_zero, zero_mul]; exact zero_mem _⟩ add_mem' := by`. Introduce and unpack `c d ⟨s, hs, hc⟩ ⟨t, ht, hd⟩`. Use `⟨s ∪ t, fun y hy => (Finset.mem_union.mp hy).elim (hs y) (ht y), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, add_mul]`.

Conclude with `add_mem (Cmono _ _ Finset.subset_union_left hc) (Cmono _ _ Finset.subset_union_right hd)`. Use the proof step `smul_mem' := by`. Introduce and unpack `c d ⟨s, hs, hd⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, _root_.mul_assoc]`.

Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hd }`. Set `T : Set Γ(S, W)` to `{c | ∃ g : Γ(S, V), S.basicOpen g ≤ W ∧ (S.presheaf.map (homOfLE hWV).op).hom g = c}`. Establish `hspan : Ideal.span T = ⊤`. Use `hW.self_le_iSup_basicOpen_iff.mp ?_` and prove the remaining obligations. Introduce `x hx`.

Take `⟨g, hg, hxg⟩` from `hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWV hx)`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Use `⟨⟨_, g, hg, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show x ∈ S.basicOpen ((S.presheaf.map (homOfLE hWV).op).hom g)`. Rewrite using `[Scheme.basicOpen_res]`.

Conclude with `⟨hx, hxg⟩`. Establish `hT : T ⊆ J.radical`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `set D := S.basicOpen g with hD`. Break down `eq_bot_or_eq_top_of_sp K (gp ⁻¹ᵁ D) with h0 | h1` into its components or cases.

Establish `hz : (gp.app V).hom g = 0`. Rewrite using `[← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]`. Conclude with `h0`. Use `⟨1, ∅, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, ← resK_app, hz, map_zero, zero_mul]`.

Conclude with `zero_mem _`. Establish `hDW : D ≤ W` using `hg`. Establish `hDV : D ≤ V` using `hDW.trans hWV`. Use `hV.isLocalization_basicOpen g` as an intermediate fact. Use `letI : Algebra Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := (gp.app D).hom.toAlgebra`.

Use `letI : Algebra Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := ((gp.app D).hom.comp (algebraMap Γ(S, V) Γ(S, D))).toAlgebra`. Use `haveI : IsScalarTower Γ(S, V) Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `sq : (resK gp hDW).comp (gp.app W).hom = (gp.app D).hom.comp (S.presheaf.map (homOfLE hDW).op).hom`. Use extensionality with `a`. Conclude with `resK_app gp hDW a`.

Establish `hb' : IsIntegral Γ(S, D) (resK gp hDW b)`. Use `hb.map (resK gp hDW)` as an intermediate fact. Rewrite `this` using `[sq]`. Conclude with `RingHom.isIntegralElem.of_comp _ _ this`. Take `⟨⟨_, N, rfl⟩, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g) (Rₘ := Γ(S, D)) _ hb'`.

Establish `top : ∀ U : S.Opens, gp ⁻¹ᵁ U ≤ gp ⁻¹ᵁ D` using `fun _ => h1 ▸ le_top`. Take `⟨y, hy⟩` from `(resK_bijective gp hDV (top V)).2 ((g ^ N) • resK gp hDW b)`. Establish `alg : ∀ a : Γ(S, V), algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) a = resK gp hDV ((gp.app V).hom a)`. Introduce `a`. Rewrite using `[resK_app]`.

Both sides reduce to the same expression. Establish `hyi : (gp.app V).hom.IsIntegralElem y`. Use `isIntegralElem_of_comp_injective _ (resK gp hDV) (resK_bijective gp hDV (top V)).1 ?_` and prove the remaining obligations. Establish `e : (resK gp hDV).comp (gp.app V).hom = algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D)`. Use extensionality with `a`.

Conclude with `(alg a).symm`. Rewrite using `[e, hy]`. Conclude with `hm`. Use `⟨N, {y}, by simpa using hyi, ?_⟩` and prove the remaining obligations. Establish `key : resK gp hWV y = (gp.app W).hom ((S.presheaf.map (homOfLE hWV).op).hom g ^ N) * b`.

Apply `(resK_bijective gp hDW (top W)).1` to reduce the goal to its premises. Rewrite using `[resK_resK, hy, Algebra.smul_def, alg, map_mul]`. Simplify using `only [map_pow]`. Rewrite using `[← resK_app gp hWV g, resK_resK]`. Rewrite using `[← key]`.

Conclude with `Subring.subset_closure (Or.inr ⟨y, by simp, rfl⟩)`. Establish `hJ : J = ⊤` using `Ideal.radical_eq_top.mp (top_unique (hspan ▸ Ideal.span_le.mpr hT))`. Take `⟨s, hs, h⟩ : (1 : Γ(S, W)) ∈ J` from `hJ ▸ Submodule.mem_top`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Simplify using `using h`.
-/
theorem mem_closure_of_isIntegralElem_affine_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  intro S K _ gp V W hWV hV hW b hb
  classical
  let C : Finset Γ(Sp K, gp ⁻¹ᵁ V) → Subring Γ(Sp K, gp ⁻¹ᵁ W) := fun s =>
    Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _))
  have Cmono : ∀ s t : Finset Γ(Sp K, gp ⁻¹ᵁ V), s ⊆ t → C s ≤ C t := by
    intro s t hst
    refine Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono ?_))
    exact_mod_cast hst
  let J : Ideal Γ(S, W) :=
    { carrier := {c | ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
        (gp.app W).hom c * b ∈ C s}
      zero_mem' := ⟨∅, by simp, by rw [map_zero, zero_mul]; exact zero_mem _⟩
      add_mem' := by
        rintro c d ⟨s, hs, hc⟩ ⟨t, ht, hd⟩
        refine ⟨s ∪ t, fun y hy => (Finset.mem_union.mp hy).elim (hs y) (ht y), ?_⟩
        rw [map_add, add_mul]
        exact add_mem (Cmono _ _ Finset.subset_union_left hc) (Cmono _ _ Finset.subset_union_right hd)
      smul_mem' := by
        rintro c d ⟨s, hs, hd⟩
        refine ⟨s, hs, ?_⟩
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hd }
  let T : Set Γ(S, W) := {c | ∃ g : Γ(S, V), S.basicOpen g ≤ W ∧ (S.presheaf.map (homOfLE hWV).op).hom g = c}
  have hspan : Ideal.span T = ⊤ := by
    refine hW.self_le_iSup_basicOpen_iff.mp ?_
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWV hx)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨_, g, hg, rfl⟩, ?_⟩
    show x ∈ S.basicOpen ((S.presheaf.map (homOfLE hWV).op).hom g)
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hxg⟩
  have hT : T ⊆ J.radical := by
    rintro _ ⟨g, hg, rfl⟩
    set D := S.basicOpen g with hD
    rcases eq_bot_or_eq_top_of_sp K (gp ⁻¹ᵁ D) with h0 | h1
    ·
      have hz : (gp.app V).hom g = 0 := by
        rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
        exact h0
      refine ⟨1, ∅, by simp, ?_⟩
      rw [pow_one, ← resK_app, hz, map_zero, zero_mul]
      exact zero_mem _
    ·
      have hDW : D ≤ W := hg
      have hDV : D ≤ V := hDW.trans hWV
      have := hV.isLocalization_basicOpen g
      letI : Algebra Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := (gp.app D).hom.toAlgebra
      letI : Algebra Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := ((gp.app D).hom.comp (algebraMap Γ(S, V) Γ(S, D))).toAlgebra
      haveI : IsScalarTower Γ(S, V) Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have sq : (resK gp hDW).comp (gp.app W).hom =
          (gp.app D).hom.comp (S.presheaf.map (homOfLE hDW).op).hom := by
        ext a; exact resK_app gp hDW a
      have hb' : IsIntegral Γ(S, D) (resK gp hDW b) := by
        have := hb.map (resK gp hDW)
        rw [sq] at this
        exact RingHom.isIntegralElem.of_comp _ _ this
      obtain ⟨⟨_, N, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g)
        (Rₘ := Γ(S, D)) _ hb'
      have top : ∀ U : S.Opens, gp ⁻¹ᵁ U ≤ gp ⁻¹ᵁ D := fun _ => h1 ▸ le_top
      obtain ⟨y, hy⟩ := (resK_bijective gp hDV (top V)).2 ((g ^ N) • resK gp hDW b)
      have alg : ∀ a : Γ(S, V), algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) a = resK gp hDV ((gp.app V).hom a) := by
        intro a; rw [resK_app]; rfl
      have hyi : (gp.app V).hom.IsIntegralElem y := by
        refine isIntegralElem_of_comp_injective _ (resK gp hDV) (resK_bijective gp hDV (top V)).1 ?_
        have e : (resK gp hDV).comp (gp.app V).hom = algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := by
          ext a; exact (alg a).symm
        rw [e, hy]
        exact hm
      refine ⟨N, {y}, by simpa using hyi, ?_⟩
      have key : resK gp hWV y = (gp.app W).hom ((S.presheaf.map (homOfLE hWV).op).hom g ^ N) * b := by
        apply (resK_bijective gp hDW (top W)).1
        rw [resK_resK, hy, Algebra.smul_def, alg, map_mul]
        simp only [map_pow]
        rw [← resK_app gp hWV g, resK_resK]
      rw [← key]
      exact Subring.subset_closure (Or.inr ⟨y, by simp, rfl⟩)
  have hJ : J = ⊤ := Ideal.radical_eq_top.mp (top_unique (hspan ▸ Ideal.span_le.mpr hT))
  obtain ⟨s, hs, h⟩ : (1 : Γ(S, W)) ∈ J := hJ ▸ Submodule.mem_top
  refine ⟨s, hs, ?_⟩
  simpa using h

end GlobalTheory.Mum
