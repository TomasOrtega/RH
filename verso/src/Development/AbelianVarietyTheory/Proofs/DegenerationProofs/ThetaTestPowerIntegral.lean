import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.MultInt

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

/- English proof (translation)
Set `h' : Over.mk (T.hom ≫ f) ⟶ T₀` to `Over.homMk h hh`. Establish `e : TorsionLift.ptsEquiv f G T _ rfl x = h' ≫ x₀` using `Over.OverMorphism.ext ((TorsionLift.ptsEquiv_left f G T _ rfl x).trans hx.symm)`. Rewrite using `[← TorsionLift.ptsEquiv_left f G T _ rfl, map_pow, e, ← comp_pow]`. Both sides reduce to the same expression.
-/
theorem pow_left_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {T : Over S'} {T₀ : Over S}
    (h : T.left ⟶ T₀.left) (hh : h ≫ T₀.hom = T.hom ≫ f) (x : T ⟶ (Over.pullback f).obj G) (x₀ : T₀ ⟶ G)
    (hx : h ≫ x₀.left = x.left ≫ pullback.fst G.hom f) (k : ℕ) :
    h ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst G.hom f := by
  let h' : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk h hh
  have e : TorsionLift.ptsEquiv f G T _ rfl x = h' ≫ x₀ :=
    Over.OverMorphism.ext ((TorsionLift.ptsEquiv_left f G T _ rfl x).trans hx.symm)
  rw [← TorsionLift.ptsEquiv_left f G T _ rfl, map_pow, e, ← comp_pow]
  rfl

/- English proof (translation)
Take `⟨U, hU, ψ', hψ'⟩` from `exists_affineOpen_factor_of_isLocalRing x`. Set `A : Type` to `Γ(X, U)`. Set `i : Sp A ⟶ X` to `hU.fromSpec`. Use `haveI : IsOpenImmersion i := hU.isOpenImmersion_fromSpec`. Set `ψ : A →+* PadicAlgCl p` to `ψ'.hom`.

Establish `hψ : spMap ψ ≫ i = x` using `hψ'`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : V →+* A, spMap α = i ≫ s := by`. Take `⟨α, hα⟩` from `Spec.map_surjective (i ≫ s)`. Conclude with `⟨α.hom, hα⟩`. Establish `hft : α.FiniteType`.

Establish `: LocallyOfFiniteType (spMap α)` using `by rw [hα]; infer_instance`. Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this`. Establish `hψα : ψ.comp α = φ`. Use `congrArg CommRingCat.Hom.hom (Spec.map_injective (?_ : spMap _ = spMap _))` and prove the remaining obligations. Rewrite using `[← spMap_comp_spMap, hα, ← Category.assoc, hψ, hx]`.

Use `letI := α.toAlgebra`. Take `⟨t, ht⟩` from `Algebra.FiniteType.out (self := hft)`. Use `haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype`. Use `haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))) := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Set `K : IntermediateField ℚ_[p] (PadicAlgCl p)` to `K₀ ⊔ IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))`.

Establish `hk : K₀ ≤ K` using `le_sup_left`. Establish `hmem : ∀ x, ψ x ∈ K`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin V (t : Set A)` using `ht ▸ Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Conclude with `(le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)`. Consider the case `algebraMap r`. Express the relevant statement in the definitionally equal form `(ψ.comp α) r ∈ K`. Rewrite using `[hψα]`.

Conclude with `hk (hφ r)`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`.

Use `⟨K, hk, IntermediateField.finiteDimensional_sup _ _, spMap (ψ.codRestrict K hmem) ≫ i, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_comp_spMap]`. Conclude with `hψ`.
-/
theorem exists_finite_factor {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (φ : V →+* PadicAlgCl p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hφ : ∀ v, φ v ∈ K₀) (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ s = spMap φ) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K ∧ FiniteDimensional ℚ_[p] K ∧
      ∃ x' : Sp K ⟶ X, spMap K.val.toRingHom ≫ x' = x := by
  obtain ⟨U, hU, ψ', hψ'⟩ := exists_affineOpen_factor_of_isLocalRing x
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let ψ : A →+* PadicAlgCl p := ψ'.hom
  have hψ : spMap ψ ≫ i = x := hψ'
  obtain ⟨α, hα⟩ : ∃ α : V →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hψα : ψ.comp α = φ := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (?_ : spMap _ = spMap _))
    rw [← spMap_comp_spMap, hα, ← Category.assoc, hψ, hx]
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hft)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))
  have hk : K₀ ≤ K := le_sup_left
  have hmem : ∀ x, ψ x ∈ K := by
    intro x
    have hx : x ∈ Algebra.adjoin V (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change (ψ.comp α) r ∈ K
      rw [hψα]; exact hk (hφ r)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K, hk, IntermediateField.finiteDimensional_sup _ _, spMap (ψ.codRestrict K hmem) ≫ i, ?_⟩
  rw [← Category.assoc, spMap_comp_spMap]
  exact hψ

/- English proof (translation)
Establish `e : spMap χ ≫ spMap ψ = spMap β ≫ spMap α` using `by rw [spMap_comp_spMap, spMap_comp_spMap, h]`. Establish `H` using `(IsPullback.of_hasPullback (pullback.snd s (spMap ψ)) (spMap χ)).paste_horiz (IsPullback.of_hasPullback s (spMap ψ))`. Rewrite `H` using `[e]`. Conclude with `ProjSpace.isProjOver_of_isPullback_spMap β (IsPullback.of_right' H (IsPullback.of_hasPullback s (spMap α))) hp`.
-/
theorem isProjOver_snd_snd {V F O K : Type} [CommRing V] [CommRing F] [CommRing O] [CommRing K] {X : Scheme.{0}}
    (s : X ⟶ Sp V) (α : V →+* F) (β : F →+* K) (ψ : V →+* O) (χ : O →+* K) (h : β.comp α = χ.comp ψ)
    (hp : IsProjOver (pullback.snd s (spMap α))) :
    IsProjOver (pullback.snd (pullback.snd s (spMap ψ)) (spMap χ)) := by
  have e : spMap χ ≫ spMap ψ = spMap β ≫ spMap α := by rw [spMap_comp_spMap, spMap_comp_spMap, h]
  have H := (IsPullback.of_hasPullback (pullback.snd s (spMap ψ)) (spMap χ)).paste_horiz
    (IsPullback.of_hasPullback s (spMap ψ))
  rw [e] at H
  exact ProjSpace.isProjOver_of_isPullback_spMap β
    (IsPullback.of_right' H (IsPullback.of_hasPullback s (spMap α))) hp

end GlobalTheory.ZH.MultInt

namespace GlobalTheory.ZH
open MultInt

/- English proof (translation)
Introduce `_ o Ω _ _ _ _ S ρ p _ y₀ u a`. Take `⟨-, -, -, K₀, hK₀, hr⟩` from `GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u`. Use `haveI := u.semi.smooth`. Use `haveI := u.semi.separated`. Set `θ : FractionRing u.V →+* PadicAlgCl p` to `algebraMap _ _`.

Set `α : u.V →+* FractionRing u.V` to `algebraMap _ _`. Establish `hθ : ∀ v, θ v ∈ K₀` using `fun v => show θ v ∈ (K₀ : Set _) from hr ▸ ⟨v, rfl⟩`. Establish `ha : u.toG a ≫ u.G.hom = spMap (θ.comp α)`. Use `Over.w a` as an intermediate fact. Rewrite using `[← spMap_comp_spMap, ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition, ← Category.assoc]`.

Conclude with `congrArg (· ≫ spMap α) this`. Take `⟨K, hK, hfd, x, hx⟩` from `exists_finite_factor u.G.hom (θ.comp α) K₀ (fun v => hθ _) (u.toG a) ha`. Set `β : FractionRing u.V →+* K` to `θ.codRestrict K fun v => hK (hθ v)`. Set `ψ : u.V →+* integralClosure ℤ_[p] K` to `(β.comp α).codRestrict (integralClosure ℤ_[p] K) fun v => (mem_integralClosure_padicInt_iff K _).mpr ((u.norm_le _).2 ⟨v, rfl⟩)`. Set `χ : integralClosure ℤ_[p] K →+* K` to `algebraMap _ _`.

Establish `hc : β.comp α = χ.comp ψ` using `rfl`. Establish `hxG : x ≫ u.G.hom = spMap χ ≫ spMap ψ`. Take `⟨δ, hδ⟩` from `Spec.map_surjective (x ≫ u.G.hom)`. Establish `h1 : spMap K.val.toRingHom ≫ spMap δ.hom = spMap (θ.comp α)`. Rewrite using `[← ha, ← hx, Category.assoc, ← hδ]`.

Both sides reduce to the same expression. Rewrite `h1` using `[spMap_comp_spMap]`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Establish `h3 : δ.hom = χ.comp ψ` using `RingHom.ext fun v => Subtype.ext (RingHom.congr_fun h2 v)`. Rewrite using `[spMap_comp_spMap, ← h3, ← hδ]`.

Both sides reduce to the same expression. Establish `hp : IsProjOver (pullback.snd u.G.hom (spMap α))`. Establish `: IsIso u.U.gen.inv.left` using `((Over.forget _).mapIso u.U.gen).isIso_inv`. Use `ProjSpace.isProjOver_of_isIso_comp (Y := pullback u.G.hom (spMap α)) u.U.gen.inv.left ?_` and prove the remaining obligations. Use `ProjSpace.isProjOver_polAV u.A` as an intermediate fact.

Rewrite `this` using `[← Over.w u.U.gen.inv]`. Conclude with `this`. Set `G'` to `(Over.pullback (spMap ψ)).obj u.G`. Use `haveI : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd u.G.hom (spMap ψ)))`. Use `haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd u.G.hom (spMap ψ)))`.

Set `a' : Over.mk (spMap χ) ⟶ G'` to `Over.homMk (pullback.lift x (spMap χ) hxG) (pullback.lift_snd _ _ _)`. Take `⟨k, hk, g, hg⟩` from `GlobalTheory.T.exists_pow_point_integral_padic_groupScheme p K G' (isProjOver_snd_snd u.G.hom α β ψ χ hc hp) a'`. Set `a₀ : Over.mk (spMap χ ≫ spMap ψ) ⟶ u.G` to `Over.homMk x hxG`. Establish `e₁` using `pow_left_pullback (spMap ψ) u.G (T := Over.mk (spMap χ)) (𝟙 _) (Category.id_comp _) a' a₀ ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm) k`. Establish `e₂` using `pow_left_pullback (jK u.V) u.G (spMap K.val.toRingHom) (show spMap K.val.toRingHom ≫ spMap χ ≫ spMap ψ = spMap θ ≫ spMap α by`.

Simplify using `only [spMap_comp_spMap]`. Use the proof step `rfl) a a₀ hx k`. Establish `hgw : g.left ≫ pullback.snd u.G.hom (spMap ψ) = 𝟙 _` using `Over.w g`. Establish `hg' : spMap χ ≫ g.left = (a' ^ k).left`. Rewrite using `[← hg]`.

Both sides reduce to the same expression. Use `⟨k, hk, spMap (integralClosureToPadicAlgClIntegers K) ≫ g.left ≫ pullback.fst u.G.hom (spMap ψ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, reassoc_of% hgw, spMap_comp_spMap]`. Both sides reduce to the same expression. Establish `e₃ : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) = spMap K.val.toRingHom ≫ spMap χ`.

Rewrite using `[spMap_comp_spMap, spMap_comp_spMap]`. Both sides reduce to the same expression. Rewrite using `[reassoc_of% e₃, reassoc_of% hg']`. Use `Eq.trans ?_ e₂` and prove the remaining obligations. Conclude with `congrArg _ (e₁.symm.trans (Category.id_comp _))`.
-/
theorem exists_int_pow : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u a
  obtain ⟨-, -, -, K₀, hK₀, hr⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  haveI := u.semi.smooth
  haveI := u.semi.separated
  let θ : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  let α : u.V →+* FractionRing u.V := algebraMap _ _
  have hθ : ∀ v, θ v ∈ K₀ := fun v => show θ v ∈ (K₀ : Set _) from hr ▸ ⟨v, rfl⟩
  have ha : u.toG a ≫ u.G.hom = spMap (θ.comp α) := by
    have := Over.w a
    rw [← spMap_comp_spMap, ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap α) this
  obtain ⟨K, hK, hfd, x, hx⟩ := exists_finite_factor u.G.hom (θ.comp α) K₀ (fun v => hθ _) (u.toG a) ha
  let β : FractionRing u.V →+* K := θ.codRestrict K fun v => hK (hθ v)
  let ψ : u.V →+* integralClosure ℤ_[p] K := (β.comp α).codRestrict (integralClosure ℤ_[p] K) fun v =>
    (mem_integralClosure_padicInt_iff K _).mpr ((u.norm_le _).2 ⟨v, rfl⟩)
  let χ : integralClosure ℤ_[p] K →+* K := algebraMap _ _
  have hc : β.comp α = χ.comp ψ := rfl
  have hxG : x ≫ u.G.hom = spMap χ ≫ spMap ψ := by
    obtain ⟨δ, hδ⟩ := Spec.map_surjective (x ≫ u.G.hom)
    have h1 : spMap K.val.toRingHom ≫ spMap δ.hom = spMap (θ.comp α) := by
      rw [← ha, ← hx, Category.assoc, ← hδ]; rfl
    rw [spMap_comp_spMap] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : δ.hom = χ.comp ψ := RingHom.ext fun v => Subtype.ext (RingHom.congr_fun h2 v)
    rw [spMap_comp_spMap, ← h3, ← hδ]; rfl
  have hp : IsProjOver (pullback.snd u.G.hom (spMap α)) := by
    have : IsIso u.U.gen.inv.left := ((Over.forget _).mapIso u.U.gen).isIso_inv
    refine ProjSpace.isProjOver_of_isIso_comp (Y := pullback u.G.hom (spMap α)) u.U.gen.inv.left ?_
    have := ProjSpace.isProjOver_polAV u.A
    rw [← Over.w u.U.gen.inv] at this
    exact this
  let G' := (Over.pullback (spMap ψ)).obj u.G
  haveI : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd u.G.hom (spMap ψ)))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd u.G.hom (spMap ψ)))
  let a' : Over.mk (spMap χ) ⟶ G' := Over.homMk (pullback.lift x (spMap χ) hxG) (pullback.lift_snd _ _ _)
  obtain ⟨k, hk, g, hg⟩ := GlobalTheory.T.exists_pow_point_integral_padic_groupScheme p K G' (isProjOver_snd_snd u.G.hom α β ψ χ hc hp) a'
  let a₀ : Over.mk (spMap χ ≫ spMap ψ) ⟶ u.G := Over.homMk x hxG
  have e₁ := pow_left_pullback (spMap ψ) u.G (T := Over.mk (spMap χ)) (𝟙 _) (Category.id_comp _) a' a₀
    ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm) k
  have e₂ := pow_left_pullback (jK u.V) u.G (spMap K.val.toRingHom)
    (show spMap K.val.toRingHom ≫ spMap χ ≫ spMap ψ = spMap θ ≫ spMap α by
      simp only [spMap_comp_spMap]; rfl) a a₀ hx k
  have hgw : g.left ≫ pullback.snd u.G.hom (spMap ψ) = 𝟙 _ := Over.w g
  have hg' : spMap χ ≫ g.left = (a' ^ k).left := by
    rw [← hg]; rfl
  refine ⟨k, hk, spMap (integralClosureToPadicAlgClIntegers K) ≫ g.left ≫ pullback.fst u.G.hom (spMap ψ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hgw, spMap_comp_spMap]
    rfl
  · have e₃ : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) = spMap K.val.toRingHom ≫ spMap χ := by
      rw [spMap_comp_spMap, spMap_comp_spMap]; rfl
    rw [reassoc_of% e₃, reassoc_of% hg']
    refine Eq.trans ?_ e₂
    exact congrArg _ (e₁.symm.trans (Category.id_comp _))

end GlobalTheory.ZH
