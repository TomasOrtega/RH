import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsSplitPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

/- English proof (translation)
Introduce `U f`. Take `⟨h1, h2⟩` from `hy U f`. Establish `e : {b ∈ (Set.univ : Set V) | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}` using `Set.ext fun z => ⟨fun h => ⟨hB z, h.2⟩, fun h => ⟨trivial, h.2⟩⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[e]`. Conclude with `h1.preimage hφ.continuous`. Use `beta_reduce`. Rewrite using `[e]`. Conclude with `DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (f := φ) h2 hφ.differentiableOn fun z hz => hz`.
-/
theorem isHolTo_subst {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  have e : {b ∈ (Set.univ : Set V) | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨fun h => ⟨hB z, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [e]
    exact h1.preimage hφ.continuous
  · beta_reduce
    rw [e]
    exact DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (f := φ) h2 hφ.differentiableOn fun z hz => hz

/- English proof (translation)
The claim follows from `isHolTo_subst (φ := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 (by fun_prop) fun _ => ⟨trivial, trivial⟩`.
-/
theorem isHolTo_ex_at_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) :
    IsHolTo Set.univ (fun z => (F.ex i P z).left) :=
  isHolTo_subst (φ := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))
    (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    (by fun_prop) fun _ => ⟨trivial, trivial⟩

/- English proof (translation)
Take `⟨C, io, hC⟩` from `hfix`. Establish `hτσ : (τ : ℂ →+* ℂ).comp σ = σ` using `GlobalTheory.ConjPermutes.ringHom_ext hA (by show τ (σ _) = σ _`. Rewrite using `[hσ, hτ])`. Take `⟨i', P', hP', hu⟩` from `F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P) (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])`. Take `⟨Φ, hE, hp, hm, hlev⟩` from `marking_conj E H D l Xo σ g ty F hD hσ hty hA τ hτ C io hC.1 i P hP i' P' hP' hs hu.symm (1, 0) hC`.

Take `⟨L, hL⟩` from `exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha) (fun a ha => (hm a).2 ha)`. Establish `hw : wE H (1, 0) = 1` using `by simp [wE]`. Establish `hA' : ∀ a, ∃ x, Φ (F.t i a) = F.t i' a + l.A • x` using `fun a => ⟨Φ (F.t i a) - F.t i' a, by rw [hA, one_smul, add_sub_cancel]⟩`. Use `hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i') (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P') ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, …` and prove the remaining obligations. Establish `hmem : F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)`.

Rewrite using `[show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨e, he⟩` from `hlev v hv a ha b hb hab.symm`. Rewrite `he` using `[hw, map_one, one_smul, one_smul, hab]`.

Conclude with `⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩`.
-/
theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ)
    (hτ : τ H.rt0 = H.rt0) (hfix : FixesCurve H τ l.M) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := GlobalTheory.ConjPermutes.ringHom_ext hA (by
    show τ (σ _) = σ _
    rw [hσ, hτ])
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlev⟩ := marking_conj E H D l Xo σ g ty F hD hσ hty hA τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hA' : ∀ a, ∃ x, Φ (F.t i a) = F.t i' a + l.A • x := fun a =>
    ⟨Φ (F.t i a) - F.t i' a, by rw [hA, one_smul, add_sub_cancel]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  have hmem : F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F hpq hσ hty hA hsig τ hτ hC`. Take `⟨π, hπ⟩` from `GlobalTheory.ConjPermutes.exists_perm E H D l Xo σ g ty F hpq hσ hty hA τ hτ`. Establish `hid : ∀ i, π i = i`. Introduce `i`. Take `⟨P, hP, hs⟩` from `exists_isSplit_period E H D l Xo σ g ty F hpq hσ hty hA hsig i`.

Establish `h1` using `conj_point_eq_of_isSplit F hpq hσ hty hA τ hτ hC i P hP hs`. Take `⟨P', hP', h2⟩` from `hπ i P hP`. Conclude with `(F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm`. Establish `: (π : Fin F.n → Fin F.n) = id` using `funext hid`. Rewrite `hπ` using `[this]`. Then use the resulting hypothesis.
-/
theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ l.M → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hA hsig τ hτ hC
  obtain ⟨π, hπ⟩ := GlobalTheory.ConjPermutes.exists_perm E H D l Xo σ g ty F hpq hσ hty hA τ hτ
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := exists_isSplit_period E H D l Xo σ g ty F hpq hσ hty hA hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty hA τ hτ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat
