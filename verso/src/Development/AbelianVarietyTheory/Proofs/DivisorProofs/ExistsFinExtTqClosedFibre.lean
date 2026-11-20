import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTqLevelZeroOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Use `letI : Algebra (ResidueField R) Ω := e₀.toAlgebra`. Establish `hint : IsIntegral (ResidueField R) t` using `⟨q, hq, hqt⟩`. Use `set p := minpoly (ResidueField R) t with hpdef`. Establish `hpm : p.Monic` using `minpoly.monic hint`. Establish `hirr : Irreducible p` using `minpoly.irreducible hint`.

Establish `hdeg : 0 < p.degree` using `minpoly.degree_pos hint`. Establish `hpt : p.eval₂ e₀ t = 0` using `minpoly.aeval _ t`. Establish `hlift : p ∈ Polynomial.lifts (residue R)` using `(Polynomial.lifts_iff_set_range p).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)`. Take `⟨P, hPmap, hPdeg, hPm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hlift hpm`. Set `C` to `AdjoinRoot P`.

Establish `hfinC : (AdjoinRoot.of P).Finite`. Establish `: Module.Finite R (AdjoinRoot P)` using `(AdjoinRoot.powerBasis' hPm).finite`. Conclude with `RingHom.finite_algebraMap.2 this`. Establish `hinjC : Function.Injective (AdjoinRoot.of P)`. Use `(injective_iff_map_eq_zero _).2 fun r hr => ?_` and prove the remaining obligations.

Rewrite `hr` using `[AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero]`. Establish `h0` using `Polynomial.eq_zero_of_dvd_of_degree_lt hr (lt_of_le_of_lt Polynomial.degree_C_le (hPdeg ▸ hdeg))`. Simplify using `using h0`. Take `⟨R', i1, i2, i3, ρ, σ, hcn', hinj', hfin', hloc, hσ⟩` from `GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (AdjoinRoot.of P) hR hinjC hfinC`. Set `r : ResidueField R'` to `residue R' (σ (AdjoinRoot.root P))`.

Establish `hres : (ResidueField.map ρ).comp (residue R) = (residue R').comp ρ` using `ResidueField.map_comp_residue ρ`. Establish `hr : p.eval₂ (ResidueField.map ρ) r = 0`. Rewrite using `[← hPmap, Polynomial.eval₂_map, hres, ← hσ]`. Use `show Polynomial.eval₂ (((residue R').comp σ).comp (AdjoinRoot.of P)) (((residue R').comp σ) (AdjoinRoot.root P)) P = 0`. Rewrite using `[← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]`.

Use `haveI : Fact (Irreducible p) := ⟨hirr⟩`. Set `gam : AdjoinRoot p →+* ResidueField R'` to `AdjoinRoot.lift (ResidueField.map ρ) r hr`. Set `del : AdjoinRoot p →+* Ω` to `AdjoinRoot.lift e₀ t hpt`. Use `letI : Algebra (AdjoinRoot p) (ResidueField R') := gam.toAlgebra`. Use `letI : Algebra (AdjoinRoot p) Ω := del.toAlgebra`.

Establish `hintR : ρ.IsIntegral` using `hfin'.to_isIntegral`. Use `haveI : Algebra.IsIntegral (AdjoinRoot p) (ResidueField R') := by`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`.

Take `⟨m, hm, hmx⟩` from `hintR x`. Use `⟨(m.map (residue R)).map (AdjoinRoot.of p), (hm.map _).map _, ?_⟩` and prove the remaining obligations. Use `show Polynomial.eval₂ gam (residue R' x) ((m.map (residue R)).map (AdjoinRoot.of p)) = 0`. Rewrite using `[Polynomial.eval₂_map, Polynomial.eval₂_map]`. Establish `hgam : (gam.comp (AdjoinRoot.of p)).comp (residue R) = (residue R').comp ρ`.

Rewrite using `[← hres]`. Use `congr 1`. Use extensionality with `a`. Conclude with `AdjoinRoot.lift_of hr`. Rewrite using `[hgam, ← Polynomial.hom_eval₂, hmx, map_zero]`.

Set `β₀ : ResidueField R' →ₐ[AdjoinRoot p] Ω` to `IsAlgClosed.lift`. Establish `hβ : ∀ a, β₀ (gam a) = del a` using `fun a => β₀.commutes a`. Use `⟨R', i1, i2, i3, ρ, hloc, β₀.toRingHom, hcn', hinj', hfin', ?_, ⟨gam (AdjoinRoot.root p), ?_⟩⟩` and prove the remaining obligations. Use extensionality with `a`. Establish `h1 : ResidueField.map ρ a = gam (AdjoinRoot.of p a)` using `(AdjoinRoot.lift_of hr).symm`.

Use `show β₀ (ResidueField.map ρ a) = e₀ a`. Rewrite using `[h1, hβ]`. Conclude with `AdjoinRoot.lift_of hpt`. Use `show β₀ (gam (AdjoinRoot.root p)) = t`. Rewrite using `[hβ]`.

Conclude with `AdjoinRoot.lift_root hpt`.
-/
theorem exists_cover_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (t : Ω) (q : Polynomial (ResidueField R))
    (hq : q.Monic) (hqt : q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ t ∈ Set.range β := by
  letI : Algebra (ResidueField R) Ω := e₀.toAlgebra
  have hint : IsIntegral (ResidueField R) t := ⟨q, hq, hqt⟩
  set p := minpoly (ResidueField R) t with hpdef
  have hpm : p.Monic := minpoly.monic hint
  have hirr : Irreducible p := minpoly.irreducible hint
  have hdeg : 0 < p.degree := minpoly.degree_pos hint
  have hpt : p.eval₂ e₀ t = 0 := minpoly.aeval _ t
  have hlift : p ∈ Polynomial.lifts (residue R) :=
    (Polynomial.lifts_iff_set_range p).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨P, hPmap, hPdeg, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  let C := AdjoinRoot P
  have hfinC : (AdjoinRoot.of P).Finite := by
    have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPm).finite
    exact RingHom.finite_algebraMap.2 this
  have hinjC : Function.Injective (AdjoinRoot.of P) := by
    refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
    rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hr
      (lt_of_le_of_lt Polynomial.degree_C_le (hPdeg ▸ hdeg))
    simpa using h0
  obtain ⟨R', i1, i2, i3, ρ, σ, hcn', hinj', hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (AdjoinRoot.of P) hR hinjC hfinC
  let r : ResidueField R' := residue R' (σ (AdjoinRoot.root P))
  have hres : (ResidueField.map ρ).comp (residue R) = (residue R').comp ρ := ResidueField.map_comp_residue ρ
  have hr : p.eval₂ (ResidueField.map ρ) r = 0 := by
    rw [← hPmap, Polynomial.eval₂_map, hres, ← hσ]
    show Polynomial.eval₂ (((residue R').comp σ).comp (AdjoinRoot.of P)) (((residue R').comp σ) (AdjoinRoot.root P)) P = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  let gam : AdjoinRoot p →+* ResidueField R' := AdjoinRoot.lift (ResidueField.map ρ) r hr
  let del : AdjoinRoot p →+* Ω := AdjoinRoot.lift e₀ t hpt
  letI : Algebra (AdjoinRoot p) (ResidueField R') := gam.toAlgebra
  letI : Algebra (AdjoinRoot p) Ω := del.toAlgebra
  have hintR : ρ.IsIntegral := hfin'.to_isIntegral
  haveI : Algebra.IsIntegral (AdjoinRoot p) (ResidueField R') := by
    constructor
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨m, hm, hmx⟩ := hintR x
    refine ⟨(m.map (residue R)).map (AdjoinRoot.of p), (hm.map _).map _, ?_⟩
    show Polynomial.eval₂ gam (residue R' x) ((m.map (residue R)).map (AdjoinRoot.of p)) = 0
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
    have hgam : (gam.comp (AdjoinRoot.of p)).comp (residue R) = (residue R').comp ρ := by
      rw [← hres]; congr 1; ext a; exact AdjoinRoot.lift_of hr
    rw [hgam, ← Polynomial.hom_eval₂, hmx, map_zero]
  let β₀ : ResidueField R' →ₐ[AdjoinRoot p] Ω := IsAlgClosed.lift
  have hβ : ∀ a, β₀ (gam a) = del a := fun a => β₀.commutes a
  refine ⟨R', i1, i2, i3, ρ, hloc, β₀.toRingHom, hcn', hinj', hfin', ?_, ⟨gam (AdjoinRoot.root p), ?_⟩⟩
  · ext a
    have h1 : ResidueField.map ρ a = gam (AdjoinRoot.of p a) := (AdjoinRoot.lift_of hr).symm
    show β₀ (ResidueField.map ρ a) = e₀ a
    rw [h1, hβ]
    exact AdjoinRoot.lift_of hpt
  · show β₀ (gam (AdjoinRoot.root p)) = t
    rw [hβ]
    exact AdjoinRoot.lift_root hpt

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Conclude with `⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, inferInstance, e₀, hR, Function.injective_id, RingHom.Finite.id R, by rw [ResidueField.map_id]; rfl, by simp⟩`. Consider the case `insert t s ht ih`. Take `⟨R₁, i1, i2, i3, ρ₁, hl₁, β₁, hcn₁, hinj₁, hfin₁, hβ₁, hs₁⟩` from `ih fun u hu => hs u (Finset.mem_insert_of_mem hu)`.

Take `⟨q, hq, hqt⟩` from `hs t (Finset.mem_insert_self t s)`. Establish `hqt' : (q.map (ResidueField.map ρ₁)).eval₂ β₁ t = 0` using `by rw [Polynomial.eval₂_map, hβ₁, hqt]`. Take `⟨R₂, j1, j2, j3, ρ₂, hl₂, β₂, hcn₂, hinj₂, hfin₂, hβ₂, ht₂⟩` from `exists_cover_step R₁ hcn₁ β₁ t _ (hq.map _) hqt'`. Use `⟨R₂, j1, j2, j3, ρ₂.comp ρ₁, inferInstance, β₂, hcn₂, hinj₂.comp hinj₁, hfin₂.comp hfin₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ResidueField.map_comp, ← RingHom.comp_assoc, hβ₂, hβ₁]`.

Rewrite using `[Finset.coe_insert]`. Use `Set.insert_subset ht₂ (hs₁.trans ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨ResidueField.map ρ₂ a, by rw [← hβ₂]; rfl⟩`.
-/
theorem exists_cover_residue (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (s : Finset Ω)
    (hs : ∀ t ∈ s, ∃ q : Polynomial (ResidueField R), q.Monic ∧ q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ (s : Set Ω) ⊆ Set.range β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, inferInstance, e₀, hR, Function.injective_id,
      RingHom.Finite.id R, by rw [ResidueField.map_id]; rfl, by simp⟩
  | insert t s ht ih =>
    obtain ⟨R₁, i1, i2, i3, ρ₁, hl₁, β₁, hcn₁, hinj₁, hfin₁, hβ₁, hs₁⟩ :=
      ih fun u hu => hs u (Finset.mem_insert_of_mem hu)
    obtain ⟨q, hq, hqt⟩ := hs t (Finset.mem_insert_self t s)
    have hqt' : (q.map (ResidueField.map ρ₁)).eval₂ β₁ t = 0 := by rw [Polynomial.eval₂_map, hβ₁, hqt]
    obtain ⟨R₂, j1, j2, j3, ρ₂, hl₂, β₂, hcn₂, hinj₂, hfin₂, hβ₂, ht₂⟩ :=
      exists_cover_step R₁ hcn₁ β₁ t _ (hq.map _) hqt'
    refine ⟨R₂, j1, j2, j3, ρ₂.comp ρ₁, inferInstance, β₂, hcn₂, hinj₂.comp hinj₁, hfin₂.comp hfin₁, ?_, ?_⟩
    · rw [ResidueField.map_comp, ← RingHom.comp_assoc, hβ₂, hβ₁]
    · rw [Finset.coe_insert]
      refine Set.insert_subset ht₂ (hs₁.trans ?_)
      rintro _ ⟨a, rfl⟩
      exact ⟨ResidueField.map ρ₂ a, by rw [← hβ₂]; rfl⟩

/- English proof (translation)
Introduce `R _ _ _ hR G _ _ hG`. Establish `hcn : GlobalTheory.TorRef.IsCN R` using `⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩`. Establish `h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G)` using `IsSemiAbelian.pullback _ G hG`. Use `haveI := h₀.smooth`. Use `haveI := h₀.quasiCompact`.

Use `haveI := h₀.separated`. Set `k` to `ResidueField R`. Set `Ω` to `AlgebraicClosure k`. Take `⟨T⟩` from `h₀.fibres Ω (spMap (algebraMap k Ω))`. Take `⟨s, hs, H⟩` from `GlobalTheory.FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T`.

Take `⟨R', i1, i2, i3, ρ, hl, β, hcn', hinj, hfin, hβ, hr⟩` from `exists_cover_residue R hcn (algebraMap k Ω) hs.toFinset (fun t _ => ⟨minpoly k t, minpoly.monic (Algebra.IsIntegral.isIntegral t), minpoly.aeval k t⟩)`. Establish `hT` using `H (ResidueField R') (ResidueField.map ρ) β hβ (by simpa using hr)`. Set `G'` to `(Over.pullback (spMap ρ)).obj G`. Establish `hT' : Nonempty (TorusExtension ((Over.pullback (spMap (residue R'))).obj G'))`. Use `GlobalTheory.nonempty_torusExtension_of_comp_eq ?_ G hT` and prove the remaining obligations.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ResidueField.map_comp_residue]`. Take `⟨X, _, _, _, ⟨Q⟩⟩` from `GlobalTheory.Raynaud.exists_tq_level_zero_of_torusExtension R' G' hT'`. Conclude with `⟨R', i1, i2, i3, ρ, G', inferInstance, inferInstance, _, X, inferInstance, inferInstance, inferInstance, ⟨⟨hcn'.1, inferInstance, hcn'.2.1, hcn'.2.2.1⟩, hinj, hfin⟩, isGrpPullback_pullback G (spMap ρ), ⟨Q⟩⟩`.
-/
theorem exists_finExt_tq_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), FinExt ρ ∧ IsGrpPullback G' G (spMap ρ) β ∧ Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G') X) := by
  intro R _ _ _ hR G _ _ hG
  have hcn : GlobalTheory.TorRef.IsCN R := ⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField R
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := GlobalTheory.FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  obtain ⟨R', i1, i2, i3, ρ, hl, β, hcn', hinj, hfin, hβ, hr⟩ := exists_cover_residue R hcn (algebraMap k Ω) hs.toFinset
    (fun t _ => ⟨minpoly k t, minpoly.monic (Algebra.IsIntegral.isIntegral t), minpoly.aeval k t⟩)
  have hT := H (ResidueField R') (ResidueField.map ρ) β hβ (by simpa using hr)
  let G' := (Over.pullback (spMap ρ)).obj G
  have hT' : Nonempty (TorusExtension ((Over.pullback (spMap (residue R'))).obj G')) := by
    refine GlobalTheory.nonempty_torusExtension_of_comp_eq ?_ G hT
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ResidueField.map_comp_residue]
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := GlobalTheory.Raynaud.exists_tq_level_zero_of_torusExtension R' G' hT'
  exact ⟨R', i1, i2, i3, ρ, G', inferInstance, inferInstance, _, X, inferInstance, inferInstance, inferInstance,
    ⟨⟨hcn'.1, inferInstance, hcn'.2.1, hcn'.2.2.1⟩, hinj, hfin⟩, isGrpPullback_pullback G (spMap ρ), ⟨Q⟩⟩

end GlobalTheory.Mum

end
