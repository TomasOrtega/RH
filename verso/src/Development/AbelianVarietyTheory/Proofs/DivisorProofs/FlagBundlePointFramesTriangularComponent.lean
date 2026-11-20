import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.VarFlag

section Tri

variable {ι : Type} {m : ι → ℕ}

/- English proof (translation)
Introduce `τ` and use `by refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩ · show (ψ.mapMatrix (M τ)).det ≠ 0 rw [← RingHom.map_det] exact ((hu τ).map ψ).ne_zero · show ψ (M τ i j) = 0 rw [hl τ i j hij, map_zero]`.
-/
theorem par_map {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) {M : Mat m R} (hu : ∀ τ, IsUnit (M τ).det)
    (hl : ∀ τ i k, i < k → M τ i k = 0) : Par m ⊤ (M.map ψ) := fun τ => by
  refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩
  · show (ψ.mapMatrix (M τ)).det ≠ 0
    rw [← RingHom.map_det]
    exact ((hu τ).map ψ).ne_zero
  · show ψ (M τ i j) = 0
    rw [hl τ i j hij, map_zero]

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

/- English proof (translation)
Take `⟨y, ψ, φ₁, f, t, t', hp, h2, h3⟩` from `hc`. Establish `hsp : p (IsLocalRing.closedPoint K) ⤳ y`. Establish `: p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y)`. Rewrite using `[hp]`. Conclude with `⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Establish `hψ : ψ = (Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by`. Use `EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)` and prove the remaining obligations. Establish `e1` using `spMap_stalkClosedPointTo p`. Establish `e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp`.

Establish `e3 : spMap ((Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) = spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by`. Simplify using `[spMap, Spec.map_comp]`. Rewrite using `[e3, Category.assoc, e2, e1]`. Conclude with `hp.symm`. Establish `hρ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint K))` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp`.

Establish `hx₀ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ (stalkPt C.Y y ≫ C.π ≫ genι Z) = stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z`. Rewrite using `[← Category.assoc, hρ]`. Take `⟨g₀, hg₀⟩` from `ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀`. Conclude with `⟨_, g₀, t, t', ValCoord.tri_bc hx₀ hg₀ (by rw [← CarriesAt.algebraMap_eq_comp_specializes hsp]; exact h2), ValCoord.tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)⟩`.
-/
theorem carries_at_image {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p g) :
    ∃ (φ₀ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))
      (g₀ : EigFrame Z φ₀ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
      g₀.Tri (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t ∧
      g₀.Tri (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g t' := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, h2, h3⟩ := hc
  have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
    have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
      (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
        (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫
          spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hρ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ stalkPt C.Y y =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hx₀ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ (stalkPt C.Y y ≫ C.π ≫ genι Z) =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨g₀, hg₀⟩ := ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀
  exact ⟨_, g₀, t, t', ValCoord.tri_bc hx₀ hg₀ (by rw [← CarriesAt.algebraMap_eq_comp_specializes hsp]; exact h2),
    ValCoord.tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)⟩

/- English proof (translation)
Take `⟨φ₀, g₀, t, s, T1, T2⟩` from `carries_at_image C hg`. Take `⟨φ₀', g₀', t₂, s₂, T1', T2'⟩` from `carries_at_image C hg'`. Establish `hinj : Function.Injective (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)` using `IsFractionRing.injective _ _`. Take `rfl : φ₀' = φ₀` from `RingHom.ext fun a => hinj ((RingHom.congr_fun T1'.2.1 a).symm.trans (RingHom.congr_fun T1.2.1 a))`. Establish `hφ : φ' = φ` using `T2'.2.1.trans T2.2.1.symm`.

Take `⟨T, hT, hTd, hTl⟩` from `(g₀.tri_iff _ C.f0 t).1 T1`. Take `⟨T₂, hT₂, hT₂d, hT₂l⟩` from `(g₀'.tri_iff _ C.f0 t₂).1 T1'`. Take `⟨h, hh, hhd, hhl⟩` from `(g₀.tri_iff _ g s).1 T2`. Take `⟨h₂, hh₂, hh₂d, hh₂l⟩` from `(g₀'.tri_iff _ g' s₂).1 T2'`. Establish `hS₀ : g₀.Stable` using `EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g₀ inferInstance`.

Establish `hid : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z = spMap (RingHom.id _) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z`. Rewrite using `[show spMap (RingHom.id (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))) = 𝟙 _ from Spec.map_id _, Category.id_comp]`. Take `⟨⟨M, hM, -⟩, hMu⟩` from `(EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ (RingHom.id _) inferInstance hS₀ hid (RingHom.id_comp _).symm).1 g₀'`. Establish `hMd` using `hMu M hM`. Establish `hc1 : g₀.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (T₂ * M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField))`.

Use `CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ C.f0 (RingHom.id _) (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) M T₂ inferInstance hM hT₂` as an intermediate fact. Rewrite `this` using `[RingHom.comp_id]`. Then use the resulting hypothesis. Establish `heq` using `(((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hT.1 hT.2.1).1 C.f0).1).unique hT hc1`. Establish `hPT : Par Dw.mult ⊤ T` using `CarriesAt.par_of_tri (fun τ i => by rw [hTd]; exact Units.ne_zero _) hTl`. Establish `hPT₂ : Par Dw.mult ⊤ T₂` using `CarriesAt.par_of_tri (fun τ i => by rw [hT₂d]; exact Units.ne_zero _) hT₂l`.

Establish `hPM : Par Dw.mult ⊤ (M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField))`. Establish `e : M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = T₂⁻¹ * T`. Rewrite using `[heq, ← mul_assoc, Mat.inv_mul hPT₂.det_ne, one_mul]`. Rewrite using `[e]`. Conclude with `hPT₂.inv.mul hPT`.

Establish `hMl : ∀ τ i k, i < k → M τ i k = 0` using `fun τ i k hik => by`. Establish `h0` using `(hPM τ).2.2.2 i k i.2 hik`. Conclude with `hinj (by rw [map_zero]; exact h0)`. Establish `hSg : g.Stable` using `EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g inferInstance`. Establish `hidK : x = spMap (RingHom.id K) ≫ x`.

Rewrite using `[show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]`. Take `⟨⟨N, hN, -⟩, -⟩` from `(EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g _ φ' _ (RingHom.id K) inferInstance hSg hidK (by rw [RingHom.id_comp]; exact hφ)).1 g'`. Establish `c1 : g₀.Coord (Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) p).hom g' (N * h.map (RingHom.id K)) := by`. Use `CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g _ _ _ g' (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom (RingHom.id K) h N inferInstance hh hN` as an intermediate fact. Rewrite `this` using `[RingHom.id_comp]`. Then use the resulting hypothesis.

Establish `c2 : g₀.Coord (Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) p).hom g' (h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom) := by`. Use `CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ g' (RingHom.id _) (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom M h₂ inferInstance hM hh₂` as an intermediate fact. Rewrite `this` using `[RingHom.comp_id]`. Then use the resulting hypothesis. Establish `heqK` using `(((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hh₂.1 hh₂.2.1).1 g').1).unique c1 c2`. Establish `hmid : h.map (RingHom.id K) = h` using `funext fun τ => by ext i j; rfl`.

Rewrite `heqK` using `[hmid]`. Establish `hPh : Par Dw.mult ⊤ h` using `CarriesAt.par_of_tri (fun τ i => by rw [hhd]; exact Units.ne_zero _) hhl`. Establish `hPh₂ : Par Dw.mult ⊤ h₂` using `CarriesAt.par_of_tri (fun τ i => by rw [hh₂d]; exact Units.ne_zero _) hh₂l`. Establish `hPMK` using `par_map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom hMd hMl`. Establish `hNe : N = h₂ * M.map (Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) p).hom * h⁻¹ := by`.

Rewrite using `[← heqK, mul_assoc, Mat.mul_inv hPh.det_ne, mul_one]`. Establish `hPN : Par Dw.mult ⊤ N`. Rewrite using `[hNe]`. Conclude with `(hPh₂.mul hPMK).mul hPh.inv`. Conclude with `⟨fun τ i => Units.mk0 _ (CarriesAt.Par.diag_ne hPN τ i), (g.tri_iff _ g' _).2 ⟨N, hN, fun _ _ => rfl, fun τ i k hik => (hPN τ).2.2.2 i k i.2 hik⟩⟩`.
-/
theorem tri_of_carries {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} {g' : EigFrame Z φ' x}
    (hg : C.Carries p g) (hg' : C.Carries p g') : ∃ t, g.Tri (RingHom.id K) g' t := by
  obtain ⟨φ₀, g₀, t, s, T1, T2⟩ := carries_at_image C hg
  obtain ⟨φ₀', g₀', t₂, s₂, T1', T2'⟩ := carries_at_image C hg'
  have hinj : Function.Injective
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) :=
    IsFractionRing.injective _ _
  obtain rfl : φ₀' = φ₀ := RingHom.ext fun a =>
    hinj ((RingHom.congr_fun T1'.2.1 a).symm.trans (RingHom.congr_fun T1.2.1 a))
  have hφ : φ' = φ := T2'.2.1.trans T2.2.1.symm
  obtain ⟨T, hT, hTd, hTl⟩ := (g₀.tri_iff _ C.f0 t).1 T1
  obtain ⟨T₂, hT₂, hT₂d, hT₂l⟩ := (g₀'.tri_iff _ C.f0 t₂).1 T1'
  obtain ⟨h, hh, hhd, hhl⟩ := (g₀.tri_iff _ g s).1 T2
  obtain ⟨h₂, hh₂, hh₂d, hh₂l⟩ := (g₀'.tri_iff _ g' s₂).1 T2'
  have hS₀ : g₀.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g₀ inferInstance
  have hid : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (RingHom.id _) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp]

  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ (RingHom.id _)
    inferInstance hS₀ hid (RingHom.id_comp _).symm).1 g₀'
  have hMd := hMu M hM

  have hc1 : g₀.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0
      (T₂ * M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ C.f0 (RingHom.id _)
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) M T₂ inferInstance hM hT₂
    rwa [RingHom.comp_id] at this
  have heq := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hT.1 hT.2.1).1
    C.f0).1).unique hT hc1
  have hPT : Par Dw.mult ⊤ T := CarriesAt.par_of_tri (fun τ i => by rw [hTd]; exact Units.ne_zero _) hTl
  have hPT₂ : Par Dw.mult ⊤ T₂ := CarriesAt.par_of_tri (fun τ i => by rw [hT₂d]; exact Units.ne_zero _) hT₂l
  have hPM : Par Dw.mult ⊤
      (M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have e : M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) =
        T₂⁻¹ * T := by
      rw [heq, ← mul_assoc, Mat.inv_mul hPT₂.det_ne, one_mul]
    rw [e]
    exact hPT₂.inv.mul hPT
  have hMl : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hik => by
    have h0 := (hPM τ).2.2.2 i k i.2 hik
    exact hinj (by rw [map_zero]; exact h0)

  have hSg : g.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g inferInstance
  have hidK : x = spMap (RingHom.id K) ≫ x := by
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨N, hN, -⟩, -⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g _ φ' _ (RingHom.id K)
    inferInstance hSg hidK (by rw [RingHom.id_comp]; exact hφ)).1 g'
  have c1 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (N * h.map (RingHom.id K)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g _ _ _ g'
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom (RingHom.id K) h N inferInstance hh hN
    rwa [RingHom.id_comp] at this
  have c2 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ g' (RingHom.id _)
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom M h₂ inferInstance hM hh₂
    rwa [RingHom.comp_id] at this
  have heqK := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hh₂.1 hh₂.2.1).1
    g').1).unique c1 c2
  have hmid : h.map (RingHom.id K) = h := funext fun τ => by ext i j; rfl
  rw [hmid] at heqK
  have hPh : Par Dw.mult ⊤ h := CarriesAt.par_of_tri (fun τ i => by rw [hhd]; exact Units.ne_zero _) hhl
  have hPh₂ : Par Dw.mult ⊤ h₂ := CarriesAt.par_of_tri (fun τ i => by rw [hh₂d]; exact Units.ne_zero _) hh₂l
  have hPMK := par_map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom hMd hMl
  have hNe : N = h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom * h⁻¹ := by
    rw [← heqK, mul_assoc, Mat.mul_inv hPh.det_ne, mul_one]
  have hPN : Par Dw.mult ⊤ N := by
    rw [hNe]
    exact (hPh₂.mul hPMK).mul hPh.inv
  exact ⟨fun τ i => Units.mk0 _ (CarriesAt.Par.diag_ne hPN τ i),
    (g.tri_iff _ g' _).2 ⟨N, hN, fun _ _ => rfl, fun τ i k hik => (hPN τ).2.2.2 i k i.2 hik⟩⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y C K _ φ φ' x p g g' hg hg'`. Conclude with `tri_of_carries C hg hg'`.
-/
theorem carriesTri : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)},
    ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  intro E _ _ _ H Dw l Xo c Y C K _ φ φ' x p g g' hg hg'
  exact tri_of_carries C hg hg'

end GlobalTheory.VarFlag
