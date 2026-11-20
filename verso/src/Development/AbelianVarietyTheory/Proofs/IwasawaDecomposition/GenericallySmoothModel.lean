import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ModelCharts

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem exists_etale_coords_of_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (D : ℕ)
    (W : X.Opens) [SmoothOfRelativeDimension D (W.ι ≫ p)] {z : X} (hz : z ∈ W) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have hzr : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨z', rfl⟩ := hzr
  obtain ⟨U', x', hU', hzU', hx'⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'
  let e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U') := (W.ι.appIso U').commRingCatIsoToRingEquiv
  refine ⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩
  have h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) =
      p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom := by
    first
    | rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    | (rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    | simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]
    | (simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])
  have halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX
    rw [h2]
    rfl
  have heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' =
      (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp
        (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [halg]
    · intro i; simp
  rw [heq] at hx'
  have h3 := RingHom.Etale.respectsIso.left _ e.symm hx'
  convert h3 using 1
  ext <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem injective_emb {F : Type} [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hne (RingHom.mem_ker.2 hx)
    (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  exact hn0 hn

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem exists_algChart_mem_source {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := by
  obtain ⟨a, ha⟩ := y
  obtain ⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ :=
    ⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩
  have hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K) := by
    rw [ha]; unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨b, hb⟩ : ∃ b, b ≫ j = a := ⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩
  haveI : Flat (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K
  obtain ⟨W, hW, hsm⟩ := GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D
    (b (IsLocalRing.closedPoint ℂ))
  haveI := hsm
  have hz : a (IsLocalRing.closedPoint ℂ) ∈ W := by
    rw [← hb]
    first | exact hW | simpa using hW
  obtain ⟨U, x, hU, hzU, hx⟩ := exists_etale_coords_of_opens p D W hz
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩)
    (GlobalTheory.CxPts.mem_ptsIn.2 hzU)
  exact ⟨c, hc⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_chart {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := exists_algChart_mem_source h hτ y

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem genSmooth_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y),
    GenSmooth M.p Y.dim := by
  intro F _ _ Y M σ
  haveI : LocallyOfFinitePresentation M.p := by
    obtain ⟨N, i, hi, hip⟩ :=
      (show ∃ N i, IsClosedImmersion i ∧ i ≫ PSpace.str (𝓞 F) N = M.p from M.ar.isProjOver)
    rw [← hip]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 F) N
    first
    | infer_instance
    | exact (locallyOfFinitePresentation_iff_locallyOfFiniteType (f := i ≫ PSpace.str (𝓞 F) N)).2 inferInstance
  exact ⟨{ ι := CxPts M.p σ
           chart := fun y => (exists_chart M.pb (injective_emb σ) y).choose
           cover := fun y => ⟨y, (exists_chart M.pb (injective_emb σ) y).choose_spec⟩ }⟩

end GlobalTheory.ModelCharts
