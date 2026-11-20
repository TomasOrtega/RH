import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `hIncl hIdx`. Unfold `LayerOf`. Introduce `E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex`. Take `⟨A, hA, τ, hτ, hτ'⟩` from `hτex`. Unfold `Cuts at hX hY`.

Establish `overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w → IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E)))`. Introduce `B w hB x`. Rewrite using `[HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]`. Both sides reduce to the same expression. Establish `resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g), AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E` using `E) g hg) = g := fun g hg => AlgEquiv.ext fun x => rfl`.

Establish `hτD` using `Ine_le_Dec A hτ`. Take `⟨hτE, hτH⟩` from `hDec A hA τ hτD`. Take `⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ` from `⟨_, resLift τ hτE⟩`. Establish `fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))` using `Subgroup.ext fun g => hY g`. Establish `fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))` using `Subgroup.ext fun g => hX g`.

Establish `hidx` using `hIdx (G (maximalRealSubfield E) Ω) (G E Ω) (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩`. Take `⟨x0, t0E, t0Ω, hgal, hfin⟩` from `hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)`. Rewrite `hfin` using `[fY, fX, hidx]`. Take `⟨w, hw⟩` from `GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA`. Establish `hwu : w.under (𝓞 (maximalRealSubfield E)) = u` using `eq_of_isPlaceOver (overUnder A w hw) hA`.

Establish `hfixX : Fixes X.K τ'` using `(hX τ').2 (by rw [hres]; exact hτH)`. Use `⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw, GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `hwS`. Conclude with `hS w hwS hwu`. Introduce `B hB g hg`.

Establish `hBu : IsPlaceOver B u`. Rewrite using `[← hwu]`. Conclude with `overUnder B w hB`. Take `⟨hgE, hgH⟩` from `hDec B hBu g hg`. Use `⟨hgE, ?_⟩` and prove the remaining obligations.

Establish `h1` using `(hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)`. Conclude with `h1`. Substitute `hres` using the available equality. Rewrite using `[mem_Ine]`. Establish `hτI` using `(mem_Ine (A := A)).1 hτ`.

Conclude with `⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩`. Introduce `hfix`. Conclude with `hτ' (by rw [← hres]; exact (hY τ').1 hfix)`. Introduce `x1 t1`. Establish `hx : x1 = x0`.

Use `Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_` and prove the remaining obligations. Rewrite using `[← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r, ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]`. Substitute `hx` using the available equality. Conclude with `hfin`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
