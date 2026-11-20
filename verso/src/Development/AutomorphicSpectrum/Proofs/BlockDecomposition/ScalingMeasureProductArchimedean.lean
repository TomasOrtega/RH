import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.InfScale

open GlobalTheory.CompanionTheory.SW.LocInf

/- English proof (translation)
Establish `key : ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp ((eInf F h).toRingHom.comp θ)) = RingHom.id ℝ` using `Subsingleton.elim _ _`. Conclude with `congrArg (fun f : ℝ →+* ℝ => f t) key`.
-/
theorem eInf_theta {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F) (t : ℝ)
    (w : InfinitePlace F) : eInf F h (θ t) w = t := by
  have key : ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
      ((eInf F h).toRingHom.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  exact congrArg (fun f : ℝ →+* ℝ => f t) key

/- English proof (translation)
Use `haveI := h`. Rewrite using `[Module.finrank_fintype_fun_eq_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]`.
-/
theorem finrank_fun_places (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) :
    Module.finrank ℝ (InfinitePlace F → ℝ) = Module.finrank ℚ F := by
  haveI := h
  rw [Module.finrank_fintype_fun_eq_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

/- English proof (translation)
Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Establish `hc : Continuous (eInf F h)` using `continuous_eInf F h`. Establish `hcs : Continuous (eInf F h).symm` using `continuous_eInf_symm F h`. Establish `hm : Measurable (eInf F h)` using `hc.measurable`. Establish `hms : Measurable (eInf F h).symm` using `hcs.measurable`.

Establish `hL : Measurable (fun x : InfinitePlace F → ℝ => ε • x)` using `(continuous_const_smul ε).measurable`. Establish `hθ : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h)`. Use function extensionality and compare the values at `y`. Apply `(eInf F h).injective` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]`.

Use function extensionality and compare the values at `w`. Rewrite using `[Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]`. Use `haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs`. Establish `hdet : LinearMap.det (ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ))) ≠ 0`. Rewrite using `[LinearMap.det_smul, LinearMap.det_id, mul_one]`.

Conclude with `pow_ne_zero _ hε.ne'`. Establish `hmapL` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (Measure.map (eInf F h) li) hdet`. Rewrite `hmapL` using `[LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_fun_places F h]`. Establish `hcoe : (⇑(ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ)))) = fun x => ε • x`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite `hmapL` using `[hcoe]`. Establish `hid : (eInf F h).symm ∘ (eInf F h) = id`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Rewrite using `[hθ, ← Measure.map_map hms (hL.comp hm), ← Measure.map_map hL hm, hmapL, Measure.map_smul, Measure.map_map hms hm, hid, Measure.map_id, abs_of_pos (inv_pos.mpr (pow_pos hε _))]`.
-/
theorem map_theta_mul {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (li : Measure (Ainf F)) [li.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun y : Ainf F => θ ε * y) li =
      ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  have hL : Measurable (fun x : InfinitePlace F → ℝ => ε • x) := (continuous_const_smul ε).measurable
  have hθ : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
    funext y
    apply (eInf F h).injective
    simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
    funext w
    rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  have hdet : LinearMap.det (ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ))) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hε.ne'
  have hmapL := Measure.map_linearMap_addHaar_eq_smul_addHaar (Measure.map (eInf F h) li) hdet
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_fun_places F h] at hmapL
  have hcoe : (⇑(ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ)))) =
      fun x => ε • x := by
    funext x
    simp
  rw [hcoe] at hmapL
  have hid : (eInf F h).symm ∘ (eInf F h) = id := by
    funext x
    simp
  rw [hθ, ← Measure.map_map hms (hL.comp hm), ← Measure.map_map hL hm, hmapL, Measure.map_smul,
    Measure.map_map hms hm, hid, Measure.map_id, abs_of_pos (inv_pos.mpr (pow_pos hε _))]

/- English proof (translation)
Use `Measure.pi_eq fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`.
-/
theorem pi_const_smul {X : Type} [MeasurableSpace X] (ι : Type) [Fintype ι] (μ : Measure X) [SigmaFinite μ]
    (c : ENNReal) [SigmaFinite (c • μ)] :
    (Measure.pi fun _ : ι => c • μ) = c ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

/- English proof (translation)
Introduce `F _ _ h θ _ li _ ι _ ε hε`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Establish `h1` using `map_theta_mul h θ li hε`. Establish `hc : Continuous (eInf F h)` using `continuous_eInf F h`. Establish `hcs : Continuous (eInf F h).symm` using `continuous_eInf_symm F h`.

Establish `hm : Measurable (eInf F h)` using `hc.measurable`. Establish `hms : Measurable (eInf F h).symm` using `hcs.measurable`. Use `haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs`. Use `haveI : SigmaFinite (Measure.map (eInf F h) li) := Measure.IsAddHaarMeasure.sigmaFinite _`. Set `me : (InfinitePlace F → ℝ) ≃ᵐ Ainf F` to `{ toEquiv := (eInf F h).symm.toEquiv measurable_toFun := hms measurable_invFun := hm }`.

Establish `hme : (⇑me : (InfinitePlace F → ℝ) → Ainf F) = (eInf F h).symm` using `rfl`. Establish `hli : Measure.map me (Measure.map (eInf F h) li) = li`. Rewrite using `[Measure.map_map me.measurable hm, hme]`. Establish `hid : ((eInf F h).symm ∘ (eInf F h)) = id`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite using `[hid, Measure.map_id]`. Use `haveI : SigmaFinite li := by`. Rewrite using `[← hli]`. Conclude with `MeasurableEquiv.sigmaFinite_map me`.

Use `haveI hsf : SigmaFinite (ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li) := by`. Establish `hle : ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li = ((ε ^ Module.finrank ℚ F)⁻¹).toNNReal • li` using `rfl`. Rewrite using `[hle]`. Use `infer_instance`. Establish `hmeas : Measurable (fun y : Ainf F => θ ε * y)`.

Establish `hθ' : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h)`. Use function extensionality and compare the values at `y`. Apply `(eInf F h).injective` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]`. Use function extensionality and compare the values at `w`.

Rewrite using `[Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]`. Rewrite using `[hθ']`. Conclude with `hms.comp ((continuous_const_smul ε).measurable.comp hm)`. Establish `h2` using `Measure.pi_map_pi (μ := fun _ : ι => li) (f := fun _ y => θ ε * y) (hμ := fun _ => by show SigmaFinite (Measure.map (fun y : Ainf F => θ ε * y) li)`. Rewrite using `[h1]`.

Conclude with `hsf)`. Use the proof step `(fun _ => hmeas.aemeasurable)`. Rewrite using `[h2]`. Simplify using `only [h1]`. Rewrite using `[pi_const_smul ι li _, ← ENNReal.ofReal_pow (inv_nonneg.mpr (pow_nonneg hε.le _)), inv_pow, ← pow_mul]`.
-/
theorem map_theta_mul_pi : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε →
    Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) =
      ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  intro F _ _ h θ _ li _ ι _ ε hε
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have h1 := map_theta_mul h θ li hε
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  haveI : SigmaFinite (Measure.map (eInf F h) li) := Measure.IsAddHaarMeasure.sigmaFinite _
  let me : (InfinitePlace F → ℝ) ≃ᵐ Ainf F :=
    { toEquiv := (eInf F h).symm.toEquiv
      measurable_toFun := hms
      measurable_invFun := hm }
  have hme : (⇑me : (InfinitePlace F → ℝ) → Ainf F) = (eInf F h).symm := rfl
  have hli : Measure.map me (Measure.map (eInf F h) li) = li := by
    rw [Measure.map_map me.measurable hm, hme]
    have hid : ((eInf F h).symm ∘ (eInf F h)) = id := by
      funext x
      simp
    rw [hid, Measure.map_id]
  haveI : SigmaFinite li := by
    rw [← hli]
    exact MeasurableEquiv.sigmaFinite_map me
  haveI hsf : SigmaFinite (ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li) := by
    have hle : ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li =
        ((ε ^ Module.finrank ℚ F)⁻¹).toNNReal • li := rfl
    rw [hle]
    infer_instance
  have hmeas : Measurable (fun y : Ainf F => θ ε * y) := by
    have hθ' : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
      funext y
      apply (eInf F h).injective
      simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
      funext w
      rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
    rw [hθ']
    exact hms.comp ((continuous_const_smul ε).measurable.comp hm)
  have h2 := Measure.pi_map_pi (μ := fun _ : ι => li) (f := fun _ y => θ ε * y)
    (hμ := fun _ => by
      show SigmaFinite (Measure.map (fun y : Ainf F => θ ε * y) li)
      rw [h1]
      exact hsf)
    (fun _ => hmeas.aemeasurable)
  rw [h2]
  simp only [h1]
  rw [pi_const_smul ι li _, ← ENNReal.ofReal_pow (inv_nonneg.mpr (pow_nonneg hε.le _)), inv_pow, ← pow_mul]

end GlobalTheory.CompanionTheory.Equi.InfScale

end
