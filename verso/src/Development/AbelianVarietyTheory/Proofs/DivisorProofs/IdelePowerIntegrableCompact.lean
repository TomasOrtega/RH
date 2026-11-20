import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LocTateConv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev bas [Module.Finite F E] (v : Pl F) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

/- English proof (translation)
Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Set `b` to `bas (E := E) v`. Set `φ` to `b.equivFun`. Set `M : Fv F v ⊗[F] E → Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (Fv F v)` to `Algebra.leftMulMatrix b`.

Establish `hM : Continuous M` using `IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap`. Establish `hφs : Continuous φ.symm` using `IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap`. Establish `hmul : ∀ x y, M x *ᵥ φ y = φ (x * y)` using `fun x y => by`. Simplify using `only [φ, M, Module.Basis.equivFun_apply]`. Conclude with `Algebra.leftMulMatrix_mulVec_repr b x y`.

Establish `hdet : ∀ x, (M x).det = Algebra.norm (Fv F v) x` using `fun x => (Algebra.norm_eq_matrix_det b x).symm`. Set `f : Fv F v ⊗[F] E → Fv F v ⊗[F] E` to `fun x => φ.symm ((M x)⁻¹ *ᵥ φ 1)`. Establish `hinv : ∀ x, Algebra.norm (Fv F v) x ≠ 0 → x * f x = 1`. Introduce `x hx`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[← hmul, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [hdet]; exact hx.isUnit), Matrix.one_mulVec]`. Establish `hiff : ∀ x, IsUnit x ↔ Algebra.norm (Fv F v) x ≠ 0` using `fun x => ⟨fun h => (h.map (Algebra.norm (Fv F v))).ne_zero, fun h => isUnit_iff_exists_inv.2 ⟨_, hinv x h⟩⟩`. Establish `hfu : ∀ u : (Fv F v ⊗[F] E)ˣ, f u = ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)` using `fun u => (Units.inv_eq_of_mul_eq_one_right (hinv u ((hiff u).1 u.isUnit))).symm`. Establish `hfc : ContinuousOn f {x | IsUnit x}`. Establish `h1 : ContinuousOn (fun x => (M x)⁻¹) {x | IsUnit x}`.

Establish `e : (fun x => (M x)⁻¹) = fun x => Ring.inverse (M x).det • (M x).adjugate`. Use function extensionality and compare the values at `fun x => Matrix.inv_def _`. Rewrite using `[e]`. Use `ContinuousOn.smul (f := fun x => Ring.inverse (M x).det) (g := fun x => (M x).adjugate) ?_ hM.matrix_adjugate.continuousOn` and prove the remaining obligations. Rewrite using `[Ring.inverse_eq_inv']`.

Conclude with `continuousOn_inv₀.comp hM.matrix_det.continuousOn (fun x hx => by show (M x).det ≠ 0`. Rewrite using `[hdet]`. Conclude with `(hiff x).1 hx)`. Conclude with `hφs.comp_continuousOn ((continuous_id.matrix_mulVec continuous_const).comp_continuousOn h1)`. Use `⟨Units.isEmbedding_val_mk' hfc hfu, ?_⟩` and prove the remaining obligations.

Establish `hr : Set.range (Units.val : (Fv F v ⊗[F] E)ˣ → Fv F v ⊗[F] E) = Algebra.norm (Fv F v) ⁻¹' {0}ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`. Conclude with `⟨fun ⟨u, hu⟩ => hu ▸ (hiff u).1 u.isUnit, fun h => ⟨((hiff x).2 h).unit, rfl⟩⟩`. Rewrite using `[hr]`.

Conclude with `isOpen_compl_singleton.preimage GlobalTheory.Doubling.continuous_norm_tens`.
-/
theorem isOpenEmbedding_val_tens [Module.Finite F E] (v : Pl F) :
    IsOpenEmbedding (Units.val : (Fv F v ⊗[F] E)ˣ → Fv F v ⊗[F] E) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  let b := bas (E := E) v
  let φ := b.equivFun
  let M : Fv F v ⊗[F] E → Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (Fv F v) :=
    Algebra.leftMulMatrix b
  have hM : Continuous M := IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
  have hmul : ∀ x y, M x *ᵥ φ y = φ (x * y) := fun x y => by
    simp only [φ, M, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr b x y
  have hdet : ∀ x, (M x).det = Algebra.norm (Fv F v) x := fun x => (Algebra.norm_eq_matrix_det b x).symm
  let f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun x => φ.symm ((M x)⁻¹ *ᵥ φ 1)
  have hinv : ∀ x, Algebra.norm (Fv F v) x ≠ 0 → x * f x = 1 := by
    intro x hx
    apply φ.injective
    rw [← hmul, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (by rw [hdet]; exact hx.isUnit), Matrix.one_mulVec]
  have hiff : ∀ x, IsUnit x ↔ Algebra.norm (Fv F v) x ≠ 0 := fun x =>
    ⟨fun h => (h.map (Algebra.norm (Fv F v))).ne_zero, fun h => isUnit_iff_exists_inv.2 ⟨_, hinv x h⟩⟩
  have hfu : ∀ u : (Fv F v ⊗[F] E)ˣ, f u = ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := fun u =>
    (Units.inv_eq_of_mul_eq_one_right (hinv u ((hiff u).1 u.isUnit))).symm
  have hfc : ContinuousOn f {x | IsUnit x} := by
    have h1 : ContinuousOn (fun x => (M x)⁻¹) {x | IsUnit x} := by
      have e : (fun x => (M x)⁻¹) = fun x => Ring.inverse (M x).det • (M x).adjugate :=
        funext fun x => Matrix.inv_def _
      rw [e]
      refine ContinuousOn.smul (f := fun x => Ring.inverse (M x).det) (g := fun x => (M x).adjugate) ?_
        hM.matrix_adjugate.continuousOn
      rw [Ring.inverse_eq_inv']
      exact continuousOn_inv₀.comp hM.matrix_det.continuousOn (fun x hx => by
        show (M x).det ≠ 0
        rw [hdet]; exact (hiff x).1 hx)
    exact hφs.comp_continuousOn ((continuous_id.matrix_mulVec continuous_const).comp_continuousOn h1)
  refine ⟨Units.isEmbedding_val_mk' hfc hfu, ?_⟩
  have hr : Set.range (Units.val : (Fv F v ⊗[F] E)ˣ → Fv F v ⊗[F] E) = Algebra.norm (Fv F v) ⁻¹' {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ (hiff u).1 u.isUnit, fun h => ⟨((hiff x).2 h).unit, rfl⟩⟩
  rw [hr]
  exact isOpen_compl_singleton.preimage GlobalTheory.Doubling.continuous_norm_tens

/- English proof (translation)
Use `haveI := GlobalTheory.FinUniq.sc_Fv v`. Use `set M := Algebra.leftMulMatrix (bas (E := E) v) h.1 with hMdef`. Establish `hMd : M.det = Algebra.norm (Fv F v) h.1` using `(Algebra.norm_eq_matrix_det _ _).symm`. Establish `hd : M.det ≠ 0` using `by rw [hMd]; exact (h.isUnit.map _).ne_zero`. Set `lam : Measure (Fv F v)` to `Measure.addHaar`.

Establish `hc` using `GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map lam (Units.mk0 M.det hd)`. Establish `hn : distribHaarChar (Fv F v) (Units.mk0 M.det hd) = ‖M.det‖₊` using `GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v M.det hd`. Rewrite `hc` using `[hn]`. Establish `hne : (‖M.det‖₊) ≠ 0` using `nnnorm_ne_zero_iff.2 hd`. Establish `hc' : lam.map (fun x => algebraMap (Fv F v) (Fv F v) M.det * x) = (‖M.det‖₊)⁻¹ • lam` using `by conv_rhs => rw [← hc]`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul (Fv F v) (Fv F v) _ M hd lam inferInstance _ hc' ν inferInstance`. Rewrite using `[← hMd]`. Simplify `key` using `[Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]`.
-/
theorem map_mulVec_leftMul [Module.Finite F E] (v : Pl F) [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)]
    (ν : Measure (Fin (Module.finrank F E) → Fv F v)) [ν.IsAddHaarMeasure] (h : (Fv F v ⊗[F] E)ˣ) :
    ν.map (fun y => Algebra.leftMulMatrix (bas (E := E) v) h.1 *ᵥ y) =
      (‖Algebra.norm (Fv F v) h.1‖₊)⁻¹ • ν := by
  haveI := GlobalTheory.FinUniq.sc_Fv v
  set M := Algebra.leftMulMatrix (bas (E := E) v) h.1 with hMdef
  have hMd : M.det = Algebra.norm (Fv F v) h.1 := (Algebra.norm_eq_matrix_det _ _).symm
  have hd : M.det ≠ 0 := by rw [hMd]; exact (h.isUnit.map _).ne_zero
  let lam : Measure (Fv F v) := Measure.addHaar
  have hc := GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map lam (Units.mk0 M.det hd)
  have hn : distribHaarChar (Fv F v) (Units.mk0 M.det hd) = ‖M.det‖₊ :=
    GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v M.det hd
  rw [hn] at hc
  have hne : (‖M.det‖₊) ≠ 0 := nnnorm_ne_zero_iff.2 hd
  have hc' : lam.map (fun x => algebraMap (Fv F v) (Fv F v) M.det * x) = (‖M.det‖₊)⁻¹ • lam := by
    conv_rhs => rw [← hc]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rfl
  have key := GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul (Fv F v) (Fv F v) _ M hd lam inferInstance _ hc' ν
    inferInstance
  rw [← hMd]
  simpa [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using key

/- English proof (translation)
Establish `hje : MeasurableEmbedding j` using `hj.measurableEmbedding`. Establish `hN1 : ∀ g, N g * N g⁻¹ = 1` using `fun g => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hN0 : ∀ g, N g ≠ 0` using `fun g h => by simpa [h] using hN1 g`. Use `set lam0 : Measure G := lam.comap j with hlam0`. Establish `hlam0map : ∀ g, lam0.map (fun l => g * l) = (N g)⁻¹ • lam0`.

Introduce `g`. Use extensionality with `s hs`. Establish `e : j '' ((fun l => g * l) ⁻¹' s) = m g ⁻¹' (j '' s)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨l, hl, rfl⟩`. Conclude with `⟨g * l, hl, hjm g l⟩`. Introduce and unpack `⟨l, hl, hy⟩`. Use `⟨g⁻¹ * l, by simpa using hl, hinj g ?_⟩` and prove the remaining obligations. Rewrite using `[← hjm, mul_inv_cancel_left, hy]`.

Rewrite using `[Measure.map_apply (measurable_const_mul g) hs, hlam0, hje.comap_apply, e, ← Measure.map_apply (hm g) (hje.measurableSet_image.2 hs), hmap, Measure.smul_apply, Measure.smul_apply, hje.comap_apply]`. Use `haveI : IsFiniteMeasureOnCompacts lam0 := ⟨fun C hC => by`. Rewrite using `[hlam0, hje.comap_apply]`. Conclude with `(hC.image hj.continuous).measure_lt_top⟩`. Establish `hw : Continuous fun l : G => N l⁻¹` using `hN.comp continuous_inv`.

Establish `hwm : Measurable fun l : G => (N l⁻¹ : ENNReal)` using `hw.measurable.coe_nnreal_ennreal`. Use `set ν : Measure G := lam0.withDensity fun l => (N l⁻¹ : ENNReal) with hν`. Use `haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe hw`. Use `haveI : ν.IsMulLeftInvariant := ⟨fun g => by`. Use extensionality with `s hs`.

Establish `hs' : MeasurableSet ((fun l => g * l) ⁻¹' s)` using `measurable_const_mul g hs`. Rewrite using `[Measure.map_apply (measurable_const_mul g) hs, hν, withDensity_apply _ hs, withDensity_apply _ hs']`. Establish `e : (fun l : G => (N l⁻¹ : ENNReal)) = fun l => (N g : ENNReal) * (N (g * l)⁻¹ : ENNReal)`. Use function extensionality and compare the values at `l`. Rewrite using `[← ENNReal.coe_mul, mul_inv_rev, map_mul, mul_left_comm, hN1, mul_one]`.

Use `conv_lhs => rw [e]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← setLIntegral_map hs hwm (measurable_const_mul g), hlam0map, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (hN0 g), ENNReal.coe_one, one_mul]⟩`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul ν μ`. Use `set c := ν.haarScalarFactor μ`. Establish `hc0 : c ≠ 0`.

Introduce `h`. Rewrite `hc` using `[h, zero_smul, hν, withDensity_eq_zero_iff hwm.aemeasurable]`. Establish `h1 : lam0 Set.univ = 0`. Use `measure_mono_null (fun l _ => ?_) hc` and prove the remaining obligations. Simplify using `using hN0 l⁻¹`.

Rewrite `h1` using `[hlam0, hje.comap_apply, Set.image_univ]`. Conclude with `(hj.isOpen_range.measure_pos lam ⟨_, 1, rfl⟩).ne' h1`. Establish `hKm : MeasurableSet (j ⁻¹' K)` using `hje.measurable hK.measurableSet`. Establish `h2 : ∫⁻ l in j ⁻¹' K, (N l : ENNReal) ∂ν < ⊤`. Rewrite using `[hν, setLIntegral_withDensity_eq_setLIntegral_mul _ hwm hN.measurable.coe_nnreal_ennreal hKm]`.

Establish `e : ((fun l : G => (N l⁻¹ : ENNReal)) * fun l => (N l : ENNReal)) = fun _ => 1`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.mul_apply, ← ENNReal.coe_mul, mul_comm, hN1, ENNReal.coe_one]`. Rewrite using `[e, setLIntegral_one, hlam0, hje.comap_apply]`. Conclude with `(measure_mono (Set.image_preimage_subset _ _)).trans_lt hK.measure_lt_top`.

Rewrite `h2` using `[hc, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`. Conclude with `ENNReal.lt_top_of_mul_ne_top_right h2.ne (by simpa using hc0)`.
-/
theorem lintegral_lt_top_of_module {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (j : G → V) (hj : IsOpenEmbedding j) (lam : Measure V) [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure]
    (N : G →* ℝ≥0) (hN : Continuous N) (m : G → V → V) (hm : ∀ g, Measurable (m g))
    (hinj : ∀ g, Function.Injective (m g)) (hjm : ∀ g l, j (g * l) = m g (j l))
    (hmap : ∀ g, lam.map (m g) = (N g)⁻¹ • lam) (μ : Measure G) [μ.IsHaarMeasure] {K : Set V} (hK : IsCompact K) :
    ∫⁻ l in j ⁻¹' K, (N l : ENNReal) ∂μ < ⊤ := by
  have hje : MeasurableEmbedding j := hj.measurableEmbedding
  have hN1 : ∀ g, N g * N g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hN0 : ∀ g, N g ≠ 0 := fun g h => by simpa [h] using hN1 g
  set lam0 : Measure G := lam.comap j with hlam0
  have hlam0map : ∀ g, lam0.map (fun l => g * l) = (N g)⁻¹ • lam0 := by
    intro g
    ext s hs
    have e : j '' ((fun l => g * l) ⁻¹' s) = m g ⁻¹' (j '' s) := by
      ext y
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨g * l, hl, hjm g l⟩
      · rintro ⟨l, hl, hy⟩
        refine ⟨g⁻¹ * l, by simpa using hl, hinj g ?_⟩
        rw [← hjm, mul_inv_cancel_left, hy]
    rw [Measure.map_apply (measurable_const_mul g) hs, hlam0, hje.comap_apply, e,
      ← Measure.map_apply (hm g) (hje.measurableSet_image.2 hs), hmap, Measure.smul_apply, Measure.smul_apply,
      hje.comap_apply]
  haveI : IsFiniteMeasureOnCompacts lam0 := ⟨fun C hC => by
    rw [hlam0, hje.comap_apply]
    exact (hC.image hj.continuous).measure_lt_top⟩
  have hw : Continuous fun l : G => N l⁻¹ := hN.comp continuous_inv
  have hwm : Measurable fun l : G => (N l⁻¹ : ENNReal) := hw.measurable.coe_nnreal_ennreal
  set ν : Measure G := lam0.withDensity fun l => (N l⁻¹ : ENNReal) with hν
  haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe hw
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    have hs' : MeasurableSet ((fun l => g * l) ⁻¹' s) := measurable_const_mul g hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hν, withDensity_apply _ hs, withDensity_apply _ hs']
    have e : (fun l : G => (N l⁻¹ : ENNReal)) = fun l => (N g : ENNReal) * (N (g * l)⁻¹ : ENNReal) := by
      funext l
      rw [← ENNReal.coe_mul, mul_inv_rev, map_mul, mul_left_comm, hN1, mul_one]
    conv_lhs => rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      ← setLIntegral_map hs hwm (measurable_const_mul g), hlam0map, Measure.restrict_smul, lintegral_smul_measure,
      ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (hN0 g), ENNReal.coe_one,
      one_mul]⟩
  have hc := Measure.isMulLeftInvariant_eq_smul ν μ
  set c := ν.haarScalarFactor μ
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul, hν, withDensity_eq_zero_iff hwm.aemeasurable] at hc
    have h1 : lam0 Set.univ = 0 := by
      refine measure_mono_null (fun l _ => ?_) hc
      simpa using hN0 l⁻¹
    rw [hlam0, hje.comap_apply, Set.image_univ] at h1
    exact (hj.isOpen_range.measure_pos lam ⟨_, 1, rfl⟩).ne' h1
  have hKm : MeasurableSet (j ⁻¹' K) := hje.measurable hK.measurableSet
  have h2 : ∫⁻ l in j ⁻¹' K, (N l : ENNReal) ∂ν < ⊤ := by
    rw [hν, setLIntegral_withDensity_eq_setLIntegral_mul _ hwm hN.measurable.coe_nnreal_ennreal hKm]
    have e : ((fun l : G => (N l⁻¹ : ENNReal)) * fun l => (N l : ENNReal)) = fun _ => 1 := by
      funext l
      rw [Pi.mul_apply, ← ENNReal.coe_mul, mul_comm, hN1, ENNReal.coe_one]
    rw [e, setLIntegral_one, hlam0, hje.comap_apply]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hK.measure_lt_top
  rw [hc, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul] at h2
  exact ENNReal.lt_top_of_mul_ne_top_right h2.ne (by simpa using hc0)

/- English proof (translation)
Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evFin F v)`. Use `haveI := GlobalTheory.FinUniq.sc_Fv v`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `letI : MeasurableSpace (Fv F v) := borel _`.

Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Set `b` to `bas (E := E) v`. Set `φ` to `b.equivFun`. Establish `hφ : Continuous φ` using `IsModuleTopology.continuous_of_linearMap φ.toLinearMap`. Establish `hφs : Continuous φ.symm` using `IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap`.

Set `φh : (Fv F v ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Fv F v)` to `⟨φ.toEquiv, hφ, hφs⟩`. Set `e` to `idelesAtEquiv E v`. Set `u : idelesAt E (evFin F v) → Fv F v ⊗[F] E` to `fun l => (e l).1`. Establish `hu : IsOpenEmbedding u` using `(isOpenEmbedding_val_tens v).comp e.toHomeomorph.isOpenEmbedding`. Establish `hj : IsOpenEmbedding (fun l => φ (u l))` using `φh.isOpenEmbedding.comp hu`.

Set `N : idelesAt E (evFin F v) →* ℝ≥0` to `(GlobalTheory.Doubling.absEv F E v).comp e.toMonoidHom`. Establish `hNa : ∀ l, N l = ‖Algebra.norm (Fv F v) (u l)‖₊` using `fun l => GlobalTheory.Doubling.absEv_apply v (e l)`. Establish `hnc : Continuous fun x : Fv F v ⊗[F] E => ‖Algebra.norm (Fv F v) x‖₊` using `GlobalTheory.Doubling.continuous_norm_tens.nnnorm`. Establish `hN : Continuous N`. Rewrite using `[show (N : _ → ℝ≥0) = fun l => ‖Algebra.norm (Fv F v) (u l)‖₊ from funext hNa]`.

Conclude with `hnc.comp hu.continuous`. Establish `hmul : ∀ x y, Algebra.leftMulMatrix b x *ᵥ φ y = φ (x * y)` using `fun x y => by`. Simplify using `only [φ, Module.Basis.equivFun_apply]`. Conclude with `Algebra.leftMulMatrix_mulVec_repr b x y`. Establish `key` using `lintegral_lt_top_of_module (fun l => φ (u l)) hj Measure.addHaar N hN (fun g y => Algebra.leftMulMatrix b (e g).1 *ᵥ y) (fun g => (continuous_const.matrix_mulVec continuous_id).measurable) (fun g y y' h => by`.

Take `⟨x, rfl⟩` from `φ.surjective y`. Take `⟨x', rfl⟩` from `φ.surjective y'`. Simplify using `only [hmul] at h`. Rewrite using `[(e g).isUnit.mul_left_cancel (φ.injective h)])`. Use the proof step `(fun g l => by show φ (e (g * l)).1 = _`.

Rewrite using `[hmul, map_mul, Units.val_mul])`. Use the proof step `(fun g => by rw [hNa]; exact map_mulVec_leftMul v _ (e g)) μ (hC.image hφ)`. Establish `hS : (fun l => φ (u l)) ⁻¹' (φ '' C) = u ⁻¹' C`. Use extensionality with `l`. Simplify using `only [Set.mem_preimage]`.

Conclude with `φ.injective.mem_set_image`. Rewrite `key` using `[hS]`. Establish `hSm : MeasurableSet (u ⁻¹' C)` using `(hC.isClosed.preimage hu.continuous).measurableSet`. Establish `h1 : IntegrableOn (fun l => (N l : ℝ)) (u ⁻¹' C) μ`. Use `⟨(NNReal.continuous_coe.comp hN).aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[hasFiniteIntegral_iff_enorm]`. Simplify using `using key`. Take `⟨B, hB⟩` from `(hC.image hnc).bddAbove`. Establish `hf : (fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ)) ^ z) = fun l => (N l : ℝ) ^ z`. Use function extensionality and compare the values at `fun l => by rw [absE_of_mem l.2]; rfl`.

Rewrite using `[hf]`. Use `show IntegrableOn _ (u ⁻¹' C) μ`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le' hz`. Use `Integrable.mono' (h1.const_mul ((B : ℝ) ^ k)) ((NNReal.continuous_coe.comp hN).pow _).aestronglyMeasurable ?_` and prove the remaining obligations. Use `ae_restrict_of_forall_mem hSm fun l hl => ?_` and prove the remaining obligations.

Establish `hle : (N l : ℝ) ≤ B`. Rewrite using `[hNa]`. Conclude with `hB ⟨_, hl, rfl⟩` after adjusting the coercions. Rewrite using `[Real.norm_of_nonneg (by positivity), pow_succ]`. Use `gcongr`.
-/
theorem integrableOn_absE_pow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))) (hμ : μ.IsHaarMeasure) (C : Set (Fv F v ⊗[F] E)) (hC : IsCompact C)
    (z : ℕ) (hz : 1 ≤ z) : IntegrableOn (fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ)) ^ z)
      {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} μ := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := GlobalTheory.FinUniq.sc_Fv v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  let b := bas (E := E) v
  let φ := b.equivFun
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
  have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
  let φh : (Fv F v ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Fv F v) := ⟨φ.toEquiv, hφ, hφs⟩
  let e := idelesAtEquiv E v
  let u : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => (e l).1
  have hu : IsOpenEmbedding u := (isOpenEmbedding_val_tens v).comp e.toHomeomorph.isOpenEmbedding
  have hj : IsOpenEmbedding (fun l => φ (u l)) := φh.isOpenEmbedding.comp hu
  let N : idelesAt E (evFin F v) →* ℝ≥0 := (GlobalTheory.Doubling.absEv F E v).comp e.toMonoidHom
  have hNa : ∀ l, N l = ‖Algebra.norm (Fv F v) (u l)‖₊ := fun l => GlobalTheory.Doubling.absEv_apply v (e l)
  have hnc : Continuous fun x : Fv F v ⊗[F] E => ‖Algebra.norm (Fv F v) x‖₊ :=
    GlobalTheory.Doubling.continuous_norm_tens.nnnorm
  have hN : Continuous N := by
    rw [show (N : _ → ℝ≥0) = fun l => ‖Algebra.norm (Fv F v) (u l)‖₊ from funext hNa]
    exact hnc.comp hu.continuous
  have hmul : ∀ x y, Algebra.leftMulMatrix b x *ᵥ φ y = φ (x * y) := fun x y => by
    simp only [φ, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr b x y
  have key := lintegral_lt_top_of_module (fun l => φ (u l)) hj Measure.addHaar N hN
    (fun g y => Algebra.leftMulMatrix b (e g).1 *ᵥ y)
    (fun g => (continuous_const.matrix_mulVec continuous_id).measurable)
    (fun g y y' h => by
      obtain ⟨x, rfl⟩ := φ.surjective y
      obtain ⟨x', rfl⟩ := φ.surjective y'
      simp only [hmul] at h
      rw [(e g).isUnit.mul_left_cancel (φ.injective h)])
    (fun g l => by
      show φ (e (g * l)).1 = _
      rw [hmul, map_mul, Units.val_mul])
    (fun g => by rw [hNa]; exact map_mulVec_leftMul v _ (e g)) μ (hC.image hφ)
  have hS : (fun l => φ (u l)) ⁻¹' (φ '' C) = u ⁻¹' C := by
    ext l
    simp only [Set.mem_preimage]
    exact φ.injective.mem_set_image
  rw [hS] at key
  have hSm : MeasurableSet (u ⁻¹' C) := (hC.isClosed.preimage hu.continuous).measurableSet
  have h1 : IntegrableOn (fun l => (N l : ℝ)) (u ⁻¹' C) μ := by
    refine ⟨(NNReal.continuous_coe.comp hN).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa using key
  obtain ⟨B, hB⟩ := (hC.image hnc).bddAbove
  have hf : (fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ)) ^ z) = fun l => (N l : ℝ) ^ z :=
    funext fun l => by rw [absE_of_mem l.2]; rfl
  rw [hf]
  show IntegrableOn _ (u ⁻¹' C) μ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hz
  refine Integrable.mono' (h1.const_mul ((B : ℝ) ^ k))
    ((NNReal.continuous_coe.comp hN).pow _).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hSm fun l hl => ?_
  have hle : (N l : ℝ) ≤ B := by
    rw [hNa]; exact_mod_cast hB ⟨_, hl, rfl⟩
  rw [Real.norm_of_nonneg (by positivity), pow_succ]
  gcongr

end GlobalTheory.LocTateConv
