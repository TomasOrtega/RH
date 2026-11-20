import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct ENNReal NNReal Matrix Classical NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ModConj

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e`. Take `⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν` from `⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩`. Establish `he : Measurable e` using `e.continuous.measurable`. Establish `h2 : ν.map (e ∘ e) = (b * b) • ν`. Rewrite using `[← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]`.

Establish `hid : (e ∘ e : G → G) = id` using `funext he2`. Rewrite `h2` using `[hid, Measure.map_id]`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : G)`. Establish `hpos : ν K ≠ 0` using `(Measure.measure_pos_of_mem_nhds ν hK0).ne'`. Establish `hfin : ν K ≠ ∞` using `hK.measure_lt_top.ne`.

Establish `hbb : b * b = 1`. Establish `h3 : ((b * b : ℝ≥0) • ν) K = ((1 : ℝ≥0) • ν) K` using `by rw [← h2, one_smul]`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3`. Conclude with `(ENNReal.mul_left_inj hpos hfin).1 h3` after adjusting the coercions. Establish `hb1 : b = 1`.

Use `(mul_self_eq_one_iff (a := (b : ℝ))).1 (by exact_mod_cast hbb)` as an intermediate fact. Break down `this with h | h` into its components or cases. Conclude with `h` after adjusting the coercions. Use `b.2` as an intermediate fact. Simplify using `only [NNReal.val_eq_coe] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hb, hb1, one_smul]`.
-/
theorem map_involution_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he2 : ∀ x, e (e x) = x) (ν : Measure G) [ν.IsAddHaarMeasure] [SecondCountableTopology G] :
    ν.map e = ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]
  have hid : (e ∘ e : G → G) = id := funext he2
  rw [hid, Measure.map_id] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbb : b * b = 1 := by
    have h3 : ((b * b : ℝ≥0) • ν) K = ((1 : ℝ≥0) • ν) K := by rw [← h2, one_smul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  have hb1 : b = 1 := by
    have := (mul_self_eq_one_iff (a := (b : ℝ))).1 (by exact_mod_cast hbb)
    rcases this with h | h
    · exact_mod_cast h
    · have := b.2; simp only [NNReal.val_eq_coe] at this; linarith
  rw [hb, hb1, one_smul]

def conjA (σ : E →ₐ[F] E) : 𝔸[E] →+* 𝔸[E] :=
  (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).toRingEquiv.toRingHom.comp
    ((sigR (AF F) σ).comp (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm.toRingEquiv.toRingHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjA_apply (σ : E →ₐ[F] E) (y : 𝔸[E]) :
    conjA σ y = GroundTheory.BlockD.ThmBHecke.adeleEquiv F E
      (sigR (AF F) σ ((GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm y)) := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR, hσ]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem sig_sig {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
The claim follows from `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.1`.
-/
theorem continuous_sig {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : Continuous (sigR (AF F) σ) :=
  (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.1

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2, hcm.2.2.2, star_star]`.
-/
theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

def conjE {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : 𝔸[E] ≃ₜ+ 𝔸[E] where
  toFun := conjA σ
  invFun := conjA σ
  left_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  right_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  map_add' := map_add _
  continuous_toFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)
  continuous_invFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm x`. Use `letI : MeasurableSpace 𝔸[E] := measurableSpace_adeleRing E`. Use `set a := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x with ha`. Use `set a' := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x) with ha'`. Use `set e := conjE hcm with he`.

Use `set ν := adeleMeasure E with hν`. Establish `hinv : ∀ y, e (e y) = y` using `fun y => e.left_inv y`. Establish `hcoe : ∀ y, e y = conjA σ y` using `fun _ => rfl`. Establish `hea : e (a : 𝔸[E]) = (a' : 𝔸[E])`. Rewrite using `[hcoe, conjA_apply, ha, ha', GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, AlgEquiv.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `key : ∀ y : 𝔸[E], a' • y = e (a • e y)` using `fun y => by`. Rewrite using `[Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcoe (_ * _), map_mul, ← hcoe, ← hcoe, hinv, hea]`. Establish `hmeas : Measurable e` using `e.continuous.measurable`. Establish `hm : Measurable (fun y : 𝔸[E] => a • y)` using `(Homeomorph.smul a).continuous.measurable`.

Establish `hνe : ν.map e = ν` using `map_involution_eq e hinv ν`. Establish `hfun : (fun y : 𝔸[E] => a' • y) = e ∘ (fun y => a • y) ∘ e` using `funext key`. Establish `h1 : ν.map (fun y : 𝔸[E] => a' • y) = ENNReal.ofReal ((IdeleGroup.ideleModule E a : ℝ))⁻¹ • ν`. Rewrite using `[hfun, ← Measure.map_map hmeas (hm.comp hmeas), ← Measure.map_map hm hmeas, hνe, hν, map_smul_adeleMeasure, Measure.map_smul, ← hν, hνe]`. Establish `h2` using `map_smul_adeleMeasure (K := E) a'`.

Rewrite `h2` using `[← hν, h1]`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : 𝔸[E])`. Establish `hpos : ν K ≠ 0` using `(Measure.measure_pos_of_mem_nhds ν hK0).ne'`. Establish `hfin : ν K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `h3` using `congrArg (fun m : Measure 𝔸[E] => m K) h2`.

Simplify using `only [Measure.smul_apply, smul_eq_mul] at h3`. Establish `h4` using `(ENNReal.mul_left_inj hpos hfin).1 h3`. Establish `h5` using `(ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule E a).2.le) (inv_nonneg.2 (IdeleGroup.ideleModule E a').2.le)).1 h4`. Conclude with `(inv_injective h5).symm`.
-/
theorem ideleModule_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : (AF F ⊗[F] E)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E
        (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ) =
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) := by
  intro F E _ _ _ _ _ σ hcm x
  letI : MeasurableSpace 𝔸[E] := measurableSpace_adeleRing E
  set a := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x with ha
  set a' := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x) with ha'
  set e := conjE hcm with he
  set ν := adeleMeasure E with hν
  have hinv : ∀ y, e (e y) = y := fun y => e.left_inv y
  have hcoe : ∀ y, e y = conjA σ y := fun _ => rfl
  have hea : e (a : 𝔸[E]) = (a' : 𝔸[E]) := by
    rw [hcoe, conjA_apply, ha, ha', GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv,
      GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, AlgEquiv.symm_apply_apply]
    rfl
  have key : ∀ y : 𝔸[E], a' • y = e (a • e y) := fun y => by
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcoe (_ * _), map_mul, ← hcoe, ← hcoe,
      hinv, hea]
  have hmeas : Measurable e := e.continuous.measurable
  have hm : Measurable (fun y : 𝔸[E] => a • y) := (Homeomorph.smul a).continuous.measurable
  have hνe : ν.map e = ν := map_involution_eq e hinv ν
  have hfun : (fun y : 𝔸[E] => a' • y) = e ∘ (fun y => a • y) ∘ e := funext key
  have h1 : ν.map (fun y : 𝔸[E] => a' • y) =
      ENNReal.ofReal ((IdeleGroup.ideleModule E a : ℝ))⁻¹ • ν := by
    rw [hfun, ← Measure.map_map hmeas (hm.comp hmeas), ← Measure.map_map hm hmeas, hνe, hν,
      map_smul_adeleMeasure, Measure.map_smul, ← hν, hνe]
  have h2 := map_smul_adeleMeasure (K := E) a'
  rw [← hν, h1] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : 𝔸[E])
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have h3 := congrArg (fun m : Measure 𝔸[E] => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule E a).2.le)
    (inv_nonneg.2 (IdeleGroup.ideleModule E a').2.le)).1 h4
  exact (inv_injective h5).symm

end GlobalTheory.CompanionTheory.SW.ModConj
