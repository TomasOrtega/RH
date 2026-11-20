import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh MeasureTheory Matrix

namespace GlobalTheory.DiscreteUnit

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]

/- English proof (translation)
Establish `e` using `Measure.isMulLeftInvariant_eq_smul μ μ'`. Establish `hF2 : IsFundamentalDomain Γ F' μ` using `hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')`. Rewrite using `[hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]`. Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top h`.
-/
theorem lintegral_lt_top {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ F' μ') {φ : G → ENNReal}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (h : ∫⁻ g in F', φ g ∂μ' < ⊤) : ∫⁻ g in F, φ g ∂μ < ⊤ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hF2 : IsFundamentalDomain Γ F' μ := hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')
  rw [hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

/- English proof (translation)
Establish `hm : MeasurePreserving (fun g => g * x) μ μ` using `⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩`. Establish `hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ` using `hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x`. Rewrite using `[hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by`. Express the relevant statement in the definitionally equal form `φ (γ.1 * g * x) = _`. Rewrite using `[mul_assoc, hφ γ γ.2]]`.

Conclude with `hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F`.
-/
theorem integral_mul_right {μ : Measure G} [μ.IsHaarMeasure] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) {x : G} (hx : Measure.modularCharacter x = 1) :
    ∫ g in F, φ (g * x) ∂μ = ∫ g in F, φ g ∂μ := by
  have hm : MeasurePreserving (fun g => g * x) μ μ :=
    ⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩
  have hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ :=
    hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x
  rw [hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by
    change φ (γ.1 * g * x) = _
    rw [mul_assoc, hφ γ γ.2]]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F

/- English proof (translation)
Take `⟨μ, F, hμ, hF, -⟩` from `h2 0`. Establish `hm : ∀ v, MemLp (f v) 2 (μ.restrict F)` using `fun v => by`. Take `⟨μ', F', hμ', hF', h⟩` from `h2 v`. Establish `h3` using `lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h`. Use `⟨(hc v).aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]`. Simplify using `using h3`. Establish `hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F)` using `fun v w => (hm v).integrable_mul (hm w).star`. Use `⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ) (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_, fun h v w => ?_⟩` and prove the remaining obligations. Rewrite using `[← integral_add (hi _ _) (hi _ _)]`.

Simplify using `[add_mul]`. Simplify using `[mul_assoc, integral_const_mul]`. Rewrite using `[← integral_add (hi _ _) (hi _ _)]`. Simplify using `[mul_add]`. Simplify using `[mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]`.

Simplify using `only [LinearMap.mk₂'ₛₗ_apply]`. Rewrite using `[← integral_conj]`. Simplify using `[mul_comm]`. Simplify using `only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]`. Rewrite using `[integral_complex_ofReal, Complex.ofReal_re]`.

Establish `hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F)`. Simplify `(hi v v).re` using `[Complex.mul_conj]`. Use `(integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)` and prove the remaining obligations. Establish `ho : IsOpen (Function.support fun g => Complex.normSq (f v g))` using `(Complex.continuous_normSq.comp (hc v)).isOpen_support`. Rewrite `h0` using `[Measure.restrict_apply ho.measurableSet]`.

Establish `h4` using `hF.measure_zero_of_invariant _ (fun γ => by`. Use extensionality with `g`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]`. Express the relevant statement in the definitionally equal form `Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _`. Rewrite using `[hl v _ (γ⁻¹).2]) h0`.

Establish `h5` using `Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)`. Use `hf (funext fun g => ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `Complex.normSq_eq_zero.1 (congrFun h5 g)`. Simplify using `only [LinearMap.mk₂'ₛₗ_apply, hρ]`.

Conclude with `integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g)) (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)`.
-/
theorem isUnitarisable_of_embedding {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (ι : H → G) (hι : ∀ h, Measure.modularCharacter (ι h) = 1) (f : X →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hc : ∀ v, Continuous (f v)) (hl : ∀ v, ∀ γ ∈ Γ, ∀ g, f v (γ * g) = f v g)
    (h2 : ∀ v, ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∫⁻ g in F, ‖f v g‖ₑ ^ 2 ∂μ < ⊤)
    (hρ : ∀ h v g, f (ρ h v) g = f v (g * ι h)) : IsUnitarisable ρ := by
  obtain ⟨μ, F, hμ, hF, -⟩ := h2 0
  have hm : ∀ v, MemLp (f v) 2 (μ.restrict F) := fun v => by
    obtain ⟨μ', F', hμ', hF', h⟩ := h2 v
    have h3 := lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h
    refine ⟨(hc v).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using h3
  have hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F) := fun v w =>
    (hm v).integrable_mul (hm w).star
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ)
    (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_,
    fun h v w => ?_⟩
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [add_mul]
  · simp [mul_assoc, integral_const_mul]
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [mul_add]
  · simp [mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F) := by
      simpa [Complex.mul_conj] using (hi v v).re
    refine (integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)
    have ho : IsOpen (Function.support fun g => Complex.normSq (f v g)) :=
      (Complex.continuous_normSq.comp (hc v)).isOpen_support
    rw [Measure.restrict_apply ho.measurableSet] at h0
    have h4 := hF.measure_zero_of_invariant _ (fun γ => by
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
      change Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _
      rw [hl v _ (γ⁻¹).2]) h0
    have h5 := Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)
    refine hf (funext fun g => ?_)
    rw [map_zero]
    exact Complex.normSq_eq_zero.1 (congrFun h5 g)
  · simp only [LinearMap.mk₂'ₛₗ_apply, hρ]
    exact integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g))
      (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)

end General

def transInv (A : Type) [CommRing A] (n : ℕ) : GL (Fin n) A ≃* GL (Fin n) A where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  invFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change ((g * h)⁻¹).valᵀ = (g⁻¹).valᵀ * (h⁻¹).valᵀ
    rw [← transpose_mul, _root_.mul_inv_rev, Units.val_mul])

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`.
-/
theorem continuous_transInv (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (transInv A n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) = (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)`. Simplify using `only [Matrix.one_apply, eq_comm]`.
-/
theorem cornerGL_transInv {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (s : R →ₙ+* S) (g : GL (Fin n) R) :
    cornerGL n s (transInv R n g) = transInv S n (cornerGL n s g) := by
  ext i j
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm]

/- English proof (translation)
Use `borelize (GL (Fin n) S)`. Use `GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g` and prove the remaining obligations. Take `rfl : g' = transInv _ n g` from `Units.ext e`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, h]`. Conclude with `GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _`.
-/
theorem modular_eq_one {k S : Type} [Field k] [Infinite k] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n : ℕ}
    [LocallyCompactSpace (GL (Fin n) S)] [SecondCountableTopology (GL (Fin n) S)] (ι : GL (Fin n) k →* GL (Fin n) S)
    (h : ∀ g, ι (transInv k n g) = transInv S n (ι g)) (g : GL (Fin n) k) : Measure.modularCharacter (ι g) = 1 := by
  borelize (GL (Fin n) S)
  refine GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g
  obtain rfl : g' = transInv _ n g := Units.ext e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))`. Use `haveI : Countable (GL (Fin N) E) := Units.val_injective.countable`. Set `f : FreeGroup (Option (GL (Fin N) E)) →* GA E N` to `FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)`. Establish `h : latticeGL E N ≤ f.range` using `sup_le (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩) (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)`.

Use `haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable`. Conclude with `((Set.countable_range f).mono h).to_subtype`.
-/
theorem countable_latticeGL : Countable (latticeGL E N) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))
  haveI : Countable (GL (Fin N) E) := Units.val_injective.countable
  let f : FreeGroup (Option (GL (Fin N) E)) →* GA E N :=
    FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)
  have h : latticeGL E N ≤ f.range := sup_le
    (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩)
    (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)
  haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable
  exact ((Set.countable_range f).mono h).to_subtype

/- English proof (translation)
Set `S : Subgroup (GA E N)` to `{ carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g} one_mem' := fun g => by rw [one_mul] mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy] inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }`. Establish `: latticeGL E N ≤ S` using `sup_le (by rintro _ ⟨γ, rfl⟩; exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))`. Conclude with `this`.
-/
theorem left_latticeGL {φ : Sm E N} (h : IsAutForm φ) (h' : IsSqInt φ.1) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))
  exact this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩`. Use `letI : MeasurableSpace (GA E N) := borel _`. Use `haveI : BorelSpace (GA E N) := ⟨rfl⟩`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Use `haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) := inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))`. Use `haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) := inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI := countable_latticeGL (E := E) (N := N)`. Use `haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective`. Establish `hinj : Function.Injective f`.

Break down `((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hρ, hv, map_zero]) with h | h`. Conclude with `LinearMap.ker_eq_bot.1 h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) h0`.

Use `isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_) ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj) (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level) (fun v => left_l …` and prove the remaining obligations. Conclude with `modular_eq_one ((finGL E N).comp (locGL E N w)) (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g`.
-/
theorem isUnitarisable_of_isLocCompGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N),
    IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  intro E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  have hinj : Function.Injective f := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  refine isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level)
    (fun v => left_latticeGL (hV.aut _ (hf v)) (hV.sqInt _ (hf v))) (fun v => (hV.sqInt _ (hf v)).2)
    fun g v x => congrFun (congrArg Subtype.val (hρ g v)) x
  exact modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g

end GlobalTheory.DiscreteUnit
