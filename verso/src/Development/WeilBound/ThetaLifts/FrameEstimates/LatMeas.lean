import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def e0 : AF F := ((0 : Ainf F), (1 : Af F))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `h` to reduce the goal to its premises. Use `show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0`. Conclude with `map_zero _`.

Introduce `h u hu`. Establish `hu1 : u.1 = 0`. Establish `hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0` using `hu`. Conclude with `(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)`. Establish `hue : u = u * e0 F`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show u.1 = u.1 * (0 : Ainf F)`. Rewrite using `[hu1, zero_mul]`. Use `show u.2 = u.2 * (1 : Af F)`. Rewrite using `[mul_one]`.

Rewrite using `[hue, mul_smul, h, smul_zero]`.
-/
theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
/- English proof (translation)
Use `haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe`. Use `haveI : T2Space (NumberField.InfiniteAdeleRing F) := show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance`. Use `show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)`. Use `infer_instance`.
-/
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  haveI : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
/- English proof (translation)
Use `haveI := t2Space_adeleRing_of_numberField F`. Set `b` to `Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)`. Conclude with `T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)`.
-/
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
/- English proof (translation)
Conclude with `IsModuleTopology.isTopologicalRing (AF F) (AE F E)`.
-/
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
/- English proof (translation)
Set `φ : AF F →+* ℂ` to `(NumberField.InfinitePlace.Completion.extensionEmbedding w).comp (GlobalTheory.AdelicU.evInf F w).toRingHom`. Establish `hφ : Continuous φ` using `(NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`. Use `letI : Module (AF F) ℂ := Module.compHom ℂ φ`. Use `haveI : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩`. Establish `hpt : ∀ (b : AF F) (e : E), piInf τ (b ⊗ₜ[F] e) = φ b * (τ.1 e)` using `fun b e => rfl`.

Set `Lm : AE F E →ₗ[AF F] ℂ` to `{ toFun := piInf τ map_add' := map_add _ map_smul' := by`. Introduce `a x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b e`.

Rewrite using `[TensorProduct.smul_tmul', hpt, hpt, smul_eq_mul, map_mul]`. Use `show φ a * φ b * τ.1 e = φ a * (φ b * τ.1 e)`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`. Rewrite using `[smul_add, map_add, hx, hy, map_add, smul_add] }`.

Conclude with `IsModuleTopology.continuous_of_linearMap Lm`.
-/
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  let φ : AF F →+* ℂ := (NumberField.InfinitePlace.Completion.extensionEmbedding w).comp
    (GlobalTheory.AdelicU.evInf F w).toRingHom
  have hφ : Continuous φ :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  letI : Module (AF F) ℂ := Module.compHom ℂ φ
  haveI : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  have hpt : ∀ (b : AF F) (e : E), piInf τ (b ⊗ₜ[F] e) = φ b * (τ.1 e) := fun b e => rfl
  let Lm : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b e =>
          rw [TensorProduct.smul_tmul', hpt, hpt, smul_eq_mul, map_mul]
          show φ a * φ b * τ.1 e = φ a * (φ b * τ.1 e)
          ring
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add, smul_add] }
  exact IsModuleTopology.continuous_of_linearMap Lm

variable {n d : ℕ}

/- English proof (translation)
Conclude with `continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm`.
-/
theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

/- English proof (translation)
Use `haveI := t2Space_cm_host_adeles F E`. Establish `hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} = (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C)`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, hzc⟩`. Conclude with `⟨c, hc, hzc.symm⟩`. Introduce and unpack `⟨c, hc, hzc⟩`. Conclude with `⟨c, hc, hzc.symm⟩`. Rewrite using `[hset]`.

Conclude with `(hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))`.
-/
theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  haveI := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

/- English proof (translation)
Establish `hcl` using `isClosed_supp (F := F) (E := E) (n := n) (d := d) hC`. Use `delta maj`. Use `Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const` and prove the remaining obligations. Conclude with `((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv`.
-/
theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
/- English proof (translation)
Conclude with `Units.continuous_coe_inv.comp continuous_subtype_val`.
-/
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtype_val

end LatticeQuotientMeasure

open LatticeQuotientMeasure in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h`. Use `haveI := ring_AE F E`. Use `haveI := t2Space_cm_host_adeles F E`. Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`. Use `haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance`.

Use `haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩`. Use `delta latSum`. Use `Measurable.ennreal_tsum fun x => ENNReal.measurable_ofReal.comp ?_` and prove the remaining obligations. Conclude with `measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)`.
-/
theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  haveI := ring_AE F E
  haveI := t2Space_cm_host_adeles F E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.ennreal_tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

/- English proof (translation)
Conclude with `fun _ => latMeas`.
-/
theorem latMeas_of : GrpTop → LatMeas := by
  exact fun _ => latMeas

end PositivityTheory.ThKEst

end
