import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : m = GroundTheory.Global.measurableSpace_adeleRing F` using `hB.measurable_eq.trans (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm`. Substitute `h1` using the available equality. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GroundTheory.Global.borelSpace_adeleRing F`. Use `haveI := GroundTheory.Global.instIsAddHaarMeasureAdeleRingRingOfIntegersAdeleMeasure F`.

Use `⟨GroundTheory.Global.adeleMeasure F, inferInstance, inferInstance, fun r => ?_⟩` and prove the remaining obligations. Conclude with `GroundTheory.Global.map_smul_adeleMeasure r`.
-/
theorem adeleHaarB {m : MeasurableSpace (AF F)} (hB : @BorelSpace (AF F) _ m) :
    ∃ μ : @Measure (AF F) m, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ ∀ r : GroundTheory.Global.IdeleGroup F,
      μ.map (fun y => (r : AF F) * y) =
        (((((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal : NNReal) : ENNReal) • μ := by
  have h1 : m = GroundTheory.Global.measurableSpace_adeleRing F :=
    hB.measurable_eq.trans (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  subst h1
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GroundTheory.Global.instIsAddHaarMeasureAdeleRingRingOfIntegersAdeleMeasure F
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, inferInstance, fun r => ?_⟩
  exact GroundTheory.Global.map_smul_adeleMeasure r

/- English proof (translation)
Use `haveI : SigmaFinite (μ.map f) := by`. Rewrite using `[hμ]`. Conclude with `(inferInstance : SigmaFinite (c • μ))`. Rewrite using `[Measure.pi_map_pi (fun _ => hf.aemeasurable)]`. Simplify using `only [hμ]`.

Use `haveI : SigmaFinite ((c : ENNReal) • μ) := (inferInstance : SigmaFinite (c • μ))`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`.
-/
theorem pi_map_const {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → X) (hf : Measurable f)
    (c : NNReal) (hμ : μ.map f = (c : ENNReal) • μ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Measure.pi fun _ : ι => μ).map (fun y i => f (y i)) = ((c : ENNReal) ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by
    rw [hμ]
    exact (inferInstance : SigmaFinite (c • μ))
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hμ]
  haveI : SigmaFinite ((c : ENNReal) • μ) := (inferInstance : SigmaFinite (c • μ))
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI hBA : BorelSpace (AF F) := ⟨rfl⟩`. Use `haveI hBE : BorelSpace (AE F E) := ⟨rfl⟩`. Take `⟨ν, hνH, hνS, hν⟩` from `adeleHaarB (F := F) hBA`. Set `ψ` to `(Algebra.TensorProduct.basis (AF F) bs).equivFun`.

Establish `hψ : Continuous ψ` using `IsModuleTopology.continuous_of_linearMap (ψ : AE F E →ₗ[AF F] (Fin n → AF F))`. Establish `hψs : Continuous ψ.symm` using `IsModuleTopology.continuous_of_linearMap (ψ.symm : (Fin n → AF F) →ₗ[AF F] AE F E)`. Set `e : ((Fin k → Fin n → AF F) × AF F) ≃+ ((Fin k → AE F E) × AF F)` to `AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv) (AddEquiv.refl _)`. Establish `he : Continuous e`. Express the relevant statement in the definitionally equal form `Continuous fun p : (Fin k → Fin n → AF F) × AF F => ((fun j => ψ.symm (p.1 j)), p.2)`.

Conclude with `(continuous_pi fun j => hψs.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd`. Establish `hes : Continuous e.symm`. Express the relevant statement in the definitionally equal form `Continuous fun p : (Fin k → AE F E) × AF F => ((fun j => ψ (p.1 j)), p.2)`. Conclude with `(continuous_pi fun j => hψ.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd`. Set `μW : Measure (Fin k → Fin n → AF F)` to `Measure.pi fun _ => Measure.pi fun _ => ν`.

Use `⟨(μW.prod ν).map e, e.isAddHaarMeasure_map _ he hes, fun r => ?_⟩` and prove the remaining obligations. Use `set a : AF F := (r : AF F) with ha`. Use `set b : AF F := ((r⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) with hb`. Establish `hab : b * a = 1` using `r.inv_mul`. Establish `hba : a * b = 1` using `r.mul_inv`.

Set `S : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F` to `fun c => (fun j => a • c.1 j, (a * a) • c.2)`. Set `S' : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F` to `fun c => (fun j => b • c.1 j, (b * b) • c.2)`. Establish `hS : Continuous S` using `(continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul a).prodMk (continuous_snd.const_smul (a * a))`. Establish `hS' : Continuous S'` using `(continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul b).prodMk (continuous_snd.const_smul (b * b))`. Set `sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F)` to `{ toFun := S invFun := S' left_inv := fun c => by`.

Use `Prod.ext (funext fun j => ?_) ?_` and prove the remaining obligations. Use `show b • a • c.1 j = c.1 j`. Rewrite using `[smul_smul, hab, one_smul]`. Use `show (b * b) • (a * a) • c.2 = c.2`. Rewrite using `[smul_smul, show b * b * (a * a) = (b * a) * (b * a) by ring, hab, one_mul, one_smul]`.

Use `right_inv := fun c => by`. Use `Prod.ext (funext fun j => ?_) ?_` and prove the remaining obligations. Use `show a • b • c.1 j = c.1 j`. Rewrite using `[smul_smul, hba, one_smul]`. Use `show (a * a) • (b * b) • c.2 = c.2`.

Rewrite using `[smul_smul, show a * a * (b * b) = (a * b) * (a * b) by ring, hba, one_mul, one_smul]`. Use `measurable_toFun := hS.measurable`. Use `measurable_invFun := hS'.measurable }`. Use `⟨sc, fun c => rfl, ?_⟩` and prove the remaining obligations. Set `T1 : (Fin k → Fin n → AF F) → (Fin k → Fin n → AF F)` to `fun w j i => a * w j i`.

Set `T2 : AF F → AF F` to `fun t => (a * a) * t`. Establish `hT1 : Continuous T1` using `continuous_pi fun j => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply j))`. Establish `hT2 : Continuous T2` using `continuous_const.mul continuous_id`. Establish `hcomm : (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) ∘ e = e ∘ Prod.map T1 T2`. Use function extensionality and compare the values at `p`.

Use `Prod.ext (funext fun j => ?_) rfl` and prove the remaining obligations. Use `show a • ψ.symm (p.1 j) = ψ.symm (fun i => a * p.1 j i)`. Rewrite using `[← map_smul]`. Both sides reduce to the same expression. Use `set c : NNReal := (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal with hc`.

Establish `h1 : ν.map (fun y => a * y) = (c : ENNReal) • ν` using `hν r`. Establish `hm1 : Measurable fun y : AF F => a * y` using `(continuous_const.mul continuous_id).measurable`. Establish `hin : (Measure.pi fun _ : Fin n => ν).map (fun y i => a * y i) = ((c ^ n : NNReal) : ENNReal) • Measure.pi fun _ : Fin n => ν`. Rewrite using `[pi_map_const ν (fun y => a * y) hm1 c h1 (Fin n), Fintype.card_fin, ENNReal.coe_pow]`. Establish `hW : μW.map T1 = ((c : ENNReal) ^ n) ^ k • μW`.

Establish `hm2 : Measurable fun y : Fin n → AF F => fun i => a * y i` using `(continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable`. Use `pi_map_const (Measure.pi fun _ : Fin n => ν) (fun y i => a * y i) hm2 (c ^ n) hin (Fin k)` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, ENNReal.coe_pow]`. Conclude with `this`. Establish `hA : ν.map T2 = (c : ENNReal) ^ 2 • ν`.

Establish `: T2 = (fun y => a * y) ∘ (fun y => a * y)`. Use function extensionality and compare the values at `t`. Simplify using `[T2, mul_assoc]`. Rewrite using `[this, ← Measure.map_map hm1 hm1, h1, Measure.map_smul, h1, smul_smul, sq]`. Rewrite using `[show ((μW.prod ν).map e).map sc = ((μW.prod ν).map e).map (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) from rfl, Measure.map_map sc.measurable he.measurable, hcomm, ← Measure.map_map he.measurable (hT1.measurable.prodMap hT2.measurable), ← Measure.map_prod_map μW ν h …`.

Use `congr 1`. Establish `hx : (0 : ℝ) ≤ ((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹` using `inv_nonneg.mpr (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule F r).2)`. Rewrite using `[ENNReal.ofReal_pow hx, ← pow_mul, ← pow_add]`. Both sides reduce to the same expression.
-/
theorem measN (n k : ℕ) (bs : Module.Basis (Fin n) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (n * k + 2)) • κ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI hBA : BorelSpace (AF F) := ⟨rfl⟩
  haveI hBE : BorelSpace (AE F E) := ⟨rfl⟩
  obtain ⟨ν, hνH, hνS, hν⟩ := adeleHaarB (F := F) hBA
  let ψ := (Algebra.TensorProduct.basis (AF F) bs).equivFun
  have hψ : Continuous ψ :=
    IsModuleTopology.continuous_of_linearMap (ψ : AE F E →ₗ[AF F] (Fin n → AF F))
  have hψs : Continuous ψ.symm :=
    IsModuleTopology.continuous_of_linearMap (ψ.symm : (Fin n → AF F) →ₗ[AF F] AE F E)
  let e : ((Fin k → Fin n → AF F) × AF F) ≃+ ((Fin k → AE F E) × AF F) :=
    AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv) (AddEquiv.refl _)
  have he : Continuous e := by
    change Continuous fun p : (Fin k → Fin n → AF F) × AF F => ((fun j => ψ.symm (p.1 j)), p.2)
    exact (continuous_pi fun j => hψs.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  have hes : Continuous e.symm := by
    change Continuous fun p : (Fin k → AE F E) × AF F => ((fun j => ψ (p.1 j)), p.2)
    exact (continuous_pi fun j => hψ.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  let μW : Measure (Fin k → Fin n → AF F) := Measure.pi fun _ => Measure.pi fun _ => ν
  refine ⟨(μW.prod ν).map e, e.isAddHaarMeasure_map _ he hes, fun r => ?_⟩
  set a : AF F := (r : AF F) with ha
  set b : AF F := ((r⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) with hb
  have hab : b * a = 1 := r.inv_mul
  have hba : a * b = 1 := r.mul_inv
  let S : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => a • c.1 j, (a * a) • c.2)
  let S' : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => b • c.1 j, (b * b) • c.2)
  have hS : Continuous S :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul a).prodMk
      (continuous_snd.const_smul (a * a))
  have hS' : Continuous S' :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul b).prodMk
      (continuous_snd.const_smul (b * b))
  let sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F) :=
    { toFun := S
      invFun := S'
      left_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show b • a • c.1 j = c.1 j
          rw [smul_smul, hab, one_smul]
        · show (b * b) • (a * a) • c.2 = c.2
          rw [smul_smul, show b * b * (a * a) = (b * a) * (b * a) by ring, hab, one_mul, one_smul]
      right_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show a • b • c.1 j = c.1 j
          rw [smul_smul, hba, one_smul]
        · show (a * a) • (b * b) • c.2 = c.2
          rw [smul_smul, show a * a * (b * b) = (a * b) * (a * b) by ring, hba, one_mul, one_smul]
      measurable_toFun := hS.measurable
      measurable_invFun := hS'.measurable }
  refine ⟨sc, fun c => rfl, ?_⟩
  let T1 : (Fin k → Fin n → AF F) → (Fin k → Fin n → AF F) := fun w j i => a * w j i
  let T2 : AF F → AF F := fun t => (a * a) * t
  have hT1 : Continuous T1 := continuous_pi fun j => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply j))
  have hT2 : Continuous T2 := continuous_const.mul continuous_id
  have hcomm : (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) ∘ e = e ∘ Prod.map T1 T2 := by
    funext p
    refine Prod.ext (funext fun j => ?_) rfl
    show a • ψ.symm (p.1 j) = ψ.symm (fun i => a * p.1 j i)
    rw [← map_smul]
    rfl
  set c : NNReal := (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal with hc
  have h1 : ν.map (fun y => a * y) = (c : ENNReal) • ν := hν r
  have hm1 : Measurable fun y : AF F => a * y := (continuous_const.mul continuous_id).measurable
  have hin : (Measure.pi fun _ : Fin n => ν).map (fun y i => a * y i) =
      ((c ^ n : NNReal) : ENNReal) • Measure.pi fun _ : Fin n => ν := by
    rw [pi_map_const ν (fun y => a * y) hm1 c h1 (Fin n), Fintype.card_fin, ENNReal.coe_pow]
  have hW : μW.map T1 = ((c : ENNReal) ^ n) ^ k • μW := by
    have hm2 : Measurable fun y : Fin n → AF F => fun i => a * y i :=
      (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
    have := pi_map_const (Measure.pi fun _ : Fin n => ν) (fun y i => a * y i) hm2 (c ^ n) hin (Fin k)
    rw [Fintype.card_fin, ENNReal.coe_pow] at this
    exact this
  have hA : ν.map T2 = (c : ENNReal) ^ 2 • ν := by
    have : T2 = (fun y => a * y) ∘ (fun y => a * y) := by
      funext t
      simp [T2, mul_assoc]
    rw [this, ← Measure.map_map hm1 hm1, h1, Measure.map_smul, h1, smul_smul, sq]
  rw [show ((μW.prod ν).map e).map sc = ((μW.prod ν).map e).map (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) from rfl,
    Measure.map_map sc.measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (hT1.measurable.prodMap hT2.measurable),
    ← Measure.map_prod_map μW ν hT1.measurable hT2.measurable, hW, hA,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  congr 1
  have hx : (0 : ℝ) ≤ ((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule F r).2)
  rw [ENNReal.ofReal_pow hx, ← pow_mul, ← pow_add]
  rfl

/- English proof (translation)
The claim follows from `measN 2 k bs`.
-/
theorem measEx' (k : ℕ) (bs : Module.Basis (Fin 2) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (2 * k + 2)) • κ :=
  measN 2 k bs

end PositivityTheory.SiegelWeilFormula.Act.CL

end
