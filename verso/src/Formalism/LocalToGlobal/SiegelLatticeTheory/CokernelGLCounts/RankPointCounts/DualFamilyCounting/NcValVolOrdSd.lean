import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.SdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
  PI.UnitaryGroupMassFormula.LocJacTyp.Sd.finDim

/- English proof (translation)
Introduce `F E _ _ _ _ _ v ι _ hE μ _ x hx`. Set `z : ι → Fv F v ⊗[F] E` to `fun i => LocVol.sc v (x i)`. Set `f` to `PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v z`. Establish `hLM` using `PI.NglqJacSplitW.linModulusV_of (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)`. Establish `hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2`.

Rewrite using `[Module.finrank_baseChange]`. Conclude with `hE`. Establish `hdet : LinearMap.det f = ∏ i, x i ^ 2`. Rewrite using `[PI.UnitaryGroupMassFormula.LocJacTyp.BM.det_mulL]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) (x i)) = _`. Rewrite using `[Algebra.norm_algebraMap, hrank]`. Establish `hdet0 : LinearMap.det f ≠ 0`. Rewrite using `[hdet]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx i)`.

Use `set S := Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | LocVol.sc v (x i) * c ∈ LocVol.OEv v} with hSdef`. Establish `hpre : S = f ⁻¹' (Set.univ.pi fun _ : ι => LocVol.OEv v)`. Use extensionality with `y`. Simplify using `[S, f, z, PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]`. Establish `hcont : Continuous f` using `IsModuleTopology.continuous_of_linearMap f`.

Establish `hS : MeasurableSet S`. Rewrite using `[hpre]`. Use `(IsOpen.preimage hcont ?_).measurableSet` and prove the remaining obligations. Conclude with `isOpen_set_pi Set.finite_univ fun i _ => PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v`. Establish `himg : f '' S = Set.univ.pi fun _ : ι => LocVol.OEv v`.

Rewrite using `[hpre, Set.image_preimage_eq]`. Introduce `y`. Use `⟨fun i => ((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]`.

Express the relevant statement in the definitionally equal form `(x i ⊗ₜ[F] (1 : E)) * (((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i) = y i`. Rewrite using `[← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hx i), one_mul, ← Algebra.TensorProduct.one_def, one_mul]`. Set `b` to `Module.finBasis (Fv F v) (ι → Fv F v ⊗[F] E)`. Set `e0` to `b.equivFun`. Set `e : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E)) → Fv F v)` to `{ e0 with continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }`.

Establish `h` using `hLM (Fv F v) (ι → Fv F v ⊗[F] E) (Fin _) ⟨e⟩ f hdet0 μ inferInstance S hS`. Establish `hne : (∏ i, x i ^ 2) ≠ 0` using `hdet ▸ hdet0`. Rewrite `h` using `[himg, hdet, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hne, PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod]`. Establish `hpos : ∀ i, 0 < PI.LocJacTyp.absV v (x i)` using `fun i => PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v (hx i)`. Establish `hP : 0 < ∏ i, PI.LocJacTyp.absV v (x i ^ 2)` using `Finset.prod_pos fun i _ => by rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]; exact pow_pos (hpos i) 2`.

Establish `hR` using `congrArg ENNReal.toReal h`. Rewrite `hR` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal hP.le]`. Express the relevant statement in the definitionally equal form `(μ S).toReal = (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal * ∏ i, (PI.LocJacTyp.absV v (x i) ^ 2)⁻¹`. Express the relevant statement in the definitionally equal form `(μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _ at hR`. Rewrite using `[hR, Finset.prod_inv_distrib]`.

Rewrite `hP`, the goal using `[PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem boxScaleL_holds : BoxScaleL := by
  intro F E _ _ _ _ _ v ι _ hE μ _ x hx
  classical
  let z : ι → Fv F v ⊗[F] E := fun i => LocVol.sc v (x i)
  let f := PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v z
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hdet : LinearMap.det f = ∏ i, x i ^ 2 := by
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.det_mulL]
    refine Finset.prod_congr rfl fun i _ => ?_
    change Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) (x i)) = _
    rw [Algebra.norm_algebraMap, hrank]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx i)
  set S := Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | LocVol.sc v (x i) * c ∈ LocVol.OEv v} with hSdef
  have hpre : S = f ⁻¹' (Set.univ.pi fun _ : ι => LocVol.OEv v) := by
    ext y
    simp [S, f, z, PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
  have hcont : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hS : MeasurableSet S := by
    rw [hpre]
    refine (IsOpen.preimage hcont ?_).measurableSet
    exact isOpen_set_pi Set.finite_univ fun i _ => PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have himg : f '' S = Set.univ.pi fun _ : ι => LocVol.OEv v := by
    rw [hpre, Set.image_preimage_eq]
    intro y
    refine ⟨fun i => ((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i, ?_⟩
    funext i
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
    change (x i ⊗ₜ[F] (1 : E)) * (((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i) = y i
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hx i), one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  let b := Module.finBasis (Fv F v) (ι → Fv F v ⊗[F] E)
  let e0 := b.equivFun
  let e : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have h := hLM (Fv F v) (ι → Fv F v ⊗[F] E) (Fin _) ⟨e⟩ f hdet0 μ inferInstance S hS
  have hne : (∏ i, x i ^ 2) ≠ 0 := hdet ▸ hdet0
  rw [himg, hdet, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hne, PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod] at h
  have hpos : ∀ i, 0 < PI.LocJacTyp.absV v (x i) := fun i => PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v (hx i)
  have hP : 0 < ∏ i, PI.LocJacTyp.absV v (x i ^ 2) :=
    Finset.prod_pos fun i _ => by rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]; exact pow_pos (hpos i) 2
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP.le] at hR
  change (μ S).toReal = (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ∏ i, (PI.LocJacTyp.absV v (x i) ^ 2)⁻¹
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _ at hR
  rw [hR, Finset.prod_inv_distrib]
  simp_rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow] at hP ⊢
  field_simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ v d _ hE hd hann ι _`. Establish `hone : (1 : Fv F v ⊗[F] E) ∈ PI.LocJacTyp.OEv v`. Simplify using `using PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1`. Establish `hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2`. Rewrite using `[Module.finrank_baseChange]`.

Conclude with `hE`. Establish `hinv : LocVol.sc v d * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1`. Express the relevant statement in the definitionally equal form `(d ⊗ₜ[F] (1 : E)) * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hd, one_mul, ← Algebra.TensorProduct.one_def]`. Establish `hker : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ`.

Use `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ (2 * d⁻¹) (mul_ne_zero two_ne_zero (inv_ne_zero hd)) ?_` and prove the remaining obligations. Introduce `c hc`. Establish `h1` using `(hann (d⁻¹ ⊗ₜ[F] (1 : E))).mpr (by rw [hinv]; exact hone)`. Establish `h2` using `h1 (c • (1 : Fv F v ⊗[F] E)) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.oev_smul v hc hone)`. Establish `htr : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E))) = c * (2 * d⁻¹)`.

Establish `: c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E)) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (c * d⁻¹)`. Rewrite using `[Algebra.smul_def, mul_one, map_mul]`. Both sides reduce to the same expression. Rewrite using `[this, Algebra.trace_algebraMap, hrank]`. Simplify using `only [nsmul_eq_mul, Nat.cast_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← htr]`. Conclude with `h2`. Establish `hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Take `⟨t0, ht0⟩` from `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v`. Establish `h1` using `(hann ((d⁻¹ ⊗ₜ[F] (1 : E)) * t0)).mp (fun x _ => hall _)`. Rewrite `h1` using `[← mul_assoc, hinv, one_mul]`. Conclude with `ht0 h1`.

Take `hex` from `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hker hnt ι`. Establish `hμ : LocVol.sdE ψ v ι = hex.choose`. Express the relevant statement in the definitionally equal form `PI.LocJacTyp.sdE ψ v ι = _`. Rewrite using `[PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq, dif_pos hex]`. Establish `hsd` using `hex.choose_spec`.

Rewrite using `[hμ]`. Use `haveI : hex.choose.IsAddHaarMeasure := hsd.1`. Use `⟨hsd.1, inferInstance, ?_⟩` and prove the remaining obligations. Use `set μ := hex.choose`. Establish `hDopen` using `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_dbox (E := E) v ψ hker ι`.

Establish `hDcpt` using `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_dbox (E := E) v ψ hker hnt ι`. Establish `htest` using `PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test v ψ ι μ hsd hDopen.measurableSet hDcpt.measure_lt_top`. Establish `hD : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox v ψ ι = Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | LocVol.sc v d * c ∈ LocVol.OEv v}`. Use extensionality with `y`. Simplify using `only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, Set.mem_pi, Set.mem_univ, true_implies]`.

Conclude with `forall_congr' fun i => hann (y i)`. Establish `hbs` using `boxScaleL_holds v ι hE μ (fun _ => d) (fun _ => hd)`. Rewrite `hbs` using `[← hD]`. Simplify using `only [Measure.real] at htest`. Rewrite `htest` using `[hbs]`.

Express the relevant statement in the definitionally equal form `(μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _`. Express the relevant statement in the definitionally equal form `(μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal * ((μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal * ∏ _i : ι, (PI.LocJacTyp.absV v d ^ 2)⁻¹) = 1 at htest`. Use `set a := (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal`. Establish `hpos : 0 < PI.LocJacTyp.absV v d` using `PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hd`. Rewrite `htest` using `[Finset.prod_const, Finset.card_univ]`.

Establish `ha : 0 ≤ a` using `ENNReal.toReal_nonneg`. Establish `hsq : a ^ 2 = (PI.LocJacTyp.absV v d ^ Fintype.card ι) ^ 2`. Establish `hq : 0 < ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι` using `by positivity`. Establish `: a ^ 2 * ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι = 1`. Rewrite using `[← htest]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[inv_pow, ← pow_mul]`. Clear denominators, using `at this` for the nonvanishing conditions. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(pow_left_inj₀ ha (by positivity) two_ne_zero).mp hsq`.
-/
theorem sdFromAnn_holds : SdFromAnn := by
  intro F E _ _ _ _ _ ψ v d _ hE hd hann ι _
  classical
  have hone : (1 : Fv F v ⊗[F] E) ∈ PI.LocJacTyp.OEv v := by
    simpa using PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hinv : LocVol.sc v d * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
    change (d ⊗ₜ[F] (1 : E)) * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hd, one_mul,
      ← Algebra.TensorProduct.one_def]
  have hker : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ (2 * d⁻¹) (mul_ne_zero two_ne_zero (inv_ne_zero hd)) ?_
    intro c hc
    have h1 := (hann (d⁻¹ ⊗ₜ[F] (1 : E))).mpr (by rw [hinv]; exact hone)
    have h2 := h1 (c • (1 : Fv F v ⊗[F] E)) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.oev_smul v hc hone)
    have htr : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E)))
        = c * (2 * d⁻¹) := by
      have : c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E))
          = algebraMap (Fv F v) (Fv F v ⊗[F] E) (c * d⁻¹) := by
        rw [Algebra.smul_def, mul_one, map_mul]; rfl
      rw [this, Algebra.trace_algebraMap, hrank]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [← htr]; exact h2
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    by_contra hall
    push_neg at hall
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have h1 := (hann ((d⁻¹ ⊗ₜ[F] (1 : E)) * t0)).mp (fun x _ => hall _)
    rw [← mul_assoc, hinv, one_mul] at h1
    exact ht0 h1
  obtain hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hker hnt ι
  have hμ : LocVol.sdE ψ v ι = hex.choose := by
    change PI.LocJacTyp.sdE ψ v ι = _
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq, dif_pos hex]
  have hsd := hex.choose_spec
  rw [hμ]
  haveI : hex.choose.IsAddHaarMeasure := hsd.1
  refine ⟨hsd.1, inferInstance, ?_⟩
  set μ := hex.choose
  have hDopen := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_dbox (E := E) v ψ hker ι
  have hDcpt := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_dbox (E := E) v ψ hker hnt ι
  have htest := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test v ψ ι μ hsd hDopen.measurableSet hDcpt.measure_lt_top
  have hD : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox v ψ ι
      = Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | LocVol.sc v d * c ∈ LocVol.OEv v} := by
    ext y
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => hann (y i)
  have hbs := boxScaleL_holds v ι hE μ (fun _ => d) (fun _ => hd)
  rw [← hD] at hbs
  simp only [Measure.real] at htest
  rw [hbs] at htest
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ((μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
      ∏ _i : ι, (PI.LocJacTyp.absV v d ^ 2)⁻¹) = 1 at htest
  set a := (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal
  have hpos : 0 < PI.LocJacTyp.absV v d := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hd
  rw [Finset.prod_const, Finset.card_univ] at htest
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hsq : a ^ 2 = (PI.LocJacTyp.absV v d ^ Fintype.card ι) ^ 2 := by
    have hq : 0 < ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι := by positivity
    have : a ^ 2 * ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι = 1 := by
      rw [← htest]; ring
    rw [inv_pow, ← pow_mul] at this
    field_simp at this
    rw [this]; ring
  exact (pow_left_inj₀ ha (by positivity) two_ne_zero).mp hsq

end Formalism.L2.SG.Pf.NcVal.SdW
