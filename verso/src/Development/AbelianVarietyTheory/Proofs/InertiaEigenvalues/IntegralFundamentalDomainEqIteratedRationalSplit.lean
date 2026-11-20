import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CoordUnfold

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη`. Take `⟨i1, i2, i3, i4, i5, -⟩` from `GlobalTheory.MixModel.lattice_Mx D s m`. Take `⟨j1, j2, j3, j4, j5, -⟩` from `GlobalTheory.MixModel.lattice_Mx D t m`. Take `⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩` from `GlobalTheory.MixModel.lattice_Mx D r m`. Use `haveI : BorelSpace (Mx D s m) := ⟨rfl⟩`.

Use `haveI : BorelSpace (Mx D t m) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D r m) := ⟨rfl⟩`. Use `haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Use `haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Use `haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Use `haveI := hμ.1`. Use `haveI := hν.1`. Use `haveI := hη.1`. Use `haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩`. Use `haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩`.

Use `set rJ : Mx D r s := J.map (incA D) with hrJ`. Use `set rK : Mx D r t := K.map (incA D) with hrK`. Use `set rL : Mx D s r := L.map (incA D) with hrL`. Use `set rM : Mx D t r := M.map (incA D) with hrM`. Establish `hLJ' : rL * rJ = 1` using `by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one`.

Establish `hLK' : rL * rK = 0` using `by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero`. Establish `hMJ' : rM * rJ = 0` using `by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero`. Establish `hMK' : rM * rK = 1` using `by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one`. Establish `hJLKM' : rJ * rL + rK * rM = 1`. Rewrite using `[hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, hJLKM]`.

Conclude with `GlobalTheory.MixModel.rat_one`. Conclude with `fun a b => map_add (incA D) a b`. Set `Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m` to `{ toFun := fun p => rJ * p.2 + rK * p.1 invFun := fun u => (rM * u, rL * u) left_inv := by`. Introduce and unpack `⟨v, y⟩`. Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]`.

Use `right_inv := by`. Introduce `u`. Use `show rJ * (rL * u) + rK * (rM * u) = u`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]`. Use the proof step `map_add' := by`.

Introduce and unpack `⟨v, y⟩ ⟨v', y'⟩`. Simplify using `only [Prod.mk_add_mk, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Use `continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))`. Use `continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }`.

Establish `hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v` using `fun _ _ => rfl`. Set `Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m` to `Ec.toHomeomorph.toMeasurableEquiv`. Establish `hMe : ∀ p, Me p = Ec p` using `fun _ => rfl`. Use `set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam`. Use `haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`.

Use `set mm : Measure (Mx D r m) := lam.map Me with hm`. Use `haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam`. Establish `hμm` using `Measure.isAddLeftInvariant_eq_smul μ mm`. Use `set c := Measure.addHaarScalarFactor μ mm with hcdef`. Establish `hc : 0 < c` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm`.

Use `set Γ : AddSubgroup (Mx D t m × Mx D s m) := (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ`. Establish `hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m`. Introduce and unpack `⟨v, y⟩`. Rewrite using `[hEapp]`. Simplify using `only [Γ, AddSubgroup.mem_prod]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, hy⟩`. Conclude with `add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy) (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)`. Introduce `h`. Establish `h1 : rM * (rJ * y + rK * v) = v`.

Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]`. Establish `h2 : rL * (rJ * y + rK * v) = y`. Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`.

Conclude with `GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h`. Rewrite using `[← h2]`. Conclude with `GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h`. Establish `hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam` using `isAddFundamentalDomain_prod hη.2.1 hν.2.1`. Establish `hac : lam.map Me ≪ μ`.

Introduce `A hA`. Rewrite `hA` using `[hμm, Measure.smul_apply]`. Conclude with `(smul_eq_zero.1 hA).resolve_left hc.ne'`. Establish `hqmp : Measure.QuasiMeasurePreserving Me lam μ` using `⟨Me.measurable, hac⟩`. Set `eΓ : GlobalTheory.MixModel.ratMx D r m → Γ` to `fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩`.

Establish `heΓ : Function.Bijective eΓ`. Use `⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩` and prove the remaining obligations. Use `congrArg (fun q : Γ => Ec q.1) h` as an intermediate fact. Simplify `this` using `[eΓ]`. Simplify using `[eΓ]`.

Use `haveI : Countable Γ := heΓ.2.countable`. Establish `hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam` using `hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p`. Rewrite using `[hMe, hMe, map_add, Ec.apply_symm_apply])`. Use `⟨(c : ℝ), fun T hT hper => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hKK.exists_bound_of_continuousOn hT.continuousOn`.

Establish `hbd : ∀ x, ‖T x‖ ≤ C` using `fun x => by`. Take `⟨γ, hγ, hx⟩` from `hKKc x`. Rewrite using `[← hper γ hγ x]`. Conclude with `hC _ hx`. Establish `hTE : Continuous fun p => T (Me p)` using `hT.comp Ec.continuous`.

Establish `e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm`. Rewrite using `[hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]`. Establish `e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam` using `setIntegral_map_equiv Me T 𝓕`. Establish `e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam` using `hFDE.setIntegral_eq hFDP (fun g p => by show T (Me ((g : _) + p)) = T (Me p)`. Rewrite using `[hMe, hMe, map_add]`.

Conclude with `hper _ ((hmemΓ _).1 g.2) _)`. Establish `e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨)`. Rewrite using `[Measure.prod_restrict]`. Rewrite using `[e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)), Complex.real_smul]`. Both sides reduce to the same expression.
-/
theorem integral_fundamentalDomain_eq_iterated_split : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  intro D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D s m
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D t m
  obtain ⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩ := GlobalTheory.MixModel.lattice_Mx D r m
  haveI : BorelSpace (Mx D s m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r m) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  haveI := hν.1
  haveI := hη.1
  haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩
  set rJ : Mx D r s := J.map (incA D) with hrJ
  set rK : Mx D r t := K.map (incA D) with hrK
  set rL : Mx D s r := L.map (incA D) with hrL
  set rM : Mx D t r := M.map (incA D) with hrM
  have hLJ' : rL * rJ = 1 := by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one
  have hLK' : rL * rK = 0 := by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero
  have hMJ' : rM * rJ = 0 := by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero
  have hMK' : rM * rK = 1 := by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one
  have hJLKM' : rJ * rL + rK * rM = 1 := by
    rw [hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, hJLKM]
    · exact GlobalTheory.MixModel.rat_one
    · exact fun a b => map_add (incA D) a b
  let Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m :=
    { toFun := fun p => rJ * p.2 + rK * p.1
      invFun := fun u => (rM * u, rL * u)
      left_inv := by
        rintro ⟨v, y⟩
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      right_inv := by
        intro u
        show rJ * (rL * u) + rK * (rM * u) = u
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]
      map_add' := by
        rintro ⟨v, y⟩ ⟨v', y'⟩
        simp only [Prod.mk_add_mk, Matrix.mul_add]
        abel
      continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))
      continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }
  have hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v := fun _ _ => rfl
  let Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m := Ec.toHomeomorph.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl
  set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set mm : Measure (Mx D r m) := lam.map Me with hm
  haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hμm := Measure.isAddLeftInvariant_eq_smul μ mm
  set c := Measure.addHaarScalarFactor μ mm with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm
  set Γ : AddSubgroup (Mx D t m × Mx D s m) :=
    (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m := by
    rintro ⟨v, y⟩
    rw [hEapp]
    simp only [Γ, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨hv, hy⟩
      exact add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy)
        (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)
    · intro h
      have h1 : rM * (rJ * y + rK * v) = v := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]
      have h2 : rL * (rJ * y + rK * v) = y := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h
      · rw [← h2]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h
  have hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam := isAddFundamentalDomain_prod hη.2.1 hν.2.1
  have hac : lam.map Me ≪ μ := by
    intro A hA
    rw [hμm, Measure.smul_apply] at hA
    exact (smul_eq_zero.1 hA).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam μ := ⟨Me.measurable, hac⟩
  let eΓ : GlobalTheory.MixModel.ratMx D r m → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p
      rw [hMe, hMe, map_add, Ec.apply_symm_apply])
  refine ⟨(c : ℝ), fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hKK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm := by
    rw [hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨) := by
    rw [Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  rfl

end GlobalTheory.CoordUnfold

end
