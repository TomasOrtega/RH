import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section NinLamPfLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Introduce `c y hy`. Unfold `NcS at hy`. Rewrite `hy` using `[Submodule.mem_inf, Submodule.mem_inf]`. Take `⟨⟨hyN, hyD⟩, hyL⟩` from `hy`. Rewrite `hyN` using `[Submodule.restrictScalars_mem]`.

Unfold `LamPS`. Rewrite using `[Submodule.mem_inf, Submodule.mem_inf]`. Use `⟨⟨?_, hyD⟩, hyL⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, Submodule.mem_comap]`. Unfold `letS at hyL`.

Rewrite `hyL` using `[LinearMap.mem_ker]`. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hyL`. Establish `hNl : y ∈ W.Nl T c`. Unfold `LocWach.Nl`. Use `Submodule.mem_map.2 ⟨y, hyN, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, hyL]`. Establish `h5'` using `h5 c y hNl`. Establish `hQ : W.Q = W.q` using `by simp [LocWach.Q, hs1]`. Establish `hE : Eπ ^ h' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ h' * W.Q ^ h'`. Rewrite using `[hQ, hw, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]`.

Unfold `Formalism.MainNotions.DeltaInvariantLattices.smulA`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, hE, mul_smul]`. Conclude with `Submodule.smul_mem _ _ h5'`.
-/
theorem ninLamPf_local (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Eπ : LetA O n) (h' : ℕ)
    (w : (LetA O n)ˣ) (hs1 : W.s = 1) (hw : W.q = (w : LetA O n) * Eπ)
    (h5 : ∀ i, ∀ y ∈ W.Nl T i, W.Q ^ h' • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    NinLam W T Eπ h' := by
  intro c y hy
  unfold NcS at hy
  rw [Submodule.mem_inf, Submodule.mem_inf] at hy
  obtain ⟨⟨hyN, hyD⟩, hyL⟩ := hy
  rw [Submodule.restrictScalars_mem] at hyN
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine ⟨⟨?_, hyD⟩, hyL⟩
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap]
  unfold letS at hyL
  rw [LinearMap.mem_ker] at hyL
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hyL
  have hNl : y ∈ W.Nl T c := by
    unfold LocWach.Nl
    refine Submodule.mem_map.2 ⟨y, hyN, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hyL]
  have h5' := h5 c y hNl
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs1]
  have hE : Eπ ^ h' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ h' * W.Q ^ h' := by
    rw [hQ, hw, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
  rw [LinearMap.smul_apply, LinearMap.id_apply, hE, mul_smul]
  exact Submodule.smul_mem _ _ h5'

end NinLamPfLocal

/- English proof (translation)
Introduce `D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T h' hcrys hjumps`. Establish `hT1` using `hA.1 l K 1 LL hG`. Establish `hP5` using `hT1.2.2.2.2.1`. Take `⟨w, hw⟩` from `hp9.2.2.2.2.1`. Establish `hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hG) T (fun _ => h') (fun _ => h')`.

Introduce `τ i _`. Conclude with `hjumps τ`. Establish `h5` using `(hP5 T (fun _ => h') (fun _ => h') hcrys hJ).2.1`. Conclude with `ninLamPf_local _ T _ h' w ((HW l).W_s K 1 LL hG) hw h5`.
-/
theorem ninlam_pf : NinLamStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T h' hcrys hjumps
  have hT1 := hA.1 l K 1 LL hG
  have hP5 := hT1.2.2.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.2.2.1
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hG) T (fun _ => h') (fun _ => h') := by
    intro τ i _
    exact hjumps τ
  have h5 := (hP5 T (fun _ => h') (fun _ => h') hcrys hJ).2.1
  exact ninLamPf_local _ T _ h' w ((HW l).W_s K 1 LL hG) hw h5

end Formalism.MainNotions.N.Ln34

end
