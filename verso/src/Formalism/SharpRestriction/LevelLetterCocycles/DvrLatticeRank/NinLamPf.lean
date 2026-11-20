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
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
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
