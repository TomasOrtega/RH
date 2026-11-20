import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LeviGLInvVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LeviParabolicGL
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}
end PositivityTheory.ThKW.LeviParabolicGL
set_option maxHeartbeats 800000 in
open PositivityTheory.ThKW.LeviParabolicGL in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n JT hT`. Establish `hc : IsCMExt F E σ` using `hB.cm`. Establish `hcc` using `GlobalTheory.SplitLagrF.cAF_invol hc`. Establish `hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x` using `fun x => GlobalTheory.SplitDetCharF.sig_invol hc x`. Use `set rE : E := (2 : E)⁻¹ with hrE`.

Establish `hrE2 : 2 * rE = 1` using `mul_inv_cancel₀ two_ne_zero`. Establish `hr : 2 * (inclR (F` using `F) (AF F)) rE = 1 := by`. Use `congrArg (inclR (F := F) (AF F)) hrE2` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis. Establish `hJ : ((JR (F` using `F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by`.

Use extensionality with `i j`. Use `show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j`. Rewrite using `[hT.1]`. Establish `hJE : (JT.map (σ : E →+* E))ᵀ = JT`. Use extensionality with `i j`.

Conclude with `hT.1 i j`. Establish `hu : IsUnit (JR (F` using `F) (AF F) JT).det := by`. Use `((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `huE : IsUnit JT.det` using `Ne.isUnit hT.2`.

Establish `eJ : JR (F` using `F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) = (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`.

Apply the tactic sequence `simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]`. Establish `eJE : GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT = (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm` using `rfl`. Set `mG` to `leviGL (cAF σ) hr hu`. Establish `hmem : ∀ t, mG t ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)`. Introduce `t`.

Establish `h` using `leviGL_mem (cAF σ) hcc hr hJ hu t`. Rewrite `h` using `[← eJ]`. Conclude with `h`. Set `m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)` to `mG.codRestrict _ hmem`. Set `m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)` to `{ toFun := fun t => m₀ t map_one' := m₀.map_one map_mul' := m₀.map_mul }`.

Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Establish `hcont_c : Continuous (cAF (F` using `F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF`. Establish `hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g → Continuous fun t => (L (cAF σ) (inclR (F` using `F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by`. Introduce `f g hf hg`. Use `Continuous.matrix_submatrix ?_ _ _` and prove the remaining obligations.

Simplify using `only [L, sM]`. Use `((continuous_const.matrix_mul ?_).matrix_mul continuous_const)` and prove the remaining obligations. Use `Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const`. Establish `hmG : Continuous mG`.

Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Conclude with `hL _ _ Units.continuous_val Units.continuous_coe_inv`. Use `show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Conclude with `hL _ _ Units.continuous_coe_inv Units.continuous_val`.

Establish `hm : Continuous m`. Establish `: Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT))` using `hmG.subtype_mk _`. Conclude with `this`. Use `⟨m, hm, ?_, ?_⟩` and prove the remaining obligations. Introduce `t`.

Conclude with `leviGL_col (cAF σ) hr hu t`. Introduce `a`. Set `a' : GL (Fin n) (AF F ⊗[F] E)` to `Matrix.GeneralLinearGroup.map (incAF F E) a`. Use `show ((m₀ a' : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈ HFin (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)`. Use `⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a`. Rewrite `h` using `[← eJE]`. Conclude with `h`. Conclude with `leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a`.
-/
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
    ∃ m : GL (Fin nT) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), Continuous m ∧
      (∀ t, mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (m t) * PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT =
        PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT * t.1) ∧
      ∀ a : GL (Fin nT) E, m (Matrix.GeneralLinearGroup.map (incAF F E) a) ∈
        GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
  intro F E _ _ _ _ _ σ B hB n JT hT
  classical
  have hc : IsCMExt F E σ := hB.cm
  have hcc := GlobalTheory.SplitLagrF.cAF_invol hc
  have hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SplitDetCharF.sig_invol hc x
  set rE : E := (2 : E)⁻¹ with hrE
  have hrE2 : 2 * rE = 1 := mul_inv_cancel₀ two_ne_zero
  have hr : 2 * (inclR (F := F) (AF F)) rE = 1 := by
    have := congrArg (inclR (F := F) (AF F)) hrE2
    rwa [map_mul, map_ofNat, map_one] at this
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hJE : (JT.map (σ : E →+* E))ᵀ = JT := by
    ext i j
    exact hT.1 i j
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have huE : IsUnit JT.det := Ne.isUnit hT.2
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  have eJE : GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT =
      (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  let mG := leviGL (cAF σ) hr hu
  have hmem : ∀ t, mG t ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    intro t
    have h := leviGL_mem (cAF σ) hcc hr hJ hu t
    rw [← eJ] at h
    exact h
  let m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := mG.codRestrict _ hmem
  let m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) :=
    { toFun := fun t => m₀ t
      map_one' := m₀.map_one
      map_mul' := m₀.map_mul }
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hcont_c : Continuous (cAF (F := F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF
  have hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g →
      Continuous fun t => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro f g hf hg
    refine Continuous.matrix_submatrix ?_ _ _
    simp only [L, sM]
    refine ((continuous_const.matrix_mul ?_).matrix_mul continuous_const)
    refine Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_
    exact (continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const
  have hmG : Continuous mG := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_val Units.continuous_coe_inv
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_coe_inv Units.continuous_val
  have hm : Continuous m := by
    have : Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) :=
      hmG.subtype_mk _
    exact this
  refine ⟨m, hm, ?_, ?_⟩
  · intro t
    exact leviGL_col (cAF σ) hr hu t
  · intro a
    let a' : GL (Fin n) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (incAF F E) a
    show ((m₀ a' : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈
      HFin (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    refine ⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩
    · have h := leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a
      rw [← eJE] at h
      exact h
    · exact leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a
end
end
