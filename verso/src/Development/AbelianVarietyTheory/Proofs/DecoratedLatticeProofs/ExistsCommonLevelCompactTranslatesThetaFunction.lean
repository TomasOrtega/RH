import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Level

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mt' {D : D7} (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Unfold `actO`. Rewrite using `[mt_one', Matrix.one_mul, Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]`.
-/
theorem actO_mul_mt {D : D7} (S T : HSp D) (k : GA D S) (u : WO S T) :
    actO S T k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) = u := by
  unfold actO
  rw [mt_one', Matrix.one_mul, Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]

/- English proof (translation)
Introduce `D ψ S T χS χT om hW K hK f hf`. Take `⟨U₀, hU₀, hUf⟩` from `hf.level`. Set `U : AddSubgroup (WO S T)` to `{ carrier := {u | ∀ k ∈ K, (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀} add_mem' := fun {a b} ha hb k hk => by`. Use `U₀.add_mem (ha k hk) (hb k hk)` as an intermediate fact. Rewrite `this` using `[← Matrix.add_mul]`. Then use the resulting hypothesis.

Use the proof step `zero_mem' := fun k _ => by`. Rewrite using `[Matrix.zero_mul]`. Conclude with `U₀.zero_mem`. Use the proof step `neg_mem' := fun {a} ha k hk => by`. Use `U₀.neg_mem (ha k hk)` as an intermediate fact.

Rewrite using `[← Matrix.neg_mul] at this }` and apply the resulting hypothesis. Use `⟨U, U.isOpen_of_mem_nhds (g := 0) ?_, fun k hk u hu h0 => ?_⟩` and prove the remaining obligations. Use `hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u k => (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀) fun k _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun p : WO S T × GA D S => (HMul.hMul (p.1 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S p.2) : WO S T)` using `continuous_fst.matrix_mul ((continuous_mt' S).comp continuous_snd)`. Use `(hU₀.preimage hc).mem_nhds ?_` and prove the remaining obligations.

Use `show (HMul.hMul (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀`. Rewrite using `[Matrix.zero_mul]`. Conclude with `U₀.zero_mem`. Establish `h1` using `hUf _ (hu k hk) (by rw [Matrix.map_mul, h0]; simp)`. Establish `h2` using `hW.om_heis k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) f hf`.

Rewrite `h2` using `[h1, actO_mul_mt]`. Conclude with `h2.symm`.
-/
theorem exists_common_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  intro D ψ S T χS χT om hW K hK f hf
  obtain ⟨U₀, hU₀, hUf⟩ := hf.level
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ k ∈ K,
        (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀}
      add_mem' := fun {a b} ha hb k hk => by
        have := U₀.add_mem (ha k hk) (hb k hk)
        rwa [← Matrix.add_mul] at this
      zero_mem' := fun k _ => by
        rw [Matrix.zero_mul]; exact U₀.zero_mem
      neg_mem' := fun {a} ha k hk => by
        have := U₀.neg_mem (ha k hk)
        rwa [← Matrix.neg_mul] at this }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 0) ?_, fun k hk u hu h0 => ?_⟩
  · refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u k =>
      (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀) fun k _ => ?_
    have hc : Continuous fun p : WO S T × GA D S =>
        (HMul.hMul (p.1 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S p.2) : WO S T) :=
      continuous_fst.matrix_mul ((continuous_mt' S).comp continuous_snd)
    refine (hU₀.preimage hc).mem_nhds ?_
    show (HMul.hMul (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀
    rw [Matrix.zero_mul]; exact U₀.zero_mem
  · have h1 := hUf _ (hu k hk) (by rw [Matrix.map_mul, h0]; simp)
    have h2 := hW.om_heis k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) f hf
    rw [h1, actO_mul_mt] at h2
    exact h2.symm

end GlobalTheory.Core.Rk.Level
