import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb

variable {D : D7}

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw`. Establish `hc : ∀ b, c b = 0`. Introduce `b`. Establish `h` using `hf b`. Simplify using `only [map_sum, map_smul, smul_eq_mul] at h`.

Establish `hfe : ∀ a, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0`. Introduce `a`. Rewrite using `[a_herm, X.ef a b]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`.

Conclude with `h`. Simplify using `[hc]`.
-/
theorem eq_zero_of_mem_span_eX (X : HidaSetting D) (w : (VS D).V)
    (hw : w ∈ Submodule.span D.host.E (Set.range X.eX)) (hf : ∀ b, (VS D).hT (X.fY b) w = 0) : w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := hf b
    simp only [map_sum, map_smul, smul_eq_mul] at h
    have hfe : ∀ a, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
      intro a
      rw [a_herm, X.ef a b]
      split_ifs <;> simp
    simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  simp [hc]

/- English proof (translation)
Introduce `D X u τ x hx`. Establish `hpos : (GlobalTheory.TypeAsm.F0 X u).PosDefAt τ` using `Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (GlobalTheory.TypeAsm.tu_ne D u) (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) τ`. Use `set w : (VS D).V := ((x : Wb X) : (VS D).V) with hwdef`. Establish `hWb` using `(mem_Wb X _).1 (x : Wb X).2`. Establish `hUb` using `(mem_Ub X u _).1 x.2`.

Establish `hw0 : w ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Conclude with `Subtype.ext (Subtype.ext h)`. Establish `h1 : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) w = 0`.

Introduce `a`. Express the relevant statement in the definitionally equal form `(VS D).hT w ((X.Fu u).fvec a) = 0`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Rewrite using `[FlagG.fvec, Fin.snoc_last, X.flagZVector]`.

Conclude with `p_symm_zero (VS D) hUb`. Consider the case `cast b`. Rewrite using `[FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]`. Conclude with `p_symm_zero (VS D) (hWb b).1`. Establish `h2 : w ∉ (GlobalTheory.TypeAsm.F0 X u).X`.

Introduce `hX`. Apply `hw0` to reduce the goal to its premises. Use `eq_zero_of_mem_span_eX X w ?_ (fun b => (hWb b).2)` and prove the remaining obligations. Use `(Submodule.span_le.2 ?_) hX` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`.

Express the relevant statement in the definitionally equal form `(X.Fu u).fvec b.castSucc ∈ _`. Rewrite using `[FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Use `hpos w h1 h2` as an intermediate fact. Rewrite using `[hU_apply]`.

Conclude with `this`.
-/
theorem pd_hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  intro D X u τ x hx
  have hpos : (GlobalTheory.TypeAsm.F0 X u).PosDefAt τ :=
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (GlobalTheory.TypeAsm.tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) τ
  set w : (VS D).V := ((x : Wb X) : (VS D).V) with hwdef
  have hWb := (mem_Wb X _).1 (x : Wb X).2
  have hUb := (mem_Ub X u _).1 x.2
  have hw0 : w ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext (Subtype.ext h)
  have h1 : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) w = 0 := by
    intro a
    change (VS D).hT w ((X.Fu u).fvec a) = 0
    induction a using Fin.lastCases with
    | last =>
      rw [FlagG.fvec, Fin.snoc_last, X.flagZVector]
      exact p_symm_zero (VS D) hUb
    | cast b =>
      rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
      exact p_symm_zero (VS D) (hWb b).1
  have h2 : w ∉ (GlobalTheory.TypeAsm.F0 X u).X := by
    intro hX
    apply hw0
    refine eq_zero_of_mem_span_eX X w ?_ (fun b => (hWb b).2)
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨b, -, rfl⟩
    change (X.Fu u).fvec b.castSucc ∈ _
    rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
    exact Submodule.subset_span ⟨b, rfl⟩
  have := hpos w h1 h2
  rw [hU_apply]
  exact this

end GlobalTheory.RowsOrb
