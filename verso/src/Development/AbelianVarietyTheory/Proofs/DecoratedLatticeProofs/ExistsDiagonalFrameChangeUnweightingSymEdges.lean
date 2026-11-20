import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

/- English proof (translation)
Use `haveI : PP.asIdeal.IsMaximal := PP.isMaximal`. Use `letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal`. Conclude with `isUnit_iff_ne_zero.mpr hx`.
-/
theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D n ρ k Pg Λ β₀ hβ a ha`. Set `w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ` to `fun PP i j => if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1`. Set `d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ` to `fun PP => GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)`. Establish `hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j`. Introduce `PP hPP i j h`.

Establish `e` using `congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)`. Rewrite `e` using `[Units.val_mul]`. Rewrite using `[e]`. Simplify using `only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]`. Use `choose u hu using fun j : Fin n => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)`.

Establish `hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀`. Introduce `M`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩`.

Introduce and unpack `⟨y, rfl⟩`. Use `⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.FrameRescale.frGL_mul]`. Use `congr 1`. Use `group`.

Establish `hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀, Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M = (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP)`. Introduce `PP hPP M hM`. Take `⟨y, rfl⟩` from `hM`. Establish `e1 : Formalism.L2.DIV.frGL β₀ y = Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)`. Rewrite using `[GlobalTheory.FrameRescale.frGL_mul]`.

Use `congr 1`. Use `group`. Establish `hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Use `show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) = ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.D …`. Rewrite using `[GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hu i PP hPP`.

Conclude with `map_zero _`. Establish `e3` using `Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)`. Establish `e4` using `Formalism.L2.DIV.redFn_frGL β₀ PP y`. Rewrite `e3` using `[← e1]`. Rewrite using `[e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]`.

Use `⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[hβ x]`. Establish `hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) * (β₀⁻¹).val`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]`.

Rewrite using `[hinv]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]`. Establish `hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1` using `congrArg Subtype.val (u i).mul_inv`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h`. Introduce `h`. Establish `h2` using `Subring.mul_mem _ (u i).val.2 h`. Rewrite `h2` using `[← mul_assoc, hm, one_mul]`. Then use the resulting hypothesis.

Use extensionality with `M`. Conclude with `hSt M`. Introduce `PP hPP y hy`. Rewrite using `[hred PP hPP y hy]`. Use `⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩` and prove the remaining obligations.

Unfold `Formalism.L2.DIV.edgeSum`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]`. Expand and normalize the polynomial expressions, which then agree.

Both sides reduce to the same expression.
-/
theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  choose u hu using fun j : Fin n => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
