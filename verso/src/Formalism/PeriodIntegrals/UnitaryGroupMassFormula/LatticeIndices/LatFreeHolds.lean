import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGl
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanTopFamily

noncomputable section

namespace MassDataIdxLatFree

open NumberField

variable {E K : Type} [Field E] [NumberField E] [Field K] (O : ValuationSubring K) (ι : E →+* K)
  {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem int_mem (a : 𝓞 E) : ι (a : E) ∈ O := by
  have h1 : IsIntegral ℤ (ι (a : E)) := (RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  have h2 : IsIntegral O (ι (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

def Mι (L : Submodule (𝓞 E) (n → E)) : Submodule O (n → K) :=
  Submodule.span O ((fun l : n → E => fun j => ι (l j)) '' (L : Set (n → E)))

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fg (L : Submodule (𝓞 E) (n → E)) (hL : L.FG) : (Mι O ι L).FG := by
  classical
  obtain ⟨S, hS⟩ := hL
  refine ⟨S.image (fun l : n → E => fun j => ι (l j)), ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.2
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    exact Submodule.subset_span ⟨l, hS ▸ Submodule.subset_span hl, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    rw [← hS] at hl
    induction hl using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | zero =>
        have : (fun j => ι ((0 : n → E) j)) = 0 := by funext j; simp
        beta_reduce; rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        have : (fun j => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
          funext j; simp
        beta_reduce; rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        have : (fun j => ι ((a • x) j)) = (⟨ι (a : E), int_mem O ι a⟩ : O) • (fun j => ι (x j)) := by
          funext j
          simp [Algebra.smul_def]
        beta_reduce; rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem span_top (L : Submodule (𝓞 E) (n → E)) (hL : Submodule.span E (L : Set (n → E)) = ⊤) :
    Submodule.span K (Mι O ι L : Set (n → K)) = ⊤ :=
  by apply _root_.UpperTheory.Reformulated.B.SpanTopFamily.span_top <;> assumption

end MassDataIdxLatFree

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latFree_holds {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    LatFreeP X p θ :=
  MassDataIdxLatFree.exists_gl (OpX X p) (Mlat1 X p θ)
    (MassDataIdxLatFree.fg (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_fg)
    (MassDataIdxLatFree.span_top (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_span)

end MassDataIdxSteps
