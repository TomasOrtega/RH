import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagPartialWedge

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a}`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`.

Use `⟨Fin.castLE hl b, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢`. Conclude with `hb`. Introduce and unpack `⟨b, hb, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb`.

Use `⟨⟨b.val, by omega⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Fin.lt_def]`. Conclude with `hb`. Conclude with `congrArg y (Fin.ext rfl)`. Unfold `majorantDistance`.

Rewrite using `[hS]`.
-/
theorem len_castLE {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {l n : ℕ} (hl : l ≤ n)
    (y : Fin n → V) (a : Fin l) :
    majorantDistance (fun b : Fin l => y (Fin.castLE hl b)) a = majorantDistance y (Fin.castLE hl a) := by
  have ha := a.isLt
  have hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a} := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Fin.castLE hl b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢
      exact hb
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Fin.lt_def]
        exact hb
      · exact congrArg y (Fin.ext rfl)
  unfold majorantDistance
  rw [hS]

/- English proof (translation)
Introduce `k r l hl z hz`. Use `⟨fun s hs => ?_, fun g _ => ?_⟩` and prove the remaining obligations. Take `⟨U, hU0, hU1, hsF⟩` from `Formalism.QuantumDeterminants.S_F hz hs`. Rewrite using `[GlobalTheory.TensLen.cmp_mulVec_wedge]`. Use `GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `c a hac`. Simplify using `only [Matrix.submatrix_apply]`. Use `hU0 _ _ ?_` and prove the remaining obligations. Simplify using `only [Fin.lt_def, Fin.val_castLE] at hac ⊢`. Conclude with `hac`.

Introduce `c`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `hU1 _`. Introduce `i a`. Establish `ha` using `a.isLt`.

Use `show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i = ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)`. Establish `h1` using `congrFun (congrFun hsF i) (Fin.castLE hl a)`. Simplify using `only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1`. Establish `h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i = ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j` using `rfl`. Rewrite using `[h2, h1]`.

Use `Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_` and prove the remaining obligations. Introduce `j hj`. Use `show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0`. Rewrite using `[hU0 j (Fin.castLE hl a) ?_, mul_zero]`. Rewrite using `[Fin.lt_def, Fin.val_castLE]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `congr 1`. Conclude with `len_castLE hl (fun b : Fin (r + 1) => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a`.
-/
theorem fixes_partial_wedge_and_length : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  intro k r l hl z hz
  refine ⟨fun s hs => ?_, fun g _ => ?_⟩
  ·
    obtain ⟨U, hU0, hU1, hsF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
    refine GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_
    · intro c a hac
      simp only [Matrix.submatrix_apply]
      refine hU0 _ _ ?_
      simp only [Fin.lt_def, Fin.val_castLE] at hac ⊢
      exact hac
    · intro c
      simp only [Matrix.submatrix_apply]
      exact hU1 _
    · intro i a
      have ha := a.isLt
      show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
        ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)
      have h1 := congrFun (congrFun hsF i) (Fin.castLE hl a)
      simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1
      have h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
          ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j := rfl
      rw [h2, h1]
      refine Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_
      intro j hj
      show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0
      rw [hU0 j (Fin.castLE hl a) ?_, mul_zero]
      rw [Fin.lt_def, Fin.val_castLE]
      omega
  ·
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    exact len_castLE hl (fun b : Fin (r + 1) =>
      (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a

end GlobalTheory.FlagPartialWedge
