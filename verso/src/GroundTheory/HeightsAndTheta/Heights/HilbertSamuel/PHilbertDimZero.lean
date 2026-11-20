import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mixedDiff_zero {K : Type*} (h : (K → ℤ) → ℤ) (bs : Fin 0 → K → ℤ) :
    mixedDiff bs h = h := by
  simp [mixedDiff]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem relDim_eq_zero_of_ringKrullDim {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hd]
  simp
  change WithTop.map (fun e : ℕ => (e : ℤ) - (Fintype.card K : ℤ))
    ((Fintype.card K : ℕ) : WithTop ℕ) = 0
  exact congrArg WithTop.some (sub_self _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem HilbertDimZero.proof : HilbertDimZero.Statement.{u} := by
  intro F _ K _ _ ι _ q hq hd
  have h0 := ((GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst.full.{u} F K ι q hq.multiHomog
    hq.relevant 0 (relDim_eq_zero_of_ringKrullDim q hd)).1 (![] : Fin 0 → K → ℤ))
  simp only [mixedDiff_zero] at h0
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h0
  refine ⟨Finset.univ.sup fun k => (b k).toNat, fun a ha => hb _ fun k => ?_⟩
  have h1 : (b k).toNat ≤ a k :=
    le_trans (Finset.le_sup (f := fun k => (b k).toNat) (Finset.mem_univ k)) (ha k)
  have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
  show b k ≤ (a k : ℤ)
  omega

end GroundTheory.Heights₂.Heights.HilbertSamuel
