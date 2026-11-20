import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermFourierZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {n : ℕ}

namespace FZNH

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem unipotent_block_mul_add {R : Type} [CommRing R] (b c : Matrix (Fin n) (Fin n) R) :
    blk4 1 b 0 1 * blk4 1 c 0 1 = blk4 (1 : Matrix (Fin n) (Fin n) R) (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [add_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem mat_injective : Function.Injective (mat (D := D) (n := n)) := fun x y h =>
  GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext h)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mat_mul (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem nb_add {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b c : hermA D n) :
    nb (b + c) = nb b * nb c := by
  apply mat_injective
  rw [mat_mul, h, h, h, unipotent_block_mul_add]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nb_zero {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : nb 0 = 1 := by
  apply mat_injective
  rw [h, mat_one]
  exact block_matrix_one

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem nb_neg {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b : hermA D n) : (nb b)⁻¹ = nb (-b) := by
  have h' : nb (-b) * nb b = 1 := by rw [← nb_add h, neg_add_cancel, nb_zero h]
  exact (eq_inv_of_mul_eq_one_left h').symm

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nb_continuous {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : Continuous nb := by
  obtain ⟨i1, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  have he := GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)
  rw [he.continuous_iff, Units.continuous_iff]
  have hc : Continuous fun b : hermA D n => blk4 (1 : Mx D n n) b.1 0 1 := by
    unfold blk4
    exact (continuous_const.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const).matrix_submatrix _ _
  refine ⟨?_, ?_⟩
  · convert hc using 1
    funext b
    exact h b
  · convert hc.comp continuous_neg using 1
    funext b
    simp only [Function.comp_apply]
    rw [← map_inv, nb_neg h]
    exact h (-b)

end FZNH

open FZNH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem fourierZeroN : FourierZeroN := by
  intro D n ψ hψ nb lam 𝓖 hcd f hf hinv hco
  obtain ⟨hnb, hH, h𝓖, -⟩ := hcd
  funext g
  have key := hermFourierZero D n ψ hψ lam hH 𝓖 h𝓖 (fun b => f (nb b * g))
    (hf.comp ((nb_continuous hnb).mul continuous_const)) (fun x l hl => by
      obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := n)).2 ⟨l, hl⟩
      show f (nb (x + l) * g) = f (nb x * g)
      rw [show x + l = l + x from add_comm x l, nb_add hnb, mul_assoc]
      refine hinv l ⟨β, ?_⟩ _
      rw [← ofHermE_val, hβ]) (fun β => hco β g) 0
  simpa [nb_zero hnb] using key

end PositivityTheory.Rg.Sw.Glob
