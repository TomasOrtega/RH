import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.UnifConj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_unif_isUnif : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (Pb : Formalism.L2.DIV.Pl E) (Ut : Formalism.L2.Col.MhlUnif Pb), Formalism.L2.Col.cO E Ut.π ∈ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ∧ Formalism.L2.Col.cO E Ut.π ∉ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ^ 2 := by
  intro E _ _ _ Pb Ut
  refine ⟨(Formalism.L2.Col.mem_conjP Pb _).2 (by rw [Formalism.L2.Col.cO_cO]; exact Ut.hπ), ?_⟩
  intro h
  have h2 : Ut.π ∈ Pb.asIdeal ^ 2 := by
    have h1 : Formalism.L2.Col.cO E Ut.π ∈ (Pb.asIdeal ^ 2).comap (Formalism.L2.Col.cO E) :=
      Ideal.le_comap_pow (Formalism.L2.Col.cO E) 2 h
    rw [Ideal.mem_comap, Formalism.L2.Col.cO_cO] at h1
    exact h1
  have hle : Pb.asIdeal ≤ Pb.asIdeal ^ 2 := by
    intro p hp
    obtain ⟨t, ht⟩ := Ut.hcπ p hp
    have hcp : Ut.c * p ∈ Pb.asIdeal ^ 2 := by
      rw [ht]; exact Ideal.mul_mem_right t _ h2
    obtain ⟨a, e, he, hae⟩ := Pb.isMaximal.exists_inv Ut.hc
    have hee : e * e ∈ Pb.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul he he
    have hp' : p = a * (a * Ut.c + 2 * e) * (Ut.c * p) + (e * e) * p := by
      linear_combination (-(p) * (a * Ut.c + e + 1)) * hae
    rw [hp']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hcp) (Ideal.mul_mem_right _ _ hee)
  have hlt : Pb.asIdeal ^ 2 < Pb.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti Pb.asIdeal Pb.ne_bot Pb.isPrime.ne_top (by norm_num)
  rw [pow_one] at hlt
  exact hlt.not_ge hle

end GlobalTheory.Mem.UnifConj
