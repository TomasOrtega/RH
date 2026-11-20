import Mathlib
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WeylDimU

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem prod_sub_eq_prod_factorial (k : ℕ) :
    ∏ a : Fin k, ∏ b ∈ Finset.univ.filter (fun b : Fin k => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  rcases k with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Reduce the equality to equality of the corresponding arguments.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finrank_space {k : ℕ} (lam : Formalism.BasicNotions.DomWeight k) (u : Fin k → ℝ)
    (hu : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ))) :
    (Module.finrank ℂ (GlobalTheory.DualWeyl.Space lam.natW) : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  have h := Formalism.L2.G.Model.weyl_dualWeyl ℂ k lam.natW (Formalism.BasicNotions.factNatW k lam).1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_prod] at h2
  refine Eq.trans h2 ?_
  rw [← prod_sub_eq_prod_factorial, vand, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_div_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast
    congr 1
    linarith [hu a, hu b, GlobalTheory.NablaType.natW_add lam a, GlobalTheory.NablaType.natW_add lam b]
  · simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_eq (k : ℕ) (u : Fin k → ℝ) (hu : IsHCParam u) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : IsHCTypeU k u π) :
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨hs, hm⟩ := hu
  choose m hm using hm
  have hm' : StrictAnti m := fun a b hab => by
    have := hs hab
    have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
    exact_mod_cast h2
  have hL : Antitone fun a : Fin k => m a + (a : ℕ) := by
    rcases k with _ | n
    · exact fun a => a.elim0
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hm' (Fin.castSucc_lt_succ (i := i))
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  let lam : Formalism.BasicNotions.DomWeight k := ⟨fun a => m a + (a : ℕ), hL⟩
  have hw : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := fun a => by
    simp only [lam]
    push_cast
    linarith [hm a]
  have hK := GlobalTheory.NablaType.isKTypeOf_act lam
  have hT : IsHCTypeU k u (GlobalTheory.NablaType.act lam) := by
    refine ⟨?_, inferInstance, GlobalTheory.NablaType.isURepOn_act lam, ?_⟩
    · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
      exact ⟨v, 0, hv⟩
    · convert hK using 1
      funext a
      unfold allPos
      rw [GlobalTheory.DefiniteCheck.lowK_const, hw]
  obtain ⟨A, -⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU k u _ _ _ _ hπ hT
  rw [A.finrank_eq]
  exact finrank_space lam u hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem weyl_dimension : ∀ (k : ℕ) (u : Fin k → ℝ), IsHCParam u → (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ)) ∧ (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  intro k u hu
  refine ⟨fun H _ _ π hπ => finrank_eq k u hu H π hπ, ?_⟩
  obtain ⟨H, _, _, π, hπ⟩ := GlobalTheory.CompactDS.exists_isHCTypeU k u hu
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, H, _, _, π, hπ, rfl⟩
  obtain ⟨H', _, _, π', hπ', e⟩ := Nat.sInf_mem hne
  rw [dimPiU, ← e]
  exact finrank_eq k u hu H' π' hπ'

end GlobalTheory.WeylDimU
