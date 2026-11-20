import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForK
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

def WeylForKBody : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) σ → Formalism.MainNotions.S.IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + Formalism.REAL.rhoC ε) a - (Λ + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weyl_dimension_formula_product : WeylForKBody := by
  exact weylForK_closed

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem hw_isURepOn_mono {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {G G' : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : G' ⊆ G)
    (hU : Formalism.MainNotions.S.IsURepOn G σ) : Formalism.MainNotions.S.IsURepOn G' σ :=
  ⟨⟨hU.1.1, fun a ha b hb => hU.1.2 a (h ha) b (h hb)⟩, fun g hg v => hU.2.1 g (h hg) v,
    fun v => (hU.2.2 v).mono h⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem hw_kset_subset {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Kset ε ⊆ Formalism.MainNotions.S.UJset ε := by
  intro g hg
  obtain ⟨hu, hc⟩ := hg
  have hs : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hs, Matrix.one_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hw_rhoN_allPos (k : ℕ) (a : Fin k) : Formalism.REAL.rhoN (Formalism.MainNotions.S.allPos k) a = 0 := by
  simp [Formalism.REAL.rhoN, Formalism.MainNotions.S.allPos]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hw_rhoC_allPos (k : ℕ) (a : Fin k) :
    Formalism.REAL.rhoC (Formalism.MainNotions.S.allPos k) a = (((k : ℝ) - 1) - 2 * (a : ℕ)) / 2 := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Finset.Ioi a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have h2 : (Finset.univ.filter fun b : Fin k => b < a ∧ Formalism.MainNotions.S.allPos k b = Formalism.MainNotions.S.allPos k a) =
      Finset.Iio a := by
    ext b; simp [Formalism.MainNotions.S.allPos]
  have ha := a.isLt
  simp only [Formalism.REAL.rhoC, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem weyl_dimension_formula_unitary : Formalism.MainNotions.LocalBesselAndTopKernel.AdmittedWeylDimension := by
  intro k' u H _ _ π _ hT
  obtain ⟨_, _, hU, hK⟩ := hT
  have hUK : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k')) π :=
    hw_isURepOn_mono (hw_kset_subset _) hU
  have hW := weylForU_closed k' (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k') u) H π ⊤ hUK hK
  rw [finrank_top] at hW
  rw [hW]
  congr 1
  unfold Formalism.MainNotions.S.vand
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, hw_rhoN_allPos, hw_rhoC_allPos]
  ring

end ReciprocityTheory.ChartRestriction.DS.HW
