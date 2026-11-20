import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionEqHorizontalGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_isBetti_of_isFlat : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn), IsFlat (Φ.C k) (DV.tauEmb D τ) σ → ∃ b, IsBetti s Φ L k τ σ b := by
  intro D A N j S κ s Φ L k τ σ hσ
  classical
  have hE := detEx_eq S L τ
  have hD : divOf (Φ.C k) (detEx S τ) = (Φ.C k).LEx (GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw (L.ψ τ)) 0) := by
    simp [hE, divOf, FlagCpt.LEx]
  obtain ⟨f, ⟨hf, hv⟩, -⟩ := GlobalTheory.ShFam.existsUnique_rule_of_regular _ _ _ _ _ _ _ _ _ _ κ.e _ _ _ Φ (GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw (L.ψ τ)) 0) rfl
    (Function.update 0 k σ) (fun k' y _ => by
      by_cases h : k' = k
      · subst h
        rw [Function.update_self, ← hD]
        exact (hσ y).regularAt
      · rw [Function.update_of_ne h]
        obtain ⟨g, hg⟩ := ((Φ.C k').LEx _).exists_isEqn y
        exact ⟨g, hg, 0, by simp⟩)
  have hv' : (Φ.C k).val f = σ := (hv k).trans (Function.update_self _ _ _)
  obtain ⟨b, hb⟩ := GlobalTheory.T.flat_section_eq_horizontal_generator D A N j S κ s Φ k (L.ψ τ) (cmAt s L k τ).2 f hf (by rw [hv', L.ψ_val]; exact hσ)
  have hc := pow_ne_zero S.Dw.q (Complex.ofReal_ne_zero.2 (GlobalTheory.TrueCx.hodgeC_pos _ (cmAt s L k) τ).ne')
  refine ⟨b * (Units.mk0 _ hc)⁻¹, fun x a => ?_⟩
  letI := κ.σ₀.toAlgebra
  have h1 := GlobalTheory.ShFam.ValCoord.coordAt_val_iff _ _ _ _ _ _ _ _ _ _ κ.e (Φ.C k) ℂ ((s.U κ.σ₀).un k x) _ rfl f hf a
  rw [hv', ← hE] at h1
  refine h1.trans ((and_iff_right (carriedC_un s Φ k x)).trans ?_)
  have h2 : Formalism.L2.PjFree.rdU (s.U κ.σ₀) f k x.1 = Formalism.L2.PjFree.toC (evR s.Xo κ.c f ((s.U κ.σ₀).un k x)) := dif_pos x.2
  change a = Formalism.L2.PjFree.toC (evR s.Xo κ.c f ((s.U κ.σ₀).un k x)) ↔ _
  rw [← h2, hb x.1 x.2, bettiCo, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_assoc, inv_mul_cancel_left₀ hc]
  rfl

end GlobalTheory.ShFam.Pad
