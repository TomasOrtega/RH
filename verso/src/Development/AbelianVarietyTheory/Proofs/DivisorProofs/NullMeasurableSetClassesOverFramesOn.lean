import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSetStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.ClassesMeas

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nullMeasurableSet_classesOver_framesOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ σ, GoodEmb c σ → ∀ Z : Comp Xo c, NullMeasurableSet (classesOver (V σ) (dict σ) (framesOn (U σ) Z)) (muQ1 (V σ)) := by
  intro D H Dw l Xo c r U V dict hC σ hσ Z
  obtain ⟨hU, ⟨Kf, th, hr, hK, _, hd⟩, _, _⟩ := hC.2 σ hσ
  obtain ⟨d1, d2, ⟨x0, _, d3⟩, d4, _, _⟩ := hd
  haveI : BorelSpace (GA D (V σ)) := ⟨rfl⟩
  let S : Set (U σ).Comp := {k | ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z}
  have key : ∀ g, dict σ g ∈ framesOn (U σ) Z ↔ (dict σ g).1 ∈ S := by
    intro g
    constructor
    · intro h
      exact ⟨(dict σ g).2, h⟩
    · rintro ⟨y, hy⟩
      exact GlobalTheory.T.framePointsOverComponent_open_set D.host.E H Dw l Xo c r U σ hU Z _ y _ (d4 g) hy
  have hP : IsOpen {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    refine Filter.mem_of_superset
      (GlobalTheory.LevelOpen.level_mem_nhds D (V σ) l.M Kf (by have := l.three_le; omega) hK g₀) ?_
    rintro g ⟨k, hk, h, hh, rfl⟩
    obtain ⟨γ, _, e1⟩ := d2 k hk g₀
    obtain ⟨γ', _, e2⟩ := d3 (g₀ * k) h hh
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    show (dict σ (g₀ * k * h)).1 ∈ S
    rw [f2, f1]
    exact hg₀
  have hpre : (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ))) =
      {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    show dict σ (Quotient.mk'' g : AutQ (V σ)).out ∈ framesOn (U σ) Z ↔ _
    rw [key]
    have hrel : QuotientGroup.rightRel (GQ (V σ)) (Quotient.mk'' g : AutQ (V σ)).out g :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨γ', _, e⟩ := d1 _ (inv_mem hrel) g
    have f := congrArg Sigma.fst e
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at f
    rw [f]
  refine MeasurableSet.nullMeasurableSet ?_
  show MeasurableSet (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ)))
  rw [hpre]
  exact hP.measurableSet

end GlobalTheory.ClassesMeas
