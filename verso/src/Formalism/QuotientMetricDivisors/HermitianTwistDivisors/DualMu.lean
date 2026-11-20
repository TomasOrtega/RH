import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.DualMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep

open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

/- English proof (translation)
Introduce `K _ _ _ _ D hD X hX R hR`. Establish `hFG : R.FG` using `hR.fg`. Establish `hsp : Submodule.span K (R : Set (Fin D → K)) = ⊤` using `hR.2`. Take `⟨hdFG, hdsp, -, hsize, -⟩` from `Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG hsp`. Establish `hdX : ∀ v, IsUnit (Formalism.HN.dualFrame X v).det`.

Introduce `v`. Apply `Matrix.isUnit_nonsing_inv_det` to reduce the goal to its premises. Rewrite using `[Matrix.det_transpose]`. Conclude with `hX v`. Establish `hne : Formalism.HN.dualLat R ≠ ⊥`.

Introduce `h`. Rewrite `hdsp` using `[h, Submodule.bot_coe, Submodule.span_zero_singleton]`. Establish `hmem : (Pi.basisFun K (Fin D)).dualBasis ⟨0, hD⟩ ∈ (⊤ : Submodule K _)` using `Submodule.mem_top`. Rewrite `hmem` using `[← hdsp, Submodule.mem_bot]`. Conclude with `(Pi.basisFun K (Fin D)).dualBasis.ne_zero _ hmem`.

Establish `hmu` using `(Formalism.HN.size_maximal_slope K (Module.Dual K (Fin D → K)) (Fin D) (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) hdX (Formalism.HN.dualLat R) hdFG hne).2.1`. Establish `hht` using `(Formalism.HN.place_lattice_structure K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG).2.2`. Establish `hrk : Formalism.HN.rkK R = D`. Unfold `Formalism.HN.rkK`. Use `erw [hsp]`.

Simplify using the standard rewrite rules. Establish `hfr` using `Formalism.HN.sizeMu_finrank_eq K`. Establish `hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ)`. Establish `h0 : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `: 0 < Formalism.HN.nPl K` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `hDr : (0 : ℝ) < (D : ℝ)` using `by exact_mod_cast hD`. Rewrite using `[hmu, hsize, Real.log_inv, Formalism.HN.size, Real.log_rpow hht, hrk]`. Unfold `Formalism.DivisionValues.lcv`. Rewrite using `[hfr]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem dual_lattice_measure : DualMu := by
  intro K _ _ _ _ D hD X hX R hR
  have hFG : R.FG := hR.fg
  have hsp : Submodule.span K (R : Set (Fin D → K)) = ⊤ := hR.2
  obtain ⟨hdFG, hdsp, -, hsize, -⟩ :=
    Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG hsp
  have hdX : ∀ v, IsUnit (Formalism.HN.dualFrame X v).det := by
    intro v
    apply Matrix.isUnit_nonsing_inv_det
    rw [Matrix.det_transpose]
    exact hX v
  have hne : Formalism.HN.dualLat R ≠ ⊥ := by
    intro h
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hdsp
    have hmem : (Pi.basisFun K (Fin D)).dualBasis ⟨0, hD⟩ ∈ (⊤ : Submodule K _) := Submodule.mem_top
    rw [← hdsp, Submodule.mem_bot] at hmem
    exact (Pi.basisFun K (Fin D)).dualBasis.ne_zero _ hmem
  have hmu := (Formalism.HN.size_maximal_slope K (Module.Dual K (Fin D → K)) (Fin D) (Pi.basisFun K (Fin D)).dualBasis
    (Formalism.HN.dualFrame X) hdX (Formalism.HN.dualLat R) hdFG hne).2.1
  have hht := (Formalism.HN.place_lattice_structure K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG).2.2
  have hrk : Formalism.HN.rkK R = D := by
    unfold Formalism.HN.rkK
    erw [hsp]
    simp
  have hfr := Formalism.HN.sizeMu_finrank_eq K
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have h0 : 0 < Module.finrank ℚ K := Module.finrank_pos
    have : 0 < Formalism.HN.nPl K := by omega
    exact_mod_cast this
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [hmu, hsize, Real.log_inv, Formalism.HN.size, Real.log_rpow hht, hrk]
  unfold Formalism.DivisionValues.lcv
  rw [hfr]
  push_cast
  field_simp

end Formalism.DivisionValues
