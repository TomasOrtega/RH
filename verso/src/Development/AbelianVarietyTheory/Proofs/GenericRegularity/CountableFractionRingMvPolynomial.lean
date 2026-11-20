import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.GenericReading

/- English proof (translation)
Take `⟨s, hs⟩` from `h`. Establish `h1` using `IntermediateField.cardinalMk_adjoin_le K (s : Set L)`. Rewrite `h1` using `[hs, Cardinal.mk_congr (IntermediateField.topEquiv (F := K) (E := L)).toEquiv]`. Use `Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))` and prove the remaining obligations. Conclude with `Cardinal.mk_le_aleph0`.

Conclude with `Cardinal.mk_le_aleph0`.
-/
theorem countable_of_fg_top {K L : Type} [Field K] [Countable K] [Field L] [Algebra K L]
    (h : (⊤ : IntermediateField K L).FG) : Countable L := by
  obtain ⟨s, hs⟩ := h
  have h1 := IntermediateField.cardinalMk_adjoin_le K (s : Set L)
  rw [hs, Cardinal.mk_congr (IntermediateField.topEquiv (F := K) (E := L)).toEquiv] at h1
  refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
  · exact Cardinal.mk_le_aleph0
  · exact Cardinal.mk_le_aleph0

/- English proof (translation)
Establish `h : Countable (MvPolynomial ι L)`. Use `Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl))` and prove the remaining obligations. Conclude with `Cardinal.mk_le_aleph0`. Conclude with `Cardinal.mk_le_aleph0`. Use `Cardinal.mk_le_aleph0_iff.1 ?_` and prove the remaining obligations.

Rewrite using `[FractionRing.cardinalMk]`. Conclude with `Cardinal.mk_le_aleph0`.
-/
theorem countable_fractionRing_mvPolynomial (ι L : Type) [Countable ι] [Field L] [Countable L] :
    Countable (FractionRing (MvPolynomial ι L)) := by
  have h : Countable (MvPolynomial ι L) := by
    refine Cardinal.mk_le_aleph0_iff.1 (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0
  refine Cardinal.mk_le_aleph0_iff.1 ?_
  rw [FractionRing.cardinalMk]
  exact Cardinal.mk_le_aleph0

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U _ hU h Z`. Use `⟨?_, fun φ => ?_⟩` and prove the remaining obligations. Establish `hfin : FiniteDimensional ℚ c.F` using `c.fin`. Establish `hcF : Countable c.F` using `Cardinal.mk_le_aleph0_iff.1 (by`. Simplify `Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)` using `[Cardinal.mkRat]`.

Establish `hk : Countable (kap Z)` using `countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)`. Establish `hO : Countable (Om Z)` using `countable_fractionRing_mvPolynomial _ _`. Set `_ : Algebra c.F ℂ` to `σ.toAlgebra`. Conclude with `GlobalTheory.nonempty_algHom_complex_of_countable c.F (Om Z)`. Take `⟨y', hy⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c (Om Z) (CAt σ) φ (genFr h Z)`.

Take `⟨k, x, t, ht⟩` from `hU.2.2.1 y'`. Conclude with `⟨k, x, y', t, hy, ht⟩`.
-/
theorem embedding_read_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c), Nonempty (Om Z →ₐ[c.F] CAt σ) ∧ ∀ φ : Om Z →ₐ[c.F] CAt σ, ∃ (k : U.Comp) (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU h Z
  refine ⟨?_, fun φ => ?_⟩
  · have hfin : FiniteDimensional ℚ c.F := c.fin
    have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
      simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
    have hk : Countable (kap Z) := countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
    have hO : Countable (Om Z) := countable_fractionRing_mvPolynomial _ _
    let _ : Algebra c.F ℂ := σ.toAlgebra
    exact GlobalTheory.nonempty_algHom_complex_of_countable c.F (Om Z)
  · obtain ⟨y', hy⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c (Om Z)
      (CAt σ) φ (genFr h Z)
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y'
    exact ⟨k, x, y', t, hy, ht⟩

end GlobalTheory.GenericReading
