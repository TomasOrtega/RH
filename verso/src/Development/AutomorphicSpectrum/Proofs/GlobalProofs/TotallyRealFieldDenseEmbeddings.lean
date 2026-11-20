import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem denseRange_real_places (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange fun (x : F) (w : InfinitePlace F) =>
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hq : ∀ w : InfinitePlace F, ∃ q : ℚ, |(q : ℝ) - z w| < ε / 2 := by
    intro w
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show z w < z w + ε / 2 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi F)
    (fun w => WithAbs.toAbs w.1 ((q w : ℚ) : F)) (ε / 2) (by linarith)
  refine ⟨x, (dist_pi_lt_iff hε).mpr fun w => ?_⟩
  have hxw := (dist_pi_lt_iff (by linarith : (0 : ℝ) < ε / 2)).mp hx w
  try dsimp only at hxw
  rw [Pi.algebraMap_apply, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply] at hxw
  have h2 : w.1 ((q w : F) - x) =
      |(q w : ℝ) - InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x| := by
    have h := InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) ((q w : F) - x)
    rw [Real.norm_eq_abs, map_sub, map_ratCast] at h
    exact h.symm
  rw [h2] at hxw
  show dist (z w) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) < ε
  rw [Real.dist_eq]
  have h3 : |z w - (q w : ℝ)| < ε / 2 := by
    rw [abs_sub_comm]
    exact hq w
  linarith [abs_sub_le (z w) (q w : ℝ) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_place_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : F →+* ℝ) :
    ∃ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) = σ := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp σ), ?_⟩
  ext x
  have h1 := InfinitePlace.embedding_of_isReal_apply
    (IsTotallyReal.isReal (InfinitePlace.mk (Complex.ofRealHom.comp σ))) x
  rw [InfinitePlace.embedding_mk_eq_of_isReal hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe] at h1
  exact_mod_cast h1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_approx : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ),
    0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  intro F _ _ _ y ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_real_places F)
    (fun w => y (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) ε hε
  refine ⟨x, fun σ => ?_⟩
  obtain ⟨w, hw⟩ := exists_place_eq F σ
  have h := (dist_pi_lt_iff hε).mp hx w
  rw [Real.dist_eq, hw, abs_sub_comm] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density
