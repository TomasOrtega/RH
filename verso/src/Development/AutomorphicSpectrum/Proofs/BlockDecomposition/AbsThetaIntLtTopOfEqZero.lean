import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssembly

/- English proof (translation)
Set `b` to `Module.finBasis E W`. Establish `hl : LinearIndependent E fun i => B.hT (b i)`. Use `Fintype.linearIndependent_iff.2 fun c hc i => ?_` and prove the remaining obligations. Establish `h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0`. Rewrite using `[← hc]`.

Simplify using `[map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]`. Establish `h2 : (∑ i, star (c i) • b i : W) = 0` using `Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)`. Simplify using `using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i`. Establish `h3` using `Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))`. Rewrite `h3` using `[finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq]`.

Establish `h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator` using `fun y hy => by`. Rewrite using `[Submodule.mem_dualCoannihilator]`. Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem _ h => obtain ⟨i, rfl⟩ := h`.

Conclude with `hW _ (b i).2 _ hy`. Consider the case `zero => rfl`. Consider the case `add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]`. Consider the case `smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]`. Use `Submodule.finrank_mono h4` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_finrank_isotropic_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E)
    (W : Submodule E B.V) (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_isotropic_le B W hW; omega⟩`.
-/
theorem bddAbove_isotropic_dims {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_isotropic_le B W hW; omega⟩

/- English proof (translation)
Take `⟨W, h, hW⟩` from `Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_isotropic_dims B)`. Rewrite using `[Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]`. Conclude with `two_mul_finrank_isotropic_le B W hW`.
-/
theorem two_mul_wittIdx_le_rank {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_isotropic_dims B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_isotropic_le B W hW

/- English proof (translation)
Use `⟨fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Module.finBasis D.host.E U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Establish `: Set.range (fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E)) = U.subtype '' Set.range (Module.finBasis D.host.E U)`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[this, Submodule.span_image, (Module.finBasis D.host.E U).span_eq, Submodule.map_subtype_top]`.
-/
theorem exists_isRowBasis {D : D7} {n : ℕ} (U : Submodule D.host.E (Fin n → D.host.E)) :
    ∃ c, IsRowBasis U c := by
  refine ⟨fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E), ?_, ?_⟩
  · exact (Module.finBasis D.host.E U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E)) =
        U.subtype '' Set.range (Module.finBasis D.host.E U) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, (Module.finBasis D.host.E U).span_eq, Submodule.map_subtype_top]

/- English proof (translation)
Substitute `hr` using the available equality. Establish `hc : ∀ h, GlobalTheory.SiegelFormula.absTheta V φ h = ‖φ 0‖ₑ`. Introduce `h`. Unfold `GlobalTheory.SiegelFormula.absTheta`. Use `haveI : Unique (Matrix (Fin V.rank) (Fin 0) D.host.E) := inferInstanceAs (Unique (Fin V.rank → Fin 0 → D.host.E))`.

Rewrite using `[tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]`. Establish `h0 : GlobalTheory.SiegelFormula.invPt V h (default : Matrix (Fin V.rank) (Fin 0) D.host.E) = 0`. Use function extensionality and compare the values at `i j`. Conclude with `j.elim0`. Rewrite using `[h0]`.

Unfold `GlobalTheory.SiegelFormula.absThetaInt`. Establish `hq : ∀ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q = ‖φ 0‖ₑ` using `fun q => hc _`. Repeatedly rewrite using `[hq, lintegral_const]`. Conclude with `ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)`.
-/
theorem absThetaInt_lt_top_of_eq_zero {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {r : ℕ}
    (hr : r = 0) (φ : Mx D V.rank r → ℂ) : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ := by
  subst hr
  have hc : ∀ h, GlobalTheory.SiegelFormula.absTheta V φ h = ‖φ 0‖ₑ := by
    intro h
    unfold GlobalTheory.SiegelFormula.absTheta
    haveI : Unique (Matrix (Fin V.rank) (Fin 0) D.host.E) :=
      inferInstanceAs (Unique (Fin V.rank → Fin 0 → D.host.E))
    rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
    have h0 : GlobalTheory.SiegelFormula.invPt V h (default : Matrix (Fin V.rank) (Fin 0) D.host.E) = 0 := by
      funext i j; exact j.elim0
    rw [h0]
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have hq : ∀ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q = ‖φ 0‖ₑ := fun q => hc _
  simp_rw [hq, lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end GlobalTheory.CompanionTheory.SiegelAssembly

namespace GlobalTheory.CompanionTheory.SiegelAssembly

end GlobalTheory.CompanionTheory.SiegelAssembly
