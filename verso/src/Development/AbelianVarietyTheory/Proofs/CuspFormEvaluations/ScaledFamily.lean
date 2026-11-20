import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.ScaledGenerators

/- English proof (translation)
Establish `hfun : (fun k => (s : B.KO) • w0 k) = (s • (LinearMap.id : B.Cusp j wL →ₗ[𝓞 B.KO] B.Cusp j wL)) ∘ w0`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Use `first`. Consider the case `rfl`.

Consider the case `exact algebraMap_smul B.KO s (w0 k)`. Consider the case `simp`. Rewrite using `[hfun, Set.range_comp, ← Submodule.map_span, h]`. Both sides reduce to the same expression.
-/
theorem span_scaled {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (wL : WeightFamilies.Wt D j)
    (s : 𝓞 B.KO) {N : ℕ} (w0 : Fin N → B.Cusp j wL)
    (h : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL) :
    Submodule.span (𝓞 B.KO) (Set.range fun k => (s : B.KO) • w0 k) = X.WWc s wL := by

  have hfun : (fun k => (s : B.KO) • w0 k) =
      (s • (LinearMap.id : B.Cusp j wL →ₗ[𝓞 B.KO] B.Cusp j wL)) ∘ w0 := by
    funext k
    simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    first
      | rfl
      | exact algebraMap_smul B.KO s (w0 k)
      | simp
  rw [hfun, Set.range_comp, ← Submodule.map_span, h]
  rfl

/- English proof (translation)
Introduce `D B P j X ka wL wF S N w0 a b G Prw ha hb hS hspan hsup hG`. Use `set w : Fin N → B.Cusp j wL := fun k => (S.sW : B.KO) • w0 k with hw`. Establish `hspanw : Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL` using `span_scaled X wL S.sW w0 hspan`. Establish `hbound : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ a + b`. Introduce `σ k`.

Establish `hmul : B.supN j wL σ (w k) = ‖σ (S.sW : B.KO)‖ * B.supN j wL σ (w0 k)` using `B.supN_smul j wL σ _ (w0 k)`. Rewrite using `[hmul]`. Distinguish the cases in `hx : ‖σ (S.sW : B.KO)‖ = 0`. Rewrite using `[hx, zero_mul, Real.log_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hy : B.supN j wL σ (w0 k) = 0`. Rewrite using `[hy, mul_zero, Real.log_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.log_mul hx hy]`. Combine the linear relations using `[hS σ, hsup k σ]`.

Establish `hmean : (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Break down `Nat.eq_zero_or_pos (Fintype.card (B.KO →+* ℂ)) with h0 | h0` into its components or cases. Rewrite using `[h0, Nat.cast_zero, zero_mul, zero_div]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0` using `by positivity`. Rewrite using `[mul_div_cancel_left₀ _ hc]`. Conclude with `hG`. Use `⟨⟨Finset.univ.image w, ?_, fun _ => a + b, ?_, hmean⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`.

Conclude with `hspanw`. Introduce `σ g hg`. Take `⟨k, -, rfl⟩` from `Finset.mem_image.mp hg`. Conclude with `hbound σ k`. Introduce `hM hN`.

Use `⟨{ N := N w := w del := 0 th' := fun i => Fin.elim0 i rz := 0 alz := fun i => Fin.elim0 i th0 := fun i => Fin.elim0 i zc := fun i => Fin.elim0 i rq := 0 th := fun i => Fin.elim0 i iet := 0 et := 0 mx := fun _ => a + b }, ?_⟩` and prove the remaining obligations. Use `⟨hspanw, ?_, hN, fun σ k => hbound σ k, hmean⟩` and prove the remaining obligations. Introduce `k`. Apply `hM` to reduce the goal to its premises. Rewrite using `[← hspanw]`.

Conclude with `Submodule.subset_span (Set.mem_range_self k)`.
-/
theorem scaled_family : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal B) (N : ℕ) (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ), 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a) → Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL → (∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) → a + b ≤ G * wL.size → (∃ Sh : Finset (B.Cusp j wL), Submodule.span (𝓞 B.KO) (Sh : Set (B.Cusp j wL)) = X.WWc S.sW wL ∧ ∃ mx : (B.KO →+* ℂ) → ℝ, (∀ σ, ∀ g ∈ Sh, Real.log (B.supN j wL σ g) ≤ mx σ) ∧ (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size) ∧ (X.WWc S.sW wL ≤ B.Mlat j wL → Real.log N ≤ Prw * (wL.size - 1) → ∃ Gd : EtaleWeightGaps.GlobalFamilyData X ka wL wF, Gd.TiedW S G Prw) := by
  classical
  intro D B P j X ka wL wF S N w0 a b G Prw ha hb hS hspan hsup hG

  set w : Fin N → B.Cusp j wL := fun k => (S.sW : B.KO) • w0 k with hw
  have hspanw : Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL := span_scaled X wL S.sW w0 hspan

  have hbound : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ a + b := by
    intro σ k
    have hmul : B.supN j wL σ (w k) = ‖σ (S.sW : B.KO)‖ * B.supN j wL σ (w0 k) := B.supN_smul j wL σ _ (w0 k)
    rw [hmul]
    by_cases hx : ‖σ (S.sW : B.KO)‖ = 0
    · rw [hx, zero_mul, Real.log_zero]
      linarith
    by_cases hy : B.supN j wL σ (w0 k) = 0
    · rw [hy, mul_zero, Real.log_zero]
      linarith
    rw [Real.log_mul hx hy]
    linarith [hS σ, hsup k σ]

  have hmean : (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card (B.KO →+* ℂ)) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul, zero_div]
      linarith
    · have hc : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel_left₀ _ hc]
      exact hG
  refine ⟨⟨Finset.univ.image w, ?_, fun _ => a + b, ?_, hmean⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspanw
  · intro σ g hg
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hg
    exact hbound σ k
  · intro hM hN

    refine ⟨{
        N := N
        w := w
        del := 0
        th' := fun i => Fin.elim0 i
        rz := 0
        alz := fun i => Fin.elim0 i
        th0 := fun i => Fin.elim0 i
        zc := fun i => Fin.elim0 i
        rq := 0
        th := fun i => Fin.elim0 i
        iet := 0
        et := 0
        mx := fun _ => a + b }, ?_⟩
    refine ⟨hspanw, ?_, hN, fun σ k => hbound σ k, hmean⟩
    intro k
    apply hM
    rw [← hspanw]
    exact Submodule.subset_span (Set.mem_range_self k)

end GlobalTheory.ScaledGenerators
