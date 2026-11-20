import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLocApprox

/- English proof (translation)
Distinguish the cases in `hv : Integrable v μ`. Use `swap`. Conclude with `integral_undef hv`. Establish `key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ` using `fun ε hε => by`. Take `⟨u, hu, h0, hn⟩` from `h ε hε`.

Establish `e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ` using `by rw [integral_sub hu hv, h0, zero_sub]`. Rewrite using `[← norm_neg, ← e, ← integral_const_mul]`. Conclude with `norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)`. Establish `t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ))` using `((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds`. Rewrite `t` using `[zero_mul]`.

Conclude with `norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))`.
-/
theorem integral_eq_zero_of_forall_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {v : X → ℂ} {w : X → ℝ}
    (hw : Integrable w μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : X → ℂ, Integrable u μ ∧ ∫ x, u x ∂μ = 0 ∧ ∀ x, ‖u x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  by_cases hv : Integrable v μ
  swap
  · exact integral_undef hv
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨u, hu, h0, hn⟩ := h ε hε
    have e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub hu hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

variable {D : D7} {V : HSp D}

def LocApprox (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (ψ : Fin n → GA D V → ℂ),
    (∀ l, Continuous (ψ l) ∧ (∀ γ ∈ GQ V, ∀ g, ψ l (γ * g) = ψ l g) ∧ IsCuspFun V (ψ l)) ∧
    ∀ x ∈ C, ‖f x - ∑ l, ψ l x‖ < ε

/- English proof (translation)
Introduce `γ hγ g`. Use `eq_of_forall_dist_le fun ε hε => ?_` and prove the remaining obligations. Take `⟨n, ψ, hψ, happ⟩` from `h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)`. Establish `e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g` using `Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g`. Establish `h1` using `happ (γ * g) (by simp)`.

Establish `h2` using `happ g (by simp)`. Rewrite using `[dist_eq_norm]`. Establish `e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g)` using `by rw [e]; ring`. Rewrite using `[e']`. Combine the linear relations using `[norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]`.
-/
theorem leftInv_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := by
  intro γ hγ g
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, ψ, hψ, happ⟩ := h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)
  have e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g := Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g
  have h1 := happ (γ * g) (by simp)
  have h2 := happ g (by simp)
  rw [dist_eq_norm]
  have e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g) := by rw [e]; ring
  rw [e']
  linarith [norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]

/- English proof (translation)
Establish `hl` using `leftInv_of_locApprox h`. Rewrite `hl` using `[GlobalTheory.AutFunCompare.GQ_eq]`. Rewrite using `[GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]`. Introduce `W hW μ hμ 𝓕 h𝓕 g`. Establish `hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) → IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ`.

Introduce `φ hc hl'`. Rewrite `hl'` using `[GlobalTheory.AutFunCompare.GQ_eq]`. Conclude with `GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g`. Take `⟨K, hK, hKs⟩` from `GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW`. Establish `: IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)` using `⟨rfl⟩`.

Establish `: IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Establish `: IsTopologicalGroup (GA D V)` using `inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`. Establish `hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g` using `continuous_subtype_val.mul continuous_const`. Establish `hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕)`. Simplify using `using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm`.

Use `integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_` and prove the remaining obligations. Take `⟨m, ψ, hψ, happ⟩` from `h _ (hK.image hcont) ε hε`. Use `⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]`. Conclude with `Finset.sum_eq_zero fun l _ => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g`.

Take `⟨γ, hγ, hk⟩` from `hKs n`. Establish `e1 : f (n.1 * g) = f ((γ * n).1 * g)`. Rewrite using `[Subgroup.coe_mul, mul_assoc]`. Conclude with `(hl _ hγ _).symm`. Establish `e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g)` using `fun l => by`.

Establish `hl'` using `(hψ l).2.1`. Rewrite `hl'` using `[GlobalTheory.AutFunCompare.GQ_eq]`. Rewrite using `[Subgroup.coe_mul, mul_assoc]`. Conclude with `(hl' _ hγ _).symm`. Use `show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1`.

Rewrite using `[e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]`. Conclude with `(happ _ ⟨_, hk, rfl⟩).le`.
-/
theorem isCuspFun_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : IsCuspFun V f := by
  have hl := leftInv_of_locApprox h
  rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) →
      IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl'
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g :=
    continuous_subtype_val.mul continuous_const
  have hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕) := by
    simpa using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm
  refine integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_
  obtain ⟨m, ψ, hψ, happ⟩ := h _ (hK.image hcont) ε hε
  refine ⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_,
    fun n => ?_⟩
  · rw [integral_finset_sum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]
    exact Finset.sum_eq_zero fun l _ =>
      (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g
  · obtain ⟨γ, hγ, hk⟩ := hKs n
    have e1 : f (n.1 * g) = f ((γ * n).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl _ hγ _).symm
    have e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g) := fun l => by
      have hl' := (hψ l).2.1
      rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl' _ hγ _).symm
    show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1
    rw [e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]
    exact (happ _ ⟨_, hk, rfl⟩).le

end GlobalTheory.CuspLocApprox

end
