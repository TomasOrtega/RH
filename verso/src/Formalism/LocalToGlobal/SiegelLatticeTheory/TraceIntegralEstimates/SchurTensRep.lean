import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def IsTensAbs (σ : ∀ v, G v → (H v →L[ℂ] H v)) (σs : (∀ v, G v) → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) : Prop :=
  (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) ∧ (∀ g x, σs g (tens x) = tens fun v => σ v (g v) (x v)) ∧
    Dense (Submodule.span ℂ (Set.range tens) : Set Hs)

variable {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Use `set F : (∀ v, H v) → ℝ := fun x => RCLike.re (∏ v, ⟪x v, x v⟫_ℂ) - 2 * RCLike.re (∏ v, ⟪x v, x0 v⟫_ℂ) + RCLike.re (∏ v, ⟪x0 v, x0 v⟫_ℂ) with hF`. Establish `hFc : Continuous F` using `by fun_prop`. Establish `hnorm : ∀ x, ‖tens x - tens x0‖ = Real.sqrt (F x)`.

Introduce `x`. Rewrite using `[← Real.sqrt_sq (norm_nonneg _), norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), h.1, h.1, h.1]`. Establish `hF0 : F x0 = 0` using `by simp only [hF]; ring`. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`. Repeatedly rewrite using `[hnorm]`.

Establish `h2 : Tendsto (fun x => Real.sqrt (F x)) (𝓝 x0) (𝓝 (Real.sqrt (F x0)))` using `(Real.continuous_sqrt.comp hFc).tendsto x0`. Rewrite `h2` using `[hF0, Real.sqrt_zero]`. Conclude with `h2`.
-/
theorem continuous_tens (h : IsTensAbs σ σs tens) : Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x0
  set F : (∀ v, H v) → ℝ := fun x => RCLike.re (∏ v, ⟪x v, x v⟫_ℂ) -
    2 * RCLike.re (∏ v, ⟪x v, x0 v⟫_ℂ) + RCLike.re (∏ v, ⟪x0 v, x0 v⟫_ℂ) with hF
  have hFc : Continuous F := by fun_prop
  have hnorm : ∀ x, ‖tens x - tens x0‖ = Real.sqrt (F x) := by
    intro x
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      norm_sq_eq_re_inner (𝕜 := ℂ), h.1, h.1, h.1]
  have hF0 : F x0 = 0 := by simp only [hF]; ring
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have h2 : Tendsto (fun x => Real.sqrt (F x)) (𝓝 x0) (𝓝 (Real.sqrt (F x0))) :=
    (Real.continuous_sqrt.comp hFc).tendsto x0
  rw [hF0, Real.sqrt_zero] at h2
  exact h2

/- English proof (translation)
Establish `hS : ∀ b ∈ Submodule.span ℂ (Set.range tens), ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨y, rfl⟩` from `hb`.

Rewrite using `[h.2.1, h.2.1, h.1, h.1]`. Conclude with `Finset.prod_congr rfl fun v _ => (hσ v).2.2.1 (g v) (x v) (y v)`. Consider the case `zero => simp`. Consider the case `add b c _ _ hb hc => rw [map_add, inner_add_right, inner_add_right, hb, hc]`. Consider the case `smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]`.

Establish `hcl : IsClosed {b : Hs | ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ}` using `isClosed_eq (continuous_const.inner (σs g).continuous) (continuous_const.inner continuous_id)`. Establish `hsub` using `closure_minimal (fun b hb => hS b hb) hcl`. Rewrite `hsub` using `[h.2.2.closure_eq]`. Conclude with `hsub (Set.mem_univ a)`.
-/
theorem tens_unit (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a : Hs) (x : ∀ v, H v) :
    ⟪σs g (tens x), σs g a⟫_ℂ = ⟪tens x, a⟫_ℂ := by
  have hS : ∀ b ∈ Submodule.span ℂ (Set.range tens), ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      rw [h.2.1, h.2.1, h.1, h.1]
      exact Finset.prod_congr rfl fun v _ => (hσ v).2.2.1 (g v) (x v) (y v)
    | zero => simp
    | add b c _ _ hb hc => rw [map_add, inner_add_right, inner_add_right, hb, hc]
    | smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]
  have hcl : IsClosed {b : Hs | ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ} :=
    isClosed_eq (continuous_const.inner (σs g).continuous) (continuous_const.inner continuous_id)
  have hsub := closure_minimal (fun b hb => hS b hb) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

/- English proof (translation)
Establish `hS : ∀ c ∈ Submodule.span ℂ (Set.range tens), ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ`. Introduce `c hc`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc`. Take `⟨x, rfl⟩` from `hc`.

Conclude with `tens_unit hσ h g b x`. Consider the case `zero => simp`. Consider the case `add c d _ _ hc hd => rw [map_add, inner_add_left, inner_add_left, hc, hd]`. Consider the case `smul t c _ hc => rw [map_smul, inner_smul_left, inner_smul_left, hc]`. Establish `hcl : IsClosed {c : Hs | ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ}` using `isClosed_eq ((σs g).continuous.inner continuous_const) (continuous_id.inner continuous_const)`.

Establish `hsub` using `closure_minimal (fun c hc => hS c hc) hcl`. Rewrite `hsub` using `[h.2.2.closure_eq]`. Conclude with `hsub (Set.mem_univ a)`.
-/
theorem tens_unit_all (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a b : Hs) :
    ⟪σs g a, σs g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  have hS : ∀ c ∈ Submodule.span ℂ (Set.range tens), ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, rfl⟩ := hc
      exact tens_unit hσ h g b x
    | zero => simp
    | add c d _ _ hc hd => rw [map_add, inner_add_left, inner_add_left, hc, hd]
    | smul t c _ hc => rw [map_smul, inner_smul_left, inner_smul_left, hc]
  have hcl : IsClosed {c : Hs | ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ} :=
    isClosed_eq ((σs g).continuous.inner continuous_const) (continuous_id.inner continuous_const)
  have hsub := closure_minimal (fun c hc => hS c hc) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

/- English proof (translation)
Establish `hnorm : ∀ g c, ‖σs g c‖ = ‖c‖`. Introduce `g c`. Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tens_unit_all hσ h g c c]`. Establish `hspan : ∀ b ∈ Submodule.span ℂ (Set.range tens), Continuous fun g => σs g b`. Introduce `b hb`.

Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨x, rfl⟩` from `hb`. Establish `e : (fun g => σs g (tens x)) = fun g => tens (fun v => σ v (g v) (x v))`. Use function extensionality and compare the values at `fun g => h.2.1 g x`.

Rewrite using `[e]`. Conclude with `(continuous_tens h).comp (continuous_pi fun v => ((hσ v).2.2.2 (x v)).comp (continuous_apply v))`. Consider the case `zero => simp only [map_zero]`. Conclude with `continuous_const`. Consider the case `add b c _ _ hb hc => simp only [map_add]`.

Conclude with `hb.add hc`. Consider the case `smul t b _ hb => simp only [map_smul]`. Conclude with `hb.const_smul t`. Use `⟨?_, ?_, fun g a b => tens_unit_all hσ h g a b, ?_⟩` and prove the remaining obligations. Apply `ContinuousLinearMap.ext_on h.2.2` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[h.2.1]`. Simplify using `only [ContinuousLinearMap.one_apply]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Use `show σ v 1 (x v) = x v`. Rewrite using `[(hσ v).1]`. Both sides reduce to the same expression. Introduce `g g'`. Apply `ContinuousLinearMap.ext_on h.2.2` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[ContinuousLinearMap.mul_apply, h.2.1, h.2.1, h.2.1]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Use `show σ v (g v * g' v) (x v) = σ v (g v) (σ v (g' v) (x v))`.

Rewrite using `[(hσ v).2.1]`. Both sides reduce to the same expression. Introduce `a`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g0`.

Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨b, hb, hab⟩` from `h.2.2.exists_dist_lt a (by positivity : (0 : ℝ) < ε / 3)`. Establish `hc` using `Metric.tendsto_nhds.mp ((hspan b hb).tendsto g0) (ε / 3) (by positivity)`. Use `filter_upwards [hc] with g hg`.

Establish `h1 : dist (σs g a) (σs g b) = dist a b`. Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]`. Establish `h2 : dist (σs g0 b) (σs g0 a) = dist a b`. Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, norm_sub_rev]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isUnitRep_tens (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) : IsUnitRep σs := by
  have hnorm : ∀ g c, ‖σs g c‖ = ‖c‖ := by
    intro g c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tens_unit_all hσ h g c c]
  have hspan : ∀ b ∈ Submodule.span ℂ (Set.range tens), Continuous fun g => σs g b := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨x, rfl⟩ := hb
      have e : (fun g => σs g (tens x)) = fun g => tens (fun v => σ v (g v) (x v)) :=
        funext fun g => h.2.1 g x
      rw [e]
      exact (continuous_tens h).comp (continuous_pi fun v => ((hσ v).2.2.2 (x v)).comp (continuous_apply v))
    | zero => simp only [map_zero]; exact continuous_const
    | add b c _ _ hb hc => simp only [map_add]; exact hb.add hc
    | smul t b _ hb => simp only [map_smul]; exact hb.const_smul t
  refine ⟨?_, ?_, fun g a b => tens_unit_all hσ h g a b, ?_⟩
  · apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [h.2.1]
    simp only [ContinuousLinearMap.one_apply]
    congr 1
    funext v
    show σ v 1 (x v) = x v
    rw [(hσ v).1]
    rfl
  · intro g g'
    apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.mul_apply, h.2.1, h.2.1, h.2.1]
    congr 1
    funext v
    show σ v (g v * g' v) (x v) = σ v (g v) (σ v (g' v) (x v))
    rw [(hσ v).2.1]
    rfl
  · intro a
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hab⟩ := h.2.2.exists_dist_lt a (by positivity : (0 : ℝ) < ε / 3)
    have hc := Metric.tendsto_nhds.mp ((hspan b hb).tendsto g0) (ε / 3) (by positivity)
    filter_upwards [hc] with g hg
    have h1 : dist (σs g a) (σs g b) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]
    have h2 : dist (σs g0 b) (σs g0 a) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, norm_sub_rev]
    calc dist (σs g a) (σs g0 a)
        ≤ dist (σs g a) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 a) :=
          dist_triangle4 _ _ _ _
      _ < ε := by rw [h1, h2]; linarith

end Formalism.L2.S.Pv.SchurTens
