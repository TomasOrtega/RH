import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceProductAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedFibreSections
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace SheetPieceProductAnalytic

def tailL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tailL_apply {d : ℕ} (p : Fin (d + 1) → ℂ) (i : Fin d) : tailL d p i = p i.succ := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `[tailL_apply]`.
-/
theorem tailL_cons {d : ℕ} (a : ℂ) (y : Fin d → ℂ) : tailL d (Fin.cons a y) = y := by
  ext i
  simp [tailL_apply]

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `cases i using Fin.cases <;> simp [tailL_apply]`.
-/
theorem cons_tailL {d : ℕ} (p : Fin (d + 1) → ℂ) : (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ) = p := by
  ext i
  cases i using Fin.cases <;> simp [tailL_apply]

def prodFn {σ : Type} [Fintype σ] (X B U : Set (σ → ℂ)) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (p : Fin (d + 1) → ℂ) : ℂ :=
  ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}, (p 0 - ℓ x)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨p, hp⟩` from `hVne`. Establish `hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)`. Use `continuous_pi fun i => ?_` and prove the remaining obligations.

Consider the cases of `i using Fin.cases`. Simplify using `using continuous_const`. Simplify using `using continuous_apply _`. Establish `hev : δ =ᶠ[𝓝 (tailL d p)] 0`. Establish `hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p)`.

Use `hc.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Use `show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)`. Rewrite using `[cons_tailL]`. Conclude with `hV.mem_nhds hp`. Use `filter_upwards [hmem] with y hy`.

Use `h _ hy` as an intermediate fact. Rewrite `this` using `[tailL_cons]`. Then use the resulting hypothesis. Take `⟨y, hy, hy0⟩` from `hne`. Conclude with `hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)`.
-/
theorem exists_ne_zero_of_open {d : ℕ} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hδ : AnalyticOnNhd ℂ δ D) (hD : IsPreconnected D) (hne : ∃ y ∈ D, δ y ≠ 0)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hVW : V ⊆ tailL d ⁻¹' D) (hVne : V.Nonempty) :
    ∃ p ∈ V, δ (tailL d p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := hVne
  have hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases
    · simpa using continuous_const
    · simpa using continuous_apply _
  have hev : δ =ᶠ[𝓝 (tailL d p)] 0 := by
    have hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)
      rw [cons_tailL]
      exact hV.mem_nhds hp
    filter_upwards [hmem] with y hy
    have := h _ hy
    rwa [tailL_cons] at this
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)

/- English proof (translation)
Take `⟨r, g, hr, -, hrδ, hg, hfib⟩` from `hsec σ X w B d A D δ N hP _ hp₀ hδp₀`. Use `set y₀ := tailL d p₀ with hy₀def`. Establish `hy₀ : y₀ ∈ ball y₀ r` using `mem_ball_self hr`. Establish `hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U)`. Introduce `i`.

Establish `hgc : ContinuousOn (g i) (ball y₀ r)` using `(hg i).continuousOn`. Establish `hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0`. Introduce `y hy`. Establish `hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y}`. Rewrite using `[(hfib y hy).2]`.

Conclude with `⟨i, rfl⟩`. Conclude with `⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩`. Establish `hopU` using `hgc.isOpen_inter_preimage isOpen_ball hU`. Establish `hopV` using `hgc.isOpen_inter_preimage isOpen_ball hV`. Establish `hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V)`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `y ⟨hy, hyU⟩ ⟨-, hyV⟩`. Establish `: g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V)` using `⟨hS y hy, hyU, hyV⟩`. Rewrite `this` using `[hdisj]`. Conclude with `this`.

Establish `hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V)`. Introduce `y hy`. Break down `hcov (hS y hy) with h | h` into its components or cases. Conclude with `Or.inl ⟨hy, h⟩`. Conclude with `Or.inr ⟨hy, h⟩`.

Establish `hc : IsPreconnected (ball y₀ r)` using `(convex_ball y₀ r).isPreconnected`. Introduce `y hy`. Prove the components needed by the constructor for the conclusion. Introduce `hyU`. Assume the negation of the conclusion as `hy0U`.

Establish `hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V` using `(hcv hy₀).resolve_left fun h => hy0U h.2`. Establish `hsub` using `hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩`. Conclude with `Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)`. Introduce `hy0U`. Conclude with `(hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2`.

Use `set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef`. Establish `hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r → prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p)))`. Introduce `p hp`. Establish `hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} = (fun i => g i (tailL d p)) '' (I : Set (Fin N))`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxB, hxU, hxA⟩`. Establish `hx : x ∈ Set.range (fun i => g i (tailL d p))`. Rewrite using `[← (hfib _ hp).2]`. Conclude with `⟨hxB, hxA⟩`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Establish `hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p}`. Rewrite using `[(hfib _ hp).2]`.

Conclude with `⟨i, rfl⟩`. Conclude with `⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩`. Unfold `prodFn`. Rewrite using `[hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]`. Establish `hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p)))`.

Establish `hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀` using `(tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)`. Use `filter_upwards [hmem] with p hp using hrep p hp`. Use `DifferentiableAt.congr_of_eventuallyEq ?_ hev` and prove the remaining obligations. Establish `hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀`. Introduce `i`.

Establish `h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀` using `differentiableAt_apply 0 p₀`. Establish `h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀` using `ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)`. Conclude with `h1.sub h2`. Use `Finset.induction_on I ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `j s hj ih`. Simplify using `only [Finset.prod_insert hj]`. Conclude with `(hfac j).mul ih`.
-/
theorem differentiableAt_prodFn (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by
  classical
  obtain ⟨r, g, hr, -, hrδ, hg, hfib⟩ := hsec σ X w B d A D δ N hP _ hp₀ hδp₀
  set y₀ := tailL d p₀ with hy₀def
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U) := by
    intro i
    have hgc : ContinuousOn (g i) (ball y₀ r) := (hg i).continuousOn
    have hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0 := by
      intro y hy
      have hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y} := by
        rw [(hfib y hy).2]
        exact ⟨i, rfl⟩
      exact ⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩
    have hopU := hgc.isOpen_inter_preimage isOpen_ball hU
    have hopV := hgc.isOpen_inter_preimage isOpen_ball hV
    have hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy, hyU⟩ ⟨-, hyV⟩
      have : g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hS y hy, hyU, hyV⟩
      rw [hdisj] at this
      exact this
    have hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V) := by
      intro y hy
      rcases hcov (hS y hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have hc : IsPreconnected (ball y₀ r) := (convex_ball y₀ r).isPreconnected
    intro y hy
    constructor
    · intro hyU
      by_contra hy0U
      have hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V := (hcv hy₀).resolve_left fun h => hy0U h.2
      have hsub := hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩
      exact Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)
    · intro hy0U
      exact (hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2
  set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef
  have hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r →
      prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    intro p hp
    have hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} =
        (fun i => g i (tailL d p)) '' (I : Set (Fin N)) := by
      ext x
      constructor
      · rintro ⟨hxB, hxU, hxA⟩
        have hx : x ∈ Set.range (fun i => g i (tailL d p)) := by
          rw [← (hfib _ hp).2]
          exact ⟨hxB, hxA⟩
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p} := by
          rw [(hfib _ hp).2]
          exact ⟨i, rfl⟩
        exact ⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩
    unfold prodFn
    rw [hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]
  have hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    have hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀ :=
      (tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)
    filter_upwards [hmem] with p hp using hrep p hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀ := by
    intro i
    have h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀ := differentiableAt_apply 0 p₀
    have h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀ :=
      ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)
    exact h1.sub h2
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro j s hj ih
    simp only [Finset.prod_insert hj]
    exact (hfac j).mul ih

/- English proof (translation)
Take `⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩` from `hP`. Take `⟨ρ, hρ, hρD⟩` from `Metric.isOpen_iff.1 hD _ hp₀`. Use `set y₀ := tailL d p₀ with hy₀def`. Establish `hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)}` using `hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)`. Take `⟨M, hM⟩` from `isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded`.

Use `set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef`. Use `⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩` and prove the remaining obligations. Use `Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_` and prove the remaining obligations. Conclude with `(isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)`. Rewrite using `[isBounded_iff_forall_norm_le]`.

Use `⟨C ^ N, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩`. Establish `hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1` using `hpn`. Establish `hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p}` using `fun x hx => ⟨hx.1, hx.2.2⟩`. Establish `hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N` using `hcard _ hpD hpδ`.

Establish `hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite` using `(Set.finite_of_encard_eq_coe hfin).subset hsub`. Establish `hcardle : hsfin.toFinset.card ≤ N`. Establish `h1` using `Set.encard_le_encard hsub`. Rewrite `h1` using `[hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard]`. Conclude with `h1` after adjusting the coercions.

Establish `hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C`. Introduce `x hx`. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Establish `hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)}` using `⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩`. Establish `hMx` using `hM _ ⟨x, hxK, rfl⟩`.

Combine the equalities or inequalities in the displayed calculation. Unfold `prodFn`. Rewrite using `[finprod_mem_eq_finite_toFinset_prod _ hsfin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isBounded_prodFn {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by
  obtain ⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩ := hP
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD _ hp₀
  set y₀ := tailL d p₀ with hy₀def
  have hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
    hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded
  set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef
  refine ⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩
  · refine Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C ^ N, ?_⟩
  rintro _ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩
  have hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1 := hpn
  have hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p} :=
    fun x hx => ⟨hx.1, hx.2.2⟩
  have hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N := hcard _ hpD hpδ
  have hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite :=
    (Set.finite_of_encard_eq_coe hfin).subset hsub
  have hcardle : hsfin.toFinset.card ≤ N := by
    have h1 := Set.encard_le_encard hsub
    rw [hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
      ⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩
    have hMx := hM _ ⟨x, hxK, rfl⟩
    calc ‖p 0 - ℓ x‖ ≤ ‖p 0‖ + ‖ℓ x‖ := norm_sub_le _ _
      _ ≤ ‖p₀ 0‖ + 1 + M := by linarith
      _ ≤ C := le_max_right _ _
  unfold prodFn
  rw [finprod_mem_eq_finite_toFinset_prod _ hsfin]
  calc ‖∏ x ∈ hsfin.toFinset, (p 0 - ℓ x)‖ ≤ ∏ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _x ∈ hsfin.toFinset, C := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hbd
    _ = C ^ hsfin.toFinset.card := Finset.prod_const C
    _ ≤ C ^ N := pow_le_pow_right₀ (le_max_left _ _) hcardle

end SheetPieceProductAnalytic

open SheetPieceProductAnalytic in

/- English proof (translation)
Introduce `σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj`. Establish `hP'` using `hP`. Take `⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩` from `hP'`. Establish `hW : IsOpen (tailL d ⁻¹' D)` using `hD.preimage (tailL d).continuous`. Establish `hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D)` using `fun p hp => ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt`.

Take `⟨F, hF, hFG⟩` from `RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p)) (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne') (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinA …`. Establish `hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D)` using `RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF`. Establish `hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z` using `fun z => tailL_cons _ _`. Use `⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩` and prove the remaining obligations. Establish `hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D`.

Rewrite using `[Set.mem_preimage, hcons]`. Conclude with `hz`. Establish `hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z`. Rewrite using `[analyticAt_pi_iff]`. Introduce `i`.

Consider the cases of `i using Fin.cases`. Simplify using `using ℓ.analyticAt z`. Name the introduced variables `j`. Simplify using `only [Fin.cons_succ]`. Conclude with `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z`.

Conclude with `AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin`. Establish `hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0}`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, hcons]`. Conclude with `hz`.

Use `show δ (tailL d _) ≠ 0`. Rewrite using `[hcons]`. Conclude with `hδz`. Use `show F _ = _`. Rewrite using `[hFG hm]`.

Simplify using `only [prodFn, hcons, Fin.cons_zero]`.
-/
theorem SheetPieceProductAnalytic.proof (hsec : UnbranchedFibreSections.Statement) :
    SheetPieceProductAnalytic.Statement := by
  intro σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj
  have hP' := hP
  obtain ⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩ := hP'
  have hW : IsOpen (tailL d ⁻¹' D) := hD.preimage (tailL d).continuous
  have hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D) := fun p hp =>
    ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt
  obtain ⟨F, hF, hFG⟩ := RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p))
    (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne')
    (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinAt)
    (fun p hp => isBounded_prodFn U ℓ hP hp)
  have hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D) := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF
  have hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z := fun z => tailL_cons _ _
  refine ⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D := by
      rw [Set.mem_preimage, hcons]
      exact hz
    have hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z := by
      rw [analyticAt_pi_iff]
      intro i
      cases i using Fin.cases
      · simpa using ℓ.analyticAt z
      · rename_i j
        simp only [Fin.cons_succ]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z
    exact AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈
        tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hcons]
        exact hz
      · show δ (tailL d _) ≠ 0
        rw [hcons]
        exact hδz
    show F _ = _
    rw [hFG hm]
    simp only [prodFn, hcons, Fin.cons_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
