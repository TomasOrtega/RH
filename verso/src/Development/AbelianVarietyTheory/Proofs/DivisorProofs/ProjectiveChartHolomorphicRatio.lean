import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points GlobalTheory.CxPts
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjLoc

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {N : ℕ}

/- English proof (translation)
Establish `hu : u ∈ Set.range (i.appLE (ProjSpace.chart k N a) (i ⁻¹ᵁ ProjSpace.chart k N a) le_rfl).hom`. Take `⟨v, hv⟩` from `i.app_surjective _ (ProjSpace.isAffineOpen_chart k N a) u`. Conclude with `⟨v, by rw [Scheme.Hom.appLE_eq_app]; exact hv⟩`. Rewrite `hu` using `[ZJ.mem_range_appLE_chart_iff]`. Proceed by induction on `hu using Subring.closure_induction with`.

Consider the case `mem x hx`. Break down `hx with ⟨r, rfl⟩ | ⟨j, rfl⟩` into its components or cases. Use `⟨fun _ => valR (spMap σ) ⊤ r, differentiable_const _, fun y hy => ?_⟩` and prove the remaining obligations. Use `(valR_appLE y.1 (i ≫ PSpace.str k N) le_top hy r).trans ?_` and prove the remaining obligations. Rewrite using `[hp, y.2]`.

Conclude with `⟨fun w => w j, differentiable_apply j, fun y _ => rfl⟩`. Consider the case `zero => exact ⟨fun _ => 0, differentiable_const _, fun y hy => by rw [ev_eq hy, map_zero]⟩`. Consider the case `one => exact ⟨fun _ => 1, differentiable_const _, fun y hy => by rw [ev_eq hy, map_one]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨Φ, hΦ, e⟩` from `hx`.

Take `⟨Ψ, hΨ, e'⟩` from `hy`. Conclude with `⟨fun w => Φ w + Ψ w, hΦ.add hΨ, fun z hz => by rw [ev_add, e z hz, e' z hz]⟩`. Consider the case `neg x _ hx`. Take `⟨Φ, hΦ, e⟩` from `hx`. Conclude with `⟨fun w => -Φ w, hΦ.neg, fun z hz => by rw [ev_eq hz, map_neg, ← ev_eq hz, e z hz]⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨Φ, hΦ, e⟩` from `hx`. Take `⟨Ψ, hΨ, e'⟩` from `hy`. Conclude with `⟨fun w => Φ w * Ψ w, hΦ.mul hΨ, fun z hz => by rw [ev_mul, e z hz, e' z hz]⟩`.
-/
theorem exists_entire_of_chart (i : X ⟶ PSpace k N) [IsClosedImmersion i]
    (hp : i ≫ PSpace.str k N = p) (a : Fin (N + 1)) (u : Γ(X, i ⁻¹ᵁ ProjSpace.chart k N a)) :
    ∃ Φ : (Fin (N + 1) → ℂ) → ℂ, Differentiable ℂ Φ ∧ ∀ y ∈ ptsIn p σ (i ⁻¹ᵁ ProjSpace.chart k N a),
      ev p σ _ u y = Φ (fun j => ev p σ _ (ProjSpace.pullRatio i _ a le_rfl j) y) := by
  have hu : u ∈ Set.range (i.appLE (ProjSpace.chart k N a) (i ⁻¹ᵁ ProjSpace.chart k N a) le_rfl).hom := by
    obtain ⟨v, hv⟩ := i.app_surjective _ (ProjSpace.isAffineOpen_chart k N a) u
    exact ⟨v, by rw [Scheme.Hom.appLE_eq_app]; exact hv⟩
  rw [ZJ.mem_range_appLE_chart_iff] at hu
  induction hu using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨r, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨fun _ => valR (spMap σ) ⊤ r, differentiable_const _, fun y hy => ?_⟩
      refine (valR_appLE y.1 (i ≫ PSpace.str k N) le_top hy r).trans ?_
      rw [hp, y.2]
    · exact ⟨fun w => w j, differentiable_apply j, fun y _ => rfl⟩
  | zero => exact ⟨fun _ => 0, differentiable_const _, fun y hy => by rw [ev_eq hy, map_zero]⟩
  | one => exact ⟨fun _ => 1, differentiable_const _, fun y hy => by rw [ev_eq hy, map_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨Φ, hΦ, e⟩ := hx
    obtain ⟨Ψ, hΨ, e'⟩ := hy
    exact ⟨fun w => Φ w + Ψ w, hΦ.add hΨ, fun z hz => by rw [ev_add, e z hz, e' z hz]⟩
  | neg x _ hx =>
    obtain ⟨Φ, hΦ, e⟩ := hx
    exact ⟨fun w => -Φ w, hΦ.neg, fun z hz => by rw [ev_eq hz, map_neg, ← ev_eq hz, e z hz]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Φ, hΦ, e⟩ := hx
    obtain ⟨Ψ, hΨ, e'⟩ := hy
    exact ⟨fun w => Φ w * Ψ w, hΦ.mul hΨ, fun z hz => by rw [ev_mul, e z hz, e' z hz]⟩

/- English proof (translation)
Establish `hU : IsAffineOpen (i ⁻¹ᵁ ProjSpace.chart k N a)` using `(ProjSpace.isAffineOpen_chart k N a).preimage i`. Take `⟨h, hhV, hh⟩` from `hU.exists_basicOpen_le (V := V) ⟨_, mem_ptsIn.1 hxV⟩ (mem_ptsIn.1 hxW)`. Establish `hB : x ∈ ptsIn p σ (X.basicOpen h)` using `mem_ptsIn.2 hh`. Use `hU.isLocalization_basicOpen h` as an intermediate fact. Take `⟨n, g, hg⟩` from `IsLocalization.Away.surj h (resG X hhV f)`.

Establish `hg' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) g` using `hg`. Take `⟨Φg, hΦg, eg⟩` from `exists_entire_of_chart (σ := σ) i hp a g`. Take `⟨Φh, hΦh, eh⟩` from `exists_entire_of_chart (σ := σ) i hp a h`. Establish `hne : Φh (fun j => ev p σ _ (ProjSpace.pullRatio i _ a le_rfl j) x) ≠ 0` using `eh x hxW ▸ (mem_ptsIn_basicOpen hxW h).1 hB`. Use `⟨fun w => Φg w * (Φh w ^ n)⁻¹, (hΦg _).mul (((hΦh _).pow n).inv (pow_ne_zero n hne)), ?_⟩` and prove the remaining obligations.

Use `filter_upwards [(isOpen_ptsIn _).mem_nhds hB] with y hy`. Establish `hyW : y ∈ ptsIn p σ (i ⁻¹ᵁ ProjSpace.chart k N a)` using `ptsIn_mono (X.basicOpen_le h) hy`. Establish `e` using `congrArg (evHom hy) hg'`. Rewrite `e` using `[map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hy, ev_res _ hy, ev_res _ hy]`. Rewrite using `[← eg y hyW, ← eh y hyW]`.

Conclude with `(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n ((mem_ptsIn_basicOpen hyW h).1 hy))).2 e`.
-/
theorem exists_holo_pullRatio (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (N : ℕ) (i : X ⟶ PSpace k N) [IsClosedImmersion i] (hp : i ≫ PSpace.str k N = p)
    (a : Fin (N + 1)) (V : X.Opens) (f : Γ(X, V)) (x : CxPts p σ) (hxV : x ∈ ptsIn p σ V)
    (hxW : x ∈ ptsIn p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a)) :
    ∃ Ψ : (Fin (N + 1) → ℂ) → ℂ, DifferentiableAt ℂ Ψ
      (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) x) ∧
      ∀ᶠ y in 𝓝 x, ev p σ V f y =
        Ψ (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) := by
  have hU : IsAffineOpen (i ⁻¹ᵁ ProjSpace.chart k N a) := (ProjSpace.isAffineOpen_chart k N a).preimage i
  obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, mem_ptsIn.1 hxV⟩ (mem_ptsIn.1 hxW)
  have hB : x ∈ ptsIn p σ (X.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, g, hg⟩ := IsLocalization.Away.surj h (resG X hhV f)
  have hg' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) g := hg
  obtain ⟨Φg, hΦg, eg⟩ := exists_entire_of_chart (σ := σ) i hp a g
  obtain ⟨Φh, hΦh, eh⟩ := exists_entire_of_chart (σ := σ) i hp a h
  have hne : Φh (fun j => ev p σ _ (ProjSpace.pullRatio i _ a le_rfl j) x) ≠ 0 :=
    eh x hxW ▸ (mem_ptsIn_basicOpen hxW h).1 hB
  refine ⟨fun w => Φg w * (Φh w ^ n)⁻¹,
    (hΦg _).mul (((hΦh _).pow n).inv (pow_ne_zero n hne)), ?_⟩
  filter_upwards [(isOpen_ptsIn _).mem_nhds hB] with y hy
  have hyW : y ∈ ptsIn p σ (i ⁻¹ᵁ ProjSpace.chart k N a) := ptsIn_mono (X.basicOpen_le h) hy
  have e := congrArg (evHom hy) hg'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hy, ev_res _ hy, ev_res _ hy] at e
  rw [← eg y hyW, ← eh y hyW]
  exact (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n ((mem_ptsIn_basicOpen hyW h).1 hy))).2 e

end GlobalTheory.ProjLoc
