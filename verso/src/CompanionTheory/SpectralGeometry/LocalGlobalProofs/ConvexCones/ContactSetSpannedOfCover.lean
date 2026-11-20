import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDefStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMemStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupportStatement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

/- English proof (translation)
Establish `e : ∀ x : X, r (y + (x + x)) = r y + (r x + r x)` using `fun x => by rw [map_add, map_add]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Take `⟨x, rfl⟩` from `hr x`. Use `h x` as an intermediate fact.

Simplify using `only [pullR_apply, e] at this`. Conclude with `this`. Introduce `h x`. Simplify using `only [pullR_apply, e]`. Conclude with `h (r x)`.
-/
theorem isMin2_pullR_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (y : X) :
    IsMin2 (pullR r B) y ↔ IsMin2 B (r y) := by
  have e : ∀ x : X, r (y + (x + x)) = r y + (r x + r x) := fun x => by rw [map_add, map_add]
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := hr x
    have := h x
    simp only [pullR_apply, e] at this
    exact this
  · intro h x
    simp only [pullR_apply, e]
    exact h (r x)

/- English proof (translation)
Assemble the required witnesses or components as `⟨pullR_mem_psdCone hr h.1, fun i => (isMin2_pullR_iff hr B (a i)).2 (h.2 i)⟩`.
-/
theorem pullR_mem_contact {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (h : B ∈ contact bar fun i => r (a i)) : pullR r B ∈ contact bar a :=
  ⟨pullR_mem_psdCone hr h.1, fun i => (isMin2_pullR_iff hr B (a i)).2 (h.2 i)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hB, fun i => (isMin2_pullR_iff hr B (a i)).1 (h.2 i)⟩`.
-/
theorem mem_contact_of_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (hB : B ∈ psdCone bar X₁) (h : pullR r B ∈ contact bar a) : B ∈ contact bar fun i => r (a i) :=
  ⟨hB, fun i => (isMin2_pullR_iff hr B (a i)).1 (h.2 i)⟩

end Pull

/- English proof (translation)
Introduce `O _ _ _ _ bar red X _ _ _ _ ι _ a ha`. Establish `hadd : ∀ B ∈ contact bar a, ∀ B' ∈ contact bar a, B + B' ∈ contact bar a` using `fun B hB B' hB' => ⟨GlobalTheory.T.psd_cone_add_mem O bar X B B' hB.1 hB'.1, fun i x => by`. Establish `h1` using `hB.2 i x`. Establish `h2` using `hB'.2 i x`. Simplify using `only [LinearMap.add_apply]`.

Conclude with `add_le_add h1 h2⟩`. Take `⟨B₁, hB₁, hrad⟩` from `GlobalTheory.T.psd_cone_exists_maximal_support O bar X (contact bar a) ⟨0, zero_mem_contact bar a⟩ (fun B hB => hB.1) hadd`. Take `⟨X₁, _, _, _, r, B₁', hr, hbal, hdef, hfac⟩` from `id hB₁.1`. Establish `: Module.Finite O X₁` using `Module.Finite.of_surjective r hr`. Establish `hfac' : B₁ = pullR r B₁'` using `LinearMap.ext₂ hfac`.

Establish `hB₁' : B₁' ∈ contact bar fun i => r (a i)` using `mem_contact_of_pullR hr (hdef.mem_psdCone hbal) (hfac' ▸ hB₁)`. Establish `hcov : Covers2 fun i => r (a i)` using `fun y => by`. Take `⟨y, rfl⟩` from `hr y`. Take `⟨i, x, rfl⟩` from `ha y`. Conclude with `⟨i, r x, by rw [map_add, map_add]⟩`.

Take `⟨m, γ, hγ, hnn, hK, hsub⟩` from `GlobalTheory.T.contact_set_spans_of_pos_def O bar X₁ ι (fun i => r (a i)) (red X₁) hcov ⟨B₁', hB₁', hdef⟩`. Use `⟨m, fun i => pull r (γ i), fun i => pull_mem r (hγ i), fun i y => hnn i (r y), fun i => ?_, fun B hB => ?_⟩` and prove the remaining obligations. Establish `e : toReal (pull r (γ i)) = pullR r (toReal (γ i))` using `LinearMap.ext₂ fun _ _ => by simp`. Rewrite using `[e]`. Conclude with `pullR_mem_contact hr (hK i)`.

Establish `hker : ∀ y, r y = 0 → B y y = 0` using `fun y hy => hrad B hB y (by rw [hfac, hy]; simp)`. Take `⟨B', hB', rfl⟩` from `GlobalTheory.T.psd_cone_descends_along_surjection O bar X X₁ r B hr hB.1 hker`. Take `⟨t, ht, e⟩` from `hsub (mem_contact_of_pullR hr hB' hB)`. Use `⟨t, ht, LinearMap.ext₂ fun y z => ?_⟩` and prove the remaining obligations. Simplify using `[e, LinearMap.sum_apply]`.
-/
theorem isSpanned_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
      Covers2 a → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar red X _ _ _ _ ι _ a ha
  have hadd : ∀ B ∈ contact bar a, ∀ B' ∈ contact bar a, B + B' ∈ contact bar a := fun B hB B' hB' =>
    ⟨GlobalTheory.T.psd_cone_add_mem O bar X B B' hB.1 hB'.1, fun i x => by
      have h1 := hB.2 i x
      have h2 := hB'.2 i x
      simp only [LinearMap.add_apply]
      exact add_le_add h1 h2⟩
  obtain ⟨B₁, hB₁, hrad⟩ := GlobalTheory.T.psd_cone_exists_maximal_support O bar X (contact bar a) ⟨0, zero_mem_contact bar a⟩ (fun B hB => hB.1) hadd
  obtain ⟨X₁, _, _, _, r, B₁', hr, hbal, hdef, hfac⟩ := id hB₁.1
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  have hfac' : B₁ = pullR r B₁' := LinearMap.ext₂ hfac
  have hB₁' : B₁' ∈ contact bar fun i => r (a i) :=
    mem_contact_of_pullR hr (hdef.mem_psdCone hbal) (hfac' ▸ hB₁)
  have hcov : Covers2 fun i => r (a i) := fun y => by
    obtain ⟨y, rfl⟩ := hr y
    obtain ⟨i, x, rfl⟩ := ha y
    exact ⟨i, r x, by rw [map_add, map_add]⟩
  obtain ⟨m, γ, hγ, hnn, hK, hsub⟩ :=
    GlobalTheory.T.contact_set_spans_of_pos_def O bar X₁ ι (fun i => r (a i)) (red X₁) hcov ⟨B₁', hB₁', hdef⟩
  refine ⟨m, fun i => pull r (γ i), fun i => pull_mem r (hγ i), fun i y => hnn i (r y), fun i => ?_, fun B hB => ?_⟩
  · have e : toReal (pull r (γ i)) = pullR r (toReal (γ i)) := LinearMap.ext₂ fun _ _ => by simp
    rw [e]
    exact pullR_mem_contact hr (hK i)
  · have hker : ∀ y, r y = 0 → B y y = 0 := fun y hy => hrad B hB y (by rw [hfac, hy]; simp)
    obtain ⟨B', hB', rfl⟩ := GlobalTheory.T.psd_cone_descends_along_surjection O bar X X₁ r B hr hB.1 hker
    obtain ⟨t, ht, e⟩ := hsub (mem_contact_of_pullR hr hB' hB)
    refine ⟨t, ht, LinearMap.ext₂ fun y z => ?_⟩
    simp [e, LinearMap.sum_apply]

end GlobalTheory.CompanionTheory.Ar.Fan
