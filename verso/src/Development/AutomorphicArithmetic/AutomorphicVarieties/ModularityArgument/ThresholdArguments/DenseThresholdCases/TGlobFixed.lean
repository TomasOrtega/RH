import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix
namespace UpperTheory.V.Af.GlobalFixedVectors
variable {F : Type} [Field F] [NumberField F] {n M : ℕ}
end UpperTheory.V.Af.GlobalFixedVectors
open UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors in
/- English proof (translation)
Introduce `_ F _ _ n M _ V _ _ ρ hρ h`. Establish `key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact id`.

Consider the case `insert w S hw ih`. Introduce and unpack `⟨v, hv0, hv⟩`. Take `⟨σ, ⟨-, hσ⟩, hfix⟩` from `h w`. Set `W : Submodule ℂ V` to `⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)`. Establish `hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x` using `fun x => by`.

Simplify using `[W, Submodule.mem_iInf, sub_eq_zero]`. Take `⟨x, hxW, hx0, hx⟩` from `sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by`. Establish `e : k * locGL F n w g = locGL F n w g * k` using `gl_ext fun u => by`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality.

Simplify using `[(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]`. Simplify using `[pLoc_locGL_of_ne hu]`. Express the relevant statement in the definitionally equal form `ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])`. Use the proof step `(fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix`.

Use `ih ⟨x, hx0, fun k hk => ?_⟩` and prove the remaining obligations. Establish `h1` using `loc_mem w (mem_KAway.1 hk).1`. Establish `h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S)`. Use `mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩` and prove the remaining obligations. Distinguish the cases in `huw : u = w`.

Substitute `huw` using the available equality. Simplify using `[pLoc_locGL]`. Simplify using `[pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]`. Establish `h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x` using `hx _ h1`. Establish `h4` using `(hWm x).1 hxW _ h2`.

Rewrite `h4` using `[← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩`. Take `⟨σ, ⟨hV, -⟩, -⟩` from `h w`.

Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Take `⟨S, hS⟩` from `exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))`. Take `⟨x, hx0, hx⟩` from `key S ⟨v, hv, fun k hk => hS hk⟩`. Conclude with `⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩`.
-/
theorem UpperTheory.V.Af.globFixed_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.GlobFixed := by
  classical
  intro _ F _ _ n M _ V _ _ ρ hρ h
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hv0, hv⟩
      obtain ⟨σ, ⟨-, hσ⟩, hfix⟩ := h w
      let W : Submodule ℂ V := ⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)
      have hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x := fun x => by
        simp [W, Submodule.mem_iInf, sub_eq_zero]
      obtain ⟨x, hxW, hx0, hx⟩ := sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by
        have e : k * locGL F n w g = locGL F n w g * k := gl_ext fun u => by
          by_cases hu : u = w
          · subst hu; simp [(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]
          · simp [pLoc_locGL_of_ne hu]
        change ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])
        (fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix
      refine ih ⟨x, hx0, fun k hk => ?_⟩
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hx _ h1
      have h4 := (hWm x).1 hxW _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨σ, ⟨hV, -⟩, -⟩ := h w
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))
  obtain ⟨x, hx0, hx⟩ := key S ⟨v, hv, fun k hk => hS hk⟩
  exact ⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩
end
