import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.ProjectiveReduction

open NumberField

namespace PI.SRW

/- English proof (translation)
Introduce `E V _ _ _ _ _ _ Λ N hNΛ hfg hsat`. Set `N' : Submodule (𝓞 E) Λ` to `N.comap Λ.subtype`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Finite (𝓞 E) (Λ ⧸ N') := inferInstance`. Use `haveI : NoZeroSMulDivisors (𝓞 E) (Λ ⧸ N') := by`.

Use `⟨fun {o q} hq => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ho : o = 0`. Conclude with `Or.inl ho`. Use `right`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective N' q`.

Rewrite `hq` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hsat o x ho x.2 hq`. Use `haveI : Module.Projective (𝓞 E) (Λ ⧸ N') := PI.FGTFG.projective_reduction (𝓞 E) (Λ ⧸ N')`. Take `⟨s, hs⟩` from `Module.projective_lifting_property N'.mkQ LinearMap.id (Submodule.mkQ_surjective N')`.

Set `ρ' : Λ →ₗ[𝓞 E] Λ` to `LinearMap.id - s.comp N'.mkQ`. Establish `hρ' : ∀ x : Λ, ρ' x ∈ N'`. Introduce `x`. Establish `h1 : N'.mkQ (ρ' x) = 0`. Establish `h2` using `LinearMap.congr_fun hs (N'.mkQ x)`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h2`. Use `show N'.mkQ (x - s (N'.mkQ x)) = 0`. Rewrite using `[map_sub, h2, sub_self]`. Simplify `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `⟨Λ.subtype.comp ρ', fun x => hρ' x, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hx' : x ∈ N'` using `hx`. Establish `h0 : N'.mkQ x = 0` using `by simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'`. Simplify using `[ρ', h0]`.
-/
theorem retraction_reduction : RetrStep := by
  intro E V _ _ _ _ _ _ Λ N hNΛ hfg hsat
  let N' : Submodule (𝓞 E) Λ := N.comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite (𝓞 E) (Λ ⧸ N') := inferInstance
  haveI : NoZeroSMulDivisors (𝓞 E) (Λ ⧸ N') := by
    refine ⟨fun {o q} hq => ?_⟩
    by_cases ho : o = 0
    · exact Or.inl ho
    right
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N' q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hsat o x ho x.2 hq
  haveI : Module.Projective (𝓞 E) (Λ ⧸ N') := PI.FGTFG.projective_reduction (𝓞 E) (Λ ⧸ N')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id (Submodule.mkQ_surjective N')
  let ρ' : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s.comp N'.mkQ
  have hρ' : ∀ x : Λ, ρ' x ∈ N' := by
    intro x
    have h1 : N'.mkQ (ρ' x) = 0 := by
      have h2 := LinearMap.congr_fun hs (N'.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
      show N'.mkQ (x - s (N'.mkQ x)) = 0
      rw [map_sub, h2, sub_self]
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  refine ⟨Λ.subtype.comp ρ', fun x => hρ' x, fun x hx => ?_⟩
  have hx' : x ∈ N' := hx
  have h0 : N'.mkQ x = 0 := by simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'
  simp [ρ', h0]

end PI.SRW
