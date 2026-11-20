import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[HeckeCharacter.not_dvd_conductor_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Rewrite `ha` using `[Submonoid.mem_units_iff]`. Establish `h1 : Valued.v (a : v.adicCompletion E) ≤ 1` using `ha.1`.

Establish `h2 : Valued.v ((a⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1` using `ha.2`. Establish `h3 : Valued.v (a : v.adicCompletion E) = 1`. Use `le_antisymm h1 ?_` and prove the remaining obligations. Rewrite `h2` using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `(inv_le_one₀ (by simp [zero_lt_iff])).1 h2`.

Rewrite using `[MonoidHom.mem_ker]`. Use `show (toHecke χ hu).localComponent v a = 1`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[coe_localComponent, h a h3]`. Simplify using the standard rewrite rules.

Introduce `h x hx`. Establish `hx' : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units`. Rewrite using `[Submonoid.mem_units_iff]`. Use `⟨le_of_eq hx, ?_⟩` and prove the remaining obligations. Use `show Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1`.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Establish `hx1 : Valued.v (x : v.adicCompletion E) = 1` using `hx`. Rewrite using `[hx1, inv_one]`. Establish `h1 : (toHecke χ hu).localComponent v x = 1` using `MonoidHom.mem_ker.1 (h hx')`. Establish `h2` using `coe_localComponent χ hu v x`.

Rewrite `h2` using `[h1]`. Use `ext`. Simplify using `using h2.symm`.
-/
theorem unrAt_iff_not_dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    χ.UnrAt v ↔ ¬ v.asIdeal ∣ (toHecke χ hu).conductor := by
  rw [HeckeCharacter.not_dvd_conductor_iff]
  constructor
  · intro h a ha
    rw [Submonoid.mem_units_iff] at ha
    have h1 : Valued.v (a : v.adicCompletion E) ≤ 1 := ha.1
    have h2 : Valued.v ((a⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := ha.2
    have h3 : Valued.v (a : v.adicCompletion E) = 1 := by
      refine le_antisymm h1 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      exact (inv_le_one₀ (by simp [zero_lt_iff])).1 h2
    rw [MonoidHom.mem_ker]
    show (toHecke χ hu).localComponent v a = 1
    apply Circle.ext
    rw [coe_localComponent, h a h3]
    simp
  · intro h x hx
    have hx' : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
      rw [Submonoid.mem_units_iff]
      refine ⟨le_of_eq hx, ?_⟩
      show Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      have hx1 : Valued.v (x : v.adicCompletion E) = 1 := hx
      rw [hx1, inv_one]
    have h1 : (toHecke χ hu).localComponent v x = 1 := MonoidHom.mem_ker.1 (h hx')
    have h2 := coe_localComponent χ hu v x
    rw [h1] at h2
    ext
    simpa using h2.symm

/- English proof (translation)
Rewrite using `[(toHecke χ hu).coeff_asIdeal_eq_toIdele hv (unif_spec v), ← HeckeCharacter.localComponent_apply, coe_localComponent]`. Both sides reduce to the same expression.
-/
theorem coeff_eq_val (χ : HChar E) (hu : IsUnitary χ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor) :
    (toHecke χ hu).coeff v.asIdeal = (χ.val v : ℂ) := by
  rw [(toHecke χ hu).coeff_asIdeal_eq_toIdele hv (unif_spec v), ← HeckeCharacter.localComponent_apply,
    coe_localComponent]
  rfl

/- English proof (translation)
Introduce `E _ _ χ hu s hs`. Establish `h : eulerFactor χ s = fun v : HeightOneSpectrum (𝓞 E) ↦ (1 - (toHecke χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹`. Use function extensionality and compare the values at `v`. Unfold `eulerFactor`. Distinguish the cases in `hv : χ.UnrAt v`.

Rewrite using `[if_pos hv, coeff_eq_val χ hu ((unrAt_iff_not_dvd_conductor χ hu v).1 hv)]`. Rewrite using `[if_neg hv, HeckeCharacter.coeff_asIdeal_of_dvd _ (not_not.1 (mt (unrAt_iff_not_dvd_conductor χ hu v).2 hv))]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `(toHecke χ hu).LFunction_hasProd_all hs`.
-/
theorem hasProd_eulerFactor_toHecke : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ),
    1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  intro E _ _ χ hu s hs
  have h : eulerFactor χ s = fun v : HeightOneSpectrum (𝓞 E) ↦
      (1 - (toHecke χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
    funext v
    unfold eulerFactor
    by_cases hv : χ.UnrAt v
    · rw [if_pos hv, coeff_eq_val χ hu ((unrAt_iff_not_dvd_conductor χ hu v).1 hv)]
    · rw [if_neg hv, HeckeCharacter.coeff_asIdeal_of_dvd _
        (not_not.1 (mt (unrAt_iff_not_dvd_conductor χ hu v).2 hv))]
      simp
  rw [h]
  exact (toHecke χ hu).LFunction_hasProd_all hs

end GlobalTheory.CompanionTheory.HeckeBridge
