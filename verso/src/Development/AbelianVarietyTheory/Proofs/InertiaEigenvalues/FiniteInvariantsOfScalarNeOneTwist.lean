import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Introduce `O _ _ _ _ M _ _ e G _ ρ g a ha hg`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hb : a - 1 ≠ 0` using `sub_ne_zero.2 ha`. Take `⟨c, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ`. Establish `hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0`.

Introduce `m`. Establish `hm : ρ g (m : M) = m` using `(Representation.mem_invariants ρ (m : M)).1 m.2 g`. Establish `h1 : (a - 1) • (m : M) = 0`. Rewrite using `[sub_smul, one_smul, ← hg, hm, sub_self]`. Rewrite `h1` using `[hu, mul_smul]`.

Establish `h2` using `congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1`. Simplify using `only [smul_zero, smul_smul] at h2`. Rewrite `h2` using `[← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis. Use `haveI := (lev_pow_card hϖ e c).1`. Use `Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_` and prove the remaining obligations.

Introduce `x y hxy`. Use `congrArg Lev.val hxy` as an intermediate fact. Simplify using `only [Lev.val_mk] at this`. Conclude with `Subtype.ext this`.
-/
theorem finite_invariants_of_smul_ne_one : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  intro O _ _ _ _ M _ _ e G _ ρ g a ha hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : a - 1 ≠ 0 := sub_ne_zero.2 ha
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0 := by
    intro m
    have hm : ρ g (m : M) = m := (Representation.mem_invariants ρ (m : M)).1 m.2 g
    have h1 : (a - 1) • (m : M) = 0 := by
      rw [sub_smul, one_smul, ← hg, hm, sub_self]
    rw [hu, mul_smul] at h1
    have h2 := congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1
    simp only [smul_zero, smul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  haveI := (lev_pow_card hϖ e c).1
  refine Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_
  intro x y hxy
  have := congrArg Lev.val hxy
  simp only [Lev.val_mk] at this
  exact Subtype.ext this

end GlobalTheory.ShapeNeg
