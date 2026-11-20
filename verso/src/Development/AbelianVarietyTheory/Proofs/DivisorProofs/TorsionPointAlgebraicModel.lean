import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

/- English proof (translation)
Introduce `A₀ _ A _ p g n hA₀ hg hp hn x hx`. Use `set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht`. Establish `hM` using `GlobalTheory.abMulN_holds`. Establish `: IsAlgClosed Qb` using `(algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed`. Establish `hSub : Subsingleton (Sp Qb)` using `inferInstanceAs (Subsingleton (PrimeSpectrum Qb))`.

Establish `: Flat t` using `inferInstance`. Establish `: Surjective t` using `⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩`. Establish `: Epi t` using `Flat.epi_of_flat_of_surjective _`. Establish `hA : IsAbelianScheme A` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp`. Establish `hdim : SmoothOfRelativeDimension g A.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg`.

Take `⟨e, he⟩` from `GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm`. Establish `hnQ : ((n : ℕ) : Qb) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hnC : ((n : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h₁` using `hM Qb A₀ g n hA₀ hg hnQ`. Establish `h₂` using `hM ℂ A g n hA hdim hnC`.

Establish `hl : (toUnit (Over.mk t)).left = t` using `by simpa using Over.w (toUnit (Over.mk t))`. Set `r : {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1} → {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1}` to `fun c => ⟨e.symm (toUnit (Over.mk t) ≫ c.1), by`. Express the relevant statement in the definitionally equal form `e.symm _ ^ n = 1`. Rewrite using `[← map_pow, ← MonObj.comp_pow, c.2, MonObj.comp_one, map_one]⟩`. Establish `hr : Function.Injective r` using `fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by`.

Establish `h'` using `congrArg (fun q => (e q.1).left) h`. Simplify `h')))` using `only [r, MulEquiv.apply_symm_apply, Over.comp_left, hl]`. Establish `: Finite {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1}` using `GlobalTheory.Published.AbMulNSt.finite hM hA hdim hnC`. Take `⟨c, hc⟩` from `((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₁.trans h₂.symm⟩).2 ⟨x, hx⟩`. Use `⟨c.1, ?_⟩` and prove the remaining obligations.

Establish `h3 : e x = toUnit (Over.mk t) ≫ c.1`. Establish `hx' : e.symm (toUnit (Over.mk t) ≫ c.1) = x` using `congrArg Subtype.val hc`. Rewrite using `[← hx', MulEquiv.apply_symm_apply]`. Rewrite using `[← he x, h3, Over.comp_left, hl]`.
-/
theorem torsion_of_complex_is_algebraic : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  intro A₀ _ A _ p g n hA₀ hg hp hn x hx
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hM := GlobalTheory.abMulN_holds
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hdim : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h₁ := hM Qb A₀ g n hA₀ hg hnQ
  have h₂ := hM ℂ A g n hA hdim hnC
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1} → {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := fun c =>
    ⟨e.symm (toUnit (Over.mk t) ≫ c.1), by
      change e.symm _ ^ n = 1
      rw [← map_pow, ← MonObj.comp_pow, c.2, MonObj.comp_one, map_one]⟩
  have hr : Function.Injective r := fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by
    have h' := congrArg (fun q => (e q.1).left) h
    simpa only [r, MulEquiv.apply_symm_apply, Over.comp_left, hl] using h')))
  have : Finite {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := GlobalTheory.Published.AbMulNSt.finite hM hA hdim hnC
  obtain ⟨c, hc⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₁.trans h₂.symm⟩).2 ⟨x, hx⟩
  refine ⟨c.1, ?_⟩
  have h3 : e x = toUnit (Over.mk t) ≫ c.1 := by
    have hx' : e.symm (toUnit (Over.mk t) ≫ c.1) = x := congrArg Subtype.val hc
    rw [← hx', MulEquiv.apply_symm_apply]
  rw [← he x, h3, Over.comp_left, hl]

end GlobalTheory.RealMult
