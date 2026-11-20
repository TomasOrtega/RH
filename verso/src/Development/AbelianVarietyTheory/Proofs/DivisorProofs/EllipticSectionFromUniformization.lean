import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion

/- English proof (translation)
Introduce `Λ Ω hΩ x hx`. Establish `hx' : x ≫ GlobalTheory.WeierstrassCurve.toSpec (curve Λ Ω) = Spec.map (CommRingCat.ofHom (RingHom.id ℂ))`. Rewrite using `[hx]`. Conclude with `(Spec.map_id _).symm`. Take `⟨P, h, rfl⟩` from `GlobalTheory.WeierstrassCurve.exists_eq_ptHom (curve Λ Ω) (RingHom.id ℂ) x hx'`.

Establish `e` using `(WeierstrassCurve.Projective.equation_iff _).mp h.equation`. Simplify using `only [WeierstrassCurve.map_id, curve] at e`. Establish `hne : P ≠ 0` using `(GlobalTheory.WeierstrassCurve.isUnimodularSol_iff_ne_zero.mp h).2`. Distinguish the cases in `h2 : P 2 = 0`. Establish `h0 : P 0 = 0`.

Rewrite `e` using `[h2]`. Establish `: P 0 ^ 3 = 0` using `by linear_combination -e`. Conclude with `pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this`. Establish `h1 : P 1 ≠ 0`. Apply the tactic sequence `intro h1; apply hne; ext i; fin_cases i <;> simp [h0, h1, h2]`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Unfold `pt`. Use `(GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 1) h1, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i; fin_cases i <;> simp [coords, h0, h2]`. Use `set a := P 0 / P 2 set b := P 1 / P 2`.

Establish `hY : (2 * b * Ω ^ 3) ^ 2 = 4 * (a * Ω ^ 2) ^ 3 - Λ.g₂ * (a * Ω ^ 2) - Λ.g₃`. Simplify using `only [a, b]`. Take the linear combination `(norm := skip) (4 * Ω ^ 6 / P 2 ^ 3) * e`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨z, hz, hp, hd⟩` from `GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq Λ hY`. Use `⟨z, ?_⟩` and prove the remaining obligations. Unfold `pt`. Use `(GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 2) h2, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Use `fin_cases i`. Simplify using `[coords, hz, hp, a]`. Clear the denominators using the available nonvanishing facts. Simplify using `[coords, hz, hd, b]`. Clear the denominators using the available nonvanishing facts.

Simplify using `[coords, hz]`.
-/
theorem exists_pt_eq : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ x : Sp ℂ ⟶ scheme (curve Λ Ω), x ≫ toSpec (curve Λ Ω) = 𝟙 _ → ∃ z : ℂ, pt Λ Ω z = x := by
  intro Λ Ω hΩ x hx
  have hx' : x ≫ GlobalTheory.WeierstrassCurve.toSpec (curve Λ Ω) = Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) := by
    rw [hx]; exact (Spec.map_id _).symm
  obtain ⟨P, h, rfl⟩ := GlobalTheory.WeierstrassCurve.exists_eq_ptHom (curve Λ Ω) (RingHom.id ℂ) x hx'
  have e := (WeierstrassCurve.Projective.equation_iff _).mp h.equation
  simp only [WeierstrassCurve.map_id, curve] at e
  have hne : P ≠ 0 := (GlobalTheory.WeierstrassCurve.isUnimodularSol_iff_ne_zero.mp h).2
  by_cases h2 : P 2 = 0
  · have h0 : P 0 = 0 := by
      rw [h2] at e
      have : P 0 ^ 3 = 0 := by linear_combination -e
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    have h1 : P 1 ≠ 0 := by
      intro h1; apply hne; ext i; fin_cases i <;> simp [h0, h1, h2]
    refine ⟨0, ?_⟩
    unfold pt
    refine (GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 1) h1, ?_⟩
    ext i; fin_cases i <;> simp [coords, h0, h2]
  · set a := P 0 / P 2
    set b := P 1 / P 2
    have hY : (2 * b * Ω ^ 3) ^ 2 = 4 * (a * Ω ^ 2) ^ 3 - Λ.g₂ * (a * Ω ^ 2) - Λ.g₃ := by
      simp only [a, b]
      linear_combination (norm := skip) (4 * Ω ^ 6 / P 2 ^ 3) * e
      field_simp
      ring
    obtain ⟨z, hz, hp, hd⟩ := GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq Λ hY
    refine ⟨z, ?_⟩
    unfold pt
    refine (GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 2) h2, ?_⟩
    ext i; fin_cases i
    · simp [coords, hz, hp, a]; field_simp
    · simp [coords, hz, hd, b]; field_simp
    · simp [coords, hz]

end GlobalTheory.CMTorsion
