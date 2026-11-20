import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.ClassInvAny

open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates in

/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ s κ c χ hχ hunit y y' S S' hq hS hS'`. Take `⟨a, ⟨α, rfl⟩, u, hu, hau⟩` from `Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)`. Use `set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha`. Establish `hy' : y' = a * y * u`. Establish `: y' = y * (a * u)` using `by rw [hau]; group`.

Rewrite using `[this]; exact (by ac_rfl : y * (a * u) = a * y * u)`. Substitute `hy'` using the available equality. Establish `hL` using `GlobalTheory.ClassInv.lattice_princ_mul_unit (c := c) y α hu`. Rewrite `hS'` using `[hL]`. Establish `hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0` using `(GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).2 S' hS'`.

Establish `hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]`. Establish `hfu : finPart χ u = 1` using `hunit u hu`. Establish `hmu : modF u = 1` using `ObjModel.modF_unit hu`. Establish `hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹` using `IdeleModule.modF_princ α`.

Establish `hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0`. Establish `h0 : Algebra.norm ℚ (α : E) ≠ 0` using `Algebra.norm_ne_zero_iff.2 α.ne_zero`. Conclude with `abs_ne_zero.2 (by exact_mod_cast h0)`. Establish `hmy : modF y ≠ 0` using `(IdeleModule.modF_pos y).ne'`. Rewrite using `[hS0, GlobalTheory.ClassInv.lamInf_eq hφ hχ α]`.

Rewrite using `[map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]`. Establish `hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹` using `eq_inv_of_mul_eq_one_left hAB`.

Establish `hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hn`. Establish `hmy' : ((modF y : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hmy`. Rewrite using `[hA']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem classInv_of_unit_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E), HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ u = 1) → ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ), (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y' → IsLatSum φ (2 * s) κ (lattice c y) S → IsLatSum φ (2 * s) κ (lattice c y') S' → ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹ * S' 0 := by
  intro E _ _ _ I _ φ hφ s κ c χ hχ hunit y y' S S' hq hS hS'
  classical
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := GlobalTheory.ClassInv.lattice_princ_mul_unit (c := c) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 :=
    (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := hunit u hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, GlobalTheory.ClassInv.lamInf_eq hφ hχ α]
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInvAny
