import Mathlib
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Klen
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kexp

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `CK hCK hK l R c _ L₀ _ hmu hSec Z Exc hF L₂ _ _ _ hL₂ eps Ct c0 x n0 heps hc0 hx hgood hn hdisc e he1 heZ hex m L₁ _ _ _ hL₁`. Establish `hexp : 0 ≤ 2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4))` using `by positivity`. Distinguish the cases in `he : e ∈ Exc`. Establish `hg : (e : ℝ) ≤ x ^ (eps / (2 * CK))` using `hgood e he hex`. Take `⟨D⟩` from `ldata_nonempty (F := L₂) (Ω := AlgebraicClosure L₂) l`.

Establish `hmu2 : HasMuQ l L₂`. Take `⟨ζ, hζ⟩` from `hmu`. Conclude with `⟨algebraMap L₀ L₂ ζ, hζ.map_of_injective (algebraMap L₀ L₂).injective⟩`. Take `⟨hvt, hvb⟩` from `klen CK hK l L₂ (AlgebraicClosure L₂) D hmu2 e he1`. Establish `hkb` using `kexp CK eps c0 x e (Module.finrank ℚ L₂) n0 (discr L₂).natAbs hCK heps hc0 hx hg hn hdisc`.

Establish `hs` using `hSec e he1 m L₁ hL₁ L₂ hL₂ (AlgebraicClosure L₂) D`. Generalize the expression as in `VLen D ↑e = v at hvt hvb hs`. Generalize the expression as in `shaInv L₁ l ↑e = s at hs ⊢`. Use `lift v to ℕ using hvt`. Establish `hst : s ≠ ⊤`.

Use `ne_top_of_le_ne_top ?_ hs` and prove the remaining obligations. Rewrite using `[← Nat.cast_add]`. Conclude with `ENat.coe_ne_top _`. Use `lift s to ℕ using hst`. Establish `hs' : s ≤ v + R * (m - jZero l R)` using `by exact_mod_cast hs`.

Use `⟨ENat.coe_ne_top s, ?_⟩` and prove the remaining obligations. Rewrite using `[ENat.toNat_coe]`. Simplify using `only [ENat.toNat_coe] at hvb`. Establish `hN : s ≤ v + R * (m + jZero l R + c + Nat.log l Z)`. Use `le_trans hs' (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)` and prove the remaining obligations.

Use linear arithmetic over natural numbers and integers. Establish `hR : (s : ℝ) ≤ (v : ℝ) + (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z)`. Conclude with `hN` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `hF.2 e he1 heZ he m L₁ hL₁`.

Generalize the expression as in `shaInv L₁ l ↑e = s at hb ⊢`. Establish `hst : s ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) hb`. Use `lift s to ℕ using hst`. Establish `hs' : s ≤ R * (max m (jZero l R) + c + Nat.log l Z)` using `by exact_mod_cast hb`. Use `⟨ENat.coe_ne_top s, ?_⟩` and prove the remaining obligations.

Rewrite using `[ENat.toNat_coe]`. Establish `hN : s ≤ R * (m + jZero l R + c + Nat.log l Z)`. Use `le_trans hs' (Nat.mul_le_mul_left _ ?_)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Establish `hR : (s : ℝ) ≤ (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z)`.

Conclude with `hN` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Win.point :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R c : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], HasMuQ l L₀ → SecondBound l R L₀ →
      ∀ (Z : ℕ) (Exc : Finset ℕ), FirstBound l R c L₀ Z Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ →
          ∀ (eps Ct c0 x : ℝ) (n0 : ℕ), 0 < eps → 0 ≤ c0 → 1 ≤ x → Good (eps / (2 * CK)) Ct Exc x →
            Module.finrank ℚ L₂ ≤ n0 → Real.log (2 * ((discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (eps / 4) →
            ∀ e : ℕ, 1 ≤ e → e ≤ Z → (e : ℝ) ≤ x ^ Ct →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
                shaInv L₁ l e ≠ ⊤ ∧ ((shaInv L₁ l e).toNat : ℝ) ≤
                  (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) +
                    2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  intro CK hCK hK l R c _ L₀ _ hmu hSec Z Exc hF L₂ _ _ _ hL₂ eps Ct c0 x n0 heps hc0 hx hgood hn hdisc e he1 heZ hex m L₁ _ _ _ hL₁
  have hexp : 0 ≤ 2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by positivity
  by_cases he : e ∈ Exc
  · have hg : (e : ℝ) ≤ x ^ (eps / (2 * CK)) := hgood e he hex
    obtain ⟨D⟩ := ldata_nonempty (F := L₂) (Ω := AlgebraicClosure L₂) l
    have hmu2 : HasMuQ l L₂ := by
      obtain ⟨ζ, hζ⟩ := hmu
      exact ⟨algebraMap L₀ L₂ ζ, hζ.map_of_injective (algebraMap L₀ L₂).injective⟩
    obtain ⟨hvt, hvb⟩ := klen CK hK l L₂ (AlgebraicClosure L₂) D hmu2 e he1
    have hkb := kexp CK eps c0 x e (Module.finrank ℚ L₂) n0 (discr L₂).natAbs hCK heps hc0 hx hg hn hdisc
    have hs := hSec e he1 m L₁ hL₁ L₂ hL₂ (AlgebraicClosure L₂) D
    generalize VLen D ↑e = v at hvt hvb hs
    generalize shaInv L₁ l ↑e = s at hs ⊢
    lift v to ℕ using hvt
    have hst : s ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hs
      rw [← Nat.cast_add]
      exact ENat.coe_ne_top _
    lift s to ℕ using hst
    have hs' : s ≤ v + R * (m - jZero l R) := by exact_mod_cast hs
    refine ⟨ENat.coe_ne_top s, ?_⟩
    rw [ENat.toNat_coe]
    simp only [ENat.toNat_coe] at hvb
    have hN : s ≤ v + R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
      omega
    have hR : (s : ℝ) ≤ (v : ℝ) + (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith
  · have hb := hF.2 e he1 heZ he m L₁ hL₁
    generalize shaInv L₁ l ↑e = s at hb ⊢
    have hst : s ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hb
    lift s to ℕ using hst
    have hs' : s ≤ R * (max m (jZero l R) + c + Nat.log l Z) := by exact_mod_cast hb
    refine ⟨ENat.coe_ne_top s, ?_⟩
    rw [ENat.toNat_coe]
    have hN : s ≤ R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.mul_le_mul_left _ ?_)
      omega
    have hR : (s : ℝ) ≤ (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith
