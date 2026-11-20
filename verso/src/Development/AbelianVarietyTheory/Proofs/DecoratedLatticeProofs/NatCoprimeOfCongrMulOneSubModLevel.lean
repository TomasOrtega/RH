import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

/- English proof (translation)
Introduce `I g T M hg hMg hz`. Take `⟨t, ht, hc⟩` from `hz`. Take `⟨-, hint, hu, -⟩` from `GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg`. Establish `hg0 : (g : ℚ) ≠ 0` using `by exact_mod_cast (show g ≠ 0 by omega)`. Use `set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef`.

Establish `hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E))`. Establish `: (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ))`. Rewrite using `[hqdef]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `congrArg (fun x : ℚ => (x : I.E)) this` as an intermediate fact. Simplify using `using this`. Establish `key : Formalism.UG.inclE (F` using `I.F) (Af I.F) (q : I.E) = t := by`. Apply `hu.mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[← hc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range` using `(hint _).1 (key ▸ ht)`. Take `⟨b, hb⟩` from `hq`. Establish `h1 : IsIntegral ℤ (algebraMap ℚ I.E q)`.

Rewrite using `[eq_ratCast, ← hb]`. Conclude with `RingOfIntegers.isIntegral_coe b`. Establish `h2 : IsIntegral ℤ q` using `(isIntegral_algebraMap_iff (algebraMap ℚ I.E).injective).1 h1`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Establish `h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n`.

Establish `hn' : (n : ℚ) = q` using `by simpa using hn`. Establish `: (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ)`. Rewrite `hn'` using `[hqdef]`. Use `push_cast`. Rewrite using `[hn']`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Establish `h5 : (g : ℤ) ∣ 1 - (T : ℤ)`.

Use `Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_` and prove the remaining obligations. Rewrite using `[Int.gcd_natCast_natCast]`. Conclude with `hMg.symm`. Establish `hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1`. Establish `a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ)` using `Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)`.

Establish `b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ)` using `(Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5`. Use `dvd_add b a` as an intermediate fact. Simplify using `using this`. Conclude with `Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))`.
-/
theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ I.E).injective).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
