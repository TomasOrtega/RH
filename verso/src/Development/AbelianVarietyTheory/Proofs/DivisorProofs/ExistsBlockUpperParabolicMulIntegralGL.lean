import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import GroundTheory.AutomorphicForms.Iwasawa
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

open ValuativeRel

/- English proof (translation)
Use `haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation _) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one`.
-/
theorem mem_integer_iff_mem_Ov {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

/- English proof (translation)
Introduce `g hg`. Take `⟨h1, h2⟩` from `(GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg`. Set `A : Matrix (Fin n) (Fin n) (Ov E w)` to `Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩`. Set `B : Matrix (Fin n) (Fin n) (Ov E w)` to `Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩`. Establish `hinj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) (Ov E w).subtype) := fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)`.

Establish `hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))` using `rfl`. Establish `hB : RingHom.mapMatrix (Ov E w).subtype B = ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))` using `rfl`. Establish `hAB : A * B = 1` using `hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])`. Establish `hBA : B * A = 1` using `hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])`. Conclude with `⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩`.
-/
theorem integralGL_le_KGL {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n ≤ GlobalTheory.LFun.KGL w n := by
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg
  let A : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ov E w).subtype) :=
    fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hB : RingHom.mapMatrix (Ov E w).subtype B =
      ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

/- English proof (translation)
Introduce `E _ _ a n w g`. Establish `hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ))`. Introduce `i j hij`. Distinguish the cases in `h : a ≤ (i : ℕ)`. Establish `: a ≤ (j : ℕ)` using `h.trans (Fin.le_iff_val_le_val.1 hij)`.

Simplify using `[h, this]`. Simplify using `[h]`. Take `⟨p, hp, k, hk, rfl⟩` from `GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g`. Conclude with `⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩`.
-/
theorem exists_parabolic_mul_maximalCompact : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w),
    ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = p * k := by
  intro E _ _ a n w g
  have hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ)) := by
    intro i j hij
    by_cases h : a ≤ (i : ℕ)
    · have : a ≤ (j : ℕ) := h.trans (Fin.le_iff_val_le_val.1 hij)
      simp [h, this]
    · simp [h]
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g
  exact ⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩

end GlobalTheory.LeviDesc
