import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hg`.
-/
theorem HomLocRingMem.algebraMap_mk_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [P.IsPrime] {g : MRing ι R} (hg : g ∉ P) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

/- English proof (translation)
Introduce `R _ K _ ι P W _ hW hPW z`. Establish `hne : ∀ g : MRing ι R, g ∉ W → algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0` using `fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))`. Establish `h1W : (1 : MRing ι R) ∉ W` using `fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Use `Subring.closure_induction (fun x hx => hx) ?_ ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Conclude with `⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1W, by simp⟩`. Conclude with `⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1W, by simp⟩`. Introduce and unpack `x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩`. Use `⟨b₁ + b₂, f₁ * g₂ + g₁ * f₂, g₁ * g₂, (hf₁.mul hg₂).add ?_, hg₁.mul hg₂, fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_comm b₁ b₂, mul_comm g₁ f₂]`. Conclude with `hf₂.mul hg₁`. Simplify using `only [map_add, map_mul]`. Rewrite using `[div_add_div _ _ (hne g₁ hW₁) (hne g₂ hW₂)]`. Introduce and unpack `x - ⟨b, f, g, hf, hg, hgW, rfl⟩`.

Conclude with `⟨b, -f, g, hf.neg, hg, hgW, by simp only [map_neg, neg_div]⟩`. Introduce and unpack `x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩`. Use `⟨b₁ + b₂, f₁ * f₂, g₁ * g₂, hf₁.mul hf₂, hg₁.mul hg₂, fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Rewrite using `[div_mul_div_comm]`.

Introduce `hz`. Conclude with `Subring.subset_closure hz`.
-/
theorem HomLocRingMem.proof : HomLocRingMem.Statement := by
  intro R _ K _ ι P W _ hW hPW z
  have hne : ∀ g : MRing ι R, g ∉ W →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  constructor
  · intro hz
    refine Subring.closure_induction (fun x hx => hx) ?_ ?_ ?_ ?_ ?_ hz
    · exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * g₂ + g₁ * f₂, g₁ * g₂, (hf₁.mul hg₂).add ?_, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      · rw [add_comm b₁ b₂, mul_comm g₁ f₂]
        exact hf₂.mul hg₁
      · simp only [map_add, map_mul]
        rw [div_add_div _ _ (hne g₁ hW₁) (hne g₂ hW₂)]
    · rintro x - ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨b, -f, g, hf.neg, hg, hgW, by simp only [map_neg, neg_div]⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * f₂, g₁ * g₂, hf₁.mul hf₂, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      simp only [map_mul]
      rw [div_mul_div_comm]
  · intro hz
    exact Subring.subset_closure hz

end

end GroundTheory.Heights₂.Heights.NumbersDVR
