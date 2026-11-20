import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP W hW hPW`. Use `hP.isPrime` as an intermediate fact. Establish `hWp : W.IsPrime` using `hW.isPrime`. Establish `hne : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0` using `fun g hg => by`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hg`. Establish `hrep : ∀ x : degZeroLoc P {W}, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ P ∧ g ∉ W ∧ (x : FractionRing (MRing ι F ⧸ P)) = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quoti …` using `fun x => by`. Take `⟨b, f, g, hf, hg, hgP, hgW, hx⟩` from `h F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) x x.2`. Conclude with `⟨b, f, g, hf, hg, hgP, hgW W (Set.mem_singleton W), hx⟩`. Establish `hnon : ∀ (x : degZeroLoc P {W}) (f g : MRing ι F), g ∉ W → f ∈ W → (x : FractionRing (MRing ι F ⧸ P)) = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → ¬ IsUnit x`.

Introduce `x f g hgW hfW hx hu`. Take `⟨y, hy⟩` from `hu.exists_right_inv`. Take `⟨b', f', g', -, -, hg'P, hg'W, hy'⟩` from `hrep y`. Establish `hgP : g ∉ P` using `fun hg => hgW (hPW hg)`. Establish `h1 : ((x * y : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = 1`.

Rewrite using `[hy]`. Both sides reduce to the same expression. Rewrite `h1` using `[Subalgebra.coe_mul, hx, hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul, ← map_mul, ← map_mul]`. Establish `h2` using `Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)`. Establish `h3 : g * g' ∈ W`.

Use `W.sub_mem (W.mul_mem_right f' hfW) (hPW h2)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Break down `hWp.mem_or_mem h3 with h4 | h4` into its components or cases. Use `exacts [hgW h4, hg'W h4]`. Establish `hunit : ∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → g ∉ P → f ∉ W → (x : FractionRing (MRing ι F ⧸ P)) = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quoti …`.

Introduce `x b f g hf hg hgP hfW hx`. Establish `hfP : f ∉ P` using `fun h' => hfW (hPW h')`. Establish `hmem` using `div_mem_degZeroLoc P {W} hg hf hfP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hfW)`. Use `isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_mul, Subalgebra.coe_one, hx, div_mul_div_comm, mul_comm (algebraMap _ _ _), div_self (mul_ne_zero (hne g hgP) (hne f hfP))]`.

Establish `: Nontrivial (degZeroLoc P {W})` using `⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩`. Use `IsLocalRing.of_nonunits_add ?_` and prove the remaining obligations. Introduce `a c ha hc`. Take `⟨b, f, g, hf, hg, hgP, hgW, hx⟩` from `hrep a`. Take `⟨b', f', g', hf', hg', hg'P, hg'W, hy⟩` from `hrep c`.

Establish `hfW : f ∈ W`. Assume the negation of the conclusion as `hfW`. Conclude with `(mem_nonunits_iff.mp ha) (hunit a b f g hf hg hgP hfW hx)`. Establish `hf'W : f' ∈ W`. Assume the negation of the conclusion as `hf'W`.

Conclude with `(mem_nonunits_iff.mp hc) (hunit c b' f' g' hf' hg' hg'P hf'W hy)`. Use `mem_nonunits_iff.mpr (hnon (a + c) (f * g' + g * f') (g * g') (fun h5 => ?_) (W.add_mem (W.mul_mem_right g' hfW) (W.mul_mem_left g hf'W)) ?_)` and prove the remaining obligations. Break down `hWp.mem_or_mem h5 with h6 | h6 exacts [hgW h6, hg'W h6]` into its components or cases. Rewrite using `[Subalgebra.coe_add, hx, hy, div_add_div _ _ (hne g hgP) (hne g' hg'P)]`. Simplify using `only [map_add, map_mul]`.
-/
theorem DegZeroLocLocal.proof (h : DegZeroLocQuot.Statement.{u}) : DegZeroLocLocal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have hWp : W.IsPrime := hW.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hrep : ∀ x : degZeroLoc P {W}, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ P ∧ g ∉ W ∧
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := fun x => by
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := h F K ι P {W}
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) x x.2
    exact ⟨b, f, g, hf, hg, hgP, hgW W (Set.mem_singleton W), hx⟩

  have hnon : ∀ (x : degZeroLoc P {W}) (f g : MRing ι F), g ∉ W → f ∈ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → ¬ IsUnit x := by
    intro x f g hgW hfW hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := hrep y
    have hgP : g ∉ P := fun hg => hgW (hPW hg)
    have h1 : ((x * y : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = 1 := by
      rw [hy]; rfl
    rw [Subalgebra.coe_mul, hx, hy', div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
      ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' hfW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hWp.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W h4]

  have hunit : ∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
      IsMultiHomog g b → g ∉ P → f ∉ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → IsUnit x := by
    intro x b f g hf hg hgP hfW hx
    have hfP : f ∉ P := fun h' => hfW (hPW h')
    have hmem := div_mem_degZeroLoc P {W} hg hf hfP
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hfW)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, hx, div_mul_div_comm, mul_comm (algebraMap _ _ _),
      div_self (mul_ne_zero (hne g hgP) (hne f hfP))]
  have : Nontrivial (degZeroLoc P {W}) :=
    ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a c ha hc
  obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := hrep a
  obtain ⟨b', f', g', hf', hg', hg'P, hg'W, hy⟩ := hrep c
  have hfW : f ∈ W := by
    by_contra hfW
    exact (mem_nonunits_iff.mp ha) (hunit a b f g hf hg hgP hfW hx)
  have hf'W : f' ∈ W := by
    by_contra hf'W
    exact (mem_nonunits_iff.mp hc) (hunit c b' f' g' hf' hg' hg'P hf'W hy)
  refine mem_nonunits_iff.mpr (hnon (a + c) (f * g' + g * f') (g * g') (fun h5 => ?_)
    (W.add_mem (W.mul_mem_right g' hfW) (W.mul_mem_left g hf'W)) ?_)
  · rcases hWp.mem_or_mem h5 with h6 | h6
    exacts [hgW h6, hg'W h6]
  · rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (hne g hgP) (hne g' hg'P)]
    simp only [map_add, map_mul]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
