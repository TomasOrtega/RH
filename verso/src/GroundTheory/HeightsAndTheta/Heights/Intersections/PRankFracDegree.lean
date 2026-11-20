import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRankFracDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

/- English proof (translation)
Introduce `_`. Establish `hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a` using `fun _ => rfl`. Establish `hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0`. Introduce `a ha h0`. Establish `h10 : (1 : A) = 0` using `mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))`.

Conclude with `one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)`. Use `show IsLocalization (nonZeroDivisors A) K`. Rewrite using `[isLocalization_iff]`. Use `⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, w, hw, hyw⟩` from `Subfield.mem_closure_iff.mp (hcl z.2)`.

Rewrite `hy`, `hw` using `[← RingHom.coe_range, Subring.closure_eq]`. Take `⟨a, rfl⟩` from `hy`. Take `⟨a', rfl⟩` from `hw`. Distinguish the cases in `h0 : f a' = 0`. Use `⟨(0, 1), Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]`. Rewrite using `[← hyw, h0, div_zero]`. Establish `ha' : a' ∈ nonZeroDivisors A` using `mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)`. Use `⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [MulMemClass.coe_mul, hmap]`.

Rewrite using `[← hyw, div_mul_cancel₀ _ h0]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `hxy : x = y` using `hf (by rw [← hmap x, ← hmap y, h])`. Rewrite using `[hxy]`.
-/
theorem RankFracDegree.isFractionRing_of_closure {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    let _ := (f.codRestrict K hK).toAlgebra
    IsFractionRing A K := by
  intro _
  have hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a := fun _ => rfl
  have hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0 := by
    intro a ha h0
    have h10 : (1 : A) = 0 :=
      mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))
    exact one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)
  show IsLocalization (nonZeroDivisors A) K
  rw [isLocalization_iff]
  refine ⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp (hcl z.2)
    rw [← RingHom.coe_range, Subring.closure_eq] at hy hw
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hw
    by_cases h0 : f a' = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      simp only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]
      rw [← hyw, h0, div_zero]
    · have ha' : a' ∈ nonZeroDivisors A :=
        mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)
      refine ⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, hmap]
      rw [← hyw, div_mul_cancel₀ _ h0]
  · refine ⟨1, ?_⟩
    have hxy : x = y := hf (by rw [← hmap x, ← hmap y, h])
    rw [hxy]

/- English proof (translation)
Introduce `F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _`. Establish `hle : L₀ ≤ L`. Introduce `x hx`. Establish `h1 : x ∈ Subfield.closure (Set.range g)`. Use `Subfield.closure_mono ?_ (hL₀ hx)` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨algebraMap A B a, hfg a⟩`. Conclude with `(Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1`. Set `L'` to `IntermediateField.extendScalars hle`. Set `_ : Algebra A L₀` to `(f.codRestrict L₀ hfL₀).toAlgebra`.

Set `_ : Algebra B L'` to `(g.codRestrict L' hgL).toAlgebra`. Set `_ : Algebra A L'` to `((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra`. Establish `_ : IsScalarTower A L₀ L'` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `_ : IsScalarTower A B L'` using `IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm`. Establish `_ : IsFractionRing A L₀` using `RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀`.

Establish `_ : IsFractionRing B L'` using `RankFracDegree.isFractionRing_of_closure L' g hg hgL hL`. Rewrite using `[IntermediateField.relfinrank_eq_finrank_of_le hle]`. Conclude with `(IsFractionRing.finrank_eq A L₀ B L').symm`.
-/
theorem RankFracDegree.proof : RankFracDegree.Statement := by
  intro F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _
  have hle : L₀ ≤ L := by
    intro x hx
    have h1 : x ∈ Subfield.closure (Set.range g) := by
      refine Subfield.closure_mono ?_ (hL₀ hx)
      rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap A B a, hfg a⟩
    exact (Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1
  let L' := IntermediateField.extendScalars hle
  let _ : Algebra A L₀ := (f.codRestrict L₀ hfL₀).toAlgebra
  let _ : Algebra B L' := (g.codRestrict L' hgL).toAlgebra
  let _ : Algebra A L' := ((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra
  have _ : IsScalarTower A L₀ L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm
  have _ : IsFractionRing A L₀ := RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀
  have _ : IsFractionRing B L' := RankFracDegree.isFractionRing_of_closure L' g hg hgL hL
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact (IsFractionRing.finrank_eq A L₀ B L').symm

end GroundTheory.Heights₂.Heights.Inter
