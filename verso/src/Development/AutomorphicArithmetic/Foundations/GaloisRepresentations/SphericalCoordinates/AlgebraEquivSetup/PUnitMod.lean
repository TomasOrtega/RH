import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

noncomputable section

open NumberField

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Set `bs` to `Module.Free.chooseBasis ℤ (𝓞 E)`. Rewrite using `[Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]`. Simplify using `only [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero, Matrix.det_one, CharP.cast_eq_zero]`.
-/
private theorem norm_cast_eq_one {E : Type} [Field E] [NumberField E] (M : ℕ) (b : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (M : 𝓞 E) * b) : ℤ) : ZMod M) = 1 := by
  classical
  let bs := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]
  simp only [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Matrix.det_one, CharP.cast_eq_zero]

/- English proof (translation)
Introduce `E _ _ M c b _ h`. Use `⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.isUnit_iff_coprime]`. Establish `key` using `norm_cast_eq_one (E := E) M b`. Rewrite `key` using `[← h]`.

Break down `Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn` into its components or cases. Rewrite `key` using `[hn, Int.cast_natCast]`. Rewrite using `[key]`. Conclude with `isUnit_one`. Rewrite `key` using `[hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]`.

Rewrite using `[key]`. Conclude with `isUnit_one.neg`. Establish `hm` using `Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))`. Rewrite `hm` using `[Ideal.absNorm_span_singleton, Ideal.mem_span_singleton]`. Take `⟨c', hc'⟩` from `hm`.

Conclude with `⟨c', hc'.symm⟩`.
-/
theorem pUnitMod : UnitMod := by
  intro E _ _ M c b _ h
  refine ⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    have key := norm_cast_eq_one (E := E) M b
    rw [← h] at key
    rcases Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn
    · rw [hn, Int.cast_natCast] at key
      rw [key]
      exact isUnit_one
    · rw [hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg] at key
      rw [key]
      exact isUnit_one.neg
  · have hm := Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))
    rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', hc'.symm⟩

end UpperTheory.Gal.W2.Seed
