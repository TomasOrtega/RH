import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

/- English proof (translation)
Take `⟨S, rfl⟩` from `hL`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : S × ι => (p.1 : ι → K) p.2)`. Use `⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩` and prove the remaining obligations. Introduce `y hy i`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨c, hc⟩` from `hb (⟨x, hx⟩, i)`. Conclude with `⟨c, by rw [hc, Algebra.smul_def]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, hc⟩` from `hx`. Take `⟨d, hd⟩` from `hy`. Conclude with `⟨c + d, by rw [map_add, hc, hd, Pi.add_apply, mul_add]⟩`. Consider the case `smul a x _ hx`. Take `⟨c, hc⟩` from `hx`.

Conclude with `⟨a * c, by rw [map_mul, hc, Pi.smul_apply, Algebra.smul_def]; ring⟩`.
-/
private lemma UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg {R K ι : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (L : Submodule R (ι → K)) (hL : L.FG) :
    ∃ b : R, b ≠ 0 ∧ ∀ y ∈ L, ∀ i : ι, ∃ c : R, algebraMap R K c = algebraMap R K b * y i := by
  obtain ⟨S, rfl⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : S × ι => (p.1 : ι → K) p.2)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro y hy i
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := hb (⟨x, hx⟩, i)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add, hc, hd, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [map_mul, hc, Pi.smul_apply, Algebra.smul_def]; ring⟩

/- English proof (translation)
Introduce `I`. Conclude with `UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg I.L I.L_fg`.
-/
theorem UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator :
    ∀ (I : Formalism.MainNotions.S.AutInst),
      ∃ (b : NumberField.RingOfIntegers I.E),
        b ≠ (0 : NumberField.RingOfIntegers I.E) ∧
          ∀ y ∈ I.L, ∀ (i : Fin I.n), ∃ (c : NumberField.RingOfIntegers I.E), (↑c : I.E) = (↑b : I.E) * y i := by
  intro I
  exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg I.L I.L_fg
