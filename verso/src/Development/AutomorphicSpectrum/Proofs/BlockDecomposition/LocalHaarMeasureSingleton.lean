import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

/- English proof (translation)
Introduce `F _ _ v lam hstd`. Take `⟨hH, h1⟩` from `hstd`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective`. Establish `hs : ∀ x : Fv F v, lam {x} = lam {0}`.

Introduce `x`. Rewrite using `[← measure_preimage_add lam x ({x} : Set (Fv F v))]`. Use `congr 1`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Assume the negation of the conclusion as `h0`. Take `⟨N, hN⟩` from `ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top`. Establish `hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N`. Rewrite using `[Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]`. Establish `hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v)) = N * lam {0}`.

Rewrite using `[← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard, nsmul_eq_mul]`. Establish `hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v)) ⊆ (v.adicCompletionIntegers F : Set (Fv F v))`. Introduce `x hx`. Simplify using `only [Finset.coe_image, Set.mem_image] at hx`. Take `⟨n, -, rfl⟩` from `hx`.

Conclude with `natCast_mem (v.adicCompletionIntegers F) n`. Establish `hle` using `measure_mono (μ := lam) hsub`. Rewrite `hle` using `[hsum, h1]`. Conclude with `absurd hN (not_lt.2 hle)`.
-/
theorem isStdV_measure_singleton_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  intro F _ _ v lam hstd
  obtain ⟨hH, h1⟩ := hstd
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : CharZero (Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs : ∀ x : Fv F v, lam {x} = lam {0} := by
    intro x
    rw [← measure_preimage_add lam x ({x} : Set (Fv F v))]
    congr 1
    ext y
    simp
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top
  have hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      = N * lam {0} := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard,
      nsmul_eq_mul]
  have hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact natCast_mem (v.adicCompletionIntegers F) n
  have hle := measure_mono (μ := lam) hsub
  rw [hsum, h1] at hle
  exact absurd hN (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
