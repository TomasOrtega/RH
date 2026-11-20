import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

/- English proof (translation)
Introduce `hmem`. Set `x : maximalRealSubfield L` to `⟨δ, hmem⟩`. Establish `hx : x ^ 2 = -(p : maximalRealSubfield L)` using `Subtype.ext (by simpa [x] using hδ)`. Take `⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L))` from `inferInstance`. Establish `hv : v.IsReal` using `IsTotallyReal.isReal v`.

Establish `h` using `congrArg (InfinitePlace.embedding_of_isReal hv) hx`. Rewrite `h` using `[map_pow, map_neg, map_natCast]`. Establish `h1 : (0 : ℝ) < p` using `by exact_mod_cast hp`. Use polynomial arithmetic with `[sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]`.
-/
theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

/- English proof (translation)
Introduce `L _ _ _ p q δ hp hδ hdvd w hw`. Use `set Lp := maximalRealSubfield L`. Use `set u := w.under (𝓞 Lp)`. Take `⟨k, hk⟩` from `hdvd`. Use `set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz`.

Establish `hq : (q : 𝓞 Lp) ∈ u.asIdeal`. Express the relevant statement in the definitionally equal form `_ ∈ Ideal.comap _ _`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hw`. Establish `hzu : z ∈ u.asIdeal`.

Rewrite using `[hz]`. Conclude with `u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))`. Establish `hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp)`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 Lp) hk` after adjusting the coercions. Establish `hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp)`.

Rewrite using `[hz]`. Move the coercions through the operations in `at hk'`. Take the linear combination `hk'`. Establish `h1` using `GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu`. Rewrite `h1` using `[hsq]`.

Use `GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl) (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_` and prove the remaining obligations. Simplify using `using h1`.
-/
theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
