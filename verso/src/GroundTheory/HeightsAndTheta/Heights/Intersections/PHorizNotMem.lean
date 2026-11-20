import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StHorizNotMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, ringKrullDim_quotient]`. Establish `: Nonempty (PrimeSpectrum.zeroLocus (R` using `R) W) := ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩`. Rewrite using `[← Order.krullDim_withBot]`. Set `f : WithBot (PrimeSpectrum.zeroLocus (R` to `R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ := fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x`. Use `Order.krullDim_le_of_strictMono f ?_` and prove the remaining obligations.

Introduce `a b hab`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hab (lt_irrefl _)`.

Consider the case `coe q`. Express the relevant statement in the definitionally equal form `(⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩`. Conclude with `Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (hlt.trans_le (fun _ h => q.2 h)))`. Consider the case `coe p`. Proceed by induction on `b using WithBot.recBotCoe with`.

Consider the case `bot => exact absurd hab (WithBot.not_lt_bot _)`. Consider the case `coe q`. Express the relevant statement in the definitionally equal form `(⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩`. Conclude with `Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))`.
-/
theorem HorizNotMem.ringKrullDim_quotient_add_one_le {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))

/- English proof (translation)
Introduce `K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W`. Establish `: P.IsPrime` using `hP.2.1.1`. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Establish `hle : P ⊔ Ideal.span {s'} ≤ W` using `sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)`. Take `⟨W₀, hW₀, hW₀W⟩` from `Ideal.exists_minimalPrimes_le hle`.

Establish `: W₀.IsPrime` using `hW₀.1.1`. Establish `h1` using `dim_quot_minimal_add_one P W s hsP hW.1`. Establish `h2` using `dim_quot_minimal_add_one P W₀ s' hs'P hW₀`. Establish `heq : W₀ = W`. Assume the negation of the conclusion as `hne`.

Establish `hstep` using `HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)`. Establish `h3` using `add_le_add hstep (le_refl (1 : WithBot ℕ∞))`. Rewrite `h3` using `[h1, h2, hP.2.2.2]`. Establish `h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)`. Conclude with `h3` after adjusting the coercions.

Establish `h5` using `WithBot.coe_le_coe.mp h4`. Establish `h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K` using `by exact_mod_cast h5`. Use linear arithmetic over natural numbers and integers. Conclude with `hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh`.
-/
theorem HorizNotMem.proof : HorizNotMem.Statement := by
  intro K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W
  have : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hle : P ⊔ Ideal.span {s'} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)
  obtain ⟨W₀, hW₀, hW₀W⟩ := Ideal.exists_minimalPrimes_le hle
  have : W₀.IsPrime := hW₀.1.1
  have h1 := dim_quot_minimal_add_one P W s hsP hW.1
  have h2 := dim_quot_minimal_add_one P W₀ s' hs'P hW₀
  have heq : W₀ = W := by
    by_contra hne
    have hstep := HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)
    have h3 := add_le_add hstep (le_refl (1 : WithBot ℕ∞))
    rw [h1, h2, hP.2.2.2] at h3
    have h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h5
    omega
  exact hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh

end GroundTheory.Heights₂.Heights.Inter
