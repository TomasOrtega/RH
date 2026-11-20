import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IdDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRank
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLength
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE`. Establish `: P'.IsPrime` using `hP'.2.1.1`. Establish `: (imageZ v P').IsPrime` using `hP.2.1.1`. Take `⟨t, ht, htW⟩` from `exists_form_notMem hW.2 hW.1.1.1 α`. Establish `ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P')) (Ideal.Quotient.mk _ t) ≠ 0`.

Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))`. Use `set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) / algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy`. Establish `hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) = algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s)` using `div_mul_cancel₀ _ ht0`. Take `⟨hyA, hm⟩` from `hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt`.

Take `⟨hNoeth, hLocal, hDim⟩` from `hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW`. Set `_ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))` to `(locToSemiloc hv P' W).toAlgebra`. Take `⟨hBf, hBt⟩` from `hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW`. Establish `hrk` using `hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW`. Take `⟨N, hlen, hN⟩` from `hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE`.

Establish `hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0` using `fun h => by`. Establish `h' : y = 0` using `congrArg Subtype.val h`. Rewrite `h'` using `[hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h'.elim hsP ht0`. Use `ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim` as an intermediate fact.

Establish `key` using `ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0`. Establish `hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ = (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞)`. Establish `hfin` using `Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)`. Rewrite using `[hm, locIdeal_eq_span hyA]`. Conclude with `(ENat.natCast_toNat hfin).symm`.

Rewrite `key` using `[hlen, hord]`. Establish `hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) * multAt (imageZ v P' ⊔ Ideal.span {s}) W`. Conclude with `key` after adjusting the coercions. Rewrite using `[← hN, hNat, ← hrk]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem ArithmeticIntersectionDivisorPushforward.proof (hDeh : regularityDehomogenization_holds.Statement) (hLoc : LocRingDimOne.Statement)
    (hFin : SemilocFinite.Statement) (hRank : SemilocRank.Statement) (hLen : SemilocLength.Statement) :
    ArithmeticIntersectionDivisorPushforward.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE
  have : P'.IsPrime := hP'.2.1.1
  have : (imageZ v P').IsPrime := hP.2.1.1

  obtain ⟨t, ht, htW⟩ := exists_form_notMem hW.2 hW.1.1.1 α
  have ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P'))
      (Ideal.Quotient.mk _ t) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))
  set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) /
    algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy
  have hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) := div_mul_cancel₀ _ ht0
  obtain ⟨hyA, hm⟩ := hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt
  obtain ⟨hNoeth, hLocal, hDim⟩ := hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW
  let _ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) := (locToSemiloc hv P' W).toAlgebra
  obtain ⟨hBf, hBt⟩ := hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW
  have hrk := hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW
  obtain ⟨N, hlen, hN⟩ := hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE
  have hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0 := fun h => by
    have h' : y = 0 := congrArg Subtype.val h
    rw [hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact h'.elim hsP ht0

  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim
  have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0
  have hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ =
      (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞) := by
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)
    rw [hm, locIdeal_eq_span hyA]
    exact (ENat.natCast_toNat hfin).symm
  rw [hlen, hord] at key
  have hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) *
      multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    exact_mod_cast key
  rw [← hN, hNat, ← hrk]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.Inter
