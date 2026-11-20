import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

/- English proof (translation)
Use `set Y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p y with hY`. Establish `hfin : {q | Y q ∉ (A.L q).O}.Finite`. Use `(Set.finite_singleton p).subset fun q hq => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hq` to reduce the goal to its premises.

Simplify using `only [hY]`. Rewrite using `[Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hne)]`. Conclude with `(A.L q).O.zero_mem`. Take `⟨x, hx⟩` from `happ Y hfin`. Take `⟨o, ho, hxo⟩` from `hx p`.

Establish `hYp : Y p = y` using `by simp [hY]`. Rewrite `hxo` using `[hYp]`. Establish `halg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨d, hd0, hd⟩` from `halg.exists_integral_multiple`. Use `⟨d.natAbs, Int.natAbs_ne_zero.2 hd0, ?_⟩` and prove the remaining obligations.

Establish `hint : IsIntegral ℤ ((d.natAbs : E) * x)`. Break down `Int.natAbs_eq d with h | h` into its components or cases. Establish `: ((d.natAbs : E) * x) = d • x`. Rewrite using `[zsmul_eq_mul]`. Use `congr 1`.

Conclude with `(Int.cast_natCast (R := E) d.natAbs).symm.trans (congrArg _ h.symm)`. Rewrite using `[this]`. Conclude with `hd`. Establish `: ((d.natAbs : E) * x) = -(d • x)`. Rewrite using `[zsmul_eq_mul, ← neg_mul]`.

Use `congr 1`. Establish `h'` using `congrArg (Int.cast (R := E)) h`. Rewrite using `[h', Int.cast_neg, Int.cast_natCast, neg_neg]`. Rewrite using `[this]`. Conclude with `hd.neg`.

Establish `h1` using `ιE_mem A p _ hint`. Establish `hy : (d.natAbs : (A.loc p).Ep) * y = (A.loc p).ιE ((d.natAbs : E) * x) - (d.natAbs : (A.loc p).Ep) * o`. Rewrite using `[map_mul, map_natCast, ← hxo]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`.

Conclude with `(A.L p).O.sub_mem h1 ((A.L p).O.mul_mem (natCast_mem (A.L p).O _) ho)`.
-/
theorem exists_nat_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = o)
    (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O := by
  set Y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p y with hY
  have hfin : {q | Y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    simp only [hY]
    rw [Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hne)]
    exact (A.L q).O.zero_mem
  obtain ⟨x, hx⟩ := happ Y hfin
  obtain ⟨o, ho, hxo⟩ := hx p
  have hYp : Y p = y := by simp [hY]
  rw [hYp] at hxo
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := halg.exists_integral_multiple
  refine ⟨d.natAbs, Int.natAbs_ne_zero.2 hd0, ?_⟩
  have hint : IsIntegral ℤ ((d.natAbs : E) * x) := by
    rcases Int.natAbs_eq d with h | h
    · have : ((d.natAbs : E) * x) = d • x := by
        rw [zsmul_eq_mul]; congr 1
        exact (Int.cast_natCast (R := E) d.natAbs).symm.trans (congrArg _ h.symm)
      rw [this]; exact hd
    · have : ((d.natAbs : E) * x) = -(d • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have h' := congrArg (Int.cast (R := E)) h
        rw [h', Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this]; exact hd.neg
  have h1 := ιE_mem A p _ hint
  have hy : (d.natAbs : (A.loc p).Ep) * y =
      (A.loc p).ιE ((d.natAbs : E) * x) - (d.natAbs : (A.loc p).Ep) * o := by
    rw [map_mul, map_natCast, ← hxo]; ring
  rw [hy]
  exact (A.L p).O.sub_mem h1 ((A.L p).O.mul_mem (natCast_mem (A.L p).O _) ho)

end GlobalTheory.HL.Glue
