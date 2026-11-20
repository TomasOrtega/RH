import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds

namespace GlobalTheory.SmulMemOfSpan

open NumberField

/- English proof (translation)
Establish `hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L`. Introduce `n w hw`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]`. Conclude with `L.smul_mem n hw`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]`. Conclude with `hx`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨d, hd, hdy⟩` from `hy`. Use `⟨c * d, mul_ne_zero hc hd, ?_⟩` and prove the remaining obligations. Establish `e : ((c * d : RingOfIntegers E) : E) • (x + y) = (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y)`.

Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.add_mem (hL d _ hcx) (hL c _ hdy)`.

Consider the case `smul a x _ hx`. Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨n, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := RingOfIntegers E) a`. Establish `hy0 : algebraMap (RingOfIntegers E) E y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Use `⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩` and prove the remaining obligations.

Establish `e : ((y * c : RingOfIntegers E) : E) • ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) = (n : E) • ((c : E) • x)`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `hL n _ hcx`.
-/
theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin r → E))) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ (c : E) • v ∈ L := by
  have hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L := by
    intro n w hw
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact L.smul_mem n hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]
    exact hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : ((c * d : RingOfIntegers E) : E) • (x + y) =
        (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
    rw [e]
    exact L.add_mem (hL d _ hcx) (hL c _ hdy)
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨n, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) a
    have hy0 : algebraMap (RingOfIntegers E) E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩
    have e : ((y * c : RingOfIntegers E) : E) •
        ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) =
        (n : E) • ((c : E) • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      field_simp
    rw [e]
    exact hL n _ hcx

/- English proof (translation)
Introduce `E _ _ _ r X v`. Use `exists_smul_mem_of_span X.Λ v ?_` and prove the remaining obligations. Rewrite using `[X.Λ_span]`. Conclude with `Submodule.mem_top`.
-/
theorem exists_smul_mem_lattice : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E), ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ (↑c : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by
  intro E _ _ _ r X v
  refine exists_smul_mem_of_span X.Λ v ?_
  rw [X.Λ_span]
  exact Submodule.mem_top

end GlobalTheory.SmulMemOfSpan
