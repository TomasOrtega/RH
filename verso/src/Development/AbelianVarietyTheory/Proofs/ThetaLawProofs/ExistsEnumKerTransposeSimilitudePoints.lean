import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CardHomVanishingOfDiagBasis
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

/- English proof (translation)
Introduce `laws K _ _ x m al hm hal`. Use `haveI := x.P.isAb.comm`. Use `haveI := x.P.isAb.smooth`. Use `haveI : LocallyOfFiniteType x.P.A.hom := inferInstance`. Establish `hm0 : m ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hm Nat.cast_zero`. Use `letI : CommGroup (Pt x) := Hom.commGroup`. Establish `hG : ∀ k : ℕ, k ∣ m → Nat.card {y : Pt x // y ^ k = 1} = k ^ (2 * x.P.g)`. Introduce and unpack `k ⟨l, rfl⟩`.

Establish `hk : (k : K) ≠ 0` using `fun h => hm (by rw [Nat.cast_mul, h, zero_mul])`. Establish `hk1 : 1 ≤ k` using `Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])`. Conclude with `(laws.mulN (Sp K) x.P k hk1).2.2.2.2 K (𝟙 _) hk`. Establish `hcard` using `GlobalTheory.card_ker_int_matrix_four (Pt x) m (2 * x.P.g) al (Nat.pos_of_ne_zero hm0) hal hG`. Establish `hfin : Finite {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1}` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)`.

Establish `hc : Nat.card (Fin 4 → Fin (m ^ x.P.g)) = Nat.card {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1}`. Rewrite using `[hcard, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take `⟨e⟩` from `Finite.card_eq.mp hc`.

Use `⟨fun I => (e I).1, fun I I' hI p => ?_, fun I c => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne push_neg at hne`. Use `hI (e.injective (Subtype.ext (funext fun r => ?_)))` and prove the remaining obligations. Establish `hp : p = IsLocalRing.closedPoint K` using `Subsingleton.elim _ _`. Substitute `hp` using the available equality.

Conclude with `Over.OverMorphism.ext (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) (hne r))`. Rewrite using `[List.prod_ofFn]`. Conclude with `(e I).2 c`.
-/
theorem exists_enum_ker_transpose : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧ (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) := by
  intro laws K _ _ x m al hm hal
  classical
  haveI := x.P.isAb.comm
  haveI := x.P.isAb.smooth
  haveI : LocallyOfFiniteType x.P.A.hom := inferInstance
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm Nat.cast_zero
  letI : CommGroup (Pt x) := Hom.commGroup
  have hG : ∀ k : ℕ, k ∣ m → Nat.card {y : Pt x // y ^ k = 1} = k ^ (2 * x.P.g) := by
    rintro k ⟨l, rfl⟩
    have hk : (k : K) ≠ 0 := fun h => hm (by rw [Nat.cast_mul, h, zero_mul])
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
    exact (laws.mulN (Sp K) x.P k hk1).2.2.2.2 K (𝟙 _) hk
  have hcard := GlobalTheory.card_ker_int_matrix_four (Pt x) m (2 * x.P.g) al (Nat.pos_of_ne_zero hm0) hal hG
  have hfin : Finite {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
  have hc : Nat.card (Fin 4 → Fin (m ^ x.P.g)) =
      Nat.card {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    congr 1
    ring
  obtain ⟨e⟩ := Finite.card_eq.mp hc
  refine ⟨fun I => (e I).1, fun I I' hI p => ?_, fun I c => ?_⟩
  · by_contra hne
    push_neg at hne
    refine hI (e.injective (Subtype.ext (funext fun r => ?_)))
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) (hne r))
  · rw [List.prod_ofFn]
    exact (e I).2 c

end GlobalTheory.KeyKa
