import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

/- English proof (translation)
Introduce `laws K _ _ P m ξ ξ' u hm hu hinv`. Use `haveI : IsCommMonObj P.A := P.isAb.comm`. Establish `hmul : ∀ {Z : Over (Sp K)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A m = y ^ m` using `fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]`. Take `⟨v, hv⟩` from `exists_isGen_of_invariant P.isLB (K := Fin 2) ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] ![1, -1] (Out.mulA P.A m).left (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ m = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => by`. Rewrite using `[← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul, Out.mulA])`.

Use the proof step `(fun U f hf => torsion_invariant_descends (fun S _ Q n hn =>`. Set `⟨a, b, c, d, _⟩` to `laws.mulN S Q n hn`. Use the proof step `⟨a, b, c, d⟩) K P m hm U f fun y hy => hf ⟨y, hy⟩) _`. Use the proof step `(fun i => by fin_cases i`. Express the relevant statement in the definitionally equal form `((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left = (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left`.

Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA]`. Express the relevant statement in the definitionally equal form `((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left = (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left`. Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA])`. Use `u hu (fun y z J hJ => hinv y.1 y.2 z J hJ)`. Set `B : Over (Sp K)` to `Over.mk (𝟙 (Sp K))`.

Set `x : B ⟶ P.A` to `toUnit B ≫ (ξ * ξ'⁻¹)`. Set `r : B ⊗ P.A ⟶ P.A` to `snd B P.A * (toUnit _ ≫ ξ'⁻¹)`. Establish `hx : x = toUnit _ ≫ η[P.A]`. Use `P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Establish `h3 : (fun i => r.left ≫ ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) = ![(lift (fst B P.A ≫ x) (snd B P.A) ≫ μ[P.A]).left, (snd B P.A).left]`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Express the relevant statement in the definitionally equal form `(r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left = ((fst B P.A ≫ x) * snd B P.A).left`. Use `congr 1`. Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]`.

Simplify using `only [r, x, comp_toUnit_assoc, MonObj.comp_mul]`. Rewrite using `[_root_.mul_assoc, _root_.mul_comm (snd B P.A), _root_.mul_comm (toUnit _ ≫ ξ'⁻¹)]`. Express the relevant statement in the definitionally equal form `(r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left = (snd B P.A).left`. Use `congr 1`. Rewrite using `[MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]`.

Simplify using `only [r]`. Rewrite using `[GrpObj.comp_inv, inv_mul_cancel_right]`. Establish `h4 : ∃ w : LB.Gen (LB.LinComb P.L (fun i => r.left ≫ ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) ![1, -1]), w.IsGen` using `⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩`. Rewrite `h4` using `[h3]`. Take `⟨w, hw⟩` from `h4`.

Conclude with `exists_isGen_pull (Out.translDiff P.A P.L x) w hw _`. Set `s : 𝟙_ (Over (Sp K)) ⟶ B` to `Over.homMk (𝟙_ (Over (Sp K))).hom (Category.comp_id _)`. Establish `h5` using `congrArg (fun q => s ≫ q) hx`. Simplify using `only [x, comp_toUnit_assoc] at h5`. Rewrite `h5` using `[← Hom.one_def, toUnit_unit, Category.id_comp]`.

Conclude with `mul_inv_eq_one.1 h5`.
-/
theorem eq_of_invariantGen_translates :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (ξ ξ' : 𝟙_ (Over (Sp K)) ⟶ P.A) (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left, ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left] ![1, -1])), (m : K) ≠ 0 → u.IsGen → (∀ δ : 𝟙_ (Over (Sp K)) ⟶ P.A, δ ^ m = 1 → ∀ (y : P.A.left) J, Good P.L y J → val u ((toUnit P.A ≫ δ) * 𝟙 P.A).left y J = val u (𝟙 _) y J) → ξ = ξ' := by
  intro laws K _ _ P m ξ ξ' u hm hu hinv
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hmul : ∀ {Z : Over (Sp K)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A m = y ^ m :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] ![1, -1]
    (Out.mulA P.A m).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ m = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul,
        Out.mulA])
    (fun U f hf => torsion_invariant_descends (fun S _ Q n hn =>
      let ⟨a, b, c, d, _⟩ := laws.mulN S Q n hn; ⟨a, b, c, d⟩) K P m hm U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA]
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA])
    u hu (fun y z J hJ => hinv y.1 y.2 z J hJ)
  let B : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let x : B ⟶ P.A := toUnit B ≫ (ξ * ξ'⁻¹)
  let r : B ⊗ P.A ⟶ P.A := snd B P.A * (toUnit _ ≫ ξ'⁻¹)
  have hx : x = toUnit _ ≫ η[P.A] := by
    refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) =
        ![(lift (fst B P.A ≫ x) (snd B P.A) ≫ μ[P.A]).left, (snd B P.A).left] := by
      funext i
      fin_cases i
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left = ((fst B P.A ≫ x) * snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r, x, comp_toUnit_assoc, MonObj.comp_mul]
        rw [_root_.mul_assoc, _root_.mul_comm (snd B P.A), _root_.mul_comm (toUnit _ ≫ ξ'⁻¹)]
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left = (snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r]
        rw [GrpObj.comp_inv, inv_mul_cancel_right]
    have h4 : ∃ w : LB.Gen (LB.LinComb P.L (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) ![1, -1]),
        w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (Out.translDiff P.A P.L x) w hw _
  let s : 𝟙_ (Over (Sp K)) ⟶ B := Over.homMk (𝟙_ (Over (Sp K))).hom (Category.comp_id _)
  have h5 := congrArg (fun q => s ≫ q) hx
  simp only [x, comp_toUnit_assoc] at h5
  rw [← Hom.one_def, toUnit_unit, Category.id_comp] at h5
  exact mul_inv_eq_one.1 h5

end GlobalTheory
