import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

/- English proof (translation)
The claim follows from `fun p hp ↦ Set.mem_iInter.2 fun _ ↦ h hp`.
-/
theorem le_pull_chart {X Y : Scheme.{0}} (L : LB X) (q : Y ⟶ X) {D : Type} [CommRing D] (x : Sp D ⟶ Y)
    (i : L.ι) (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ (L.pull q).U (fun _ ↦ i) :=
  fun p hp ↦ Set.mem_iInter.2 fun _ ↦ h hp

/- English proof (translation)
Unfold `evU`. Rewrite using `[dif_pos h, dif_pos h, dif_pos h, map_mul]`.
-/
theorem evU_mul {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU x U (a * b) = evU x U a * evU x U b := by
  unfold evU
  rw [dif_pos h, dif_pos h, dif_pos h, map_mul]

/- English proof (translation)
Introduce `R _ X Y L _ q hT`. Take `⟨s, hs⟩` from `hT`. Use `⟨fun E _ _ z i ↦ evU z.left ((L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i)).val, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `E _ _ z i hi`. Establish `hz` using `le_pull_chart L q.left z.left i hi`.

Use `show IsUnit (evU _ _ _)`. Unfold `evU`. Rewrite using `[dif_pos hz]`. Conclude with `(s.s _).isUnit.map _`. Introduce `E _ _ E' _ _ ψ z i hi`.

Establish `hz` using `le_pull_chart L q.left z.left i hi`. Conclude with `evalSectionAtPointOrZero_specMap_comp _ E E' (ψ : E →+* E') z.left _ _ hz`. Introduce `E _ _ z i j hi hj`. Establish `hzi` using `le_pull_chart L q.left z.left i hi`. Establish `hzj` using `le_pull_chart L q.left z.left j hj`.

Establish `hV : ⊤ ≤ z.left ⁻¹ᵁ ((L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j))` using `fun p hp ↦ ⟨hzi hp, hzj hp⟩`. Establish `hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U i ⊓ L.U j)` using `fun p hp ↦ ⟨hi hp, hj hp⟩`. Establish `e` using `congrArg (fun u ↦ evU z.left _ (Units.val u)) (hs (fun _ ↦ i) (fun _ ↦ j))`. Simplify using `only [Units.val_mul] at e`. Rewrite `e` using `[evU_mul _ _ hV]`.

Establish `e1 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i))).val = evU z.left _ (s.s (fun _ ↦ i)).val` using `evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV`. Establish `e2 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ j)) (s.s (fun _ ↦ j))).val = evU z.left _ (s.s (fun _ ↦ j)).val` using `evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV`. Establish `e3 : evU z.left _ ((L.pull q.left).g (fun _ ↦ i) (fun _ ↦ j)).val = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val`. Unfold `evU`. Rewrite using `[dif_pos hV]`.

Establish `hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U i ⊓ L.U j)` using `hij`. Rewrite using `[dif_pos hij']`. Conclude with `(evalAt_pull_g L q.left z.left (fun _ ↦ i) (fun _ ↦ j) hij hV).symm`. Rewrite `e` using `[e1, e2, e3]`. Conclude with `e`.
-/
theorem exists_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  intro R _ X Y L _ q hT
  obtain ⟨s, hs⟩ := hT
  refine ⟨fun E _ _ z i ↦ evU z.left ((L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i)).val, ?_, ?_, ?_⟩
  · intro E _ _ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    show IsUnit (evU _ _ _)
    unfold evU
    rw [dif_pos hz]
    exact (s.s _).isUnit.map _
  · intro E _ _ E' _ _ ψ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    exact evalSectionAtPointOrZero_specMap_comp _ E E' (ψ : E →+* E') z.left _ _ hz
  · intro E _ _ z i j hi hj
    have hzi := le_pull_chart L q.left z.left i hi
    have hzj := le_pull_chart L q.left z.left j hj
    have hV : ⊤ ≤ z.left ⁻¹ᵁ ((L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j)) :=
      fun p hp ↦ ⟨hzi hp, hzj hp⟩
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U i ⊓ L.U j) := fun p hp ↦ ⟨hi hp, hj hp⟩
    have e := congrArg (fun u ↦ evU z.left _ (Units.val u)) (hs (fun _ ↦ i) (fun _ ↦ j))
    simp only [Units.val_mul] at e
    rw [evU_mul _ _ hV] at e
    have e1 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i))).val =
        evU z.left _ (s.s (fun _ ↦ i)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e2 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ j)) (s.s (fun _ ↦ j))).val =
        evU z.left _ (s.s (fun _ ↦ j)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e3 : evU z.left _ ((L.pull q.left).g (fun _ ↦ i) (fun _ ↦ j)).val =
        evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val := by
      unfold evU
      rw [dif_pos hV]
      have hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U i ⊓ L.U j) := hij
      rw [dif_pos hij']
      exact (evalAt_pull_g L q.left z.left (fun _ ↦ i) (fun _ ↦ j) hij hV).symm
    rw [e1, e2, e3] at e
    exact e

end GlobalTheory.PtExt
