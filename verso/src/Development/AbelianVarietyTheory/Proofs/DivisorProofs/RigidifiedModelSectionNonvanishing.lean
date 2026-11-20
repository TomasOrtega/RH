import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.SecJet

/- English proof (translation)
Establish `hw : φ ≫ G.hom = G'.hom ≫ f` using `h.1.w`. Set `x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G` to `Over.homMk ((1 : 𝟙_ (Over S') ⟶ G').left ≫ φ) (by`. Rewrite using `[Category.assoc, hw, ← Category.assoc, Over.w]`. Use the proof step `rfl)`. Establish `h1` using `h.2 (𝟙_ (Over S')) 1 1 x₀ x₀ rfl rfl`.

Rewrite `h1` using `[_root_.mul_one]`. Establish `h2 : x₀ * x₀ = x₀` using `Over.OverMorphism.ext h1`. Establish `h3 : x₀ = 1` using `mul_left_cancel (h2.trans (_root_.mul_one x₀).symm)`. Establish `h4` using `congrArg (·.left) h3`. Establish `e1 : (1 : 𝟙_ (Over S') ⟶ G').left = eSec G'` using `Category.id_comp (eSec G')`.

Establish `e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left = f ≫ eSec G` using `congrArg (· ≫ eSec G) (Category.id_comp f)`. Conclude with `(congrArg (· ≫ φ) e1).symm.trans (h4.trans e2)`.
-/
theorem grpPullback_eSec_comp {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : 𝟙_ (Over S') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
  have h1 := h.2 (𝟙_ (Over S')) 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h1
  have h3 : x₀ = 1 := mul_left_cancel (h2.trans (_root_.mul_one x₀).symm)
  have h4 := congrArg (·.left) h3
  have e1 : (1 : 𝟙_ (Over S') ⟶ G').left = eSec G' := Category.id_comp (eSec G')
  have e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left = f ≫ eSec G :=
    congrArg (· ≫ eSec G) (Category.id_comp f)
  exact (congrArg (· ≫ φ) e1).symm.trans (h4.trans e2)

/- English proof (translation)
Rewrite using `[valR, dif_pos h]`. Conclude with `((s.isUnit.map _).map _).ne_zero`.
-/
theorem valR_unit_ne_zero {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) : valR x U s.val ≠ 0 := by
  rw [valR, dif_pos h]
  exact ((s.isUnit.map _).map _).ne_zero

/- English proof (translation)
Introduce `K _ _ P AA _ _ φ MM N w i₀ hm hi`. Establish `he : eSec P.A ≫ φ = spMap (algebraMap (𝓞 K) K) ≫ eSec AA` using `grpPullback_eSec_comp hm.2.2.2.1`. Establish `hex : ∃ p : PUnit → MM.L.ι, ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p)`. Set `z : Sp K` to `(default : PrimeSpectrum K)`. Establish `hz : (spMap (algebraMap (𝓞 K) K) ≫ eSec AA) z ∈ ⨆ i, MM.L.U i`.

Rewrite using `[MM.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz`. Use `⟨fun _ => i, fun y _ => ?_⟩` and prove the remaining obligations. Take `rfl : y = z` from `Subsingleton.elim (α := PrimeSpectrum K) _ _`.

Conclude with `Set.mem_iInter.2 fun _ => hi`. Rewrite using `[rigVal, dif_pos hex]`. Use `mul_ne_zero (valR_unit_ne_zero _ _ ?_ _) (valR_unit_ne_zero _ _ hex.choose_spec _)` and prove the remaining obligations. Introduce `y hy`. Use `⟨hi hy, Set.mem_iInter.2 fun k => ?_⟩` and prove the remaining obligations.

Establish `h1 : (spMap (algebraMap (𝓞 K) K) ≫ eSec AA) y ∈ MM.L.U (hex.choose k)` using `Set.mem_iInter.1 (hex.choose_spec hy) k`. Rewrite `h1` using `[← he]`. Conclude with `h1`.
-/
theorem rigVal_ne_zero : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (i₀ : (lbPow P.L N).ι), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → rigVal w i₀ ≠ 0 := by
  intro K _ _ P AA _ _ φ MM N w i₀ hm hi
  have he : eSec P.A ≫ φ = spMap (algebraMap (𝓞 K) K) ≫ eSec AA := grpPullback_eSec_comp hm.2.2.2.1
  have hex : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) := by
    let z : Sp K := (default : PrimeSpectrum K)
    have hz : (spMap (algebraMap (𝓞 K) K) ≫ eSec AA) z ∈ ⨆ i, MM.L.U i := by
      rw [MM.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine ⟨fun _ => i, fun y _ => ?_⟩
    obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact Set.mem_iInter.2 fun _ => hi
  rw [rigVal, dif_pos hex]
  refine mul_ne_zero (valR_unit_ne_zero _ _ ?_ _) (valR_unit_ne_zero _ _ hex.choose_spec _)
  intro y hy
  refine ⟨hi hy, Set.mem_iInter.2 fun k => ?_⟩
  have h1 : (spMap (algebraMap (𝓞 K) K) ≫ eSec AA) y ∈ MM.L.U (hex.choose k) :=
    Set.mem_iInter.1 (hex.choose_spec hy) k
  rw [← he] at h1
  exact h1

end GlobalTheory.SecJet
