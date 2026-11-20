import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemThetaDomainIffIsSiegelAddTranspose
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnThetaProdOfNormal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.LevelBasis

section Real
open ReciprocityTheory.PTheta Matrix

/- English proof (translation)
Establish `key : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ), Complex.exp (2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ (fun i => (m i : ℂ)) - ofRealVec b ⬝ᵥ (fun i => (n i : ℂ)) - ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l = eC ((l : ℂ) * (ofRealVec …`. Introduce `m n z`. Unfold `eC`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`.

Unfold `ofIntVec`. Expand and normalize the polynomial expressions, which then agree. Establish `e : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ), z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) = z + τ *ᵥ ofIntVec n + ofIntVec m`. Introduce `m n z`. Unfold `ofIntVec`.

Normalize the expressions using the abelian group laws. Rewrite using `[mem_thetaLevelChar]`. Use `and_congr Iff.rfl ⟨fun h n m z => ?_, fun h m n z => ?_⟩` and prove the remaining obligations. Rewrite using `[← key, ← e]`. Conclude with `h m n z`.

Rewrite using `[key, e]`. Conclude with `h n m z`.
-/
theorem isLevel_iff {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    IsLevel τ (ofRealVec a) (ofRealVec b) l F ↔ F ∈ thetaLevelChar a b l τ := by
  have key : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      Complex.exp (2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ (fun i => (m i : ℂ)) - ofRealVec b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l =
      eC ((l : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(l : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
    intro m n z
    unfold eC
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    unfold ofIntVec
    ring
  have e : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) = z + τ *ᵥ ofIntVec n + ofIntVec m := by
    intro m n z
    unfold ofIntVec
    abel
  rw [mem_thetaLevelChar]
  refine and_congr Iff.rfl ⟨fun h n m z => ?_, fun h m n z => ?_⟩
  · rw [← key, ← e]; exact h m n z
  · rw [key, e]; exact h n m z

/- English proof (translation)
Establish `H` using `thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds (Fin g) ((fun i => (c i : ℝ) / l) + a) ((l : ℝ) • b)`. Establish `hd : Differentiable ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => (((l : ℂ) • q.2, fun i j => (l : ℂ) * ((1 / 2 : ℂ) * (q.1 i j + q.1 j i))) : (Fin g → ℂ) × (Fin g → Fin g → ℂ)))` using `by fun_prop`. Use `(H.comp hd.differentiableOn fun q hq => ?_).congr fun q _ => rfl` and prove the remaining obligations. Conclude with `siegelSubDomain_and_domainOpen.1 _ (smul_mem_siegelH hq.1 hl)`.
-/
theorem holFam_levelTheta {g : ℕ} (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) (c : Fin g → ℤ) :
    HolFam (Key.phDom g) (fun p => levelTheta a b l (per p) c) := by
  have H := thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds (Fin g)
    ((fun i => (c i : ℝ) / l) + a) ((l : ℝ) • b)
  have hd : Differentiable ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) =>
      (((l : ℂ) • q.2, fun i j => (l : ℂ) * ((1 / 2 : ℂ) * (q.1 i j + q.1 j i))) :
        (Fin g → ℂ) × (Fin g → Fin g → ℂ))) := by
    fun_prop
  refine (H.comp hd.differentiableOn fun q hq => ?_).congr fun q _ => rfl
  exact siegelSubDomain_and_domainOpen.1 _ (smul_mem_siegelH hq.1 hl)

/- English proof (translation)
Set `e : Fin (l ^ g) ≃ (Fin g → Fin l)` to `finFunctionFinEquiv.symm`. Set `r : Fin (l ^ g) → Fin g → ℤ` to `fun k i => ((e k i : ℕ) : ℤ)`. Establish `hr : Function.Bijective fun k i => (r k i : ZMod l)` using `(@bijective_fin_zmod (Fin g) l hl).comp e.bijective`. Use `⟨fun k p => levelTheta a b l (per p) (r k), fun k => holFam_levelTheta a b hl _, fun p hp => ⟨fun k => (isLevel_iff _ _ _ _ _).2 (levelTheta_mem hp hl _), fun F hF => ?_⟩⟩` and prove the remaining obligations. Set `B` to `thetaLevelCharBasis a b (τ := per p) hp hl hr`.

Establish `hF'` using `(isLevel_iff _ _ _ _ _).1 hF`. Establish `hB : ∀ (c : Fin (l ^ g) → ℂ) z, ((∑ k, c k • B k : thetaLevelChar a b l (per p)) : (Fin g → ℂ) → ℂ) z = ∑ k, c k * levelTheta a b l (per p) (r k) z` using `fun c z => by`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`.

Conclude with `congrArg _ (congrFun (thetaLevelCharBasis_apply (τ := per p) hp hl hr k) z)`. Use `⟨fun k => B.repr ⟨F, hF'⟩ k, fun z => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[← hB, B.sum_repr]`. Establish `: (⟨F, hF'⟩ : thetaLevelChar a b l (per p)) = ∑ k, c k • B k` using `Subtype.ext (funext fun z => by`. Rewrite using `[hB]`.

Conclude with `hc z)`. Use function extensionality and compare the values at `k`. Rewrite using `[this, B.repr_sum_self]`.
-/
theorem exists_levBasis_real (g : ℕ) (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) :
    ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis (ofRealVec a) (ofRealVec b) l Th := by
  let e : Fin (l ^ g) ≃ (Fin g → Fin l) := finFunctionFinEquiv.symm
  let r : Fin (l ^ g) → Fin g → ℤ := fun k i => ((e k i : ℕ) : ℤ)
  have hr : Function.Bijective fun k i => (r k i : ZMod l) := (@bijective_fin_zmod (Fin g) l hl).comp e.bijective
  refine ⟨fun k p => levelTheta a b l (per p) (r k), fun k => holFam_levelTheta a b hl _, fun p hp =>
    ⟨fun k => (isLevel_iff _ _ _ _ _).2 (levelTheta_mem hp hl _), fun F hF => ?_⟩⟩
  let B := thetaLevelCharBasis a b (τ := per p) hp hl hr
  have hF' := (isLevel_iff _ _ _ _ _).1 hF
  have hB : ∀ (c : Fin (l ^ g) → ℂ) z, ((∑ k, c k • B k : thetaLevelChar a b l (per p)) : (Fin g → ℂ) → ℂ) z =
      ∑ k, c k * levelTheta a b l (per p) (r k) z := fun c z => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (congrFun (thetaLevelCharBasis_apply (τ := per p) hp hl hr k) z)
  refine ⟨fun k => B.repr ⟨F, hF'⟩ k, fun z => ?_, fun c hc => ?_⟩
  · rw [← hB, B.sum_repr]
  · have : (⟨F, hF'⟩ : thetaLevelChar a b l (per p)) = ∑ k, c k • B k := Subtype.ext (funext fun z => by
      rw [hB]; exact hc z)
    funext k
    rw [this, B.repr_sum_self]

end Real

/- English proof (translation)
Introduce `g a b l h hl`. Use `exists_levBasis_real g (fun i => (a i).re) (fun i => (b i).re) (l := l) hl` as an intermediate fact. Rewrite `this` using `[TorusAlg.ofRealVec_re h.1, TorusAlg.ofRealVec_re h.2]`. Then use the resulting hypothesis.
-/
theorem exists_levBasis : ∀ (g : ℕ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → 1 ≤ l → ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis a b l Th := by
  intro g a b l h hl
  have := exists_levBasis_real g (fun i => (a i).re) (fun i => (b i).re) (l := l) hl
  rwa [TorusAlg.ofRealVec_re h.1, TorusAlg.ofRealVec_re h.2] at this

end GlobalTheory.KeyKa.LevelBasis
end
