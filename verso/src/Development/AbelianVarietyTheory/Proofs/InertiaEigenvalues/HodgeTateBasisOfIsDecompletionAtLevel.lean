import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

/- English proof (translation)
Introduce `l _ act χ _ _ K m d M U Dm g J hD hH`. Take `⟨hdet, -, -, -, hrel⟩` from `hD`. Take `⟨e, u, hli, hu, hfix⟩` from `hH`. Establish `hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v`. Introduce `v`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w`. Introduce `v w h`. Establish `h2` using `congrArg (fun x => Dm⁻¹.mulVec x) h`. Simplify `h2` using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]`.

Use `⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩` and prove the remaining obligations. Use `LinearIndependent.of_comp Dm.mulVecLin ?_` and prove the remaining obligations. Establish `: (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e`. Use function extensionality and compare the values at `k`. Conclude with `hDe (e k)`.

Rewrite using `[this]`. Conclude with `hli`. Introduce `σ hσ k`. Apply `hinj` to reduce the goal to its premises. Establish `hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) = fun a => act σ (e k a)`.

Use function extensionality and compare the values at `a`. Use `conv_rhs => rw [← hDe (e k)]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`. Establish `h1` using `hfix σ hσ k`. Unfold `twAct at h1 ⊢`.

Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]`.
-/
theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
