import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hz`. Establish `hb` using `Cv.block`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 (Cv.κ k)`. Take `⟨p, hp⟩` from `hb.2.2.2 ⟨Cv.κ k, i⟩ ⟨k, rfl⟩`.

Establish `hk : p.1 = k` using `hb.1 (by have h := hb.2.2.1 p; rw [hp] at h; exact h.symm)`. Take `⟨k₀, i₀⟩` from `p`. Consider the cases of `hk`. Conclude with `⟨i₀, by simpa [Function.comp, hp] using hi⟩`. Establish `key : ∀ g, mConeMap (M'.x ∘ Cv.v) g = MvPolynomial.map Cv.φ (mConeMap M.x g)`.

Introduce `g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp`.

Simplify using `only [map_mul, hp]`. Use `congr 1`. Simplify using `[mConeMap, Cv.x_eq]`. Establish `h0 : mConeMap M.x f = 0` using `hf`. Establish `h1 : f ∈ mCoordIdeal (M'.x ∘ Cv.v)` using `by show mConeMap (M'.x ∘ Cv.v) f = 0`.

Rewrite using `[key, h0, map_zero]`. Establish `h2 : rename Cv.v f ∈ mCoordIdeal M'.x` using `GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ _ _ _ _ Cv.κ Cv.v _ M'.x hb h1`. Establish `h3` using `hz.2 _ h2`. Rewrite `h3` using `[map_rename, eval_rename]`. Then use the resulting hypothesis.
-/
theorem comp_v_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hz
  have hb := Cv.block
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (Cv.κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨Cv.κ k, i⟩ ⟨k, rfl⟩
    have hk : p.1 = k := hb.1 (by have h := hb.2.2.1 p; rw [hp] at h; exact h.symm)
    obtain ⟨k₀, i₀⟩ := p
    cases hk
    exact ⟨i₀, by simpa [Function.comp, hp] using hi⟩
  · have key : ∀ g, mConeMap (M'.x ∘ Cv.v) g = MvPolynomial.map Cv.φ (mConeMap M.x g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [mConeMap]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        simp [mConeMap, Cv.x_eq]
    have h0 : mConeMap M.x f = 0 := hf
    have h1 : f ∈ mCoordIdeal (M'.x ∘ Cv.v) := by
      show mConeMap (M'.x ∘ Cv.v) f = 0
      rw [key, h0, map_zero]
    have h2 : rename Cv.v f ∈ mCoordIdeal M'.x :=
      GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ _ _ _ _ Cv.κ Cv.v _ M'.x hb h1
    have h3 := hz.2 _ h2
    rwa [map_rename, eval_rename] at h3

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
