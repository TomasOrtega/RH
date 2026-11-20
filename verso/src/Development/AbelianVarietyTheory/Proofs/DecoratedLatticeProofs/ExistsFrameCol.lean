import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

def finv {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ)
    (Φ : Matrix Unit n k → ℂ) (x : Matrix n Unit k) : ℂ :=
  C * ∫ η : n → k, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν)

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `secondCountable k` as an intermediate fact. Use `t2Space k` as an intermediate fact. Set `e : (n → k) ≃ₜ Matrix Unit n k` to `{ toFun := fun η => Matrix.of fun _ r => η r invFun := fun M => M () left_inv := fun _ => rfl right_inv := fun M => by ext i j; rfl continuous_toFun := by fun_prop continuous_invFun := by fun_prop }`. Establish `h1 : Continuous fun η : n → k => Φ (Matrix.of fun _ r => η r)` using `hΦ.1.continuous.comp e.continuous`. Establish `h2 : HasCompactSupport fun η : n → k => Φ (Matrix.of fun _ r => η r)` using `hΦ.2.comp_homeomorph e`.

Use `Continuous.integrable_of_hasCompactSupport (h1.mul ?_) h2.mul_right` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (hψ.comp (by fun_prop))`.
-/
theorem integrable_row (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (x : Matrix n Unit k) :
    Integrable (fun η : n → k => Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 : Continuous fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.1.continuous.comp e.continuous
  have h2 : HasCompactSupport fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.2.comp_homeomorph e
  refine Continuous.integrable_of_hasCompactSupport (h1.mul ?_) h2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [finv, Pi.add_apply, add_mul]`. Rewrite using `[integral_add (integrable_row ψk hψ ν hΦ x) (integrable_row ψk hψ ν hΨ x), mul_add]`.
-/
theorem finv_add (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ)
    {Φ Ψ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (hΨ : Ψ ∈ SB (Matrix Unit n k)) :
    finv ψk ν C (Φ + Ψ) = finv ψk ν C Φ + finv ψk ν C Ψ := by
  funext x
  simp only [finv, Pi.add_apply, add_mul]
  rw [integral_add (integrable_row ψk hψ ν hΦ x) (integrable_row ψk hψ ν hΨ x), mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [finv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finv_smul (ψk : AddChar k Circle) (ν : Measure k) (C a : ℂ) (Φ : Matrix Unit n k → ℂ) :
    finv ψk ν C (a • Φ) = a • finv ψk ν C Φ := by
  funext x
  simp only [finv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

/- English proof (translation)
Use `secondCountable k` as an intermediate fact. Simplify using `only [finv, h]`. Rewrite using `[mul_left_comm]`. Use `congr 1`. Rewrite using `[← integral_const_mul]`.

Use `conv_lhs => rw [← integral_add_right_eq_self _ (fun r => -(x () r))]`. Use `congr 1`. Use function extensionality and compare the values at `η`. Establish `e1 : (Matrix.of fun _ r => (η + fun r => -(x () r)) r : Matrix Unit n k) + x = Matrix.of fun _ r => η r`. Use extensionality with `i j`.

Simplify using `[Subsingleton.elim i ()]`. Rewrite using `[e1]`. Establish `e2 : (η + fun r => -(x () r)) ⬝ᵥ (fun r => a r ()) = (η ⬝ᵥ fun r => a r ()) + -(∑ r, x () r * a r ())`. Simplify using `only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]`. Rewrite using `[e2, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem finv_trans (ψk : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ) (x : Matrix Unit n k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = Φ (t + x)) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = (ψk (-(∑ r, x () r * a r ())) : ℂ) * finv ψk ν C Φ a := by
  have := secondCountable k
  simp only [finv, h]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ (fun r => -(x () r))]
  congr 1
  funext η
  have e1 : (Matrix.of fun _ r => (η + fun r => -(x () r)) r : Matrix Unit n k) + x = Matrix.of fun _ r => η r := by
    ext i j; simp [Subsingleton.elim i ()]
  rw [e1]
  have e2 : (η + fun r => -(x () r)) ⬝ᵥ (fun r => a r ()) = (η ⬝ᵥ fun r => a r ()) + -(∑ r, x () r * a r ()) := by
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  rw [e2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/- English proof (translation)
Simplify using `only [finv, h]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `η`. Establish `e : (η ⬝ᵥ fun r => (a + t₀) r ()) = (η ⬝ᵥ fun r => a r ()) + ∑ r, η r * t₀ r ()`.

Simplify using `[dotProduct, mul_add, Finset.sum_add_distrib]`. Rewrite using `[e, AddChar.map_add_eq_mul, Circle.coe_mul]`. Simplify using `only [Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finv_mod (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ) (t₀ : Matrix n Unit k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ t) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = finv ψk ν C Φ (a + t₀) := by
  simp only [finv, h]
  congr 1
  congr 1
  funext η
  have e : (η ⬝ᵥ fun r => (a + t₀) r ()) = (η ⬝ᵥ fun r => a r ()) + ∑ r, η r * t₀ r () := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisO, symplOH, hs, hadd]`.
-/
theorem heis_comp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (κ : WO S L'' → WO L S)
    (hadd : ∀ w w', κ (w + w') = κ w + κ w') (hs : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w')
    (u : WO S L'') (f : WO L S → ℂ) :
    (fun w => heisO ψ L S (κ u) f (κ w)) = heisO ψ S L'' u (fun w => f (κ w)) := by
  funext w
  simp only [heisO, symplOH, hs, hadd]

/- English proof (translation)
Set `i₀ : Fin N` to `⟨0, by omega⟩`. Establish `hu : ∀ i : Fin N, i = i₀` using `fun i => Fin.ext (by omega)`. Establish `h0 : z₀ i₀ ≠ 0` using `fun h => hz (funext fun i => by rw [hu i]; exact h)`. Use `⟨⟨Matrix.of fun r _ => z₀ r, Matrix.of fun _ _ => (z₀ i₀)⁻¹, ?_, ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[hu i, hu j, Matrix.mul_apply, Matrix.one_apply_eq]`. Simplify using `[h0]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq, Fintype.sum_eq_single i₀ fun x hx => absurd (hu x) hx]`. Simplify using `[h0]`.
-/
theorem exists_frame_col {k : Type} [Field k] {N : ℕ} (hN : N = 1) (z₀ : Fin N → k) (hz : z₀ ≠ 0) :
    ∃ F : Frame k N Unit, ∀ r, F.β r () = z₀ r := by
  let i₀ : Fin N := ⟨0, by omega⟩
  have hu : ∀ i : Fin N, i = i₀ := fun i => Fin.ext (by omega)
  have h0 : z₀ i₀ ≠ 0 := fun h => hz (funext fun i => by rw [hu i]; exact h)
  refine ⟨⟨Matrix.of fun r _ => z₀ r, Matrix.of fun _ _ => (z₀ i₀)⁻¹, ?_, ?_⟩, fun _ => rfl⟩
  · ext i j
    rw [hu i, hu j, Matrix.mul_apply, Matrix.one_apply_eq]
    simp [h0]
  · ext i j
    rw [Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq, Fintype.sum_eq_single i₀ fun x hx => absurd (hu x) hx]
    simp [h0]

end GlobalTheory.KappaModel
