import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Reindex

variable {D : D7}

/- English proof (translation)
Take `⟨u, hu, h⟩` from `GlobalTheory.JacClosed.flagN_le d hn`. Establish `hb : blockX d γ = u.1` using `by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]`. Establish `hr : blockX d γ ∈ ratMx D ρ ρ` using `ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))`. Take `⟨u₀, hu₀⟩` from `mem_ratMx.1 hr`. Conclude with `⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩`.
-/
theorem exists_rat_block {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hq : γ ∈ GQ V)
    (hn : γ ∈ flagN d) : ∃ (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E),
      blockX d γ = u.1.1 ∧ rat u₀ = u.1.1 := by
  obtain ⟨u, hu, h⟩ := GlobalTheory.JacClosed.flagN_le d hn
  have hb : blockX d γ = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  have hr : blockX d γ ∈ ratMx D ρ ρ :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))
  obtain ⟨u₀, hu₀⟩ := mem_ratMx.1 hr
  exact ⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩

/- English proof (translation)
Establish `h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0` using `fun i j hij => incA_injective (by`. Rewrite using `[map_zero]`. Use `congrFun (congrFun h i) j` as an intermediate fact. Express the relevant statement in the definitionally equal form `incA D (u₀ i j) = _ at this`. Rewrite using `[this]`.

Conclude with `((mem_UX.1 u.2) i j).1 hij)`. Establish `h1 : ∀ i : Fin ρ, u₀ i i = 1` using `fun i => incA_injective (by`. Rewrite using `[map_one]`. Use `congrFun (congrFun h i) i` as an intermediate fact. Express the relevant statement in the definitionally equal form `incA D (u₀ i i) = _ at this`.

Rewrite using `[this]`. Conclude with `((mem_UX.1 u.2) i i).2)`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]`. Simplify using `[h1]`.
-/
theorem det_eq_one {ρ : ℕ} (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) (h : rat u₀ = u.1.1) :
    u₀.det = 1 := by
  have h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0 := fun i j hij => incA_injective (by
    rw [map_zero]
    have := congrFun (congrFun h i) j
    change incA D (u₀ i j) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i j).1 hij)
  have h1 : ∀ i : Fin ρ, u₀ i i = 1 := fun i => incA_injective (by
    rw [map_one]
    have := congrFun (congrFun h i) i
    change incA D (u₀ i i) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i i).2)
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]
  simp [h1]

/- English proof (translation)
Simplify using `only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem gramQ_mul (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u₀) = u₀ᴴ * gramQ W x * u₀ := by
  simp only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.Unf.Reindex

open GlobalTheory.Unf.Reindex in

/- English proof (translation)
Introduce `D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ`. Take `⟨u, u₀, hb, hu₀⟩` from `exists_rat_block d hq hn`. Establish `hdet : IsUnit u₀.det` using `by rw [det_eq_one u u₀ hu₀]; exact isUnit_one`. Establish `hdet' : IsUnit u₀ᴴ.det` using `by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one`. Use `set G₀ := gramQ W x₀`.

Establish `hG : u₀ᴴ * G₀ * u₀ = G₀`. Apply `rat_injective` to reduce the goal to its premises. Use `hx₀.2 u.1 u.2` as an intermediate fact. Rewrite using `[rat_mul, rat_mul, rat_conjTranspose, hu₀]`. Rewrite using `[Matrix.mul_assoc]`.

Conclude with `this`. Establish `key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀`. Introduce `x`. Rewrite using `[gramQ_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀` using `h.trans hG.symm`. Establish `h3` using `congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2`. Simplify using `only [Matrix.mul_assoc] at h3`. Simplify `h3` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet]`.

Introduce `h`. Rewrite using `[h, hG]`. Establish `hinv : u₀ * u₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `hinv' : u₀⁻¹ * u₀ = 1` using `Matrix.nonsing_inv_mul _ hdet`. Set `e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃ {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀}` to `{ toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩ invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by`.

Use `(key (x.1 * u₀⁻¹)).2 h` as an intermediate fact. Rewrite using `[Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩` and apply the resulting hypothesis. Use `left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])`. Use `right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }`. Establish `hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1`.

Introduce `x`. Use `(GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_` and prove the remaining obligations. Rewrite using `[rat_mul, hu₀, hb]`. Rewrite using `[tsum_congr hterm]`. Conclude with `Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)`.
-/
theorem GlobalTheory.Unf.tsum_offBase_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  intro D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ
  obtain ⟨u, u₀, hb, hu₀⟩ := exists_rat_block d hq hn
  have hdet : IsUnit u₀.det := by rw [det_eq_one u u₀ hu₀]; exact isUnit_one
  have hdet' : IsUnit u₀ᴴ.det := by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one
  set G₀ := gramQ W x₀
  have hG : u₀ᴴ * G₀ * u₀ = G₀ := by
    apply rat_injective
    have := hx₀.2 u.1 u.2
    rw [rat_mul, rat_mul, rat_conjTranspose, hu₀]
    rw [Matrix.mul_assoc]; exact this
  have key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀ := by
    intro x
    rw [gramQ_mul]
    constructor
    · intro h
      have h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀ := h.trans hG.symm
      have h3 := congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2
      simp only [Matrix.mul_assoc] at h3
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet] using h3
    · intro h; rw [h, hG]
  have hinv : u₀ * u₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv' : u₀⁻¹ * u₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  let e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃
      {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} :=
    { toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩
      invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by
        have := (key (x.1 * u₀⁻¹)).2 h
        rwa [Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩
      left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])
      right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }
  have hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀},
      term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1 := by
    intro x
    refine (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_
    rw [rat_mul, hu₀, hb]
  rw [tsum_congr hterm]
  exact Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)

end
