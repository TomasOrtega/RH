import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCoordLine

open Matrix
open scoped ComplexOrder

noncomputable def coordEquiv (D : D7) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g) :
    (Fin g → ℂ) ≃L[ℂ] VC D N N' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w τ i j => w (e (τ, i, j))
      invFun := fun z k => z (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by ext k; simp
      right_inv := fun z => by ext τ i j; simp }

/- English proof (translation)
Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Hf, dotProduct, ← e.sum_comp, Fintype.sum_prod_type]`. Simplify using `only [Fintype.sum_prod_type]`. Rewrite using `[Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Conclude with `mul_comm _ _`.
-/
theorem Hf_coordEquiv (D : D7) (T : Tor D) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g)
    (z a : Fin g → ℂ) :
    star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z =
      Hf D T (coordEquiv D N N' g e z) (coordEquiv D N N' g e a) := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Hf, dotProduct,
    ← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

/- English proof (translation)
Simplify using `[al, norm_zpow]`.
-/
theorem norm_al (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

/- English proof (translation)
Establish `h` using `hG.2 x hx z`. Establish `h0 : al D T x ≠ 0` using `fun h => by simpa [h] using norm_al D T x`. Establish `h1 : Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = 1`. Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h, U]`. Establish `h2` using `inv_mul_cancel₀ h0`. Take the linear combination `(-(G (z + x)) * (Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2))) * h2 - G (z + x) * h1`.
-/
theorem transl_of_mem (D : D7) (T : Tor D) {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {x : VC D N N'} (hx : x ∈ A) (z : VC D N N') :
    G (z + x) = (al D T x)⁻¹ * Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) * G z := by
  have h := hG.2 x hx z
  have h0 : al D T x ≠ 0 := fun h => by simpa [h] using norm_al D T x
  have h1 : Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [← h, U]
  have h2 := inv_mul_cancel₀ h0
  linear_combination (-(G (z + x)) * (Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2))) * h2 - G (z + x) * h1

/- English proof (translation)
Introduce `D T N N' A ha hd hA F hF G hG h0`. Set `e` to `Fintype.equivFin (D.what₂.Tau × Fin N' × Fin N)`. Use `set g := Fintype.card (D.what₂.Tau × Fin N' × Fin N)`. Set `L` to `coordEquiv D N N' g e`. Establish `hH : ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).PosDef` using `Matrix.PosDef.one.smul (inv_pos.2 ha)`.

Set `Λ : AddSubgroup (Fin g → ℂ)` to `A.comap L.toLinearEquiv.toAddEquiv.toAddMonoidHom`. Establish `hΛ : ∀ a, a ∈ Λ ↔ L a ∈ A` using `fun a => Iff.rfl`. Use `haveI : DiscreteTopology Λ := DiscreteTopology.of_continuous_injective (f := fun a : Λ => (⟨L a, a.2⟩ : A)) (Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _) (fun a b h => Subtype.ext (L.injective (congrArg Subtype.val h)))`. Establish `hsw : ∀ v a, (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im = -(Hf D T (L v) (L a)).im` using `fun v a => by`. Rewrite using `[ThetaTranslSpan.herm_swap hH, Hf_coordEquiv D T N N' g e]`.

Simplify using `[L]`. Establish `htr : ∀ P ∈ ThSp D T A, ∀ a ∈ Λ, ∀ z, (P ∘ L) (z + a) = (al D T (L a))⁻¹ * Complex.exp (Real.pi * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z) + Real.pi / 2 * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a)) * (P ∘ L) z` using `fun P hP a haΛ z => by`. Rewrite using `[Hf_coordEquiv D T N N' g e, Hf_coordEquiv D T N N' g e, Function.comp_apply, map_add]`. Conclude with `transl_of_mem D T hP ((hΛ a).1 haΛ) _`. Establish `hsd : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im = k) ↔ v ∈ Λ`.

Introduce `v`. Rewrite using `[hΛ, hA]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Take `⟨k, hk⟩` from `h (L.symm y) (by simpa [hΛ] using hy)`.

Rewrite `hk` using `[hsw, L.apply_symm_apply]`. Conclude with `⟨-k, by push_cast; linarith⟩`. Introduce `h a haΛ`. Take `⟨k, hk⟩` from `h (L a) ((hΛ a).1 haΛ)`. Conclude with `⟨-k, by rw [hsw, hk]; push_cast; rfl⟩`.

Take `⟨c, hc⟩` from `ThetaTranslSpan.exists_eq_smul hH Λ hsd (fun a => (al D T (L a))⁻¹) (G ∘ L) (F ∘ L) (fun a _ => by rw [norm_inv, norm_al, inv_one]) (hG.1.comp L.differentiable) (fun h => h0 (funext fun z => by simpa using congrFun h (L.symm z))) (htr G hG) (hF.1.comp L.differentiable) (htr F hF)`. Conclude with `⟨c, funext fun z => by simpa using congrFun hc (L.symm z)⟩`.
-/
theorem exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  intro D T N N' A ha hd hA F hF G hG h0
  let e := Fintype.equivFin (D.what₂.Tau × Fin N' × Fin N)
  set g := Fintype.card (D.what₂.Tau × Fin N' × Fin N)
  let L := coordEquiv D N N' g e
  have hH : ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (inv_pos.2 ha)
  let Λ : AddSubgroup (Fin g → ℂ) := A.comap L.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hΛ : ∀ a, a ∈ Λ ↔ L a ∈ A := fun a => Iff.rfl
  haveI : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := fun a : Λ => (⟨L a, a.2⟩ : A))
      (Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (L.injective (congrArg Subtype.val h)))
  have hsw : ∀ v a, (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im =
      -(Hf D T (L v) (L a)).im := fun v a => by
    rw [ThetaTranslSpan.herm_swap hH, Hf_coordEquiv D T N N' g e]; simp [L]
  have htr : ∀ P ∈ ThSp D T A, ∀ a ∈ Λ, ∀ z, (P ∘ L) (z + a) = (al D T (L a))⁻¹ * Complex.exp
      (Real.pi * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z) +
        Real.pi / 2 * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a)) *
          (P ∘ L) z := fun P hP a haΛ z => by
    rw [Hf_coordEquiv D T N N' g e, Hf_coordEquiv D T N N' g e, Function.comp_apply, map_add]
    exact transl_of_mem D T hP ((hΛ a).1 haΛ) _
  have hsd : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ,
      (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im = k) ↔ v ∈ Λ := by
    intro v
    rw [hΛ, hA]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (L.symm y) (by simpa [hΛ] using hy)
      rw [hsw, L.apply_symm_apply] at hk
      exact ⟨-k, by push_cast; linarith⟩
    · intro h a haΛ
      obtain ⟨k, hk⟩ := h (L a) ((hΛ a).1 haΛ)
      exact ⟨-k, by rw [hsw, hk]; push_cast; rfl⟩
  obtain ⟨c, hc⟩ := ThetaTranslSpan.exists_eq_smul hH Λ hsd (fun a => (al D T (L a))⁻¹)
    (G ∘ L) (F ∘ L) (fun a _ => by rw [norm_inv, norm_al, inv_one])
    (hG.1.comp L.differentiable)
    (fun h => h0 (funext fun z => by simpa using congrFun h (L.symm z)))
    (htr G hG) (hF.1.comp L.differentiable) (htr F hF)
  exact ⟨c, funext fun z => by simpa using congrFun hc (L.symm z)⟩

end GlobalTheory.ThetaCoordLine
