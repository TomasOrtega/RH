import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifDet

/- English proof (translation)
Introduce `F _ _ 𝔠 X L u δ`. Take `⟨-, h2⟩` from `UnifTangent.tangent_bijection u X.dim`. Establish `he : ∀ k : Fin (Module.finrank ℚ F), ∃ t : X.Lie, u.IsDiff (Pi.single k 1) t.hom` using `fun k => by`. Take `⟨t, ⟨ht, hd⟩, -⟩` from `h2 (Pi.single k 1)`. Conclude with `⟨Serre.Lie.mk X.rm t ht, hd⟩`.

Use `choose e he using he`. Set `T : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] X.Lie` to `Fintype.linearCombination ℂ e`. Establish `hT : ∀ w : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff w (T w).hom` using `fun w => by`. Establish `hc : IsLieComb w (fun k => (e k).hom) (T w).hom`. Rewrite using `[Serre.Lie.isLieComb_iff]`.

Simplify using `[T, Fintype.linearCombination_apply]`. Use `UnifDifferential.isDiff_of_isLieComb X.A L _ _ u (fun k => Pi.single k 1) (fun k => (e k).hom) w (T w).hom (fun k => (e k).isTangent) he hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `⟨δ.compLinearMap T (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))), fun v W hW => ?_⟩` and prove the remaining obligations. Establish `hv : v = fun j => T (W j)` using `funext fun j => Serre.Lie.ext ((h2 (W j)).unique ⟨(v j).isTangent, hW j⟩ ⟨(T (W j)).isTangent, hT (W j)⟩)`. Establish `key` using `DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))) (δ.compLinearMap T)) W`. Rewrite using `[hv]`. Use `key.trans ?_` and prove the remaining obligations.

Rewrite using `[Pi.basisFun_det]`. Both sides reduce to the same expression.
-/
theorem detOmega_eq_const_mul_det :
    ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  intro F _ _ 𝔠 X L u δ
  obtain ⟨-, h2⟩ := UnifTangent.tangent_bijection u X.dim

  have he : ∀ k : Fin (Module.finrank ℚ F), ∃ t : X.Lie, u.IsDiff (Pi.single k 1) t.hom := fun k => by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose e he using he
  let T : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ e
  have hT : ∀ w : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff w (T w).hom := fun w => by
    have hc : IsLieComb w (fun k => (e k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A L _ _ u (fun k => Pi.single k 1) (fun k => (e k).hom) w
      (T w).hom (fun k => (e k).isTangent) he hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨δ.compLinearMap T (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))), fun v W hW => ?_⟩
  have hv : v = fun j => T (W j) := funext fun j =>
    Serre.Lie.ext ((h2 (W j)).unique ⟨(v j).isTangent, hW j⟩ ⟨(T (W j)).isTangent, hT (W j)⟩)
  have key := DFunLike.congr_fun
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))) (δ.compLinearMap T)) W
  rw [hv]
  refine key.trans ?_
  rw [Pi.basisFun_det]
  rfl

end GlobalTheory.UnifDet
