import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex`. Take `⟨eL, heL⟩` from `hex`. Establish `hinj : Function.Injective (TensorProduct.mk K L N 1)`. Establish `h1 : Function.Injective ((Algebra.linearMap K L).rTensor N)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective`. Introduce `x y hxy`.

Apply `(TensorProduct.lid K N).symm.injective` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises. Simplify `hxy` using `[TensorProduct.lid_symm_apply]`. Establish `hc : ∀ a, c a a = 0`. Introduce `a`.

Apply `hinj` to reduce the goal to its premises. Apply `e₂.injective` to reduce the goal to its premises. Establish `h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0` using `AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)`. Simplify using `only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]`. Set `f : M [⋀^Fin 2]→ₗ[K] N` to `{ toFun := fun w => c (w 0) (w 1) map_update_add' := by`.

Introduce `_ w i x y`. Apply the tactic sequence `fin_cases i <;> simp`. Use the proof step `map_update_smul' := by`. Introduce `_ w i r x`. Apply the tactic sequence `fin_cases i <;> simp`.

Use the proof step `map_eq_zero_of_eq' := by`. Introduce `w i j hij hne`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [hc] }`. Set `φ` to `exteriorPower.alternatingMapLinearEquiv f`. Establish `hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1)` using `fun w => exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w`.

Set `b` to `Module.Basis.ofVectorSpace K M`. Use `letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel`. Set `B` to `b.exteriorPower 2`. Set `b'` to `(Algebra.TensorProduct.basis L b).map e₁`. Establish `hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i)` using `fun i => by`.

Simplify using `[b', Algebra.TensorProduct.basis_apply]`. Set `B'` to `b'.exteriorPower 2`. Establish `key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s)`. Introduce `s`. Rewrite using `[exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.ιMulti_family, hφ, hcomp, ← heL]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [hb']`. Set `V'` to `B'.map (eL.trans e₂.symm)`. Establish `hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s)` using `fun s => by`.

Simplify using `only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]`. Rewrite using `[← key, LinearEquiv.symm_apply_apply]`. Establish `h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s))`. Establish `h` using `V'.linearIndependent`. Rewrite `h` using `[show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV']`. Then use the resulting hypothesis.

Establish `h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s))` using `h1.restrict_scalars' K`. Establish `h3 : LinearIndependent K (φ ∘ B)` using `LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2`. Set `W` to `Submodule.span K (Set.range (φ ∘ B))`. Establish `hs : Function.Surjective (W.subtype.lTensor L)`. Establish `hr : LinearMap.range (W.subtype.baseChange L) = ⊤`.

Rewrite using `[eq_top_iff, ← V'.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[hV']`. Conclude with `⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩`. Introduce `x`.

Take `⟨y, hy⟩` from `LinearMap.range_eq_top.mp hr x`. Conclude with `⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩`. Establish `hW : Function.Surjective W.subtype` using `(Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs`. Establish `hspan : ⊤ ≤ W` using `fun x _ => by`. Take `⟨y, rfl⟩` from `hW x`.

Conclude with `y.2`. Set `V` to `Module.Basis.mk h3 hspan`. Use `⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩` and prove the remaining obligations. Establish `hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ` using `B.ext fun s => by simp [V, Module.Basis.mk_apply]`. Rewrite using `[← LinearEquiv.coe_coe, hEq, hφ]`.

Both sides reduce to the same expression.
-/
theorem exteriorSquare_equiv_of_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  intro K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex
  classical
  obtain ⟨eL, heL⟩ := hex

  have hinj : Function.Injective (TensorProduct.mk K L N 1) := by
    have h1 : Function.Injective ((Algebra.linearMap K L).rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
    intro x y hxy
    apply (TensorProduct.lid K N).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy

  have hc : ∀ a, c a a = 0 := by
    intro a
    apply hinj
    apply e₂.injective
    have h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
    simp only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]
  let f : M [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun w => c (w 0) (w 1)
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ w i r x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all [hc] }
  let φ := exteriorPower.alternatingMapLinearEquiv f
  have hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1) := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w
  let b := Module.Basis.ofVectorSpace K M
  letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower 2
  let b' := (Algebra.TensorProduct.basis L b).map e₁
  have hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i) := fun i => by
    simp [b', Algebra.TensorProduct.basis_apply]
  let B' := b'.exteriorPower 2
  have key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s) := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, hφ, hcomp, ← heL]
    congr 2
    funext i
    fin_cases i <;> simp [hb']
  let V' := B'.map (eL.trans e₂.symm)
  have hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s) := fun s => by
    simp only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := by
    have h := V'.linearIndependent
    rwa [show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV'] at h
  have h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := h1.restrict_scalars' K
  have h3 : LinearIndependent K (φ ∘ B) := LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2
  let W := Submodule.span K (Set.range (φ ∘ B))
  have hs : Function.Surjective (W.subtype.lTensor L) := by
    have hr : LinearMap.range (W.subtype.baseChange L) = ⊤ := by
      rw [eq_top_iff, ← V'.span_eq, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rw [hV']
      exact ⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hr x
    exact ⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have hW : Function.Surjective W.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs
  have hspan : ⊤ ≤ W := fun x _ => by
    obtain ⟨y, rfl⟩ := hW x
    exact y.2
  let V := Module.Basis.mk h3 hspan
  refine ⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩
  have hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ :=
    B.ext fun s => by simp [V, Module.Basis.mk_apply]
  rw [← LinearEquiv.coe_coe, hEq, hφ]
  rfl

end GlobalTheory.AbCoh
