import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralUnipFundamentalDomainCompLatticePreservi

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Simplify using `only [blk]`. Rewrite using `[emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]`. Use `group`.
-/
private theorem blk_mul_blk_inv {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    blk m₁ m₂ * blk m₁⁻¹ m₂⁻¹ = 1 := by
  simp only [blk]
  rw [emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]
  group

/- English proof (translation)
Introduce `K _ _ r s φ hφ γ₁ γ₂ g`. Establish `hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ = GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ` using `fun _ => rfl`. Take `⟨c, hc⟩` from `UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂`. Take `⟨c', hc'⟩` from `UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹`. Establish `hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹`.

Rewrite using `[← map_inv]`. Use `congr 1`. Conclude with `eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)`. Establish `hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K, unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂)`. Introduce `Y`.

Establish `h` using `hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y`. Rewrite `h` using `[← hdiag, hDD]`. Rewrite using `[h]`. Use `group`. Establish `hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K, unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) = AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹`.

Introduce `Y`. Establish `h` using `hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y`. Rewrite `h` using `[← hdiag]`. Rewrite using `[h]`. Use `group`.

Establish `hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K), X ∈ unipLattice K (r + s) r → (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r`. Introduce `d X hX`. Take `⟨y, rfl⟩` from `AddMonoidHom.mem_range.mp hX`. Use `AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Simplify using `[AddMonoidHom.compLeft_apply, map_sum, map_mul]`. Establish `hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K, Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q)`. Introduce `d`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun q _ => continuous_const.mul (continuous_apply q)`.

Establish `hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K, (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y`. Introduce `Y`. Apply `unipGL_injective` to reduce the goal to its premises. Rewrite using `[hv, hu]`. Use `group`.

Establish `hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K, (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y`. Introduce `Y`. Apply `unipGL_injective` to reduce the goal to its premises. Rewrite using `[hu, hv]`. Use `group`.

Set `α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K)` to `{ toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q left_inv := fun X => hinv1 X right_inv := fun X => hinv2 X map_add' := by`. Introduce `X Y`. Use function extensionality and compare the values at `p`. Simplify using `[mul_add, Finset.sum_add_distrib]`. Use `continuous_toFun := hcont c'`.

Use `continuous_invFun := hcont c }`. Establish `hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r`. Introduce `X`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2` using `hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h`. Rewrite `h2` using `[hinv1]`. Then use the resulting hypothesis. Conclude with `hmem c' X`. Establish `hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K, φ (unipGL (ξ + X) * g) = φ (unipGL X * g)` using `fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X`. Establish `hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K, φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g)`.

Introduce `X`. Rewrite using `[← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]`. Express the relevant statement in the definitionally equal form `_ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)`. Rewrite using `[hu]`. Use `group`.

Unfold `constantTerm`. Repeatedly rewrite using `[hstep]`. Conclude with `UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper`.
-/
theorem UpperTheory.constantTerm_levi_rational_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (φ : AdelicGLn.AdelicGL K (r + s) → ℂ), IsLeftInvariant φ → ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g, constantTerm r φ (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) = constantTerm r φ g := by
  intro K _ _ r s φ hφ γ₁ γ₂ g
  have hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ =
      GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ := fun _ => rfl
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂
  obtain ⟨c', hc'⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹
  have hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    rw [← map_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)
  have hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) =
        (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) := by
    intro Y
    have h := hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag, hDD] at h
    rw [h]
    group
  have hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) =
        AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    intro Y
    have h := hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag] at h
    rw [h]
    group
  have hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K),
      X ∈ unipLattice K (r + s) r →
        (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r := by
    intro d X hX
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hX
    refine AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩
    funext p
    simp [AddMonoidHom.compLeft_apply, map_sum, map_mul]
  have hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K,
      Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p =>
        ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) := by
    intro d
    refine continuous_pi fun p => ?_
    exact continuous_finset_sum _ fun q _ => continuous_const.mul (continuous_apply q)
  have hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hv, hu]
    group
  have hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hu, hv]
    group
  let α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q
      invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q
      left_inv := fun X => hinv1 X
      right_inv := fun X => hinv2 X
      map_add' := by
        intro X Y
        funext p
        simp [mul_add, Finset.sum_add_distrib]
      continuous_toFun := hcont c'
      continuous_invFun := hcont c }
  have hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r := by
    intro X
    constructor
    · intro h
      have h2 := hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h
      rwa [hinv1] at h2
    · exact hmem c' X
  have hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL (ξ + X) * g) = φ (unipGL X * g) :=
    fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X
  have hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g) := by
    intro X
    rw [← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]
    change _ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)
    rw [hu]
    group
  unfold constantTerm
  simp_rw [hstep]
  exact UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper
