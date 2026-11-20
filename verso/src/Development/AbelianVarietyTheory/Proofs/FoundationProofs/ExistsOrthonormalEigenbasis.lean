import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

open Module.End

namespace GlobalTheory.OrthonormalEigenbasis

/- English proof (translation)
Use `set a' := LinearMap.adjoint a with ha'`. Establish `h1 : a' * a = 1`. Use extensionality with `x`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]`. Establish `h2 : a * a' = 1` using `mul_eq_one_comm.mp h1`. Use `set A : E →ₗ[ℂ] E := a + a' with hAdef`. Use `set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef`. Establish `hA : A.IsSymmetric`.

Introduce `x y`. Simplify using `only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : B.IsSymmetric`. Introduce `x y`.

Simplify using `only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAB : Commute A B`. Establish `hc : Commute (a + a') (a' - a)` using `by show (a + a') * (a' - a) = (a' - a) * (a + a')`. Simplify using `only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]`.

Normalize the expressions using the abelian group laws. Conclude with `hc.smul_right Complex.I`. Establish `hV` using `LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB`. Establish `hV'` using `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB`. Establish `hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}`.

Use `((Module.End.finite_hasEigenvalue (f := B)).prod (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)`. Conclude with `Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)`. Establish `: Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}` using `hT.to_subtype`. Use `Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}` as an intermediate fact.

Establish `hW` using `DirectSum.isInternal_ne_bot_iff.mpr hV`. Establish `hW'` using `hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))`. Use `⟨hW.subordinateOrthonormalBasis rfl hW', fun i => ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 + Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩` and prove the remaining obligations. Establish `hmem` using `hW.subordinateOrthonormalBasis_subordinate rfl i hW'`. Rewrite `hmem` using `[Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]`.

Establish `hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v`. Introduce `v`. Simplify using `only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]`. Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]`. Use `_ = _ := by`. Rewrite using `[hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eigenbasis_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a : E →ₗ[ℂ] E) (ha : ∀ x y, inner ℂ (a x) (a y) = inner ℂ x y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (l : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, a (b i) = l i • b i := by
  set a' := LinearMap.adjoint a with ha'

  have h1 : a' * a = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]
  have h2 : a * a' = 1 := mul_eq_one_comm.mp h1

  set A : E →ₗ[ℂ] E := a + a' with hAdef
  set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef
  have hA : A.IsSymmetric := by
    intro x y
    simp only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha',
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  have hB : B.IsSymmetric := by
    intro x y
    simp only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      Complex.conj_I]
    ring
  have hAB : Commute A B := by
    have hc : Commute (a + a') (a' - a) := by
      show (a + a') * (a' - a) = (a' - a) * (a + a')
      simp only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]
      abel
    exact hc.smul_right Complex.I
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB

  have hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := by
    refine ((Module.End.finite_hasEigenvalue (f := B)).prod
      (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)
  have : Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := hT.to_subtype
  have := Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}
  classical
  have hW := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' := hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))

  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i =>
    ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 +
      Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate rfl i hW'
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hmem
  have hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v := by
    intro v
    simp only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]
    abel
  calc a (hW.subordinateOrthonormalBasis rfl hW' i)
      = (2 : ℂ)⁻¹ • (A (hW.subordinateOrthonormalBasis rfl hW' i) +
          Complex.I • B (hW.subordinateOrthonormalBasis rfl hW' i)) := by
        rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = _ := by
        rw [hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]
        congr 1
        ring

open GlobalTheory.UnitaryTheta in

/- English proof (translation)
Set `cd : InnerProductSpace.Core ℂ V` to `{ inner := fun x y => H y x conj_inner_symm := fun x y => (hH.1 y x).symm re_inner_nonneg := fun x => by`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(hH.2 x hx).le`. Use `add_left := fun x y z => by show H z (x + y) = H z x + H z y`.

Conclude with `map_add _ _ _`. Use `smul_left := fun x y r => by show H y (r • x) = (starRingEnd ℂ) r * H y x`. Rewrite using `[LinearMap.map_smulₛₗ, smul_eq_mul]`. Use `definite := fun x hx => by`. Assume the negation of the conclusion as `h`.

Use `hH.2 x h` as an intermediate fact. Simplify using `[hx] at this }`. Set `_ : NormedAddCommGroup V` to `InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)`. Set `_ : InnerProductSpace ℂ V` to `InnerProductSpace.ofCore cd.toCore`. Establish `hinner : ∀ x y : V, inner ℂ x y = H y x` using `fun _ _ => rfl`.

Apply the tactic sequence `obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)`. Use `⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]`. Conclude with `if_congr eq_comm rfl rfl`. Establish `h1 : ‖a (b i)‖ = ‖b i‖`.

Rewrite using `[norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]`. Rewrite `h1` using `[hb i, norm_smul, b.orthonormal.1 i, mul_one]`. Conclude with `h1`. Rewrite using `[OrthonormalBasis.coe_toBasis]`. Conclude with `hb i`.
-/
theorem exists_orthonormal_eigenbasis {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then (1 : ℂ) else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by

  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H y x
      conj_inner_symm := fun x y => (hH.1 y x).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hH.2 x hx).le
      add_left := fun x y z => by
        show H z (x + y) = H z x + H z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show H y (r • x) = (starRingEnd ℂ) r * H y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := hH.2 x h
        simp [hx] at this }
  let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : V, inner ℂ x y = H y x := fun _ _ => rfl
  obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)
  refine ⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]
    exact if_congr eq_comm rfl rfl
  ·
    have h1 : ‖a (b i)‖ = ‖b i‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one] at h1
    exact h1
  · rw [OrthonormalBasis.coe_toBasis]
    exact hb i

end GlobalTheory.OrthonormalEigenbasis
