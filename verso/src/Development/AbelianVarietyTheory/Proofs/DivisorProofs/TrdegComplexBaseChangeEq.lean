import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Rewrite `ht`, the goal using `[algebraicIndependent_iff_injective_aeval]`. Establish `h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L))` using `Module.Flat.lTensor_preserves_injective_linearMap (M := K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L).toLinearMap ht`. Establish `h2 : (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] t i) : MvPolynomial ι K →ₐ[K] K ⊗[k] L) = (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)).comp (MvPolynomial.algebraTensorAlgEquiv k K (σ` using `ι)).symm.toAlgHom := by`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Rewrite using `[h2]`. Conclude with `h1.comp (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.injective`.
-/
theorem algebraicIndependent_one_tmul_of_field {k K L ι : Type} [Field k] [Field K] [CommRing L] [Algebra k K] [Algebra k L]
    {t : ι → L} (ht : AlgebraicIndependent k t) :
    AlgebraicIndependent K (fun i => (1 : K) ⊗ₜ[k] t i) := by
  rw [algebraicIndependent_iff_injective_aeval] at ht ⊢
  have h1 : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L).toLinearMap ht
  have h2 : (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] t i) : MvPolynomial ι K →ₐ[K] K ⊗[k] L) =
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)).comp
        (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.toAlgHom := by
    ext i
    simp
  rw [h2]
  exact h1.comp (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.injective

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_isTranscendenceBasis k L`. Establish `hi` using `algebraicIndependent_one_tmul_of_field (K := K) hs.1`. Use `set S := Algebra.adjoin K (Set.range fun i : s => (1 : K) ⊗ₜ[k] (i : L)) with hS`. Establish `halg : Algebra.IsAlgebraic S (K ⊗[k] L)`. Establish `hA` using `hs.isAlgebraic`.

Use `set T := Algebra.adjoin k (Set.range (Subtype.val : s → L)) with hT`. Establish `hmem : ∀ x : T, (1 : K) ⊗ₜ[k] (x : L) ∈ S`. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `Algebra.subset_adjoin ⟨i, rfl⟩`. Consider the case `algebraMap r`. Establish `: (1 : K) ⊗ₜ[k] (algebraMap k L r) = algebraMap K (K ⊗[k] L) (algebraMap k K r)`. Rewrite using `[← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] L)]`.

Simplify using `only [this]`. Conclude with `S.algebraMap_mem _`. Consider the case `add x y hx hy ihx ihy`. Simplify using `only [TensorProduct.tmul_add]`. Conclude with `S.add_mem ihx ihy`.

Consider the case `mul x y hx hy ihx ihy`. Establish `: (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y)` using `by simp`. Simplify using `only [this]`. Conclude with `S.mul_mem ihx ihy`. Set `g : L →+* K ⊗[k] L` to `(Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom`.

Set `f : T →+* S` to `(g.comp T.val.toRingHom).codRestrict S hmem`. Establish `hf : Function.Injective f`. Introduce `x y hxy`. Establish `: g x = g y` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (g.injective this)`.

Use `⟨fun z => ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact isAlgebraic_zero`. Consider the case `add x y hx hy => exact hx.add hy`. Consider the case `tmul a b`.

Establish `h1 : IsAlgebraic S (g b)` using `(hA.isAlgebraic b).ringHom_of_comp_eq f g hf (by ext; rfl)`. Establish `h2 : IsAlgebraic S (algebraMap S (K ⊗[k] L) (algebraMap K S a))` using `isAlgebraic_algebraMap _`. Establish `h3 : a ⊗ₜ[k] b = algebraMap S (K ⊗[k] L) (algebraMap K S a) * g b`. Simplify using `[g]`. Rewrite using `[h3]`.

Conclude with `h2.mul h1`. Establish `hb : IsTranscendenceBasis K (fun i : s => (1 : K) ⊗ₜ[k] (i : L))` using `hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg`. Rewrite using `[← hb.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]`.
-/
theorem trdeg_tensorProduct_eq {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsDomain (K ⊗[k] L)] : Algebra.trdeg K (K ⊗[k] L) = Algebra.trdeg k L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hi := algebraicIndependent_one_tmul_of_field (K := K) hs.1
  set S := Algebra.adjoin K (Set.range fun i : s => (1 : K) ⊗ₜ[k] (i : L)) with hS
  have halg : Algebra.IsAlgebraic S (K ⊗[k] L) := by
    have hA := hs.isAlgebraic
    set T := Algebra.adjoin k (Set.range (Subtype.val : s → L)) with hT
    have hmem : ∀ x : T, (1 : K) ⊗ₜ[k] (x : L) ∈ S := by
      rintro ⟨x, hx⟩
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      | algebraMap r =>
        have : (1 : K) ⊗ₜ[k] (algebraMap k L r) = algebraMap K (K ⊗[k] L) (algebraMap k K r) := by
          rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] L)]
        simp only [this]
        exact S.algebraMap_mem _
      | add x y hx hy ihx ihy =>
        simp only [TensorProduct.tmul_add]
        exact S.add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
        have : (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) := by simp
        simp only [this]
        exact S.mul_mem ihx ihy
    let g : L →+* K ⊗[k] L := (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom
    let f : T →+* S := (g.comp T.val.toRingHom).codRestrict S hmem
    have hf : Function.Injective f := by
      intro x y hxy
      have : g x = g y := congrArg Subtype.val hxy
      exact Subtype.ext (g.injective this)
    refine ⟨fun z => ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => exact isAlgebraic_zero
    | add x y hx hy => exact hx.add hy
    | tmul a b =>
      have h1 : IsAlgebraic S (g b) :=
        (hA.isAlgebraic b).ringHom_of_comp_eq f g hf (by ext; rfl)
      have h2 : IsAlgebraic S (algebraMap S (K ⊗[k] L) (algebraMap K S a)) := isAlgebraic_algebraMap _
      have h3 : a ⊗ₜ[k] b = algebraMap S (K ⊗[k] L) (algebraMap K S a) * g b := by
        simp [g]
      rw [h3]
      exact h2.mul h1
  have hb : IsTranscendenceBasis K (fun i : s => (1 : K) ⊗ₜ[k] (i : L)) :=
    hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  rw [← hb.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]

/- English proof (translation)
The claim follows from `trdeg_tensorProduct_eq`.
-/
theorem trdeg_complex_baseChange_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' :=
  trdeg_tensorProduct_eq

end GlobalTheory
