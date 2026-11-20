import Mathlib

/- English proof (translation)
Introduce `O O' LL Q _ _ _ _ _ _ _ _ f fK a n Y ψ hinj hf hfg hψ`. Use `haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Free O Y := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis O Y`. Set `v : Module.Free.ChooseBasisIndex O Y → Fin a → Fin n → LL` to `fun i j m => fK ((b i).1 j m)`.

Establish `h1 : LinearIndependent O (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2)`. Establish `h0 : LinearIndependent O (fun i => (b i).1)` using `b.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)`. Rewrite `h0`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `h0` to reduce the goal to its premises.

Use function extensionality and compare the values at `j m`. Use `congrFun hg (j, m)` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Establish `h2 : LinearIndependent (FractionRing O) (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2)` using `(LinearIndependent.iff_fractionRing O (FractionRing O)).mp h1`. Establish `h3 : LinearIndependent LL (fun i => fun p : Fin a × Fin n => fK ((b i).1 p.1 p.2))`.

Use `letI := fK.toAlgebra`. Conclude with `linearIndependent_algebraMap_comp_iff.mpr h2`. Establish `h4 : LinearIndependent O' v`. Rewrite `h3`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `h3 (fun i => algebraMap O' LL (g i))` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Use `congrFun (congrFun hg p.1) p.2` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply, v, Algebra.smul_def]`. Establish `hexp : ∀ y : Y, (fun j m => fK (y.1 j m)) = ∑ i, f (b.repr y i) • v i`. Introduce `y`. Use function extensionality and compare the values at `j m`. Establish `h` using `congrArg (fun z : Y => z.1 j m) (b.sum_repr y)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at h`. Rewrite using `[← h]`. Simplify using `[Finset.sum_apply, v, Algebra.smul_def, hf]`. Establish `hspan : Submodule.span O' ((fun (y : Fin a → Fin n → FractionRing O) j m => fK (y j m)) '' (Y : Set _)) = Submodule.span O' (Set.range v)`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `hexp ⟨y, hy⟩` as an intermediate fact. Simplify using `only at this`. Use `show (fun j m => fK (y j m)) ∈ Submodule.span O' (Set.range v)`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨(b i).1, (b i).2, rfl⟩`.

Set `B` to `Module.Basis.span h4`. Use `⟨(B.constr O' (fun i => ψ (b i))).comp (LinearEquiv.ofEq _ _ hspan).toLinearMap, fun y => ?_⟩` and prove the remaining obligations. Establish `h5 : (LinearEquiv.ofEq _ _ hspan) ⟨fun j m => fK (y.1 j m), Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ = ∑ i, f (b.repr y i) • B i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [LinearEquiv.coe_ofEq_apply, Submodule.coe_sum, Submodule.coe_smul, B, Module.Basis.span_apply]`.

Conclude with `hexp y`. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, h5, map_sum]`. Use `conv_rhs => rw [← b.sum_repr y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Module.Basis.constr_basis, hψ]`.
-/
theorem _root_.UpperTheory.KN.exists_linearMap_span_baseChange_of_semilinear :
    ∀ {O O' LL Q : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [CommRing O'] [Field LL] [Algebra O' LL]
      [AddCommGroup Q] [Module O' Q] (f : O →+* O') (fK : FractionRing O →+* LL) {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → FractionRing O)) (ψ : ↥Y →+ Q),
      Function.Injective (algebraMap O' LL) → (∀ c, fK (algebraMap O (FractionRing O) c) = algebraMap O' LL (f c)) → Y.FG →
      (∀ (c : O) (y : ↥Y), ψ (c • y) = f c • ψ y) →
      ∃ φ : ↥(Submodule.span O' ((fun (y : Fin a → Fin n → FractionRing O) j m => fK (y j m)) '' (Y : Set _))) →ₗ[O'] Q,
        ∀ y : ↥Y, φ ⟨fun j m => fK (y.1 j m), Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ = ψ y := by
  intro O O' LL Q _ _ _ _ _ _ _ _ f fK a n Y ψ hinj hf hfg hψ
  classical
  haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O Y := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O Y
  let v : Module.Free.ChooseBasisIndex O Y → Fin a → Fin n → LL := fun i j m => fK ((b i).1 j m)
  have h1 : LinearIndependent O (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2) := by
    have h0 : LinearIndependent O (fun i => (b i).1) :=
      b.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro g hg
    apply h0
    funext j m
    have := congrFun hg (j, m)
    simpa [Finset.sum_apply] using this
  have h2 : LinearIndependent (FractionRing O) (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2) :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp h1
  have h3 : LinearIndependent LL (fun i => fun p : Fin a × Fin n => fK ((b i).1 p.1 p.2)) := by
    letI := fK.toAlgebra
    exact linearIndependent_algebraMap_comp_iff.mpr h2
  have h4 : LinearIndependent O' v := by
    rw [Fintype.linearIndependent_iff] at h3 ⊢
    intro g hg i
    apply hinj
    rw [map_zero]
    apply h3 (fun i => algebraMap O' LL (g i))
    funext p
    have := congrFun (congrFun hg p.1) p.2
    simpa [Finset.sum_apply, v, Algebra.smul_def] using this
  have hexp : ∀ y : Y, (fun j m => fK (y.1 j m)) = ∑ i, f (b.repr y i) • v i := by
    intro y
    funext j m
    have h := congrArg (fun z : Y => z.1 j m) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at h
    rw [← h]
    simp [Finset.sum_apply, v, Algebra.smul_def, hf]
  have hspan : Submodule.span O' ((fun (y : Fin a → Fin n → FractionRing O) j m => fK (y j m)) '' (Y : Set _))
      = Submodule.span O' (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have := hexp ⟨y, hy⟩
      simp only at this
      show (fun j m => fK (y j m)) ∈ Submodule.span O' (Set.range v)
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨(b i).1, (b i).2, rfl⟩
  let B := Module.Basis.span h4
  refine ⟨(B.constr O' (fun i => ψ (b i))).comp (LinearEquiv.ofEq _ _ hspan).toLinearMap, fun y => ?_⟩
  have h5 : (LinearEquiv.ofEq _ _ hspan) ⟨fun j m => fK (y.1 j m), Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩
      = ∑ i, f (b.repr y i) • B i := by
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply, Submodule.coe_sum, Submodule.coe_smul, B, Module.Basis.span_apply]
    exact hexp y
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, map_sum]
  conv_rhs => rw [← b.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, hψ]
