import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {A S S' : Type} [CommRing A] [CommRing S] [CommRing S']
  [Algebra R A] [Algebra R S] [Algebra R S'] (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M]

/- English proof (translation)
Establish `h1 : ∀ m ∈ (a • ⊤ : Submodule R M), ∀ t : S, t ⊗ₜ[R] m ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))`. Introduce `m hm t`. Use `Submodule.smul_induction_on hm ?_ ?_` and prove the remaining obligations. Introduce `r hr m _`. Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul S r]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top`. Introduce `x y hx hy`. Rewrite using `[TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Establish `h2 : ∀ i ∈ I, ∀ w : S ⊗[R] M, algebraMap R S i • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))`.

Introduce `i hi w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul t m`. Rewrite using `[algebraMap_smul, ← TensorProduct.tmul_smul]`.

Conclude with `h1 _ (hI (Submodule.smul_mem_smul hi Submodule.mem_top)) t`. Consider the case `add x y hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Conclude with `h2 i hi w`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_killI (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (s : S)
    (hs : s ∈ I.map (algebraMap R S)) (w : S ⊗[R] M) :
    s • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
  have h1 : ∀ m ∈ (a • ⊤ : Submodule R M), ∀ t : S,
      t ⊗ₜ[R] m ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro m hm t
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr m _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have h2 : ∀ i ∈ I, ∀ w : S ⊗[R] M,
      algebraMap R S i • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro i hi w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      exact h1 _ (hI (Submodule.smul_mem_smul hi Submodule.mem_top)) t
    | add x y hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact h2 i hi w
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_smul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[Ideal.map_map, AlgHom.comp_algebraMap]`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_map (f : A →ₐ[R] S) (J : Ideal R) :
    (J.map (algebraMap R A)).map (f : A →+* S) = J.map (algebraMap R S) := by
  rw [Ideal.map_map, AlgHom.comp_algebraMap]

/- English proof (translation)
Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `UpperTheory.V.Pa.Core.spCong_killI I a M hI _ ?_ w` and prove the remaining obligations. Take `⟨b, hb, c, hc, rfl⟩` from `Submodule.mem_sup.1 hz`. Rewrite using `[map_add, (RingHom.mem_ker).1 hb, zero_add, ← UpperTheory.V.Pa.Core.spCong_map f I]`.

Conclude with `Ideal.mem_map_of_mem (f : A →+* S) hc`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_kill (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S) (z : A)
    (hz : z ∈ RingHom.ker f ⊔ I.map (algebraMap R A))
    (x : (S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) : f z • x = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine UpperTheory.V.Pa.Core.spCong_killI I a M hI _ ?_ w
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add, (RingHom.mem_ker).1 hb, zero_add, ← UpperTheory.V.Pa.Core.spCong_map f I]
  exact Ideal.mem_map_of_mem (f : A →+* S) hc

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul t m => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_smul (f : A →ₐ[R] S) (z : A) (x : A ⊗[R] M) :
    f.toLinearMap.rTensor M (z • x) = f z • f.toLinearMap.rTensor M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Establish `hF : Function.Surjective (f.toLinearMap.rTensor M)` using `LinearMap.rTensor_surjective M hf`. Establish `h1 : ∀ y ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)), ∃ x, f.toLinearMap.rTensor M x = y ∧ f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))`. Introduce `y hy`. Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `s hs w _`.

Rewrite `hs` using `[← UpperTheory.V.Pa.Core.spCong_map f a]`. Take `⟨z, hz, rfl⟩` from `(Ideal.mem_map_iff_of_surjective (f : A →+* S) hf).1 hs`. Take `⟨x, rfl⟩` from `hF w`. Use `⟨z • x, UpperTheory.V.Pa.Core.spCong_smul M f z x, ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.V.Pa.Core.spCong_smul]`.

Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Rewrite using `[← UpperTheory.V.Pa.Core.spCong_map f' a]`. Conclude with `Ideal.mem_map_of_mem (f' : A →+* S') hz`. Introduce and unpack `_ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩`. Conclude with `⟨x + y, map_add _ _ _, by rw [map_add]; exact Submodule.add_mem _ hx hy⟩`.

Establish `h2 : ∀ w : (LinearMap.ker f.toLinearMap) ⊗[R] M, f'.toLinearMap.rTensor M ((LinearMap.ker f.toLinearMap).subtype.rTensor M w) ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul t m`.

Establish `h` using `UpperTheory.V.Pa.Core.spCong_kill I a M hI f' t (hk t.2) (Submodule.Quotient.mk (1 ⊗ₜ[R] m))`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Simplify `h` using `[TensorProduct.smul_tmul']`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Take `⟨x', hx', hm⟩` from `h1 _ hx`. Establish `hex` using `rTensor_exact M (LinearMap.exact_subtype_ker_map f.toLinearMap) hf`. Take `⟨w, hw⟩` from `(hex (x - x')).1 (by rw [map_sub, hx', sub_self])`. Establish `h3` using `h2 w`.

Rewrite `h3` using `[hw, map_sub]`. Simplify using `using Submodule.add_mem _ h3 hm`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_ker (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f)
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A)) (x : A ⊗[R] M)
    (hx : f.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :
    f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
  have hF : Function.Surjective (f.toLinearMap.rTensor M) := LinearMap.rTensor_surjective M hf
  have h1 : ∀ y ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)), ∃ x, f.toLinearMap.rTensor M x = y ∧
      f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro s hs w _
      rw [← UpperTheory.V.Pa.Core.spCong_map f a] at hs
      obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : A →+* S) hf).1 hs
      obtain ⟨x, rfl⟩ := hF w
      refine ⟨z • x, UpperTheory.V.Pa.Core.spCong_smul M f z x, ?_⟩
      rw [UpperTheory.V.Pa.Core.spCong_smul]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← UpperTheory.V.Pa.Core.spCong_map f' a]
      exact Ideal.mem_map_of_mem (f' : A →+* S') hz
    · rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
      exact ⟨x + y, map_add _ _ _, by rw [map_add]; exact Submodule.add_mem _ hx hy⟩
  have h2 : ∀ w : (LinearMap.ker f.toLinearMap) ⊗[R] M,
      f'.toLinearMap.rTensor M ((LinearMap.ker f.toLinearMap).subtype.rTensor M w) ∈
        (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      have h := UpperTheory.V.Pa.Core.spCong_kill I a M hI f' t (hk t.2) (Submodule.Quotient.mk (1 ⊗ₜ[R] m))
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      simpa [TensorProduct.smul_tmul'] using h
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  obtain ⟨x', hx', hm⟩ := h1 _ hx
  have hex := rTensor_exact M (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  obtain ⟨w, hw⟩ := (hex (x - x')).1 (by rw [map_sub, hx', sub_self])
  have h3 := h2 w
  rw [hw, map_sub] at h3
  simpa using Submodule.add_mem _ h3 hm

/- English proof (translation)
Set `φ : A ⊗[R] M →+ ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)))` to `(Submodule.mkQ _).toAddMonoidHom.comp (f.toLinearMap.rTensor M).toAddMonoidHom`. Set `φ' : A ⊗[R] M →+ ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)))` to `(Submodule.mkQ _).toAddMonoidHom.comp (f'.toLinearMap.rTensor M).toAddMonoidHom`. Establish `e : ∀ x, φ x = Submodule.Quotient.mk (f.toLinearMap.rTensor M x)` using `fun _ => rfl`. Establish `e' : ∀ x, φ' x = Submodule.Quotient.mk (f'.toLinearMap.rTensor M x)` using `fun _ => rfl`. Establish `hφ : Function.Surjective φ` using `(Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f.toLinearMap) hf)`.

Establish `hφ' : Function.Surjective φ'` using `(Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f'.toLinearMap) hf')`. Establish `hker : φ.ker = φ'.ker`. Use extensionality with `x`. Rewrite using `[AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, e, e', Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨UpperTheory.V.Pa.Core.spCong_ker I a M hI f f' hf hk x, UpperTheory.V.Pa.Core.spCong_ker I a M hI f' f hf' hk' x⟩`.

Set `κ` to `((QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm.trans (QuotientAddGroup.quotientAddEquivOfEq hker)).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ' hφ')`. Establish `hκ : ∀ x, κ (φ x) = φ' x`. Introduce `x`. Establish `: (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = QuotientAddGroup.mk x`. Rewrite using `[AddEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `only [κ, AddEquiv.trans_apply, this]`. Both sides reduce to the same expression. Use `⟨κ, fun z x => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hφ x`.

Establish `h1 : f z • φ x = φ (z • x)`. Rewrite using `[e, e, UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]`. Rewrite using `[h1, hκ, hκ, e', e', UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]`.
-/
private theorem UpperTheory.V.Pa.Core.spCong_gen (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A))
    (hk' : RingHom.ker f' ≤ RingHom.ker f ⊔ I.map (algebraMap R A)) :
    ∃ κ : ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) ≃+
      ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))),
      ∀ z x, κ (f z • x) = f' z • κ x := by
  let φ : A ⊗[R] M →+ ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f.toLinearMap.rTensor M).toAddMonoidHom
  let φ' : A ⊗[R] M →+ ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f'.toLinearMap.rTensor M).toAddMonoidHom
  have e : ∀ x, φ x = Submodule.Quotient.mk (f.toLinearMap.rTensor M x) := fun _ => rfl
  have e' : ∀ x, φ' x = Submodule.Quotient.mk (f'.toLinearMap.rTensor M x) := fun _ => rfl
  have hφ : Function.Surjective φ :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f.toLinearMap) hf)
  have hφ' : Function.Surjective φ' :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f'.toLinearMap) hf')
  have hker : φ.ker = φ'.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, e, e', Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨UpperTheory.V.Pa.Core.spCong_ker I a M hI f f' hf hk x, UpperTheory.V.Pa.Core.spCong_ker I a M hI f' f hf' hk' x⟩
  let κ := ((QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ' hφ')
  have hκ : ∀ x, κ (φ x) = φ' x := by
    intro x
    have : (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = QuotientAddGroup.mk x := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [κ, AddEquiv.trans_apply, this]
    rfl
  refine ⟨κ, fun z x => ?_⟩
  obtain ⟨x, rfl⟩ := hφ x
  have h1 : f z • φ x = φ (z • x) := by
    rw [e, e, UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]
  rw [h1, hκ, hκ, e', e', UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]

/- English proof (translation)
Unfold `spIdeal`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, k, rfl⟩`. Use `Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.V.Pa.Core.spCong_ideal {q n : ℕ} (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I) :
    spIdeal P ut ≤ spIdeal P' ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `R _ q n P P' ut I a M _ _ h hI`. Establish `hk : ∀ Q : Fin q → Polynomial R, RingHom.ker (Sp.mk Q ut) = spIdeal Q ut` using `fun Q => Ideal.Quotient.mkₐ_ker R (spIdeal Q ut)`. Establish `hs : ∀ Q : Fin q → Polynomial R, Function.Surjective (Sp.mk Q ut)` using `fun Q => Ideal.Quotient.mkₐ_surjective R (spIdeal Q ut)`. Establish `hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) = algebraMap R (MvPowerSeries (Fin q × Fin n) R)` using `by ext1 r`. Simplify using `[MvPowerSeries.algebraMap_apply]`.

Establish `h' : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I` using `fun j k => by`. Rewrite using `[← neg_sub]`. Conclude with `I.neg_mem (h j k)`. Take `⟨κ, hκ⟩` from `UpperTheory.V.Pa.Core.spCong_gen I a M hI (Sp.mk P ut) (Sp.mk P' ut) (hs P) (hs P') (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P P' ut h') (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P' P ut h)`. Use `⟨κ, hκ, fun z hz x => UpperTheory.V.Pa.Core.spCong_kill I a M hI _ z ?_ x⟩` and prove the remaining obligations.

Rewrite using `[hk, ← hC]`. Conclude with `hz`.
-/
theorem UpperTheory.V.Pa.Core.spCong :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M], (∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) → (I • ⊤ : Submodule R M) ≤ a • ⊤ → ∃ κ : ((Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M))) ≃+ ((Sp P' ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P' ut)) • ⊤ : Submodule (Sp P' ut) (Sp P' ut ⊗[R] M))), (∀ z x, κ (Sp.mk P ut z • x) = Sp.mk P' ut z • κ x) ∧ ∀ z ∈ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R), ∀ x : (Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M)), Sp.mk P ut z • x = 0 := by
  intro R _ q n P P' ut I a M _ _ h hI
  have hk : ∀ Q : Fin q → Polynomial R, RingHom.ker (Sp.mk Q ut) = spIdeal Q ut := fun Q =>
    Ideal.Quotient.mkₐ_ker R (spIdeal Q ut)
  have hs : ∀ Q : Fin q → Polynomial R, Function.Surjective (Sp.mk Q ut) := fun Q =>
    Ideal.Quotient.mkₐ_surjective R (spIdeal Q ut)
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
      algebraMap R (MvPowerSeries (Fin q × Fin n) R) := by
    ext1 r
    simp [MvPowerSeries.algebraMap_apply]
  have h' : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I := fun j k => by
    rw [← neg_sub]
    exact I.neg_mem (h j k)
  obtain ⟨κ, hκ⟩ := UpperTheory.V.Pa.Core.spCong_gen I a M hI (Sp.mk P ut) (Sp.mk P' ut) (hs P) (hs P')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P P' ut h')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P' P ut h)
  refine ⟨κ, hκ, fun z hz x => UpperTheory.V.Pa.Core.spCong_kill I a M hI _ z ?_ x⟩
  rw [hk, ← hC]
  exact hz
