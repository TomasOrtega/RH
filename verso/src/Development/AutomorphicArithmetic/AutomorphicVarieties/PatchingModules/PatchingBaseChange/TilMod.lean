import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilEv

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `O O' _ _ _ _ S R _ _ _ _ _ _ f M _ _ _ _ h`. Use `letI : Module O M := Module.compHom M (algebraMap O R)`. Use `haveI : IsScalarTower O R M := ⟨fun o r m => by show (o • r) • m = (algebraMap O R o) • (r • m)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Use `haveI : IsScalarTower O S M := ⟨fun o s m => by show (o • s) • m = (algebraMap O R o) • (s • m)`.

Rewrite using `[h (o • s) m, h s m, Algebra.smul_def o s, map_mul, f.commutes, mul_smul]⟩`. Establish `hfin : Module.Finite R M`. Use `letI : Algebra S R := f.toRingHom.toAlgebra`. Use `haveI : IsScalarTower S R M := ⟨fun s r m => by show (f s * r) • m = s • (r • m)`. Rewrite using `[mul_smul, h]⟩`.

Conclude with `Module.Finite.of_restrictScalars_finite S R M`. Use `haveI := hfin`. Take `⟨e1, he1⟩` from `BC.til_ev O O' S M`. Take `⟨e2, he2⟩` from `BC.til_ev O O' R M`. Establish `hact : ∀ (m : M) (x : O' ⊗[O] S), Til.act O' m (Algebra.TensorProduct.map (AlgHom.id O' O') f x) = Til.act O' m x`.

Introduce `m x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o s => simp [Til.act, h]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Establish `hcoeff : ∀ k a, Til.coeff O O' R k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' S k a)`. Introduce `k a`. Both sides reduce to the same expression. Establish `key : ∀ a m, e1 (a ⊗ₜ m) = e2 (Til.map O' f a ⊗ₜ m)`. Introduce `a m`.

Use function extensionality and compare the values at `k`. Rewrite using `[he1, he2, hcoeff, hact]`. Establish `hform : ∀ a m, (e1.trans e2.symm) (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m`. Introduce `a m`. Rewrite using `[AddEquiv.trans_apply, key, AddEquiv.symm_apply_apply]`.

Use `⟨e1.trans e2.symm, hform, ?_⟩` and prove the remaining obligations. Introduce `a z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b m => rw [TensorProduct.smul_tmul', hform, hform, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]`.

Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
theorem UpperTheory.V.Pa.BC.til_mod :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (f : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] [Module S M] [Module.Finite S M], (∀ (a : S) (m : M), a • m = f a • m) → ∃ e : Til O O' S ⊗[S] M ≃+ Til O O' R ⊗[R] M, (∀ a m, e (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m) ∧ ∀ a z, e (a • z) = Til.map O' f a • e z := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ f M _ _ _ _ h
  letI : Module O M := Module.compHom M (algebraMap O R)
  haveI : IsScalarTower O R M := ⟨fun o r m => by
    show (o • r) • m = (algebraMap O R o) • (r • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower O S M := ⟨fun o s m => by
    show (o • s) • m = (algebraMap O R o) • (s • m)
    rw [h (o • s) m, h s m, Algebra.smul_def o s, map_mul, f.commutes, mul_smul]⟩
  have hfin : Module.Finite R M := by
    letI : Algebra S R := f.toRingHom.toAlgebra
    haveI : IsScalarTower S R M := ⟨fun s r m => by
      show (f s * r) • m = s • (r • m)
      rw [mul_smul, h]⟩
    exact Module.Finite.of_restrictScalars_finite S R M
  haveI := hfin
  obtain ⟨e1, he1⟩ := BC.til_ev O O' S M
  obtain ⟨e2, he2⟩ := BC.til_ev O O' R M
  have hact : ∀ (m : M) (x : O' ⊗[O] S), Til.act O' m (Algebra.TensorProduct.map (AlgHom.id O' O') f x) = Til.act O' m x := by
    intro m x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o s => simp [Til.act, h]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcoeff : ∀ k a, Til.coeff O O' R k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' S k a) := by
    intro k a
    rfl
  have key : ∀ a m, e1 (a ⊗ₜ m) = e2 (Til.map O' f a ⊗ₜ m) := by
    intro a m
    funext k
    rw [he1, he2, hcoeff, hact]
  have hform : ∀ a m, (e1.trans e2.symm) (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m := by
    intro a m
    rw [AddEquiv.trans_apply, key, AddEquiv.symm_apply_apply]
  refine ⟨e1.trans e2.symm, hform, ?_⟩
  intro a z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rw [TensorProduct.smul_tmul', hform, hform, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
