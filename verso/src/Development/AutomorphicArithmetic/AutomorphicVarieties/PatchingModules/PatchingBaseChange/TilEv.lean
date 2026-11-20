import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

section
variable {R : Type} [CommRing R] {ι : Type} (N : Type) [AddCommGroup N] [Module R N]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]`.
-/
private theorem UpperTheory.V.Pa.BC.ev_nat {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (x : M ⊗[R] (ι → N)) (k : ι) :
    TensorProduct.piRightHom R R M' (fun _ : ι => N) (f.rTensor _ x) k =
      f.rTensor N (TensorProduct.piRightHom R R M (fun _ : ι => N) x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/- English proof (translation)
Set `e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N)` to `TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))`. Set `e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N)` to `LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))`. Establish `key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x = e2.symm (Equiv.piComm _ (e1 x))`. Introduce `x`. Apply `e2.injective` to reduce the goal to its premises.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero`. Use extensionality with `k i`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Consider the case `tmul v f`. Use extensionality with `k i`. Simplify using `[e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]`. Consider the case `add a b ha hb`.

Use extensionality with `k i`. Establish `h1` using `congrFun (congrFun ha k) i`. Establish `h2` using `congrFun (congrFun hb k) i`. Simplify using `only [map_add, Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢`. Rewrite using `[h1, h2]`.

Both sides reduce to the same expression. Establish `hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) = e2.symm ∘ (Equiv.piComm _) ∘ e1` using `funext key`. Rewrite using `[hfun]`. Conclude with `e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)`.
-/
private theorem UpperTheory.V.Pa.BC.ev_free (n : ℕ) :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) := by
  classical
  let e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N) :=
    TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))
  let e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))
  have key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x =
      e2.symm (Equiv.piComm _ (e1 x)) := by
    intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      ext k i
      simp
      rfl
    | tmul v f =>
      ext k i
      simp [e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]
    | add a b ha hb =>
      ext k i
      have h1 := congrFun (congrFun ha k) i
      have h2 := congrFun (congrFun hb k) i
      simp only [map_add, Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢
      rw [h1, h2]
      rfl
  have hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) =
      e2.symm ∘ (Equiv.piComm _) ∘ e1 := funext key
  rw [hfun]
  exact e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)

/- English proof (translation)
Take `⟨n, p, hp⟩` from `Module.Finite.exists_fin' R M`. Introduce `z`. Use `choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)`. Take `⟨y, hy⟩` from `(UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w`. Use `⟨p.rTensor _ y, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Rewrite using `[UpperTheory.V.Pa.BC.ev_nat, hy, hw]`.
-/
private theorem UpperTheory.V.Pa.BC.ev_surj (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  intro z
  choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)
  obtain ⟨y, hy⟩ := (UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w
  refine ⟨p.rTensor _ y, ?_⟩
  funext k
  rw [UpperTheory.V.Pa.BC.ev_nat, hy, hw]

/- English proof (translation)
Use `haveI := Module.finitePresentation_of_finite R M`. Use `⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩` and prove the remaining obligations. Take `⟨n, m, f, g, hf, hfg⟩` from `Module.FinitePresentation.exists_fin' R M`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `LinearMap.rTensor_surjective (ι → N) hf x`. Establish `hex` using `rTensor_exact N hfg hf`. Establish `hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈ Set.range (g.rTensor N)`. Introduce `k`. Establish `h1` using `congrFun hx k`.

Rewrite `h1` using `[UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply]`. Conclude with `(hex _).1 h1`. Use `choose z hz using hk`. Take `⟨w, hw⟩` from `(UpperTheory.V.Pa.BC.ev_free N m).2 z`. Establish `hy : y = g.rTensor _ w`.

Apply `(UpperTheory.V.Pa.BC.ev_free N n).1` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Rewrite using `[UpperTheory.V.Pa.BC.ev_nat, hw, hz]`. Rewrite using `[hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]`.
-/
private theorem UpperTheory.V.Pa.BC.ev_bij [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  haveI := Module.finitePresentation_of_finite R M
  refine ⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (ι → N) hf x
  have hex := rTensor_exact N hfg hf
  have hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈
      Set.range (g.rTensor N) := by
    intro k
    have h1 := congrFun hx k
    rw [UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply] at h1
    exact (hex _).1 h1
  choose z hz using hk
  obtain ⟨w, hw⟩ := (UpperTheory.V.Pa.BC.ev_free N m).2 z
  have hy : y = g.rTensor _ w := by
    apply (UpperTheory.V.Pa.BC.ev_free N n).1
    funext k
    rw [UpperTheory.V.Pa.BC.ev_nat, hw, hz]
  rw [hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end

/- English proof (translation)
Introduce `O O' _ _ _ _ R _ _ _ M _ _ _ _ _`. Set `N` to `R ⊗[O] O'`. Set `tc : O' ⊗[O] R ≃ₗ[O] N` to `TensorProduct.comm O O' R`. Establish `hadd : ∀ (k : ℕ) (a b : Til O O' R), Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b`. Introduce `k a b`.

Unfold `Til.coeff`. Conclude with `map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a) (show PowerSeries (O' ⊗[O] R) from b)`. Establish `hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R), Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a`. Introduce `k r a`. Unfold `Til.coeff`.

Conclude with `PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)`. Establish `hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c`. Introduce `r c`. Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul o s`. Simplify using `only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]`. Consider the case `add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, smul_add]`. Set `cf : Til O O' R →ₗ[R] (ℕ → N)` to `{ toFun := fun a k => tc (Til.coeff O O' R k a) map_add' := fun a b => by`.

Use function extensionality and compare the values at `k`. Simplify using `only [hadd, map_add, Pi.add_apply]`. Use the proof step `map_smul' := fun r a => by`. Use function extensionality and compare the values at `k`. Simplify using `only [RingHom.id_apply, Pi.smul_apply]`.

Rewrite using `[Algebra.smul_def, hmulC, hsm] }`. Establish `hcf : Function.Bijective cf`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Apply `PowerSeries.ext` to reduce the goal to its premises.

Introduce `k`. Establish `h1` using `congrFun hab k`. Conclude with `tc.injective h1`. Introduce `f`. Use `⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k`. Rewrite using `[PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]`. Set `cfe : Til O O' R ≃ₗ[R] (ℕ → N)` to `LinearEquiv.ofBijective cf hcf`. Establish `hev` using `UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M`.

Set `eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N)` to `LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev`. Set `cb : M ⊗[R] N ≃+ O' ⊗[O] M` to `(TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans (TensorProduct.comm O M O').toAddEquiv`. Establish `hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c`. Introduce `m c`. Proceed by induction on `c using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul o s`. Simplify using `[cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]`. Rewrite using `[TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.comm_tmul]`. Consider the case `add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add]`.

Use `⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩` and prove the remaining obligations. Introduce `a m k`. Simplify using `only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul, LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]`. Rewrite using `[← hcb]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Pa.BC.til_ev :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M], ∃ e : Til O O' R ⊗[R] M ≃+ (ℕ → O' ⊗[O] M), ∀ a m k, e (a ⊗ₜ m) k = Til.act O' m (Til.coeff O O' R k a) := by
  intro O O' _ _ _ _ R _ _ _ M _ _ _ _ _
  let N := R ⊗[O] O'
  let tc : O' ⊗[O] R ≃ₗ[O] N := TensorProduct.comm O O' R
  have hadd : ∀ (k : ℕ) (a b : Til O O' R),
      Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b := by
    intro k a b
    unfold Til.coeff
    exact map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a)
      (show PowerSeries (O' ⊗[O] R) from b)
  have hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R),
      Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a := by
    intro k r a
    unfold Til.coeff
    exact PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)
  have hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c := by
    intro r c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, smul_add]
  let cf : Til O O' R →ₗ[R] (ℕ → N) :=
    { toFun := fun a k => tc (Til.coeff O O' R k a)
      map_add' := fun a b => by
        funext k
        simp only [hadd, map_add, Pi.add_apply]
      map_smul' := fun r a => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, hmulC, hsm] }
  have hcf : Function.Bijective cf := by
    constructor
    · intro a b hab
      apply PowerSeries.ext
      intro k
      have h1 := congrFun hab k
      exact tc.injective h1
    · intro f
      refine ⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩
      funext k
      change tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k
      rw [PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]
  let cfe : Til O O' R ≃ₗ[R] (ℕ → N) := LinearEquiv.ofBijective cf hcf
  have hev := UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M
  let eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N) :=
    LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev
  let cb : M ⊗[R] N ≃+ O' ⊗[O] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans
      (TensorProduct.comm O M O').toAddEquiv
  have hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c := by
    intro m c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp [cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add]
  refine ⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans
    ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩
  intro a m k
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]
  rw [← hcb]
  rfl
