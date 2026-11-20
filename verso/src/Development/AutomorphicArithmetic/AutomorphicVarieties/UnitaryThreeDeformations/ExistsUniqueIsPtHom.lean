import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
The claim follows from `SemidirectProduct.ext (Units.ext h2) h1`.
-/
private theorem gg_ext {R : Type} [CommRing R] {x y : GG 3 R} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

/- English proof (translation)
Establish `hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹`. Introduce `R' _ k`. Establish `hJ : GeneralLinearGroup.det (Jgl R' 3) * GeneralLinearGroup.det (Jgl R' 3) = 1`. Rewrite using `[← map_mul]`. Establish `: Jgl R' 3 * Jgl R' 3 = 1` using `Units.ext (Jgl R' 3).val_inv`.

Rewrite using `[this, map_one]`. Establish `hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹`. Rewrite using `[← map_inv]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]`.

Use `show GeneralLinearGroup.det (theta k) = _`. Simplify using `only [theta, map_mul, hT]`. Rewrite using `[mul_right_comm, hJ, one_mul]`. Establish `htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2)`. Introduce `R' _ t`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]`. Use `⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩` and prove the remaining obligations. Introduce `R' _ _ _ f f' t h`. Establish `hg` using `congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h`.

Simplify using `only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, SemidirectProduct.map_right, map_mu …`. Simplify using `only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg`. Establish `key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹`. Rewrite using `[map_inv, map_inv]`. Use `split_ifs with hs`.

Rewrite `hg` using `[hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor]`. Rewrite using `[hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]`. Establish `: sgnAct 3 R' (u g).right = thetaAut 3 R'` using `by simp [sgnAct, hs]`. Rewrite `hg` using `[this, hth, inv_inv, htor, GeneralLinearGroup.map_det]`. Rewrite using `[hg]`.

Generalize the expression as in `wt1 0 + wt1 1 + wt1 2 = w`. Rewrite using `[show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]`. Simplify using `only [_root_.mul_inv_rev]`. The two sides agree by associativity and commutativity. Establish `e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R')` using `fun φ => rfl`.

Rewrite using `[e f', e f, key, Units.val_mul]`.
-/
private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG 3 R) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart O u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl R' 3) * GeneralLinearGroup.det (Jgl R' 3) = 1 := by
      rw [← map_mul]
      have : Jgl R' 3 * Jgl R' 3 = 1 := Units.ext (Jgl R' 3).val_inv
      rw [this, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, SemidirectProduct.map_right, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

/- English proof (translation)
Introduce `O R Γ K _ _ _ _ _ _ _ u ξ`. Establish `hmem : ∀ g a b, (u g).mat a b ∈ Sring O u` using `fun g a b => ptMat._proof_1 u g a b`. Establish `hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring O u`. Introduce `g a b`. Take `⟨j, hj⟩` from `exists_weight_inv_det_left_mem_weight_piece (O := O) u g`.

Establish `hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring O u` using `by show _ ∈ (⨆ j, wpart O u j)`. Conclude with `Submodule.mem_iSup_of_mem j hj`. Set `M' : Matrix (Fin 3) (Fin 3) (Sring O u)` to `fun a b => ⟨(u g).mat a b, hmem g a b⟩`. Establish `hM : ((Sring O u).val : Sring O u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R)`. Use extensionality with `a b`.

Both sides reduce to the same expression. Establish `hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R)` using `(GeneralLinearGroup.val_det_apply _).symm`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `(Sring O u).mul_mem hd (M'.adjugate a b).2`.

Establish `hinj : Function.Injective (((Sring O u).val : Sring O u →+* R).mapMatrix (m` using `Fin 3)) := by`. Introduce `x y h`. Use extensionality with `a b`. Conclude with `congrFun (congrFun h a) b`. Set `large₂ : Γ → GL (Fin 3) (Sring O u)` to `fun g => { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩ inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩ val_inv := by`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one]`. Apply the tactic sequence `convert (u g).left.val_inv using 2 <;> ext a b <;> rfl`. Use `inv_val := by`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one]`. Apply the tactic sequence `convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }`. Establish `gmap_inj : Function.Injective (GG.map (m` using `3) ((Sring O u).val : Sring O u →+* R)) := by`. Introduce `x y h`. Apply `gg_ext` to reduce the goal to its premises.

Use `congrArg (fun z => z.right) h` as an intermediate fact. Simplify `this` using `[GG.map_right]`. Use extensionality with `a b`. Use `congrArg (fun z => z.mat a b) h` as an intermediate fact. Simplify `this` using `[GG.map_mat]`.

Set `vf : Γ → GG 3 (Sring O u)` to `fun g => SemidirectProduct.mk (large₂ g) (u g).right`. Establish `hv : ∀ g, GG.map ((Sring O u).val : Sring O u →+* R) (vf g) = u g`. Introduce `g`. Apply `gg_ext` to reduce the goal to its premises. Rewrite using `[GG.map_right]`.

Use extensionality with `a b`. Rewrite using `[GG.map_mat]`. Both sides reduce to the same expression. Set `v : Γ →* GG 3 (Sring O u)` to `{ toFun := vf map_one' := gmap_inj (by rw [hv, map_one, map_one]) map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }`. Establish `h0 : IsPtHom u ξ ((GG.map (ξ : Sring O u →+* K)).comp v)`.

Introduce `g`. Prove the components needed by the constructor for the conclusion. Use `show (GG.map _ (vf g)).right = _`. Rewrite using `[GG.map_right]`. Use `show (GG.map _ (vf g)).mat = _`.

Rewrite using `[GG.map_mat]`. Use extensionality with `a b`. Both sides reduce to the same expression. Use `⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩` and prove the remaining obligations.
-/
theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG 3 R) (ξ : Sring O u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring O u := fun g a b => ptMat._proof_1 u g a b
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring O u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring O u := by
      show _ ∈ (⨆ j, wpart O u j)
      exact Submodule.mem_iSup_of_mem j hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring O u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring O u).val : Sring O u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring O u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring O u).val : Sring O u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring O u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring O u).val : Sring O u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG 3 (Sring O u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring O u).val : Sring O u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG 3 (Sring O u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring O u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
