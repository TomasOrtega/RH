import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Semi

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']
  (e : V ≃+ V') (he : ∀ (c : F) (x : V), e (c • x) = r c • e x)

include he in
/- English proof (translation)
Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
private theorem symm_smul (c : F') (y : V') : e.symm (c • y) = r.symm c • e.symm y := by
  apply e.injective
  rw [he]
  simp

private def smap (W : Submodule F V) : Submodule F' V' where
  carrier := e '' W
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, W.add_mem ha hb, map_add e a b⟩
  zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨r.symm c • a, W.smul_mem _ ha, by rw [he]; simp⟩

private def scomap (W : Submodule F' V') : Submodule F V where
  carrier := e ⁻¹' W
  add_mem' := by
    intro a b ha hb
    simpa using W.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_preimage, SetLike.mem_coe, he] at ha ⊢
    exact W.smul_mem _ ha

/- English proof (translation)
Express the relevant statement in the definitionally equal form `y ∈ e '' (W : Set V) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Simplify using `using ha`. Introduce `h`.

Conclude with `⟨e.symm y, h, by simp⟩`.
-/
private theorem mem_smap {W : Submodule F V} {y : V'} : y ∈ smap r e he W ↔ e.symm y ∈ W := by
  change y ∈ e '' (W : Set V) ↔ _
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨e.symm y, h, by simp⟩

private def smapE : Submodule F V ≃ Submodule F' V' where
  toFun := smap r e he
  invFun := scomap r e he
  left_inv W := by
    ext x
    change e x ∈ smap r e he W ↔ _
    rw [mem_smap]
    simp
  right_inv W := by
    ext y
    rw [mem_smap]
    change e (e.symm y) ∈ W ↔ _
    simp

private def eRes (W : Submodule F V) : W ≃+ smap r e he W where
  toFun x := ⟨e x, (mem_smap r e he).2 (by simp)⟩
  invFun y := ⟨e.symm y, (mem_smap r e he).1 y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

include he in
/- English proof (translation)
Set `b` to `Module.finBasis F V`. Establish `hf : ∀ f : Fin (Module.finrank F V) →₀ F, Finsupp.mapRange r.symm (map_zero r.symm) (Finsupp.mapRange r (map_zero r) f) = f`. Introduce `f`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Set `repr' : V' ≃ₗ[F'] (Fin (Module.finrank F V) →₀ F')` to `{ toFun := fun y => Finsupp.mapRange r (map_zero r) (b.repr (e.symm y)) invFun := fun c => e (b.repr.symm (Finsupp.mapRange r.symm (map_zero r.symm) c)) map_add' := by`. Introduce `x y`. Use extensionality with `i`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := by`.

Introduce `c y`. Use extensionality with `i`. Simplify using `[symm_smul r e he]`. Use `left_inv := by`. Introduce `y`.

Use `show e (b.repr.symm (Finsupp.mapRange r.symm _ (Finsupp.mapRange r _ (b.repr (e.symm y))))) = y`. Rewrite using `[hf]`. Simplify using the standard rewrite rules. Use `right_inv := by`. Introduce `c`.

Use extensionality with `i`. Simplify using `}`. Set `b' : Module.Basis (Fin (Module.finrank F V)) F' V'` to `Module.Basis.ofRepr repr'`. Establish `hb' : ∀ j, b' j = e (b j)`. Introduce `j`.

Simplify using `[b', repr']`. Rewrite using `[← LinearMap.charpoly_toMatrix g b, ← LinearMap.charpoly_toMatrix g' b', ← Matrix.charpoly_map]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]`.

Use `show (Finsupp.mapRange r (map_zero r) (b.repr (e.symm (e (g (b j)))))) i = _`. Simplify using the standard rewrite rules.
-/
private theorem charpoly_semi [FiniteDimensional F V] [FiniteDimensional F' V']
    (g : Module.End F V) (g' : Module.End F' V') (hg : ∀ x, e (g x) = g' (e x)) :
    LinearMap.charpoly g' = (LinearMap.charpoly g).map r.toRingHom := by
  classical
  let b := Module.finBasis F V
  have hf : ∀ f : Fin (Module.finrank F V) →₀ F,
      Finsupp.mapRange r.symm (map_zero r.symm) (Finsupp.mapRange r (map_zero r) f) = f := by
    intro f
    ext i
    simp
  let repr' : V' ≃ₗ[F'] (Fin (Module.finrank F V) →₀ F') :=
    { toFun := fun y => Finsupp.mapRange r (map_zero r) (b.repr (e.symm y))
      invFun := fun c => e (b.repr.symm (Finsupp.mapRange r.symm (map_zero r.symm) c))
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c y
        ext i
        simp [symm_smul r e he]
      left_inv := by
        intro y
        show e (b.repr.symm (Finsupp.mapRange r.symm _ (Finsupp.mapRange r _ (b.repr (e.symm y))))) = y
        rw [hf]
        simp
      right_inv := by
        intro c
        ext i
        simp }
  let b' : Module.Basis (Fin (Module.finrank F V)) F' V' := Module.Basis.ofRepr repr'
  have hb' : ∀ j, b' j = e (b j) := by
    intro j
    simp [b', repr']
  rw [← LinearMap.charpoly_toMatrix g b, ← LinearMap.charpoly_toMatrix g' b', ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  show (Finsupp.mapRange r (map_zero r) (b.repr (e.symm (e (g (b j)))))) i = _
  simp

end Semi

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V V' _ _ _ _ _ _ e he g g' hg`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Introduce `V V' _ _ _ _ _ _ e he g g' hg`. Rewrite using `[GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, charpoly_semi r e he g g' hg, hs]`. Use `congr 1`. Establish `htop : smapE r e he ⊤ = ⊤`. Use extensionality with `y`.

Express the relevant statement in the definitionally equal form `y ∈ smap r e he ⊤ ↔ _`. Rewrite using `[mem_smap]`. Simplify using the standard rewrite rules. Establish `hsymm : ∀ y, e.symm (g' y) = g (e.symm y)`. Introduce `y`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hg]`. Simplify using the standard rewrite rules. Establish `hiff : ∀ W : Submodule F V, (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) ↔ (smapE r e he W ≠ ⊤ ∧ ∀ y ∈ smapE r e he W, g' y ∈ smapE r e he W)`. Introduce `W`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hW, hinv⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hW` to reduce the goal to its premises.

Apply `(smapE r e he).injective` to reduce the goal to its premises. Rewrite using `[h, htop]`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `g' y ∈ smap r e he W`. Express the relevant statement in the definitionally equal form `y ∈ smap r e he W at hy`.

Rewrite `hy`, the goal using `[mem_smap]`. Rewrite using `[hsymm]`. Conclude with `hinv _ hy`. Introduce and unpack `⟨hW, hinv⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hW htop`. Introduce `x hx`. Establish `h1 : e x ∈ smap r e he W`. Rewrite using `[mem_smap]`.

Simplify using `using hx`. Establish `h2` using `hinv (e x) h1`. Express the relevant statement in the definitionally equal form `g' (e x) ∈ smap r e he W at h2`. Rewrite `h2` using `[mem_smap, hsymm]`. Simplify using `using h2`.

Use `symm`. Apply `finsum_eq_of_bijective ((smapE r e he).subtypeEquiv hiff) (Equiv.bijective _)` to reduce the goal to its premises. Introduce `W`. Use `symm`. Conclude with `ih _ _ (eRes r e he W.1) (by`.

Introduce `c x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[eRes, he])`. Use `_ _`. Use the proof step `(by`.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[eRes, hg]`. Use the proof step `rfl)`.
-/
private theorem semilinear_equiv_conjugate_endomorphism {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (s : F[X] → ℂ) (s' : F'[X] → ℂ)
    (hs : ∀ P, s' (P.map r.toRingHom) = s P) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F' V']
      [FiniteDimensional F' V'] (e : V ≃+ V') (_ : ∀ (c : F) (x : V), e (c • x) = r c • e x)
      (g : Module.End F V) (g' : Module.End F' V'), (∀ x, e (g x) = g' (e x)) →
      GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s' n V' g' = GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rw [GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, charpoly_semi r e he g g' hg, hs]
    congr 1
    have htop : smapE r e he ⊤ = ⊤ := by
      ext y
      change y ∈ smap r e he ⊤ ↔ _
      rw [mem_smap]
      simp
    have hsymm : ∀ y, e.symm (g' y) = g (e.symm y) := by
      intro y
      apply e.injective
      rw [hg]
      simp
    have hiff : ∀ W : Submodule F V, (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) ↔
        (smapE r e he W ≠ ⊤ ∧ ∀ y ∈ smapE r e he W, g' y ∈ smapE r e he W) := by
      intro W
      constructor
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · intro h
          apply hW
          apply (smapE r e he).injective
          rw [h, htop]
        · intro y hy
          change g' y ∈ smap r e he W
          change y ∈ smap r e he W at hy
          rw [mem_smap] at hy ⊢
          rw [hsymm]
          exact hinv _ hy
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hW htop
        · intro x hx
          have h1 : e x ∈ smap r e he W := by
            rw [mem_smap]
            simpa using hx
          have h2 := hinv (e x) h1
          change g' (e x) ∈ smap r e he W at h2
          rw [mem_smap, hsymm] at h2
          simpa using h2
    symm
    apply finsum_eq_of_bijective ((smapE r e he).subtypeEquiv hiff) (Equiv.bijective _)
    intro W
    symm
    exact ih _ _ (eRes r e he W.1)
      (by
        intro c x
        apply Subtype.ext
        simp [eRes, he])
      _ _
      (by
        intro x
        apply Subtype.ext
        simp [eRes, hg]
        rfl)

/- English proof (translation)
Unfold `GlobalTheory.CuspGL.rootSum`. Establish `hpoly : (P.map r.toRingHom).map (algebraMap F' (AlgebraicClosure F')) = (P.map (algebraMap F (AlgebraicClosure F))).map j.toRingHom`. Rewrite using `[Polynomial.map_map, Polynomial.map_map]`. Use `congr 1`. Use extensionality with `x`.

Conclude with `(hj x).symm`. Rewrite using `[hpoly, ← roots_map_of_injective_of_card_eq_natDegree j.injective IsAlgClosed.card_roots_eq_natDegree, Multiset.map_map]`. Both sides reduce to the same expression.
-/
private theorem rootSum_iso {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
    (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ) (c : ℕ) (P : F[X]) :
    GlobalTheory.CuspGL.rootSum θ c (P.map r.toRingHom) = GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c P := by
  unfold GlobalTheory.CuspGL.rootSum
  have hpoly : (P.map r.toRingHom).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map j.toRingHom := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    exact (hj x).symm
  rw [hpoly, ← roots_map_of_injective_of_card_eq_natDegree j.injective IsAlgClosed.card_roots_eq_natDegree,
    Multiset.map_map]
  rfl

/- English proof (translation)
Introduce `F F' _ _ _ r j hj θ m c g`. Unfold `cusp psiG GlobalTheory.CuspGL.psi`. Use `congr 1`. Rewrite using `[Module.finrank_fin_fun, Module.finrank_fin_fun]`. Apply `semilinear_equiv_conjugate_endomorphism r (GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c) (GlobalTheory.CuspGL.rootSum θ c) (rootSum_iso r j hj θ c) (m + 1) (Fin m → F) (Fin m → F') (AddEquiv.piCongrRight fun _ => r.toAddEquiv)` to reduce the goal to its premises.

Introduce `a x`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Introduce `x`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.cuspIso :
    CuspIso := by
  intro F F' _ _ _ r j hj θ m c g
  unfold cusp psiG GlobalTheory.CuspGL.psi
  congr 1
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  apply semilinear_equiv_conjugate_endomorphism r (GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c) (GlobalTheory.CuspGL.rootSum θ c)
    (rootSum_iso r j hj θ c) (m + 1) (Fin m → F) (Fin m → F') (AddEquiv.piCongrRight fun _ => r.toAddEquiv)
  · intro a x
    funext i
    simp
  · intro x
    funext i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
