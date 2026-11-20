import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[red, RingHom.map_mulVec]`.
-/
private theorem red_apply_map {R k : Type} [CommRing R] [Field k] (r : R →+* k) (N : ℕ) (g : GL (Fin N) R)
    (x : Fin N → R) : red r N g (r ∘ x) = r ∘ (g : Matrix (Fin N) (Fin N) R).mulVec x := by
  funext j
  simp [red, RingHom.map_mulVec]

/- English proof (translation)
Establish `key : ∀ z ∈ RingHom.ker r • (⊤ : Submodule R M), r ∘ i z = 0`. Introduce `z hz`. Use `Submodule.smul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `a ha m _`. Use function extensionality and compare the values at `j`.

Simplify using `[(RingHom.mem_ker).1 ha]`. Introduce `z w hz hw`. Use function extensionality and compare the values at `j`. Establish `e₁` using `congrFun hz j`. Establish `e₂` using `congrFun hw j`.

Simplify using `only [Function.comp_apply, Pi.zero_apply] at e₁ e₂ ⊢`. Rewrite using `[map_add, Pi.add_apply, map_add, e₁, e₂, add_zero]`. Establish `wd : ∀ x y : M, π x = π y → r ∘ i x = r ∘ i y`. Introduce `x y hxy`. Establish `hz : x - y ∈ RingHom.ker r • (⊤ : Submodule R M)` using `h3 _ (by rw [map_sub, hxy, sub_self])`.

Establish `e` using `key _ hz`. Use function extensionality and compare the values at `j`. Establish `ej` using `congrFun e j`. Simplify using `only [map_sub, Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at ej`. Conclude with `sub_eq_zero.1 ej`.

Use `choose pre hpre using h2`. Use `⟨{ toFun := fun v => r ∘ i (pre v), map_add' := ?_, map_smul' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `v w`. Establish `e : π (pre (v + w)) = π (pre v + pre w)` using `by rw [map_add, hpre, hpre, hpre]`. Rewrite using `[wd _ _ e, map_add]`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Introduce `c v`. Take `⟨a, rfl⟩` from `hr c`. Establish `e : π (pre (r a • v)) = π (a • pre v)` using `by rw [h1, hpre, hpre]`.

Rewrite using `[wd _ _ e, map_smul]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Introduce `x`. Conclude with `wd _ _ (hpre _)`.
-/
private theorem exists_ibar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (hr : Function.Surjective r) (i : M →ₗ[R] (Fin N → R)) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) (h2 : Function.Surjective π)
    (h3 : ∀ x, π x = 0 → x ∈ RingHom.ker r • (⊤ : Submodule R M)) :
    ∃ ib : V →ₗ[k] (Fin N → k), ∀ x, ib (π x) = r ∘ i x := by
  have key : ∀ z ∈ RingHom.ker r • (⊤ : Submodule R M), r ∘ i z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      funext j
      simp [(RingHom.mem_ker).1 ha]
    · intro z w hz hw
      funext j
      have e₁ := congrFun hz j
      have e₂ := congrFun hw j
      simp only [Function.comp_apply, Pi.zero_apply] at e₁ e₂ ⊢
      rw [map_add, Pi.add_apply, map_add, e₁, e₂, add_zero]
  have wd : ∀ x y : M, π x = π y → r ∘ i x = r ∘ i y := by
    intro x y hxy
    have hz : x - y ∈ RingHom.ker r • (⊤ : Submodule R M) := h3 _ (by rw [map_sub, hxy, sub_self])
    have e := key _ hz
    funext j
    have ej := congrFun e j
    simp only [map_sub, Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at ej
    exact sub_eq_zero.1 ej
  choose pre hpre using h2
  refine ⟨{ toFun := fun v => r ∘ i (pre v), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro v w
    have e : π (pre (v + w)) = π (pre v + pre w) := by rw [map_add, hpre, hpre, hpre]
    rw [wd _ _ e, map_add]
    funext j
    simp
  · intro c v
    obtain ⟨a, rfl⟩ := hr c
    have e : π (pre (r a • v)) = π (a • pre v) := by rw [h1, hpre, hpre]
    rw [wd _ _ e, map_smul]
    funext j
    simp
  · intro x
    exact wd _ _ (hpre _)

/- English proof (translation)
Use `⟨(Pi.basisFun k (Fin N)).constr k (fun j => π (s (Pi.single j 1))), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.constr_apply_fintype]`. Establish `hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R)`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `conv_rhs => rw [hx, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, h1]`. Simplify using the standard rewrite rules.
-/
private theorem exists_sbar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (s : (Fin N → R) →ₗ[R] M) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) :
    ∃ sb : (Fin N → k) →ₗ[k] V, ∀ x, sb (r ∘ x) = π (s x) := by
  refine ⟨(Pi.basisFun k (Fin N)).constr k (fun j => π (s (Pi.single j 1))), fun x => ?_⟩
  rw [Module.Basis.constr_apply_fintype]
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h1]
  simp

/- English proof (translation)
Introduce `R _ M _ _ _ _ H _ α`. Take `⟨N, s, hs⟩` from `Module.Finite.exists_fin' R M`. Take `⟨i, hi⟩` from `Module.projective_lifting_property s LinearMap.id hs`. Establish `hsi : ∀ y, s (i y) = y` using `fun y => LinearMap.congr_fun hi y`. Set `E : H →* Module.End R (Fin N → R)` to `{ toFun := fun h => i ∘ₗ (α h).toLinearMap ∘ₗ s + (LinearMap.id - i ∘ₗ s) map_one' := LinearMap.ext fun x => by simp map_mul' := fun g h => LinearMap.ext fun x => by`.

Simplify using `[hsi, map_mul, Module.End.mul_apply] }`. Set `lam : H →* GL (Fin N) R` to `(Units.map (LinearMap.toMatrixAlgEquiv' : Module.End R (Fin N → R) ≃ₐ[R] Matrix (Fin N) (Fin N) R).toMonoidHom).comp E.toHomUnits`. Use `⟨N, lam, ?_⟩` and prove the remaining obligations. Introduce `k _ r hr V _ _ π μ h1 h2 h3 h4`. Take `⟨ib, hib⟩` from `exists_ibar r hr i π h1 h2 h3`.

Take `⟨sb, hsb⟩` from `exists_sbar r s π h1`. Establish `sbib : ∀ v, sb (ib v) = v`. Introduce `v`. Take `⟨x, rfl⟩` from `h2 v`. Rewrite using `[hib, hsb, hsi]`.

Set `f : (V × LinearMap.ker sb) →ₗ[k] (Fin N → k)` to `LinearMap.coprod ib (LinearMap.ker sb).subtype`. Establish `hfa : ∀ w : V × LinearMap.ker sb, f w = ib w.1 + (w.2 : Fin N → k)` using `fun w => rfl`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `w w' hww`.

Rewrite `hww` using `[hfa, hfa]`. Establish `e1 : w.1 = w'.1`. Use `congrArg sb hww` as an intermediate fact. Rewrite `this` using `[map_add, map_add, sbib, sbib, LinearMap.mem_ker.1 w.2.2, LinearMap.mem_ker.1 w'.2.2, add_zero, add_zero]`. Then use the resulting hypothesis. Rewrite `hww` using `[e1]`.

Conclude with `Prod.ext e1 (Subtype.ext (add_left_cancel hww))`. Introduce `y`. Use `⟨(sb y, ⟨y - ib (sb y), ?_⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, sbib, sub_self]`. Rewrite using `[hfa]`.

Simplify using the standard rewrite rules. Set `φ` to `LinearEquiv.ofBijective f hf`. Use `⟨LinearMap.ker sb, φ, ?_⟩` and prove the remaining obligations. Use `MonoidHom.ext fun h => LinearEquiv.ext fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩ : ∃ x : Fin N → R, r ∘ x = y` from `⟨fun j => (hr (y j)).choose, funext fun j => (hr (y j)).choose_spec⟩`.

Establish `rhs : (cj φ) ((sumRep μ 1) h) (r ∘ x) = f ((μ h (φ.symm (r ∘ x)).1, (φ.symm (r ∘ x)).2))` using `rfl`. Establish `hfw : f (φ.symm (r ∘ x)) = r ∘ x` using `φ.apply_symm_apply (r ∘ x)`. Simplify using `only [MonoidHom.comp_apply]`. Rewrite using `[rhs]`. Take `⟨w, hw⟩ : ∃ w, φ.symm (r ∘ x) = w` from `⟨_, rfl⟩`.

Rewrite `hfw`, the goal using `[hw]`. Establish `hyw : r ∘ x = ib w.1 + (w.2 : Fin N → k)`. Rewrite using `[← hfa]`. Conclude with `hfw.symm`. Establish `hv : π (s x) = w.1`.

Rewrite using `[← hsb, hyw, map_add, sbib, LinearMap.mem_ker.1 w.2.2, add_zero]`. Rewrite using `[red_apply_map]`. Establish `hlam : ((lam h : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x = E h x` using `by show (LinearMap.toMatrix' (E h)).mulVec x = E h x`. Rewrite using `[← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`. Rewrite using `[hlam]`.

Establish `e1 : E h x = i (α h (s x)) + (x - i (s x))` using `rfl`. Establish `e2 : ∀ a b : Fin N → R, r ∘ (a + (x - b)) = r ∘ a + (r ∘ x - r ∘ b)`. Introduce `a b`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Rewrite using `[e1, e2, ← hib, ← hib, h4, hv, hfa, hyw]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.ZK.Cl.cFree :
    UpperTheory.V.ZK.Cl.CFree := by
  intro R _ M _ _ _ _ H _ α
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hi⟩ := Module.projective_lifting_property s LinearMap.id hs
  have hsi : ∀ y, s (i y) = y := fun y => LinearMap.congr_fun hi y
  let E : H →* Module.End R (Fin N → R) :=
    { toFun := fun h => i ∘ₗ (α h).toLinearMap ∘ₗ s + (LinearMap.id - i ∘ₗ s)
      map_one' := LinearMap.ext fun x => by simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp [hsi, map_mul, Module.End.mul_apply] }
  let lam : H →* GL (Fin N) R :=
    (Units.map (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin N → R) ≃ₐ[R] Matrix (Fin N) (Fin N) R).toMonoidHom).comp E.toHomUnits
  refine ⟨N, lam, ?_⟩
  intro k _ r hr V _ _ π μ h1 h2 h3 h4
  obtain ⟨ib, hib⟩ := exists_ibar r hr i π h1 h2 h3
  obtain ⟨sb, hsb⟩ := exists_sbar r s π h1
  have sbib : ∀ v, sb (ib v) = v := by
    intro v
    obtain ⟨x, rfl⟩ := h2 v
    rw [hib, hsb, hsi]
  let f : (V × LinearMap.ker sb) →ₗ[k] (Fin N → k) := LinearMap.coprod ib (LinearMap.ker sb).subtype
  have hfa : ∀ w : V × LinearMap.ker sb, f w = ib w.1 + (w.2 : Fin N → k) := fun w => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro w w' hww
      rw [hfa, hfa] at hww
      have e1 : w.1 = w'.1 := by
        have := congrArg sb hww
        rwa [map_add, map_add, sbib, sbib, LinearMap.mem_ker.1 w.2.2, LinearMap.mem_ker.1 w'.2.2,
          add_zero, add_zero] at this
      rw [e1] at hww
      exact Prod.ext e1 (Subtype.ext (add_left_cancel hww))
    · intro y
      refine ⟨(sb y, ⟨y - ib (sb y), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker, map_sub, sbib, sub_self]
      · rw [hfa]
        simp
  let φ := LinearEquiv.ofBijective f hf
  refine ⟨LinearMap.ker sb, φ, ?_⟩
  refine MonoidHom.ext fun h => LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Fin N → R, r ∘ x = y :=
    ⟨fun j => (hr (y j)).choose, funext fun j => (hr (y j)).choose_spec⟩
  have rhs : (cj φ) ((sumRep μ 1) h) (r ∘ x) =
      f ((μ h (φ.symm (r ∘ x)).1, (φ.symm (r ∘ x)).2)) := rfl
  have hfw : f (φ.symm (r ∘ x)) = r ∘ x := φ.apply_symm_apply (r ∘ x)
  simp only [MonoidHom.comp_apply]
  rw [rhs]
  obtain ⟨w, hw⟩ : ∃ w, φ.symm (r ∘ x) = w := ⟨_, rfl⟩
  rw [hw] at hfw ⊢
  have hyw : r ∘ x = ib w.1 + (w.2 : Fin N → k) := by
    rw [← hfa]
    exact hfw.symm
  have hv : π (s x) = w.1 := by
    rw [← hsb, hyw, map_add, sbib, LinearMap.mem_ker.1 w.2.2, add_zero]
  rw [red_apply_map]
  have hlam : ((lam h : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x = E h x := by
    show (LinearMap.toMatrix' (E h)).mulVec x = E h x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hlam]
  have e1 : E h x = i (α h (s x)) + (x - i (s x)) := rfl
  have e2 : ∀ a b : Fin N → R, r ∘ (a + (x - b)) = r ∘ a + (r ∘ x - r ∘ b) := by
    intro a b
    funext j
    simp
  rw [e1, e2, ← hib, ← hib, h4, hv, hfa, hyw]
  abel
