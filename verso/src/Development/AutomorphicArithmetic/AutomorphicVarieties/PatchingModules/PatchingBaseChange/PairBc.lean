import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Use `GDet.ext fun B _ _ x => ?_` and prove the remaining obligations. Simplify using `only [GDet.map, GDet.ofRep, GDet.repAlg]`. Use `congr 4`. Apply `congrArg` to reduce the goal to its premises. Use `MonoidHom.ext fun s => ?_` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem gdet_ofRep_diagRep_map_eq_ofRep_pushCh {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (χ : Fin n → G →* Aˣ) (f : A →+* A') :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep (fun i => pushCh f (χ i))) := by
  refine GDet.ext fun B _ _ x => ?_
  simp only [GDet.map, GDet.ofRep, GDet.repAlg]
  congr 4
  apply congrArg
  refine MonoidHom.ext fun s => ?_
  ext i j
  simp [diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]
  split_ifs <;> simp

/- English proof (translation)
Use `letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra`. Set `φ : Polynomial A →ₐ[A] Polynomial A'` to `{ Polynomial.mapRingHom f with commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }`. Establish `key` using `D.nat (Polynomial A) (Polynomial A') φ (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)`. Establish `e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A')) (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x) = MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x)`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single]`.

Use `congr 1`. Simplify using `[φ]`. Use extensionality with `g`. Simplify using `[φ, MonoidAlgebra.mapRingHom]`. Rewrite `key` using `[e]`.

Conclude with `key`.
-/
private theorem gdet_map_chi_mapRingHom_eq_map_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (x : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial A' :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat (Polynomial A) (Polynomial A') φ
    (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
  have e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A'))
        (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
      = MonoidAlgebra.single 1 Polynomial.X
          - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ]
    · ext g
      simp [φ, MonoidAlgebra.mapRingHom]
  rw [e] at key
  exact key

/- English proof (translation)
Simplify using `only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]`.
-/
private theorem gdet_map_lam_mapRingHom_eq_lam {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (i : ℕ) (x : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f x) = f (D.lam i x) := by
  simp only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

/- English proof (translation)
Introduce `N`. Establish `hm : (maximalIdeal R).map g ≤ maximalIdeal R'` using `Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx`. Establish `hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm N`.

Use `(h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[Ideal.quotientMap_mk]`.
-/
private theorem adicCont_maximalIdeal_comp_of_isLocalHom {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (g : R →+* R') [IsLocalHom g] {φ : Γ → R}
    (h : AdicCont (maximalIdeal R) φ) : AdicCont (maximalIdeal R') (fun x => g (φ x)) := by
  intro N
  have hm : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have := (h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)
  convert this using 1
  funext x
  simp [Ideal.quotientMap_mk]

/- English proof (translation)
Use `show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0`. Simplify using `[(IsLocalRing.residue_eq_zero_iff x).mpr hx]`.
-/
private theorem res_eq_zero_of_mem_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (x : R) (hx : x ∈ maximalIdeal R) : res O R x = 0 := by
  show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0
  simp [(IsLocalRing.residue_eq_zero_iff x).mpr hx]

/- English proof (translation)
Introduce `l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p`. Establish `hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)`. Introduce `x`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) x`. Establish `hx : x = algebraMap O R a + (x - algebraMap O R a)` using `by ring`.

Establish `h2 : g (x - algebraMap O R a) ∈ maximalIdeal R'` using `map_nonunit g _ ha`. Rewrite using `[hx, map_add, map_add, map_add, hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero, AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq, ResidueField.map_residue]`. Establish `hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀) = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1)`. Introduce `h`. Simplify using `[MonoidAlgebra.mapRingHom_single]`.

Use `⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩` and prove the remaining obligations. Introduce `i`. Establish `key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1)) = fun h => g (p.D.lam i (MonoidAlgebra.single h 1))`. Use function extensionality and compare the values at `h`. Rewrite using `[hs1, gdet_map_lam_mapRingHom_eq_lam]`.

Use `show AdicCont _ _`. Rewrite using `[key]`. Conclude with `adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)`. Establish `hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)` using `RingHom.ext hres`. Establish `e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O') = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map (ResidueField.map (algebraMap O O'))`.

Use `GDet.ext fun B _ _ x => ?_` and prove the remaining obligations. Simplify using `only [GDet.map]`. Use `congr 2`. Use `congr 1`. Use `RingHom.ext fun y => ?_` and prove the remaining obligations.

Use `show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))`. Rewrite using `[hres]`. Rewrite using `[e1, p.red]`. Use `show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)`. Rewrite using `[gdet_ofRep_diagRep_map_eq_ofRep_pushCh]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `(hr.1 i).symm`. Introduce `v i`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont` as an intermediate fact. Simplify `this` using `[pushCh]`. Introduce `x`. Establish `h1` using `(p.psi v i).red x`. Simplify using `only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]`.

Rewrite using `[hres, h1, hr.2.1 v i]`. Simplify using `[pushCh]`. Introduce `x`. Establish `h1` using `(p.psi v i).mu x`. Simplify using `only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]`.

Rewrite using `[h1, hg, hr.2.2 v i]`. Simplify using `[pushCh]`. Introduce `i h`. Establish `he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y`. Introduce `y`.

Use `ext`. Simplify using `[GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]`. Establish `hs : F.star O' R' n (MonoidAlgebra.single h 1) = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1))`. Simplify using `[GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]`. Rewrite using `[← map_zpow]`.

Both sides reduce to the same expression. Rewrite using `[hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]`. Introduce `v gg h`. Establish `e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg)`. Rewrite using `[map_mul, ← hs1]`.

Use `congr 1`. Simplify using `[GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh, MonoidAlgebra.mapRingHom_single]`. Establish `h0` using `p.Ord v gg h`. Simplify using `only [GDet.tr] at h0 ⊢`. Rewrite using `[e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]`.

Introduce `u x hx h`. Establish `hx' : x ∈ r.Ip u`. Simplify using `only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢`. Use `⟨hx.1, fun i => ?_⟩` and prove the remaining obligations. Establish `h2` using `hx.2 i`.

Rewrite `h2` using `[hr.1 i]`. Use `ext`. Establish `h3` using `congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2`. Simplify using `only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3`. Apply `(ResidueField.map (algebraMap O O')).injective` to reduce the goal to its premises.

Rewrite using `[h3, Units.val_one, map_one]`. Establish `e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1) = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1))`. Simplify using `[MonoidAlgebra.mapRingHom_single]`. Establish `h0` using `p.I u x hx' h`. Simplify using `only [GDet.tr] at h0 ⊢`.

Rewrite using `[e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]`.
-/
theorem UpperTheory.V.Pa.BC.pair_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n), RBC r r' → ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O' R'] [IsCO O' R'] (g : R →+* R') [IsLocalHom g], (∀ a, g (algebraMap O R a) = algebraMap O' R' (algebraMap O O' a)) → ∀ p : Pair r R, (∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)) ∧ ∃ p' : Pair r' R', p.Maps g p'.D p'.ψ := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p
  have hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have hx : x = algebraMap O R a + (x - algebraMap O R a) := by ring
    have h2 : g (x - algebraMap O R a) ∈ maximalIdeal R' := map_nonunit g _ ha
    rw [hx, map_add, map_add, map_add, hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero,
      AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq,
      ResidueField.map_residue]
  have hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀)
      = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1) := by
    intro h
    simp [MonoidAlgebra.mapRingHom_single]
  refine ⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩
  · intro i
    have key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1))
        = fun h => g (p.D.lam i (MonoidAlgebra.single h 1)) := by
      funext h
      rw [hs1, gdet_map_lam_mapRingHom_eq_lam]
    show AdicCont _ _
    rw [key]
    exact adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)
  · have hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g
        = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) :=
      RingHom.ext hres
    have e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O')
        = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map
            (ResidueField.map (algebraMap O O')) := by
      refine GDet.ext fun B _ _ x => ?_
      simp only [GDet.map]
      congr 2
      congr 1
      refine RingHom.ext fun y => ?_
      show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))
      rw [hres]
    rw [e1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)
    rw [gdet_ofRep_diagRep_map_eq_ofRep_pushCh]
    congr 2
    funext i
    exact (hr.1 i).symm
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · have := adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont
      simpa [pushCh] using this
    · intro x
      have h1 := (p.psi v i).red x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [hres, h1, hr.2.1 v i]
      simp [pushCh]
    · intro x
      have h1 := (p.psi v i).mu x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [h1, hg, hr.2.2 v i]
      simp [pushCh]
  · intro i h
    have he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y := by
      intro y
      ext
      simp [GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]
    have hs : F.star O' R' n (MonoidAlgebra.single h 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1)) := by
      simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]
      rw [← map_zpow]
      rfl
    rw [hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]
  · intro v gg h
    have e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg) := by
      rw [map_mul, ← hs1]
      congr 1
      simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh,
        MonoidAlgebra.mapRingHom_single]
    have h0 := p.Ord v gg h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
  · intro u x hx h
    have hx' : x ∈ r.Ip u := by
      simp only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢
      refine ⟨hx.1, fun i => ?_⟩
      have h2 := hx.2 i
      rw [hr.1 i] at h2
      ext
      have h3 := congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
      apply (ResidueField.map (algebraMap O O')).injective
      rw [h3, Units.val_one, map_one]
    have e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1)) := by
      simp [MonoidAlgebra.mapRingHom_single]
    have h0 := p.I u x hx' h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
