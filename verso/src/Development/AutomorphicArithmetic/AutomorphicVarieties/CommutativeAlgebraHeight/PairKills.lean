import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GKillsTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Rewrite using `[GFrame.starOp, MonoidAlgebra.lift_single]`. Use `show a • MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _`. Rewrite using `[← MulOpposite.op_smul, MonoidAlgebra.smul_single']`.
-/
private theorem pk_starOp_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.starOp O R n (MonoidAlgebra.single g a) =
      MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R))) := by
  rw [GFrame.starOp, MonoidAlgebra.lift_single]
  show a • MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
  rw [← MulOpposite.op_smul, MonoidAlgebra.smul_single']

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g`. Establish `h : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right F.c_sq`. Rewrite using `[h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]`.
-/
private theorem pk_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

/- English proof (translation)
Establish `h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ)` using `by show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε g`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]`. Simplify using `only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, h]`.
-/
private theorem eps_conj_eq_eps' (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε g
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, h]

/- English proof (translation)
Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp [GFrame.star]`. Consider the case `add x y hx hy`. Simplify using `only [GFrame.star, map_add, MulOpposite.unop_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.

Consider the case `single g a => show MulOpposite.unop (F.starOp O R n (MulOpposite.unop (F.starOp O R n (MonoidAlgebra.single g a)))) = MonoidAlgebra.single g a`. Rewrite using `[pk_starOp_single, MulOpposite.unop_op, pk_starOp_single, MulOpposite.unop_op]`. Use `congr 1`. Rewrite using `[map_inv, inv_inv, pk_conj_conj]`. Rewrite using `[map_inv, eps_conj_eq_eps', inv_zpow, mul_assoc, Units.mul_inv, mul_one]`.
-/
private theorem star_star_monoidAlgebra (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (y : MonoidAlgebra R F.G₀) :
    F.star O R n (F.star O R n y) = y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [GFrame.star, map_add, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    show MulOpposite.unop (F.starOp O R n (MulOpposite.unop (F.starOp O R n (MonoidAlgebra.single g a)))) =
      MonoidAlgebra.single g a
    rw [pk_starOp_single, MulOpposite.unop_op, pk_starOp_single, MulOpposite.unop_op]
    congr 1
    · rw [map_inv, inv_inv, pk_conj_conj]
    · rw [map_inv, eps_conj_eq_eps', inv_zpow, mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Introduce `x`. Use `⟨F.star O R n (MulOpposite.unop x), ?_⟩` and prove the remaining obligations. Apply `MulOpposite.unop_injective` to reduce the goal to its premises. Conclude with `star_star_monoidAlgebra F O R n (MulOpposite.unop x)`.
-/
private theorem pk_surj (R : Type) [CommRing R] [Algebra O R] (n : ℕ) : Function.Surjective (F.starOp O R n) := by
  intro x
  refine ⟨F.star O R n (MulOpposite.unop x), ?_⟩
  apply MulOpposite.unop_injective
  exact star_star_monoidAlgebra F O R n (MulOpposite.unop x)

/- English proof (translation)
Simplify using `only [GFrame.eps, pushCh, MonoidHom.comp_apply, ← map_zpow, Units.coe_map, RingHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe]`. Conclude with `(IsScalarTower.algebraMap_apply O R B _).symm`.
-/
private theorem pk_eps (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (g : F.G₀) (m : ℤ) :
    algebraMap R B ((F.eps O R g ^ m : Rˣ) : R) = ((F.eps O B g ^ m : Bˣ) : B) := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, ← map_zpow, Units.coe_map, RingHom.coe_comp,
    Function.comp_apply, MonoidHom.coe_coe]
  exact (IsScalarTower.algebraMap_apply O R B _).symm

/- English proof (translation)
Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp [GFrame.star]`. Consider the case `add x y hx hy`. Simplify using `only [map_add, GFrame.star, MulOpposite.unop_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.

Consider the case `single g b => show _ = MulOpposite.unop (F.starOp O B n (MonoidAlgebra.single g b))`. Rewrite using `[pk_starOp_single, MulOpposite.unop_op, toT_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, pk_starOp_single, one_mul, Det.unopS, LinearMap.baseChange_tmul]`. Use `show ofT R F.G₀ B (b ⊗ₜ MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _`. Establish `hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap R B ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R))`. Simplify using `[MonoidAlgebra.mapRingHom]`.

Rewrite using `[ofT_tmul, hm, pk_eps, MonoidAlgebra.smul_single']`.
-/
private theorem pk_bc (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (n : ℕ) (y : MonoidAlgebra B F.G₀) :
    ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y))) = F.star O B n y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [map_add, GFrame.star, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g b =>
    show _ = MulOpposite.unop (F.starOp O B n (MonoidAlgebra.single g b))
    rw [pk_starOp_single, MulOpposite.unop_op, toT_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      pk_starOp_single, one_mul, Det.unopS, LinearMap.baseChange_tmul]
    show ofT R F.G₀ B (b ⊗ₜ MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
    have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B)
        (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) =
        MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap R B ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
      simp [MonoidAlgebra.mapRingHom]
    rw [ofT_tmul, hm, pk_eps, MonoidAlgebra.smul_single']

end

/- English proof (translation)
Introduce `l _ F O _ _ _ _ _ _ _ n r R _ _ _ p hphi hn`. Establish `hspan : Submodule.span R (↑(MonoidHom.mrange (MonoidAlgebra.of R F.G₀)) : Set (MonoidAlgebra R F.G₀)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `single g a`. Establish `hs : MonoidAlgebra.single g a = a • MonoidAlgebra.of R F.G₀ g`. Rewrite using `[MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]`.

Rewrite using `[hs]`. Conclude with `Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)`. Establish `hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of R F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n → p.D.toDet.lam i (MulOpposite.unop (F.starOp O R n x)) = p.D.toDet.lam i x`. Introduce and unpack `x ⟨g, rfl⟩ i _ _`. Rewrite using `[(d_toDet p.D _).2.1, (d_toDet p.D _).2.1, MonoidAlgebra.of_apply]`.

Conclude with `p.P i g`. Take `⟨hpull, hCH, hker⟩` from `d_star p.D.toDet (F.starOp O R n) _ hspan hlam`. Establish `hpolar : F.IsPolar O p.D`. Introduce `B _ _ _ _ y`. Establish `h1` using `congrArg (fun X : Det n R (MonoidAlgebra R F.G₀) => X.D B (toT R F.G₀ B y)) hpull`.

Express the relevant statement in the definitionally equal form `p.D.D B (ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y)))) = p.D.D B (ofT R F.G₀ B (toT R F.G₀ B y)) at h1`. Rewrite `h1` using `[pk_bc, ofT_toT]`. Conclude with `h1`. Use `haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom`. Use `haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)`.

Establish `he : Function.Injective (ResidueField.map (algebraMap O R))` using `(resMap_bijective O R).1`. Use `haveI : Finite (ResidueField R) := Finite.of_surjective _ (resMap_bijective O R).2`. Use `haveI : CharP (ResidueField R) l := charP_of_injective_ringHom he l`. Set `χ : Fin n → F.G₀ →* (ResidueField R)ˣ` to `fun i => (Units.map (ResidueField.map (algebraMap O R) : ResidueField O →* ResidueField R)).comp (r.chib i)`. Establish `hres : (ResidueField.map (algebraMap O R)).comp (res O R : R →+* ResidueField O) = residue R`.

Use extensionality with `x`. Use `show ResidueField.map (algebraMap O R) ((RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R x)) = residue R x`. Conclude with `(RingEquiv.ofBijective _ (resMap_bijective O R)).apply_symm_apply _`. Establish `hD : p.D.map (residue R) = GDet.ofChars χ`. Rewrite using `[← hres, ← (d_gmap p.D).2.1, p.red, Resid.Dbar, (d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2, GDet.ofChars]`.

Use `congr 1`. Use extensionality with `g i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[χ, diagRep, GDet.diagRep]`.

Simplify using `[χ, diagRep, GDet.diagRep, Matrix.diagonal_apply_ne _ hij]`. Establish `hopen : ∀ i, IsOpen (↑(χ i).ker : Set F.G₀)`. Introduce `i`. Establish `hk : (χ i).ker = (r.chib i).ker`. Use extensionality with `g`.

Simplify using `only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Units.ext` to reduce the goal to its premises. Apply `he` to reduce the goal to its premises.

Establish `h2` using `congrArg Units.val h`. Simplify using `using h2`. Introduce `h`. Rewrite using `[h, map_one]`. Rewrite using `[hk]`.

Conclude with `r.chib_open i`. Establish `hinj : Function.Injective χ`. Introduce `i j hij`. Apply `r.chib_inj` to reduce the goal to its premises. Use extensionality with `g`.

Apply `he` to reduce the goal to its premises. Establish `h2` using `congrArg (fun f : F.G₀ →* (ResidueField R)ˣ => ((f g : (ResidueField R)ˣ) : ResidueField R)) hij`. Simplify `h2` using `[χ]`. Use `haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact`. Take `⟨h, hh⟩` from `exists_multFree_of_phiCond_of_injective_chars l χ hphi hopen hinj`.

Establish `hK : ∀ y, p.D.Kills y ↔ ∀ g : F.G₀, p.D.tr (MonoidAlgebra.single g 1 * y) = 0` using `fun y => g_kills_tr p.D χ p.cont hD hh hn y`. Use `⟨hpolar, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : y ∈ p.D.toDet.ker` using `(d_ker p.D.toDet y).1.2 ((d_toDet p.D y).2.2.2.2 hy)`. Conclude with `(d_toDet p.D _).2.2.2.1 ((d_ker p.D.toDet _).1.1 (hker (pk_surj F O R n) y hy'))`.

Introduce `z hz`. Rewrite `hz`, the goal using `[← d_toDet_CH]`. Conclude with `hCH z hz`. Introduce `v g`. Conclude with `(hK _).2 (p.Ord v g)`.

Introduce `u g hg`. Conclude with `(hK _).2 (p.I u g hg)`.
-/
theorem UpperTheory.V.CA.pair_kills :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R), PhiCond F.G₀ l → 1 ≤ n → F.IsPolar O p.D ∧ (∀ y, p.D.Kills y → p.D.Kills (F.star O R n y)) ∧ (∀ z ∈ TwoSidedIdeal.span p.D.CH, F.star O R n z ∈ TwoSidedIdeal.span p.D.CH) ∧ (∀ v g, p.D.Kills (F.oEl v (p.ψ v) g)) ∧ ∀ u, ∀ g ∈ r.Ip u, p.D.Kills (MonoidAlgebra.single g 1 - 1) := by
  intro l _ F O _ _ _ _ _ _ _ n r R _ _ _ p hphi hn
  have hspan : Submodule.span R (↑(MonoidHom.mrange (MonoidAlgebra.of R F.G₀)) : Set (MonoidAlgebra R F.G₀)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | single g a =>
      have hs : MonoidAlgebra.single g a = a • MonoidAlgebra.of R F.G₀ g := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
      rw [hs]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of R F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      p.D.toDet.lam i (MulOpposite.unop (F.starOp O R n x)) = p.D.toDet.lam i x := by
    rintro x ⟨g, rfl⟩ i _ _
    rw [(d_toDet p.D _).2.1, (d_toDet p.D _).2.1, MonoidAlgebra.of_apply]
    exact p.P i g
  obtain ⟨hpull, hCH, hker⟩ := d_star p.D.toDet (F.starOp O R n) _ hspan hlam
  have hpolar : F.IsPolar O p.D := by
    intro B _ _ _ _ y
    have h1 := congrArg (fun X : Det n R (MonoidAlgebra R F.G₀) => X.D B (toT R F.G₀ B y)) hpull
    change p.D.D B (ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y)))) =
      p.D.D B (ofT R F.G₀ B (toT R F.G₀ B y)) at h1
    rw [pk_bc, ofT_toT] at h1
    exact h1
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have he : Function.Injective (ResidueField.map (algebraMap O R)) := (resMap_bijective O R).1
  haveI : Finite (ResidueField R) := Finite.of_surjective _ (resMap_bijective O R).2
  haveI : CharP (ResidueField R) l := charP_of_injective_ringHom he l
  let χ : Fin n → F.G₀ →* (ResidueField R)ˣ := fun i =>
    (Units.map (ResidueField.map (algebraMap O R) : ResidueField O →* ResidueField R)).comp (r.chib i)
  have hres : (ResidueField.map (algebraMap O R)).comp (res O R : R →+* ResidueField O) = residue R := by
    ext x
    show ResidueField.map (algebraMap O R) ((RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R x)) =
      residue R x
    exact (RingEquiv.ofBijective _ (resMap_bijective O R)).apply_symm_apply _
  have hD : p.D.map (residue R) = GDet.ofChars χ := by
    rw [← hres, ← (d_gmap p.D).2.1, p.red, Resid.Dbar, (d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2, GDet.ofChars]
    congr 1
    ext g i j
    by_cases hij : i = j
    · subst hij
      simp [χ, diagRep, GDet.diagRep]
    · simp [χ, diagRep, GDet.diagRep, Matrix.diagonal_apply_ne _ hij]
  have hopen : ∀ i, IsOpen (↑(χ i).ker : Set F.G₀) := by
    intro i
    have hk : (χ i).ker = (r.chib i).ker := by
      ext g
      simp only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply]
      constructor
      · intro h
        apply Units.ext
        apply he
        have h2 := congrArg Units.val h
        simpa using h2
      · intro h
        rw [h, map_one]
    rw [hk]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    apply r.chib_inj
    ext g
    apply he
    have h2 := congrArg (fun f : F.G₀ →* (ResidueField R)ˣ => ((f g : (ResidueField R)ˣ) : ResidueField R))
      hij
    simpa [χ] using h2
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hphi hopen hinj
  have hK : ∀ y, p.D.Kills y ↔ ∀ g : F.G₀, p.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    fun y => g_kills_tr p.D χ p.cont hD hh hn y
  refine ⟨hpolar, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ p.D.toDet.ker := (d_ker p.D.toDet y).1.2 ((d_toDet p.D y).2.2.2.2 hy)
    exact (d_toDet p.D _).2.2.2.1 ((d_ker p.D.toDet _).1.1 (hker (pk_surj F O R n) y hy'))
  · intro z hz
    rw [← d_toDet_CH] at hz ⊢
    exact hCH z hz
  · intro v g
    exact (hK _).2 (p.Ord v g)
  · intro u g hg
    exact (hK _).2 (p.I u g hg)
