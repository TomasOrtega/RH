import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

/- English proof (translation)
Set `Q : Submonoid S` to `Algebra.algebraMapSubmonoid S p.primeCompl`. Set `T` to `Localization Q`. Use `letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S`. Use `haveI : Module.Finite (Localization.AtPrime p) T := Module.Finite.of_isLocalization R S p.primeCompl`. Use `haveI : Finite (MaximalSpectrum T) := GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T`.

Take `⟨z, hz⟩` from `GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)`. Proceed by induction on `z using LocalizedModule.induction_on with`. Consider the case `h m s`. Establish `hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m}`. Introduce `x`.

Take `⟨c, hc⟩` from `hz.2 (LocalizedModule.mk x 1)`. Proceed by induction on `c using Localization.induction_on with`. Consider the case `H c`. Take `⟨a, t⟩` from `c`. Rewrite `hc` using `[LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]`.

Take `⟨u, hu⟩` from `hc`. Use `⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul]`. Establish `hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m` using `hu.symm`. Rewrite `hu'` using `[Submonoid.coe_mul]`.

Rewrite `hu'` using `[mul_smul]`. Rewrite using `[hu', Submodule.mem_span_singleton]`. Conclude with `⟨(u : S) * a, by simp [mul_smul]⟩`. Use `choose q hqQ hq using hloc`. Take `⟨F, hF⟩` from `Module.Finite.fg_top (R := S) (M := M)`.

Set `q₀ : S` to `∏ x ∈ F, q x`. Establish `hq₀ : q₀ ∈ Q` using `Q.prod_mem fun x _ => hqQ x`. Establish `key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m}`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx`. Establish `: q₀ = (∏ x' ∈ F.erase x, q x') * q x` using `(Finset.prod_erase_mul F q hx).symm`. Rewrite using `[this, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hq x)`. Consider the case `zero => rw [smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul a y _ h => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ h`.

Take `⟨r, hr, hrq⟩` from `hq₀`. Use `⟨r, hr, m, fun x => ?_⟩` and prove the remaining obligations. Use `key x (hF ▸ Submodule.mem_top)` as an intermediate fact. Rewrite `this` using `[Submodule.mem_span_singleton]`. Take `⟨a, ha⟩` from `this`.

Conclude with `⟨a, by rw [hrq]; exact ha.symm⟩`.
-/
theorem exists_smul_mem_span_away {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module S M] [Module.Invertible S M]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ m : M, ∀ x : M, ∃ a : S, algebraMap R S r • x = a • m := by
  classical
  let Q : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization Q
  letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S
  haveI : Module.Finite (Localization.AtPrime p) T :=
    Module.Finite.of_isLocalization R S p.primeCompl
  haveI : Finite (MaximalSpectrum T) :=
    GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T
  obtain ⟨z, hz⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)
  induction z using LocalizedModule.induction_on with
  | h m s =>
  have hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m} := by
    intro x
    obtain ⟨c, hc⟩ := hz.2 (LocalizedModule.mk x 1)
    induction c using Localization.induction_on with
    | H c =>
    obtain ⟨a, t⟩ := c
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩
    rw [mul_smul, mul_smul]
    have hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m := hu.symm
    rw [Submonoid.coe_mul] at hu'
    rw [mul_smul] at hu'
    rw [hu', Submodule.mem_span_singleton]
    exact ⟨(u : S) * a, by simp [mul_smul]⟩
  choose q hqQ hq using hloc
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := S) (M := M)
  let q₀ : S := ∏ x ∈ F, q x
  have hq₀ : q₀ ∈ Q := Q.prod_mem fun x _ => hqQ x
  have key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have : q₀ = (∏ x' ∈ F.erase x, q x') * q x := (Finset.prod_erase_mul F q hx).symm
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (hq x)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  obtain ⟨r, hr, hrq⟩ := hq₀
  refine ⟨r, hr, m, fun x => ?_⟩
  have := key x (hF ▸ Submodule.mem_top)
  rw [Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [hrq]; exact ha.symm⟩

/- English proof (translation)
Use `haveI := GlobalTheory.LB.isQuasicoherent_toMod hL`. Establish `hD : IsAffineOpen (X.basicOpen h)` using `hU.basicOpen h`. Use `haveI := GlobalTheory.LB.invertible_sections hL hD`. Rewrite using `[GlobalTheory.LB.isFrame_iff_bijective hD]`. Establish `h₁` using `((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1 (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1`.

Use `Module.Invertible.bijective_of_surjective (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _ ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_` and prove the remaining obligations. Introduce `s`. Take `⟨n, t, ht⟩` from `h₁ s`. Take `⟨a, ha⟩` from `hm t`. Take `⟨u, hu⟩` from `GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl`.

Establish `e1` using `GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t`. Rewrite `e1` using `[ha, GlobalTheory.LB.map_smul_resG]`. Use `⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) * resG X (X.basicOpen_le h) a, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[← hu]`. Establish `hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h))` using `hu.symm`.

Rewrite `e1` using `[hu', ← ht, ← mul_smul]`. Rewrite using `[LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow, Units.inv_mul, one_pow, one_smul]`.
-/
theorem isFrame_res_of_smul_mem {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {U : X.Opens}
    (hU : IsAffineOpen U) (h : Γ(X, U)) (m : Γ(GlobalTheory.LB.toMod L, U))
    (hm : ∀ x : Γ(GlobalTheory.LB.toMod L, U), ∃ a : Γ(X, U), h • x = a • m) :
    GlobalTheory.LB.IsFrame ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m) := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hD : IsAffineOpen (X.basicOpen h) := hU.basicOpen h
  haveI := GlobalTheory.LB.invertible_sections hL hD
  rw [GlobalTheory.LB.isFrame_iff_bijective hD]
  have h₁ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1
  refine Module.Invertible.bijective_of_surjective
    (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _
      ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_
  intro s
  obtain ⟨n, t, ht⟩ := h₁ s
  obtain ⟨a, ha⟩ := hm t
  obtain ⟨u, hu⟩ := GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl
  have e1 := GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t
  rw [ha, GlobalTheory.LB.map_smul_resG] at e1
  refine ⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) *
    resG X (X.basicOpen_le h) a, ?_⟩
  rw [← hu] at ht
  have hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h)) := hu.symm
  rw [hu', ← ht, ← mul_smul] at e1
  rw [LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

/- English proof (translation)
Introduce `X Y f _ L hL y`. Take `⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (show y ∈ (⊤ : Y.Opens) from trivial)`. Set `p : Ideal Γ(Y, W)` to `(IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom`. Use `letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra`. Use `haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW`.

Establish `hW : IsAffineOpen W` using `hW`. Establish `hU : IsAffineOpen (f ⁻¹ᵁ W)` using `hW.preimage f`. Use `haveI := GlobalTheory.LB.invertible_sections hL hU`. Take `⟨r, hr, m, hm⟩` from `exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W)) (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p`. Establish `he` using `isFrame_res_of_smul_mem hL hU (f.app W r) m hm`.

Establish `hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r)` using `Scheme.preimage_basicOpen f r`. Use `⟨Y.basicOpen r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.mem_basicOpen (x := y) (hx := hyW)]`. Assume the negation of the conclusion as `hn`. Conclude with `hr ((IsLocalRing.mem_maximalIdeal _).2 hn)`.

Set `F` to `GlobalTheory.LB.toMod L`. Set `e : Γ(F, f ⁻¹ᵁ Y.basicOpen r)` to `F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)`. Establish `he' : GlobalTheory.LB.IsFrame e` using `he.map hpre.le`. Set `u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ` to `fun i => (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left`. Establish `hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) = GlobalTheory.LB.coord e i` using `fun i => by`.

Rewrite using `[GlobalTheory.LB.IsFrame.val_unit, GlobalTheory.LB.repr_chartSec, GlobalTheory.LB.chartEquiv_apply, GlobalTheory.LB.coord_map, GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_self]`. Use `⟨u, fun i j x hxV hi hj => ?_⟩` and prove the remaining obligations. Establish `hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j` using `⟨⟨hxV, hi⟩, hj⟩`. Rewrite using `[← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO, ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO, ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right …`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]`. Conclude with `GlobalTheory.LB.coord_rel e i j _ _ _`.
-/
theorem exists_trivial_near_fibre : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB →
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  intro X Y f _ L hL y
  obtain ⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let p : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  haveI := GlobalTheory.LB.invertible_sections hL hU
  obtain ⟨r, hr, m, hm⟩ := exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W))
    (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p
  have he := isFrame_res_of_smul_mem hL hU (f.app W r) m hm
  have hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r) := Scheme.preimage_basicOpen f r
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen (x := y) (hx := hyW)]
    by_contra hn
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 hn)
  let F := GlobalTheory.LB.toMod L
  let e : Γ(F, f ⁻¹ᵁ Y.basicOpen r) :=
    F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)
  have he' : GlobalTheory.LB.IsFrame e := he.map hpre.le
  let u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ := fun i =>
    (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left
  have hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) =
      GlobalTheory.LB.coord e i := fun i => by
    rw [GlobalTheory.LB.IsFrame.val_unit, GlobalTheory.LB.repr_chartSec, GlobalTheory.LB.chartEquiv_apply, GlobalTheory.LB.coord_map,
      GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_self]
  refine ⟨u, fun i j x hxV hi hj => ?_⟩
  have hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j := ⟨⟨hxV, hi⟩, hj⟩
  rw [← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U j) hxO, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]
  exact GlobalTheory.LB.coord_rel e i j _ _ _

end GlobalTheory.LBDescent
