import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClass
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace GlobalTheory.EndDivisible

/- English proof (translation)
Take `⟨M, hM, rfl⟩` from `cls_surj c`. Take `⟨Q⟩` from `GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy K X f hf hp M hM`. Use `⟨Q.a + 1, fun B hB hc σ => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `(cls_eq_iff hB hM).1 hc`. Set `e : LB.Sec B ≃ₗ[Γ(X, ⊤)] LB.Sec M` to `(GlobalTheory.AbLaw.SecOn.topEquiv B).symm ≪≫ₗ GlobalTheory.AbLaw.SecOn.congr hB hM w hw ⊤ ≪≫ₗ GlobalTheory.AbLaw.SecOn.topEquiv M`.

Take `⟨a, ha, h⟩` from `Q.exists_relation (fun k => e (σ k))`. Set `a' : Fin (Q.a + 1) → Γ(X, ⊤)` to `fun k => f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a k))`. Establish `ev : ∀ (N : LB X) (τ : Fin (Q.a + 1) → LB.Sec N) (i : N.ι), (∑ k, a' k • τ k).f i = ∑ k, GlobalTheory.AbLaw.cst f (N.U i) (a k) * (τ k).f i` using `fun N τ i => by`. Set `F : LB.Sec N →+ Γ(X, N.U i)` to `AddMonoidHom.mk' (fun s => s.f i) (fun _ _ => rfl)`. Conclude with `map_sum F _ _`.

Establish `h1 : ∑ k, a' k • e (σ k) = 0` using `GlobalTheory.AbLaw.HighTwist.sec_eq_zero _ fun i => (ev M _ i).trans (h i)`. Establish `h2 : ∑ k, a' k • σ k = 0`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero, ← h1]`. Conclude with `Finset.sum_congr rfl fun k _ => e.map_smul _ _`.

Conclude with `⟨a, ha, fun i => (ev B σ i).symm.trans (by rw [h2]; rfl)⟩`.
-/
theorem exists_relation_of_cls (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (hf : Smooth f)
    (hp : GlobalTheory.AbLaw.IsProjBy f) (c : Pic X) :
    ∃ n : ℕ, ∀ (B : LB X) (hB : B.IsLB), cls B hB = c → ∀ σ : Fin n → LB.Sec B,
      ∃ a : Fin n → K, a ≠ 0 ∧ ∀ i, ∑ k, GlobalTheory.AbLaw.cst f (B.U i) (a k) * (σ k).f i = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨Q⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy K X f hf hp M hM
  refine ⟨Q.a + 1, fun B hB hc σ => ?_⟩
  obtain ⟨w, hw⟩ := (cls_eq_iff hB hM).1 hc
  let e : LB.Sec B ≃ₗ[Γ(X, ⊤)] LB.Sec M :=
    (GlobalTheory.AbLaw.SecOn.topEquiv B).symm ≪≫ₗ GlobalTheory.AbLaw.SecOn.congr hB hM w hw ⊤ ≪≫ₗ GlobalTheory.AbLaw.SecOn.topEquiv M
  obtain ⟨a, ha, h⟩ := Q.exists_relation (fun k => e (σ k))
  let a' : Fin (Q.a + 1) → Γ(X, ⊤) := fun k =>
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a k))
  have ev : ∀ (N : LB X) (τ : Fin (Q.a + 1) → LB.Sec N) (i : N.ι),
      (∑ k, a' k • τ k).f i = ∑ k, GlobalTheory.AbLaw.cst f (N.U i) (a k) * (τ k).f i := fun N τ i => by
    let F : LB.Sec N →+ Γ(X, N.U i) := AddMonoidHom.mk' (fun s => s.f i) (fun _ _ => rfl)
    exact map_sum F _ _
  have h1 : ∑ k, a' k • e (σ k) = 0 :=
    GlobalTheory.AbLaw.HighTwist.sec_eq_zero _ fun i => (ev M _ i).trans (h i)
  have h2 : ∑ k, a' k • σ k = 0 := by
    apply e.injective
    rw [map_sum, map_zero, ← h1]
    exact Finset.sum_congr rfl fun k _ => e.map_smul _ _
  exact ⟨a, ha, fun i => (ev B σ i).symm.trans (by rw [h2]; rfl)⟩

/- English proof (translation)
Proceed by induction on `N, hN using Nat.le_induction with`. Consider the case `base => rwa [one_nsmul]`. Consider the case `succ n _ ih => rw [succ_nsmul]`. Conclude with `GlobalTheory.EffBound.eff_add _ _ ih hc`.
-/
theorem eff_nsmul_of_pos {X : Scheme.{0}} [IsIntegral X] (c : Pic X) (hc : GlobalTheory.EffBound.Eff c) (N : ℕ)
    (hN : 1 ≤ N) : GlobalTheory.EffBound.Eff (N • c) := by
  induction N, hN using Nat.le_induction with
  | base => rwa [one_nsmul]
  | succ n _ ih => rw [succ_nsmul]; exact GlobalTheory.EffBound.eff_add _ _ ih hc

/- English proof (translation)
Establish `hF : FormEq (K` using `(Fin a ⊕ Fin (t - a)) × Fin N) (fun _ => f ≫ w) (fun _ => 1) (fun _ : Unit => u) (fun _ => ((N * t : ℕ) : ℤ)) := by`. Introduce `U _ h`. Rewrite using `[hu]`. Simplify using `only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha, zpow_natCast]`. Rewrite using `[mul_comm]`.

Take `⟨σ, hσ⟩` from `exists_sec hL hF (pullSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f)`. Use `⟨σ, (hσ _ _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩` and prove the remaining obligations. Rewrite using `[sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]`. Simplify using the standard rewrite rules.
-/
theorem exists_pull_monomial {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (t : ℕ)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) (a : ℕ) (ha : a ≤ t) :
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => ((N * t : ℕ) : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) := by
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N) (fun _ => f ≫ w) (fun _ => 1)
      (fun _ : Unit => u) (fun _ => ((N * t : ℕ) : ℤ)) := by
    intro U _ h
    rw [hu]
    simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha, zpow_natCast]
    rw [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

/- English proof (translation)
Introduce `K _ _ A _ hA L hL hamp m`. Use `hA.proper` as an intermediate fact. Establish `: GeometricallyIntegral A.hom` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected`. Establish `: IsIntegral A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton A.hom`. Establish `: A.left.IsSeparated` using `⟨by`.

Rewrite using `[← terminal.comp_from A.hom]`. Use the proof step `infer_instance⟩`. Establish `hproj : GlobalTheory.AbLaw.IsProjBy A.hom`. Take `⟨d, -, n, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp`. Conclude with `⟨_, GlobalTheory.AbLaw.isLB_pw hL d, n, s, hs⟩`.

Set `E` to `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv`. Establish `hk : IsField Γ(Spec (CommRingCat.of K), ⊤)` using `E.toMulEquiv.isField (Field.toIsField K)`. Take `⟨N, hN, M, s, hcov, hs⟩` from `hamp ⊤ (isAffineOpen_top _)`. Take `⟨n, hn⟩` from `exists_relation_of_cls K A.left A.hom hA.smooth hproj (N • m)`. Use `⟨n, fun t hnt ψ hψ heff => ?_⟩` and prove the remaining obligations.

Take `⟨P, hP, hPc, ε, p₀, hε⟩` from `eff_nsmul_of_pos _ heff N hN`. Establish `hQ` using `LB.isLB_linComb hL (K := Unit) (fun _ => ψ.left) (fun _ => ((N * t : ℕ) : ℤ))`. Establish `hT : cls _ (isLB_tens hP hQ) = N • m`. Rewrite using `[cls_tens hP hQ, hPc, cls_linComb hL, Fintype.sum_unique, natCast_zsmul, nsmul_sub, mul_nsmul', sub_add_cancel]`. Set `w` to `(A.hom ⁻¹ᵁ ⊤).ι`.

Set `f : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme` to `IsOpenImmersion.lift w ψ.left (by`. Introduce and unpack `_ -`. Rewrite using `[Scheme.Opens.range_ι]`. Use the proof step `trivial)`. Establish `hf : f ≫ w = ψ.left` using `IsOpenImmersion.lift_fac _ _ _`.

Take `⟨z⟩ : Nonempty A.left` from `inferInstance`. Take `⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i)` from `Opens.mem_iSup.1 (by rw [hcov]; trivial)`. Take `⟨hD, r, hr, hsurj⟩` from `hs i`. Take `⟨J, hJ⟩ : ∃ J, Good L z J` from `by choose I hI using fun χ : A.left ⟶ A.left => exists_chart hL (χ z)`. Conclude with `⟨I, hI⟩`.

Take `⟨p, hp⟩` from `exists_chart hP z`. Establish `hεz : gs (𝟙 _) z (P.U p) (ε.f p) ≠ 0`. Rewrite using `[gs_eq (𝟙 _) z (P.U p) hp]`. Conclude with `GlobalTheory.EffBound.germ_sec_ne_zero ε hε p z hp`. Set `κ` to `germPull A.hom z ⊤ trivial`.

Set `ρ` to `germPull f z _ hi`. Establish `hy : IsUnit (sval (s i) f z J)`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 hi`. Conclude with `isUnit_sval (s i) f z hJ k hk`. Establish `hrj : ∀ j, ρ (r j) ∈ κ.range` using `fun j => by`.

Establish `e : sval (s j) f z J = ρ (r j) * sval (s i) f z J`. Establish `hm` using `hJ.mem (K := Fin N) (fun _ => w) f`. Establish `hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U (fun _ => J (f ≫ w))` using `⟨hi, hm⟩`. Use `congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))` as an intermediate fact. Rewrite `this` using `[gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm']`.

Rewrite using `[germPull_apply]`. Conclude with `this`. Use `choose σ hσ using fun a : Fin n => exists_pull_monomial L hL w N (s i) (s j) t f ψ.left hf.symm z J hJ a (a.2.le.trans hnt)`. Take `⟨c, hc, h0⟩` from `hn _ _ hT (fun a => GlobalTheory.EffBound.tensSec ε (σ a))`. Establish `hm₂` using `hJ.mem (K := Unit) (fun _ => ψ.left) (𝟙 _)`.

Establish `hm : (𝟙 A.left : A.left ⟶ A.left) z ∈ P.U p ⊓ LB.wchart L (K` using `Unit) (fun _ => ψ.left) (fun _ => J (𝟙 _ ≫ ψ.left)) := ⟨hp, hm₂⟩`. Establish `h1` using `(map_sum _ _ _).symm.trans ((congrArg (germPull (𝟙 _) z _ hm) (h0 (p, fun _ => J (𝟙 _ ≫ ψ.left)))).trans (map_zero _))`. Establish `h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (c k) * ρ (r j) ^ (k : ℕ)) * (sval (s i) f z J ^ t * gs (𝟙 _) z (P.U p) (ε.f p)) = 0`. Rewrite using `[Finset.sum_mul, ← h1]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) A.hom z ⊤ _ le_top hm (E.symm (c k))) ((gs_mul (𝟙 _) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z inf_le_left hm _) ((gs_res (𝟙 _) z inf_le_right hm _).trans (hσ k))))).symm` and prove the remaining obligations. Establish `e₁ : (κ.comp E.symm.toRingHom) (c k) = gs (𝟙 _ ≫ A.hom) z ⊤ (E.symm (c k))`. Rewrite using `[Category.id_comp]`. Conclude with `germPull_apply _ _ _ _ _`.

Rewrite using `[e₁, e, mul_pow]`. Use `conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) c hc (ρ (r j)) ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero (hy.pow _).ne_zero hεz))`. Conclude with `⟨_, ha⟩`.

Establish `hall : ∀ a, ρ a ∈ κ.range` using `fun a => by`. Take `⟨p, rfl⟩` from `hsurj a`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[MvPolynomial.eval₂Hom_C]`.

Choose the witnesses or unpack the hypotheses as in `⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=`. Establish `: IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι` using `inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)`. Use the proof step `(ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c`. Use `⟨c', ?_⟩` and prove the remaining obligations. Use `(germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)` and prove the remaining obligations.

Use `Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))` and prove the remaining obligations. Rewrite using `[Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]`. Consider the case `add p p' h h' => rw [map_add, map_add]`. Conclude with `add_mem h h'`. Consider the case `mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']`.

Conclude with `mul_mem h (hrj j)`. Take `⟨p, hp⟩` from `exists_factor f w A.hom hk _ hD z hi (fun a => by`. Take `⟨c, hc⟩` from `hall a`. Conclude with `⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)`. Rewrite `hp` using `[hf]`.

Establish `h1 : η[A].left ≫ A.hom = 𝟙 _` using `Over.w η[A]`. Establish `h2 : η[A].left = p`. Use `congrArg (fun x => x.left) (IsMonHom.one_hom ψ)` as an intermediate fact. Simplify using `only [Over.comp_left] at this`. Rewrite using `[← this, hp, ← Category.assoc, h1]`.

Conclude with `Category.id_comp _`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hp, ← h2, Hom.one_def]`. Simplify using the standard rewrite rules.
-/
theorem constSt : ConstSt := by
  intro K _ _ A _ hA L hL hamp m
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]; infer_instance⟩
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
    exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL d, n, s, hs⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hamp ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := exists_relation_of_cls K A.left A.hom hA.smooth hproj (N • m)
  refine ⟨n, fun t hnt ψ hψ heff => ?_⟩
  obtain ⟨P, hP, hPc, ε, p₀, hε⟩ := eff_nsmul_of_pos _ heff N hN
  have hQ := LB.isLB_linComb hL (K := Unit) (fun _ => ψ.left) (fun _ => ((N * t : ℕ) : ℤ))
  have hT : cls _ (isLB_tens hP hQ) = N • m := by
    rw [cls_tens hP hQ, hPc, cls_linComb hL, Fintype.sum_unique, natCast_zsmul, nsmul_sub, mul_nsmul',
      sub_add_cancel]
  let w := (A.hom ⁻¹ᵁ ⊤).ι
  let f : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨z⟩ : Nonempty A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good L z J := by
    choose I hI using fun χ : A.left ⟶ A.left => exists_chart hL (χ z)
    exact ⟨I, hI⟩
  obtain ⟨p, hp⟩ := exists_chart hP z
  have hεz : gs (𝟙 _) z (P.U p) (ε.f p) ≠ 0 := by
    rw [gs_eq (𝟙 _) z (P.U p) hp]
    exact GlobalTheory.EffBound.germ_sec_ne_zero ε hε p z hp
  let κ := germPull A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    choose σ hσ using fun a : Fin n =>
      exists_pull_monomial L hL w N (s i) (s j) t f ψ.left hf.symm z J hJ a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn _ _ hT (fun a => GlobalTheory.EffBound.tensSec ε (σ a))
    have hm₂ := hJ.mem (K := Unit) (fun _ => ψ.left) (𝟙 _)
    have hm : (𝟙 A.left : A.left ⟶ A.left) z ∈ P.U p ⊓ LB.wchart L (K := Unit) (fun _ => ψ.left)
      (fun _ => J (𝟙 _ ≫ ψ.left)) := ⟨hp, hm₂⟩
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (p, fun _ => J (𝟙 _ ≫ ψ.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (c k) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ t * gs (𝟙 _) z (P.U p) (ε.f p)) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) A.hom z ⊤ _ le_top hm (E.symm (c k)))
        ((gs_mul (𝟙 _) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z inf_le_left hm _)
          ((gs_res (𝟙 _) z inf_le_right hm _).trans (hσ k))))).symm
      have e₁ : (κ.comp E.symm.toRingHom) (c k) = gs (𝟙 _ ≫ A.hom) z ⊤ (E.symm (c k)) := by
        rw [Category.id_comp]
        exact germPull_apply _ _ _ _ _
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) c hc (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero (hy.pow _).ne_zero hεz))
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add, map_add]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have h2 : η[A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  apply Over.OverMorphism.ext
  rw [hp, ← h2, Hom.one_def]
  simp

end GlobalTheory.AmpleRigid
