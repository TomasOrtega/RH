import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CardHomVanishingOfDiagBasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetKroneckerPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]

def kv (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def gsH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

/- English proof (translation)
The claim follows from `gs_eq f y U h a`.
-/
theorem gs_eqH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) : gs f y U a = gsH f y U h a :=
  gs_eq f y U h a

/- English proof (translation)
Simplify using `only [gs_eqH f y U h, map_sum]`.
-/
theorem gs_sum' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eqH f y U h, map_sum]

/- English proof (translation)
Simplify using `only [gs_eqH f y U h, map_prod]`.
-/
theorem gs_prod' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∏ i ∈ s, a i) = ∏ i ∈ s, gs f y U (a i) := by
  simp only [gs_eqH f y U h, map_prod]

/- English proof (translation)
Simplify using `only [gs_eqH f y U h, map_zero]`.
-/
theorem gs_zero' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eqH f y U h, map_zero]

/- English proof (translation)
The claim follows from `(gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))`.
-/
theorem gs_cst (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (cst p U a) = kv (r ≫ p) z a :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))

/- English proof (translation)
Take `⟨t, -, hv⟩` from `exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)` and prove the remaining obligations. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])`. Use the proof step `(LB.mulGen M _ _ _ _ u' (LB.invGen M _ _ u)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))`. Establish `le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`.

Take `⟨a, ha⟩` from `hp (res le (t.s PEmpty.elim)).val`. Take `⟨c, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a`. Use `⟨c, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `key : (val u' r z J * (val u r z J)⁻¹).val = kv (r ≫ p) z c`. Rewrite using `[← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]`.

Conclude with `(congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))))`. Rewrite using `[← key, ← Units.val_mul, inv_mul_cancel_right]`.
-/
theorem gen_ratio {K : Type} [Field K] {M : LB X} (hM : M.IsLB) {N : Type} [Fintype N] {φ : N → (Y ⟶ X)} {ε : N → ℤ}
    (p : Y ⟶ Sp K) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u' r z J).val = kv (r ≫ p) z c * (val u r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u' (LB.invGen M _ _ u)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u' r z J * (val u r z J)⁻¹).val = kv (r ≫ p) z c := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

/- English proof (translation)
Establish `hm : r z ∈ L.U i ⊓ L.U j` using `⟨hi, hj⟩`. Use `(gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))` and prove the remaining obligations. Conclude with `(gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))`.
-/
theorem gs_sec_pw {L : LB X} {m : ℤ} (s : LB.Sec (pw L m)) (r : Z ⟶ X) (z : Z) (i j : L.ι) (hi : r z ∈ L.U i)
    (hj : r z ∈ L.U j) :
    gs r z (L.U i) (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j) ^ m).val * gs r z (L.U j) (s.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j → gs r z (LB.wchart L φ j) (F j) = ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by`. Use `⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))), fun Z r z j h => ?_⟩` and prove the remaining obligations. Rewrite using `[gs_sum' r z _ h]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]`.

Use `congrArg _ (Finset.prod_congr rfl fun c _ => ?_)` and prove the remaining obligations. Conclude with `(gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)`. Use `⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩` and prove the remaining obligations. Use `(gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)` and prove the remaining obligations. Use `(hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]`. Use `congrArg _ (Finset.prod_congr rfl fun c _ => ?_)` and prove the remaining obligations. Conclude with `gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)`.
-/
theorem exists_boxSec {L : LB X} {m : ℤ} {N I : Type} [Fintype N] [Fintype I] (φ : N → (Y ⟶ X)) (p : Y ⟶ Sp R)
    (q : I → R) (s : I → N → LB.Sec (pw L m)) : ∃ S : LB.Sec (LB.LinComb L φ (fun _ => m)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (S.f j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
  obtain ⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (F j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
    refine ⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))),
      fun Z r z j h => ?_⟩
    rw [gs_sum' r z _ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]
    refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
    exact (gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)
  refine ⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
  exact gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)

/- English proof (translation)
Use `haveI := P.isAb.comm`. Set `k` to `AlgebraicClosure K`. Set `t : Spec (CommRingCat.of k) ⟶ Sp K` to `Spec.map (CommRingCat.ofHom (algebraMap K k))`. Establish `hm1 : 1 ≤ m` using `Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])`. Establish `hc` using `GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by`.

Establish `hn0 : (n : K) ≠ 0` using `fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])`. Use `(hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap K k)]`. Conclude with `(map_ne_zero _).2 hn0)`. Establish `hepi : Epi t` using `by haveI : Flat t := by`.

Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Use `haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective t`. Set `f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A)` to `preHom (toUnit (Over.mk t))`.

Establish `hf : Function.Injective f` using `fun a b hab => by`. Establish `h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left` using `congrArg (·.left) hab`. Establish `h2 : (toUnit (Over.mk t)).left = t` using `(Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))`. Use `haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi`. Conclude with `Over.OverMorphism.ext ((cancel_epi _).1 h1)`.

Establish `bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ → (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) → ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1}, ∀ I r, (E I).1 r = f …`. Introduce `ζ hζ he`. Set `g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1}` to `fun I => ⟨fun r => f (ζ I r), fun c => by`. Use `congrArg f (he I c)` as an intermediate fact. Rewrite `this` using `[List.prod_ofFn, map_prod, map_one]`.

Simplify `this⟩` using `only [map_zpow]`. Establish `hg : Function.Injective g` using `fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))`. Use `haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)`. Use `⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩` and prove the remaining obligations. Rewrite using `[hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]`.

Conclude with `le_of_eq (by congr 1; ring)`. Take `⟨E, hE⟩` from `bij ξ h e`. Take `⟨E', hE'⟩` from `bij ξ' h' e'`. Use `⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩` and prove the remaining obligations. Rewrite using `[← hE, ← hE']`.

Simplify using the standard rewrite rules.
-/
theorem exists_perm (hN : Out.MulNSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hm : (m : K) ≠ 0) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (ξ ξ' : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A))
    (h : Function.Injective ξ) (h' : Function.Injective ξ')
    (e : ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1)
    (e' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1) :
    ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ P.g)), ξ' = fun I => ξ (σ I) := by
  haveI := P.isAb.comm
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp K := Spec.map (CommRingCat.ofHom (algebraMap K k))
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])
  have hc := GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by
    have hn0 : (n : K) ≠ 0 := fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])
    refine (hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_
    rw [← map_natCast (algebraMap K k)]
    exact (map_ne_zero _).2 hn0)
  have hepi : Epi t := by
    haveI : Flat t := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective t
  let f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) := preHom (toUnit (Over.mk t))
  have hf : Function.Injective f := fun a b hab => by
    have h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left := congrArg (·.left) hab
    have h2 : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
    haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi
    exact Over.OverMorphism.ext ((cancel_epi _).1 h1)
  have bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ →
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) →
      ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1},
        ∀ I r, (E I).1 r = f (ζ I r) := by
    intro ζ hζ he
    let g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      fun I => ⟨fun r => f (ζ I r), fun c => by
        have := congrArg f (he I c)
        rw [List.prod_ofFn, map_prod, map_one] at this
        simpa only [map_zpow] using this⟩
    have hg : Function.Injective g := fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))
    haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    refine ⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩
    rw [hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨E, hE⟩ := bij ξ h e
  obtain ⟨E', hE'⟩ := bij ξ' h' e'
  refine ⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩
  rw [← hE, ← hE']
  simp

/- English proof (translation)
Establish `h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose)`. Use extensionality with `a b`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_apply]`. Conclude with `hQ a b`. Establish `h2` using `congrArg Matrix.det h1`.

Rewrite `h2` using `[Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Establish `h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2`. Rewrite using `[← h2, mul_pow]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Establish `h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2`.

Rewrite using `[← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun a _ => by rw [hr]; ring`. Rewrite using `[h4, pow_mul, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_calc {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (Q Q' T : Matrix I I K)
    (c rho rho' : I → K) (n : ℕ) (hQ : ∀ a b, Q (σ a) b = c a * ∑ d, Q' a d * T b d)
    (hr : ∀ a, rho' a = c a ^ n * rho (σ a)) :
    Q.det ^ (2 * n) * ∏ a, rho a ^ 2 = (Q'.det ^ (2 * n) * ∏ a, rho' a ^ 2) * T.det ^ (2 * n) := by
  have h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose) := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    exact hQ a b
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2 := by
    rw [← h2, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2 := by
    rw [← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by rw [hr]; ring
  rw [h4, pow_mul, h3]
  ring

end GlobalTheory.BoxDetUnique
end
