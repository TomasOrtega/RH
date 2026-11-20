import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsBoxSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparatedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique

/- English proof (translation)
The claim follows from `| 0 => inferInstanceAs (IsProper (𝟙 S)) | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A hA n).proper`.
-/
theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A hA n).proper

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `q hq`. Set `y : (Out.powObj A 0).left` to `IsLocalRing.closedPoint K`.

Use `choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)`. Use `hq y J hJ` as an intermediate fact. Rewrite `this` using `[Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero]`. Conclude with `funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this`. Consider the case `succ n ih`.

Introduce `q hq`. Use `haveI := hA.proper`. Use `haveI := isProper_powObj A hA n`. Use `choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K)) (fun _ _ => b i)`. Use `choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))`.

Establish `H` using `(GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m) (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by`. Establish `hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i)` using `Set.mem_iInter.2 fun _ => hy`. Use `congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))` as an intermediate fact. Use `Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))` and prove the remaining obligations. Use `(gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations.

Use `(gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)` and prove the remaining obligations. Use `congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_` and prove the remaining obligations. Rewrite using `[ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])`. Use the proof step `(fun z J hJ => by`. Use `Eq.trans ?_ (hq z J hJ)` and prove the remaining obligations.

Rewrite using `[← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `(congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]`. Use the proof step `rfl)`. Use function extensionality and compare the values at `I`. Use `ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by` as an intermediate fact. Establish `h1` using `hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)`.

Establish `h0` using `h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))`. Simplify `h0)` using `only [Category.id_comp]`. Establish `h2` using `congrFun this (Fin.tail I)`. Rewrite `h2` using `[Fin.cons_self_tail]`. Then use the resulting hypothesis.
-/
theorem box_indep {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) {m : ℤ} {N : ℕ} (b : Fin N → LB.Sec (pw L m))
    (hb : ∀ c : Fin N → K, (∀ i, ∑ k, cst A.hom (L.U i) (c k) * (show Γ(A.left, L.U i) from (b k).f i) = 0) → c = 0) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → K), (∀ (y : (Out.powObj A n).left) J, Good L y J →
      ∑ I, kv (Out.powObj A n).hom y (q I) * ∏ c, gs (Out.powPr A c).left y (L.U (J (Out.powPr A c).left))
        ((b (I c)).f (J (Out.powPr A c).left)) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    let y : (Out.powObj A 0).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)
    have := hq y J hJ
    rw [Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero] at this
    exact funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this
  | succ n ih =>
    intro q hq
    haveI := hA.proper
    haveI := isProper_powObj A hA n
    choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K))
      (fun _ _ => b i)
    choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom
      (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))
    have H := (GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m)
      (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by
        have hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i) :=
          Set.mem_iInter.2 fun _ => hy
        have := congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))
        refine Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans
          ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))
        refine (gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)
        refine congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_
        rw [ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])
      (fun z J hJ => by
        refine Eq.trans ?_ (hq z J hJ)
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_
        rw [Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]
        rfl)
    funext I
    have := ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by
      have h1 := hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)
      have h0 := h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans
        (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))
      simpa only [Category.id_comp] using h0)
    have h2 := congrFun this (Fin.tail I)
    rwa [Fin.cons_self_tail] at h2

/- English proof (translation)
Introduce `laws K _ x m al b b' B lam lam' hm hal hb hB ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hn, hQ, hlam⟩ ⟨ξ', mu', w', Q', rho', hne', hker', hmu', hw', hn', hQ', hlam'⟩`. Establish `inj : ∀ ζ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) → Function.Injective ζ`. Introduce `ζ h I I' e`. Assume the negation of the conclusion as `hI`. Take `⟨r, hr⟩` from `h I I' hI (IsLocalRing.closedPoint K)`.

Conclude with `hr (by rw [e])`. Take `⟨σ, rfl⟩` from `exists_perm laws.mulN x.P m al hm hal ξ ξ' (inj _ hne) (inj _ hne') hker hker'`. Establish `hL` using `x.P.isLB`. Establish `hmm : ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) (J), Good x.P.L z J → val mu' r z J = val mu r z J` using `by haveI := x.P.isAb.comm`. Conclude with `gen_unique hL (S₀ := Sp K) x.P.A.hom (eSec x.P.A) (Over.w η[x.P.A]) (laws.globalFns _ _ x.P.isAb).2 hmu' hmu (fun y J hJ => (hn' y J hJ).1.trans (hn y J hJ).1.symm)`.

Use `choose c hc using fun I => gen_ratio hL (Out.powObj x.P.A 4).hom (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2 (hw (σ I)) (hw' I)`. Establish `hr : ∀ I, (rho' I : K) = c I ^ (m ^ 2) * rho (σ I)`. Introduce `I`. Set `p : (𝟙_ (Over (Sp K))).left` to `IsLocalRing.closedPoint K`. Use `choose J hJ using fun χ : (𝟙_ (Over (Sp K))).left ⟶ x.P.A.left => exists_chart hL (χ p)`.

Establish `h1` using `(hn p J hJ).2 (σ I)`. Establish `h2` using `(hn' p J hJ).2 I`. Simplify using `only [hmm _ _ p J hJ] at h2`. Rewrite `h1`, `h2` using `[Units.val_mul, Units.val_pow_eq_pow_val, gs_cst _ _ p ⊤ trivial, Category.comp_id]`. Rewrite `h2` using `[hc I _ _ p J hJ, mul_pow, _root_.mul_assoc, h1, ← _root_.mul_assoc, Units.mul_left_inj, show eSec (Out.powObj x.P.A 4) ≫ (Out.powObj x.P.A 4).hom = (𝟙_ (Over (Sp K))).hom from Over.w η[Out.powObj x.P.A 4], ← map_pow, ← map_mul]`.

Conclude with `((kv _ p).injective h2).symm`. Establish `hind` using `box_indep x.P.A x.P.isAb hL b (fun c hc => by`. Take `⟨c₀, -, hu⟩` from `hb ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩`. Conclude with `(hu c fun i => (hc i).symm).trans (hu 0 fun i => (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm).symm) 4`. Establish `hq : ∀ I I', Q (σ I) I' = c I * ∑ d, Q' I d * (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d`.

Introduce `I I'`. Use `sub_eq_zero.1 (congrFun (hind (fun I' => Q (σ I) I' - c I * ∑ d, Q' I d * (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d) fun y J hJ => ?_) I')` and prove the remaining obligations. Establish `h1` using `(hQ (σ I) y J hJ).symm.trans (hQ' I y J hJ)`. Rewrite `h1` using `[hc I _ _ y J hJ, mul_comm (kv _ _ _), _root_.mul_assoc, Units.mul_right_inj]`. Simplify using `only [gs_cst _ _ y ⊤ trivial, Category.id_comp] at h1`.

Establish `h3 : ∀ (r : (Out.powObj x.P.A 4 ⟶ x.P.A)) k, gs r.left y (x.P.L.U (J r.left)) ((b' k).f (J r.left)) = ∑ k', kv (Out.powObj x.P.A 4).hom y (B.val k' k) * gs r.left y (x.P.L.U (J r.left)) ((b k').f (J r.left))`. Introduce `r k`. Use `(congrArg (gs r.left y (x.P.L.U (J r.left))) (hB k (J r.left))).trans ?_` and prove the remaining obligations. Use `(gs_sum' _ y _ (hJ _) _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)` and prove the remaining obligations. Rewrite using `[gs_mul _ y _ (hJ _), gs_cst _ _ y _ (hJ _), Over.w r]`.

Simplify using `only [h3] at h1`. Simplify using `only [map_sub, sub_mul, Finset.sum_sub_distrib, h1, map_mul, map_sum, Matrix.of_apply, map_prod, _root_.mul_assoc, ← Finset.mul_sum]`. Rewrite using `[sub_eq_zero]`. Use `congr 1`. Simplify using `only [Finset.sum_mul, _root_.mul_assoc]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]`. Simplify using `only [Finset.prod_mul_distrib]`. Establish `key` using `det_calc σ Q Q' _ c (fun I => rho I) (fun I => rho' I) (m ^ 2) hq hr`.

Rewrite `key` using `[← hlam, ← hlam', GlobalTheory.det_kroneckerPower, ← pow_mul]`. Establish `e : lam = lam' * (Matrix.GeneralLinearGroup.det B) ^ (8 * m ^ (3 * x.P.g + 2))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[key, Units.val_mul, Units.val_pow_eq_pow_val]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, _root_.mul_assoc, ← zpow_natCast, ← zpow_add]`. Simplify using the standard rewrite rules.
-/
theorem isSquareDetComparison_eq_mul_det_pow_of_basis_change : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b b' : Fin (m ^ x.P.g) → RR x m) (B : (Matrix (Fin (m ^ x.P.g)) (Fin (m ^ x.P.g)) K)ˣ) (lam lam' : Kˣ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ k, Coords x b (fun k' => B.val k' k) (b' k).f) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x m al b' lam' → lam' = lam * (Matrix.GeneralLinearGroup.det B) ^ (-8 * (m ^ (3 * x.P.g + 2) : ℕ) : ℤ) := by
  intro laws K _ x m al b b' B lam lam' hm hal hb hB
    ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hn, hQ, hlam⟩ ⟨ξ', mu', w', Q', rho', hne', hker', hmu', hw', hn', hQ', hlam'⟩
  have inj : ∀ ζ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x,
      (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) → Function.Injective ζ := by
    intro ζ h I I' e
    by_contra hI
    obtain ⟨r, hr⟩ := h I I' hI (IsLocalRing.closedPoint K)
    exact hr (by rw [e])
  obtain ⟨σ, rfl⟩ := exists_perm laws.mulN x.P m al hm hal ξ ξ' (inj _ hne) (inj _ hne') hker hker'
  have hL := x.P.isLB
  have hmm : ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) (J), Good x.P.L z J → val mu' r z J = val mu r z J := by
    haveI := x.P.isAb.comm
    exact gen_unique hL (S₀ := Sp K) x.P.A.hom (eSec x.P.A) (Over.w η[x.P.A]) (laws.globalFns _ _ x.P.isAb).2 hmu' hmu
      (fun y J hJ => (hn' y J hJ).1.trans (hn y J hJ).1.symm)
  choose c hc using fun I => gen_ratio hL (Out.powObj x.P.A 4).hom
    (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2 (hw (σ I)) (hw' I)
  have hr : ∀ I, (rho' I : K) = c I ^ (m ^ 2) * rho (σ I) := by
    intro I
    let p : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (𝟙_ (Over (Sp K))).left ⟶ x.P.A.left => exists_chart hL (χ p)
    have h1 := (hn p J hJ).2 (σ I)
    have h2 := (hn' p J hJ).2 I
    simp only [hmm _ _ p J hJ] at h2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, gs_cst _ _ p ⊤ trivial, Category.comp_id] at h1 h2
    rw [hc I _ _ p J hJ, mul_pow, _root_.mul_assoc, h1, ← _root_.mul_assoc, Units.mul_left_inj,
      show eSec (Out.powObj x.P.A 4) ≫ (Out.powObj x.P.A 4).hom = (𝟙_ (Over (Sp K))).hom from Over.w η[Out.powObj x.P.A 4],
      ← map_pow, ← map_mul] at h2
    exact ((kv _ p).injective h2).symm
  have hind := box_indep x.P.A x.P.isAb hL b (fun c hc => by
    obtain ⟨c₀, -, hu⟩ := hb ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩
    exact (hu c fun i => (hc i).symm).trans (hu 0 fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm).symm) 4
  have hq : ∀ I I', Q (σ I) I' = c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d := by
    intro I I'
    refine sub_eq_zero.1 (congrFun (hind (fun I' => Q (σ I) I' - c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d) fun y J hJ => ?_) I')
    have h1 := (hQ (σ I) y J hJ).symm.trans (hQ' I y J hJ)
    rw [hc I _ _ y J hJ, mul_comm (kv _ _ _), _root_.mul_assoc, Units.mul_right_inj] at h1
    simp only [gs_cst _ _ y ⊤ trivial, Category.id_comp] at h1
    have h3 : ∀ (r : (Out.powObj x.P.A 4 ⟶ x.P.A)) k, gs r.left y (x.P.L.U (J r.left)) ((b' k).f (J r.left)) =
        ∑ k', kv (Out.powObj x.P.A 4).hom y (B.val k' k) * gs r.left y (x.P.L.U (J r.left)) ((b k').f (J r.left)) := by
      intro r k
      refine (congrArg (gs r.left y (x.P.L.U (J r.left))) (hB k (J r.left))).trans ?_
      refine (gs_sum' _ y _ (hJ _) _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
      rw [gs_mul _ y _ (hJ _), gs_cst _ _ y _ (hJ _), Over.w r]
    simp only [h3] at h1
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, h1, map_mul, map_sum, Matrix.of_apply, map_prod,
      _root_.mul_assoc, ← Finset.mul_sum]
    rw [sub_eq_zero]
    congr 1
    simp only [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have key := det_calc σ Q Q' _ c (fun I => rho I) (fun I => rho' I) (m ^ 2) hq hr
  rw [← hlam, ← hlam', GlobalTheory.det_kroneckerPower, ← pow_mul] at key
  have e : lam = lam' * (Matrix.GeneralLinearGroup.det B) ^ (8 * m ^ (3 * x.P.g + 2)) := by
    apply Units.ext
    rw [key, Units.val_mul, Units.val_pow_eq_pow_val]
    congr 2
    ring
  rw [e, _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
  simp

end GlobalTheory.BoxDetUnique
end
