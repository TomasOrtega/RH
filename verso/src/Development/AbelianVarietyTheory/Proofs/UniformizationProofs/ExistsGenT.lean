import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.UU.IntGen

/- English proof (translation)
Take `⟨t, -, hv⟩` from `exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by`. Use `(Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)` and prove the remaining obligations. Use `h U f` as an intermediate fact. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, this, mul_inv_cancel])`. Use the proof step `(LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))`.

Establish `le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`. Use `⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val`. Rewrite using `[← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]`. Conclude with `(congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm)`.

Rewrite using `[← key, ← Units.val_mul, inv_mul_cancel_right]`.
-/
theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ a.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      have := h U f
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, this, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm)
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

/- English proof (translation)
Establish `e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left` using `congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))`. Establish `e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left` using `congrArg (fun q => q.left) (comp_cP D ρ α)`. Establish `e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left` using `congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)`. Rewrite using `[Fin.prod_univ_four, e₁, e₂, e₃]`. Use `show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _`.

Rewrite using `[zpow_one, zpow_one, zpow_neg_one]`. Both sides reduce to the same expression.
-/
theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def basePts (T : Over (Spec (CommRingCat.of R))) (α mu : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cP D T α * cP D T mu).left, (cP D T α).left, (cP D T mu).left, (1 : T ⟶ D.P.A).left]

def baseExp (k : ℕ) : Fin 4 → ℤ := ![-1, 1, 1 - k, k - 1]

/- English proof (translation)
Establish `e₀ : ρ.left ≫ basePts D T α mu 0 = (cP D T' α * cP D T' mu).left` using `congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D _ α) (cP D _ mu)).trans (by rw [comp_cP, comp_cP]))`. Establish `e₁ : ρ.left ≫ basePts D T α mu 1 = (cP D T' α).left` using `congrArg (fun q => q.left) (comp_cP D ρ α)`. Establish `e₂ : ρ.left ≫ basePts D T α mu 2 = (cP D T' mu).left` using `congrArg (fun q => q.left) (comp_cP D ρ mu)`. Establish `e₃ : ρ.left ≫ basePts D T α mu 3 = (1 : T' ⟶ D.P.A).left` using `congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)`. Rewrite using `[Fin.prod_univ_four, e₀, e₁, e₂, e₃]`.

Use `show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 - (k : ℤ)) * _ ^ ((k : ℤ) - 1) = _`. Rewrite using `[zpow_one, zpow_neg_one]`.
-/
theorem prod_base {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (α mu : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ basePts D T α mu i) ^ baseExp k i =
      (h (cP D T' α * cP D T' mu).left)⁻¹ * h (cP D T' α).left * h (cP D T' mu).left ^ (1 - (k : ℤ)) *
        h (1 : T' ⟶ D.P.A).left ^ ((k : ℤ) - 1) := by
  have e₀ : ρ.left ≫ basePts D T α mu 0 = (cP D T' α * cP D T' mu).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D _ α) (cP D _ mu)).trans (by rw [comp_cP, comp_cP]))
  have e₁ : ρ.left ≫ basePts D T α mu 1 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₂ : ρ.left ≫ basePts D T α mu 2 = (cP D T' mu).left := congrArg (fun q => q.left) (comp_cP D ρ mu)
  have e₃ : ρ.left ≫ basePts D T α mu 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 - (k : ℤ)) * _ ^ ((k : ℤ) - 1) = _
  rw [zpow_one, zpow_neg_one]

/- English proof (translation)
Set `a : T ⊗ D.P.A ⟶ D.P.A` to `cP D _ α`. Set `mm : T ⊗ D.P.A ⟶ D.P.A` to `cP D _ mu`. Set `x : T ⊗ D.P.A ⟶ D.P.A` to `snd _ _`. Establish `hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k` using `by rw [cPoint_add, cPoint_nsmul]`. Establish `htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm` using `(lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))`.

Take `⟨N, hN, vN⟩` from `exists_cubN D.cub a mm x k`. Take `⟨u₀, hu₀, vu₀⟩` from `exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (ε' := DegPre.deltaε k) (fun U _ h => by`. Establish `p₁` using `prod_cub a x mm h`. Establish `p₂` using `prod_base D π α mu k h`. Establish `p₃` using `prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h`.

Establish `p₄` using `prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h`. Simplify using `only [Over.id_left, Category.id_comp] at p₃`. Rewrite `p₃` using `[hα']`. Rewrite `p₄` using `[htr]`. Use `Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _ (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂) (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)` and prove the remaining obligations.

Rewrite using `[← _root_.mul_assoc (cP D _ α), mul_comm mm x]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]`. Use the proof step `module)`. Use the proof step `(LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left))) (LB.pullGen D.P.L _ _ v π.left))`.

Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hv _))`. Use `⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩` and prove the remaining obligations. Use `(vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_)) (val_pull hJ _ _ _)))` and prove the remaining obligations. Rewrite using `[← comp_cP D ρ α, ← comp_cP D ρ mu]`.
-/
theorem exists_genT (T S : Over (Spec (CommRingCat.of R))) (π : T ⊗ D.P.A ⟶ S) (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D S α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k)), u₀.IsGen ∧
      ∀ (T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T ⊗ D.P.A) (z : T'.left) (J), Good D.P.L z J →
        val u₀ ρ.left z J = cubN (th D z J) k (cP D T' α) (cP D T' mu) (ρ ≫ snd _ _) *
          (th D z J (cP D T' α) (ρ ≫ snd _ _) (cP D T' mu))⁻¹ * val v (ρ ≫ π).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k := by rw [cPoint_add, cPoint_nsmul]
  have htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm :=
    (lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu))
      (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := prod_base D π α mu k h
      have p₃ := prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h
      have p₄ := prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [htr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v π.left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D ρ α, ← comp_cP D ρ mu]

def multK (k : ℕ) (mu α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
    (GeneratorPullback.powGen D.P.L _ _ D.rigK k)

/- English proof (translation)
Use `(gs_pull σ (jK R) z ⊤ trivial _).symm.trans (congrArg (gs σ z ⊤) ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun f => (CommRingCat.Hom.hom f) c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm`.
-/
theorem gs_spec {Z : Scheme.{0}} (σ : Z ⟶ (TK R).left) (z : Z) (c : R) :
    gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
      gs σ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) c)) := by
  refine (gs_pull σ (jK R) z ⊤ trivial _).symm.trans (congrArg (gs σ z ⊤) ?_)
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_ratio D.P.isLB (u := multK D k mu α) (u' := LB.pullGen D.P.L _ _ v (toUnit (TK R)).left) (fun U _ h => by`. Use `Eq.trans ?_ (prod_base D (toUnit (TK R)) α mu k h).symm` and prove the remaining obligations. Establish `a₁ : ∀ χ, D.xK χ = (cP D (TK R) χ).left` using `fun χ => rfl`. Establish `a₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left` using `rfl`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]`.

Rewrite using `[add_comm mu α, cPoint_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use the proof step `module)`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α)) (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) (pullGen_isGen _ _ _ _ hv _)`.

Set `c : FractionRing R` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val`. Establish `hc : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom c = a.val` using `Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) a.val`. Establish `hc0 : c ≠ 0` using `(a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero`. Take `⟨r₁, r₂, h₂, e⟩` from `IsFractionRing.div_surjective (A := R) c`. Establish `h₂' : r₂ ≠ 0` using `nonZeroDivisors.ne_zero h₂`.

Establish `h₂K : algebraMap R (FractionRing R) r₂ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h₂'`. Use `⟨r₁, r₂, fun h => hc0 (by rw [← e, h, map_zero, zero_div]), h₂', fun Z σ z J hJ => ?_⟩` and prove the remaining obligations. Establish `e' : algebraMap R (FractionRing R) r₁ = algebraMap R (FractionRing R) r₂ * c`. Rewrite using `[← e, mul_div_cancel₀ _ h₂K]`. Rewrite using `[ha Z σ z J hJ, val_pull hJ, gs_spec, gs_spec, e', map_mul, hc, ← _root_.mul_assoc]`.

Conclude with `congrArg (· * _) (gs_mul σ z ⊤ trivial _ _).symm`.
-/
theorem multK_frac (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D (𝟙_ _) α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ r₁ r₂ : R, r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (Z : Scheme.{0}) (σ : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₂) * (val (multK D k mu α) σ z J).val =
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₁) *
        (val v (σ ≫ (toUnit (TK R)).left) z J).val := by
  obtain ⟨a, ha⟩ := exists_ratio D.P.isLB (u := multK D k mu α)
    (u' := LB.pullGen D.P.L _ _ v (toUnit (TK R)).left) (fun U _ h => by
      refine Eq.trans ?_ (prod_base D (toUnit (TK R)) α mu k h).symm
      have a₁ : ∀ χ, D.xK χ = (cP D (TK R) χ).left := fun χ => rfl
      have a₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [add_comm mu α, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) (pullGen_isGen _ _ _ _ hv _)
  let c : FractionRing R := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom c = a.val :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) a.val
  have hc0 : c ≠ 0 :=
    (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  obtain ⟨r₁, r₂, h₂, e⟩ := IsFractionRing.div_surjective (A := R) c
  have h₂' : r₂ ≠ 0 := nonZeroDivisors.ne_zero h₂
  have h₂K : algebraMap R (FractionRing R) r₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h₂'
  refine ⟨r₁, r₂, fun h => hc0 (by rw [← e, h, map_zero, zero_div]), h₂', fun Z σ z J hJ => ?_⟩
  have e' : algebraMap R (FractionRing R) r₁ = algebraMap R (FractionRing R) r₂ * c := by
    rw [← e, mul_div_cancel₀ _ h₂K]
  rw [ha Z σ z J hJ, val_pull hJ, gs_spec, gs_spec, e', map_mul, hc, ← _root_.mul_assoc]
  exact congrArg (· * _) (gs_mul σ z ⊤ trivial _ _).symm

/- English proof (translation)
Rewrite using `[h₁, h₂, Units.val_mul, Units.val_mul, mul_left_comm, h, mul_left_comm]`.
-/
theorem frac_mul {M : Type} [CommMonoid M] {g₁ g₂ : M} {u u₀ w m v : Mˣ} (h₁ : u = w * m) (h₂ : u₀ = w * v)
    (h : g₂ * m.val = g₁ * v.val) : g₂ * u.val = g₁ * u₀.val := by
  rw [h₁, h₂, Units.val_mul, Units.val_mul, mul_left_comm, h, mul_left_comm]

/- English proof (translation)
Introduce `hG R _ _ _ D T k α mu`. Take `⟨v, hv⟩` from `exists_gen_of_local (V := R) D.P.L D.P.isLB (basePts D (𝟙_ _) α mu) (baseExp k)`. Take `⟨u₀, hu₀, vu₀⟩` from `exists_genT D T (𝟙_ _) (toUnit _) k α mu v hv`. Take `⟨r₁, r₂, h₁, h₂, hr⟩` from `multK_frac D k α mu v hv`. Use `⟨u₀, r₁, r₂, hu₀, h₁, h₂, fun F _ _ φ u hu hc Z r z J hJ => ?_⟩` and prove the remaining obligations.

Set `T' : Over (Spec (CommRingCat.of R))` to `Over.mk (r ≫ (DegPre.BF D F).hom)`. Set `ρ : T' ⟶ DegPre.BF D F` to `Over.homMk r rfl`. Set `κ : T' ⟶ TK R` to `Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))`. Establish `e₁` using `(gen_fe (D := D) (F := F) hG k mu α).2 u hu hc T' ρ z J hJ`. Establish `e₂` using `vu₀ T' (ρ ≫ φ ▷ D.P.A) z J hJ`.

Establish `e₃ : val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J = val (multK D k mu α) κ.left z J` using `val_pull hJ _ _ _`. Establish `e₄` using `hr _ κ.left z J hJ`. Establish `e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D F).hom` using `Over.w κ`. Establish `e₆ : κ.left ≫ (toUnit (TK R)).left = ((ρ ≫ φ ▷ D.P.A) ≫ toUnit _).left` using `congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)`. Establish `e₇ : (ρ ≫ φ ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D F` using `by rw [Category.assoc, whiskerRight_snd]`.

Establish `g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D F).hom c) = gs (r ≫ (DegPre.BF D F).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)` using `fun c => gs_pull r (DegPre.BF D F).hom z ⊤ trivial _`. Rewrite `e₄` using `[e₅, e₆]`. Rewrite `e₁` using `[e₃, uVal, ← Category.assoc, comp_cP]`. Rewrite `e₂` using `[e₇]`. Rewrite using `[g, g]`.

Conclude with `frac_mul e₁ e₂ e₄`.
-/
theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α mu : D.X), ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k))) (r₁ r₂ : R), u₀.IsGen ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → gs r z ⊤ (scal (DegPre.BF D F).hom r₂) * (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D F).hom r₁) * (val u₀ (r ≫ (φ ▷ D.P.A).left) z J).val := by
  intro hG R _ _ _ D T k α mu
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (basePts D (𝟙_ _) α mu) (baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_genT D T (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := multK_frac D k α mu v hv
  refine ⟨u₀, r₁, r₂, hu₀, h₁, h₂, fun F _ _ φ u hu hc Z r z J hJ => ?_⟩
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D F).hom)
  let ρ : T' ⟶ DegPre.BF D F := Over.homMk r rfl
  let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
  have e₁ := (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc T' ρ z J hJ
  have e₂ := vu₀ T' (ρ ≫ φ ▷ D.P.A) z J hJ
  have e₃ : val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J = val (multK D k mu α) κ.left z J :=
    val_pull hJ _ _ _
  have e₄ := hr _ κ.left z J hJ
  have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D F).hom := Over.w κ
  have e₆ : κ.left ≫ (toUnit (TK R)).left = ((ρ ≫ φ ▷ D.P.A) ≫ toUnit _).left :=
    congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
  have e₇ : (ρ ≫ φ ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D F := by rw [Category.assoc, whiskerRight_snd]
  have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D F).hom c) =
      gs (r ≫ (DegPre.BF D F).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
    gs_pull r (DegPre.BF D F).hom z ⊤ trivial _
  rw [e₅, e₆] at e₄
  rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
  rw [e₇] at e₂
  rw [g, g]
  exact frac_mul e₁ e₂ e₄

end GlobalTheory.UU.IntGen
