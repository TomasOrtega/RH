import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GoodPoint

section General

variable {X Y W S₀ : Scheme.{0}} {L : LB W} {K : Type} [Fintype K]

/- English proof (translation)
Distinguish the cases in `h : f y ∈ U`. Rewrite using `[gs_eq f y U h, map_zero, map_zero]`. Conclude with `dif_neg h`.
-/
theorem gs_zero (f : X ⟶ Y) (y : X) (U : Y.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

/- English proof (translation)
Take `⟨t, -, hv⟩` from `exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)` and prove the remaining obligations. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])`. Use the proof step `(LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))`. Establish `le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ W)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`.

Take `⟨a, ha⟩` from `hp (res le (t.s PEmpty.elim)).val`. Use `⟨a, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `key : (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a`. Rewrite using `[← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]`. Conclude with `(congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))`.

Rewrite using `[← key, ← Units.val_mul, inv_mul_cancel_right]`.
-/
theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ W)} {ε : K → ℤ} (p : Y ⟶ S₀)
    (hp : Function.Surjective p.appTop.hom) {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val u r z J).val = gs (r ≫ p) z ⊤ a * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ W)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

/- English proof (translation)
Use `GlobalTheory.FunDescent.app_injective π (LB.wchart L φ j) (fn_ext fun y hy => ?_)` and prove the remaining obligations. Use `choose I hI using fun χ : X ⟶ W => exists_chart hL (χ y)`. Use `(gs_pull (𝟙 X) π y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 X) π y _ hy _).symm)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Use `(sec_trans s π y hy (Good.mem hI φ π)).trans ?_` and prove the remaining obligations.

Conclude with `((congrArg _ (h y I hI)).trans (mul_zero _)).trans (gs_zero π y _).symm`.
-/
theorem sec_eq_zero_of_flat (hL : L.IsLB) {φ : K → (Y ⟶ W)} {ε : K → ℤ} (π : X ⟶ Y) [Flat π] [Surjective π]
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s π y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine GlobalTheory.FunDescent.app_injective π (LB.wchart L φ j) (fn_ext fun y hy => ?_)
  choose I hI using fun χ : X ⟶ W => exists_chart hL (χ y)
  refine (gs_pull (𝟙 X) π y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 X) π y _ hy _).symm)
  rw [Category.id_comp]
  refine (sec_trans s π y hy (Good.mem hI φ π)).trans ?_
  exact ((congrArg _ (h y I hI)).trans (mul_zero _)).trans (gs_zero π y _).symm

/- English proof (translation)
Establish `le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun k => π ≫ ψ k) j` using `fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Establish `ex : ∀ j : K → L.ι, ∃ g, (π.app (LB.wchart L ψ j)).hom g = (res (le j) (u.s j)).val` using `fun j => by`. Use `hd _ _ fun i e => fn_ext fun y hy => ?_` and prove the remaining obligations. Use `choose J hJ using fun χ : X ⟶ W => exists_chart hL (χ y)`. Establish `e₁ : ∀ k, τ i ≫ π ≫ ψ k = 𝟙 X ≫ π ≫ ψ k` using `fun k => by`.

Rewrite using `[← Category.assoc, hτ, Category.id_comp]`. Establish `h` using `hinv i y J hJ`. Rewrite `h` using `[val_of u (τ i) y J (fun k => J (𝟙 X ≫ π ≫ ψ k)) (fun k => by rw [e₁])]`. Establish `m₀` using `Good.mem hJ (fun k => π ≫ ψ k) (𝟙 X)`. Establish `m₁ : τ i y ∈ LB.wchart L (fun k => π ≫ ψ k) (fun k => J (𝟙 X ≫ π ≫ ψ k))`.

Use `Good.mem hJ (fun k => π ≫ ψ k) (τ i)` as an intermediate fact. Simplify using `only [e₁] at this`. Conclude with `this`. Use `(gs_appLE (τ i) _ _ e (𝟙 X) y hy _).trans ?_` and prove the remaining obligations. Establish `hy' : τ i y ∈ π ⁻¹ᵁ LB.wchart L ψ j` using `e hy`.

Rewrite using `[Category.id_comp]`. Use `((gs_unit (τ i) y _ hy' _).trans (congrArg Units.val ?_)).trans (gs_unit (𝟙 X) y _ hy _).symm` and prove the remaining obligations. Use `((gm_res (τ i) y (le j) hy' _).trans ?_).trans (gm_res (𝟙 X) y (le j) hy _).symm` and prove the remaining obligations. Use `((gen_trans hu (τ i) y (le j hy') m₁).trans ?_).trans (gen_trans hu (𝟙 X) y (le j hy) m₀).symm` and prove the remaining obligations. Conclude with `congrArg₂ (· * ·) (by simp only [trF, e₁]) h`.

Use `choose g hg using ex`. Establish `hun : ∀ j, IsUnit (g j)` using `fun j => GlobalTheory.FunDescent.isUnit_of_isUnit_app π _ _ (by rw [hg]; exact Units.isUnit _)`. Establish `v : ∀ j (y : X), π y ∈ LB.wchart L ψ j → gs (𝟙 X ≫ π) y _ (g j) = (gm (𝟙 X) y (LB.wchart L (fun k => π ≫ ψ k) j) (u.s j)).val` using `fun j y hy => (gs_pull (𝟙 X) π y _ hy _).symm.trans ((congrArg (gs (𝟙 X) y _) (hg j)).trans ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_res (𝟙 X) y (le j) hy _))))`. Use `⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext ?_⟩` and prove the remaining obligations. Use `GlobalTheory.FunDescent.app_injective π (LB.wchart L ψ j ⊓ LB.wchart L ψ j') (fn_ext fun y hy => ?_)` and prove the remaining obligations.

Use `(gs_pull (𝟙 X) π y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 X) π y _ hy _).symm)` and prove the remaining obligations. Use `((gs_res _ y _ hy _).trans (v j y hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_linComb L ψ ε (𝟙 X ≫ π) y j j' hy.1 hy.2))) ((gs_res _ y _ hy _).trans (v j' y hy.2)))).symm)` and prove the remaining obligations. Rewrite using `[gen_trans hu (𝟙 X) y (le j hy.1) (le j' hy.2), Units.val_mul]`. Simplify using `only [trF, Category.assoc]`.
-/
theorem exists_gen_descend (hL : L.IsLB) (π : X ⟶ Y) [Flat π] [Surjective π] {I : Type} (τ : I → (X ⟶ X))
    (hτ : ∀ i, τ i ≫ π = π)
    (hd : ∀ (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U)),
      (∀ i (e : π ⁻¹ᵁ U ≤ τ i ⁻¹ᵁ (π ⁻¹ᵁ U)), ((τ i).appLE _ _ e).hom f = f) → ∃ g, (π.app U).hom g = f)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L (fun k => π ≫ ψ k) ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (τ i) y J = val u (𝟙 X) y J) :
    ∃ t : LB.Gen (LB.LinComb L ψ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun k => π ≫ ψ k) j := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have ex : ∀ j : K → L.ι, ∃ g, (π.app (LB.wchart L ψ j)).hom g = (res (le j) (u.s j)).val := fun j => by
    refine hd _ _ fun i e => fn_ext fun y hy => ?_
    choose J hJ using fun χ : X ⟶ W => exists_chart hL (χ y)
    have e₁ : ∀ k, τ i ≫ π ≫ ψ k = 𝟙 X ≫ π ≫ ψ k := fun k => by
      rw [← Category.assoc, hτ, Category.id_comp]
    have h := hinv i y J hJ
    rw [val_of u (τ i) y J (fun k => J (𝟙 X ≫ π ≫ ψ k)) (fun k => by rw [e₁])] at h
    have m₀ := Good.mem hJ (fun k => π ≫ ψ k) (𝟙 X)
    have m₁ : τ i y ∈ LB.wchart L (fun k => π ≫ ψ k) (fun k => J (𝟙 X ≫ π ≫ ψ k)) := by
      have := Good.mem hJ (fun k => π ≫ ψ k) (τ i)
      simp only [e₁] at this
      exact this
    refine (gs_appLE (τ i) _ _ e (𝟙 X) y hy _).trans ?_
    have hy' : τ i y ∈ π ⁻¹ᵁ LB.wchart L ψ j := e hy
    rw [Category.id_comp]
    refine ((gs_unit (τ i) y _ hy' _).trans (congrArg Units.val ?_)).trans (gs_unit (𝟙 X) y _ hy _).symm
    refine ((gm_res (τ i) y (le j) hy' _).trans ?_).trans (gm_res (𝟙 X) y (le j) hy _).symm
    refine ((gen_trans hu (τ i) y (le j hy') m₁).trans ?_).trans (gen_trans hu (𝟙 X) y (le j hy) m₀).symm
    exact congrArg₂ (· * ·) (by simp only [trF, e₁]) h
  choose g hg using ex
  have hun : ∀ j, IsUnit (g j) := fun j =>
    GlobalTheory.FunDescent.isUnit_of_isUnit_app π _ _ (by rw [hg]; exact Units.isUnit _)
  have v : ∀ j (y : X), π y ∈ LB.wchart L ψ j → gs (𝟙 X ≫ π) y _ (g j) =
      (gm (𝟙 X) y (LB.wchart L (fun k => π ≫ ψ k) j) (u.s j)).val := fun j y hy =>
    (gs_pull (𝟙 X) π y _ hy _).symm.trans ((congrArg (gs (𝟙 X) y _) (hg j)).trans
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_res (𝟙 X) y (le j) hy _))))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext ?_⟩
  refine GlobalTheory.FunDescent.app_injective π (LB.wchart L ψ j ⊓ LB.wchart L ψ j') (fn_ext fun y hy => ?_)
  refine (gs_pull (𝟙 X) π y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 X) π y _ hy _).symm)
  refine ((gs_res _ y _ hy _).trans (v j y hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
      (congrArg Units.val (gm_linComb L ψ ε (𝟙 X ≫ π) y j j' hy.1 hy.2)))
      ((gs_res _ y _ hy _).trans (v j' y hy.2)))).symm)
  rw [gen_trans hu (𝟙 X) y (le j hy.1) (le j' hy.2), Units.val_mul]
  simp only [trF, Category.assoc]

end General

section Translates

variable {Y S₀ : Scheme.{0}} {L : LB Y} {G : Type} [CommGroup G]

/- English proof (translation)
Establish `hc : ∀ w, w ^ n = 1 → ∃ c : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → (val u (r ≫ t w) z J).val = gs (r ≫ p) z ⊤ c * (val u r z J).val` using `fun w hw => by`. Take `⟨u', hu', hv⟩` from `exists_gen hL (φ' := fun k => M ≫ ![t (x ^ n), 𝟙 Y] k) (ε' := ![1, -1]) (fun U _ h => by simp only [← Category.assoc, tM, hw, t₁, Category.comp_id]) (LB.pullGen L _ _ u (t w)) (DVR.pullGen_isGen _ _ _ _ hu _)`. Take `⟨c, hc⟩` from `exists_ratio hL p hp hu' hu`. Conclude with `⟨c, fun Z r z J hJ => by rw [← hc Z r z J hJ, hv Z r z J hJ, val_pull hJ]⟩`. Establish `ind : ∀ i : ℕ, ∃ U : LB.Gen (LB.LinComb L (K` using `Fin 2) (fun k => M ≫ ![t ((x ^ n) ^ i), 𝟙 Y] k) ![1, -1]), U.IsGen ∧ ∀ (w : G) (c : Γ(S₀, ⊤)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → (val u (r ≫ t w) z J).val = gs (r ≫ p) z ⊤ c * (val u r z J).val) → ∀ y J, Good L y J → (val U (t w) y J).val = gs p y ⊤ c ^ i …`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Take `⟨U, hU, hv⟩` from `exists_gen hL (φ' := fun k => M ≫ ![t ((x ^ n) ^ 0), 𝟙 Y] k) (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_succ, t₁]) (LB.oneGen L (Y := Y)) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)`. Conclude with `⟨U, hU, fun w c _ y J hJ => by rw [hv _ _ y J hJ, hv _ _ y J hJ, val_one, val_one]; simp⟩`.

Consider the case `succ i ih`. Take `⟨U, hU, hv⟩` from `ih`. Take `⟨U', hU', hv'⟩` from `exists_gen hL (φ' := fun k => M ≫ ![t ((x ^ n) ^ (i + 1)), 𝟙 Y] k) (ε' := ![1, -1]) (fun U _ h => by`. Establish `e : (x ^ i) ^ n = (x ^ n) ^ i` using `pow_right_comm _ _ _`. Simplify using `[Fin.prod_univ_succ, Fintype.prod_sum_type, reassoc_of% (tM (x ^ i)), tM, tm, e, pow_succ, mul_comm])`.

Use the proof step `(LB.mulGen L _ _ _ _ U (LB.pullGen L _ _ u (t (x ^ i))))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ hU (DVR.pullGen_isGen _ _ _ _ hu _))`. Use `⟨U', hU', fun w c hw y J hJ => ?_⟩` and prove the remaining obligations. Establish `e : t w ≫ t (x ^ i) = t (x ^ i) ≫ t w` using `by rw [tm, tm, mul_comm]`. Rewrite using `[hv' _ _ y J hJ, hv' _ _ y J hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Units.val_mul, Units.val_mul, hv w c hw y J hJ, e, hw _ _ y J hJ, tp, Category.id_comp]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hU, hv⟩` from `ind n`. Use `⟨U, hU, fun w hw y J hJ => Units.ext ?_⟩` and prove the remaining obligations. Take `⟨c, hc'⟩` from `hc w hw`. Establish `pw : ∀ i : ℕ, (val u (t (w ^ i)) y J).val = gs p y ⊤ c ^ i * (val u (𝟙 Y) y J).val`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => rw [pow_zero, pow_zero, t₁, _root_.one_mul]`. Consider the case `succ i ih => rw [pow_succ w, ← tm, hc' _ _ y J hJ, tp, ih]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `pw n`. Rewrite `h1` using `[hw, t₁]`. Establish `h2 : gs p y ⊤ c ^ n = 1` using `(Units.mul_left_inj _).1 (h1.symm.trans (_root_.one_mul _).symm)`. Rewrite using `[hv w c hc' y J hJ, h2, _root_.one_mul]`.
-/
theorem exists_invariant_gen (hL : L.IsLB) (t : G → (Y ⟶ Y)) (t₁ : t 1 = 𝟙 Y)
    (tm : ∀ a b, t a ≫ t b = t (a * b)) (p : Y ⟶ S₀) (tp : ∀ a, t a ≫ p = p)
    (hp : Function.Surjective p.appTop.hom) (M : Y ⟶ Y) (n : ℕ) (tM : ∀ a, t a ≫ M = M ≫ t (a ^ n)) (x : G)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => M ≫ ![t (x ^ n), 𝟙 Y] k) ![1, -1])) (hu : u.IsGen) :
    ∃ U : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => M ≫ ![t ((x ^ n) ^ n), 𝟙 Y] k) ![1, -1]), U.IsGen ∧
      ∀ w, w ^ n = 1 → ∀ y J, Good L y J → val U (t w) y J = val U (𝟙 Y) y J := by
  have hc : ∀ w, w ^ n = 1 → ∃ c : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val u (r ≫ t w) z J).val = gs (r ≫ p) z ⊤ c * (val u r z J).val := fun w hw => by
    obtain ⟨u', hu', hv⟩ := exists_gen hL (φ' := fun k => M ≫ ![t (x ^ n), 𝟙 Y] k) (ε' := ![1, -1])
      (fun U _ h => by simp only [← Category.assoc, tM, hw, t₁, Category.comp_id])
      (LB.pullGen L _ _ u (t w)) (DVR.pullGen_isGen _ _ _ _ hu _)
    obtain ⟨c, hc⟩ := exists_ratio hL p hp hu' hu
    exact ⟨c, fun Z r z J hJ => by rw [← hc Z r z J hJ, hv Z r z J hJ, val_pull hJ]⟩
  have ind : ∀ i : ℕ, ∃ U : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => M ≫ ![t ((x ^ n) ^ i), 𝟙 Y] k) ![1, -1]),
      U.IsGen ∧ ∀ (w : G) (c : Γ(S₀, ⊤)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        (val u (r ≫ t w) z J).val = gs (r ≫ p) z ⊤ c * (val u r z J).val) →
        ∀ y J, Good L y J → (val U (t w) y J).val = gs p y ⊤ c ^ i * (val U (𝟙 Y) y J).val := by
    intro i
    induction i with
    | zero =>
      obtain ⟨U, hU, hv⟩ := exists_gen hL (φ' := fun k => M ≫ ![t ((x ^ n) ^ 0), 𝟙 Y] k) (ε' := ![1, -1])
        (fun U _ h => by simp [Fin.prod_univ_succ, t₁]) (LB.oneGen L (Y := Y))
        (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
          (_root_.mul_one _)).symm)
      exact ⟨U, hU, fun w c _ y J hJ => by rw [hv _ _ y J hJ, hv _ _ y J hJ, val_one, val_one]; simp⟩
    | succ i ih =>
      obtain ⟨U, hU, hv⟩ := ih
      obtain ⟨U', hU', hv'⟩ := exists_gen hL (φ' := fun k => M ≫ ![t ((x ^ n) ^ (i + 1)), 𝟙 Y] k) (ε' := ![1, -1])
        (fun U _ h => by
          have e : (x ^ i) ^ n = (x ^ n) ^ i := pow_right_comm _ _ _
          simp [Fin.prod_univ_succ, Fintype.prod_sum_type, reassoc_of% (tM (x ^ i)), tM, tm, e, pow_succ, mul_comm])
        (LB.mulGen L _ _ _ _ U (LB.pullGen L _ _ u (t (x ^ i))))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ hU (DVR.pullGen_isGen _ _ _ _ hu _))
      refine ⟨U', hU', fun w c hw y J hJ => ?_⟩
      have e : t w ≫ t (x ^ i) = t (x ^ i) ≫ t w := by rw [tm, tm, mul_comm]
      rw [hv' _ _ y J hJ, hv' _ _ y J hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Units.val_mul,
        Units.val_mul, hv w c hw y J hJ, e, hw _ _ y J hJ, tp, Category.id_comp]
      ring
  obtain ⟨U, hU, hv⟩ := ind n
  refine ⟨U, hU, fun w hw y J hJ => Units.ext ?_⟩
  obtain ⟨c, hc'⟩ := hc w hw
  have pw : ∀ i : ℕ, (val u (t (w ^ i)) y J).val = gs p y ⊤ c ^ i * (val u (𝟙 Y) y J).val := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, t₁, _root_.one_mul]
    | succ i ih => rw [pow_succ w, ← tm, hc' _ _ y J hJ, tp, ih]; ring
  have h1 := pw n
  rw [hw, t₁] at h1
  have h2 : gs p y ⊤ c ^ n = 1 := (Units.mul_left_inj _).1 (h1.symm.trans (_root_.one_mul _).symm)
  rw [hv w c hc' y J hJ, h2, _root_.one_mul]

end Translates

section Group

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def toBaseOver (Z : Over S) : Z ⟶ baseOver S := toUnit Z

/- English proof (translation)
The claim follows from `toUnit_unique (X := Z) f g`.
-/
theorem toBaseOver_unique {Z : Over S} (f g : Z ⟶ baseOver S) : f = g := toUnit_unique (X := Z) f g

def transl (x : baseOver S ⟶ A) : A ⟶ A := (toBaseOver A ≫ x) * 𝟙 A

/- English proof (translation)
Rewrite using `[transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toBaseOver_unique (r ≫ _) (toBaseOver Z)]`.
-/
theorem comp_transl {Z : Over S} (r : Z ⟶ A) (x : baseOver S ⟶ A) :
    r ≫ transl A x = (toBaseOver Z ≫ x) * r := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toBaseOver_unique (r ≫ _) (toBaseOver Z)]

/- English proof (translation)
Rewrite using `[mulA, MonObj.comp_pow, Category.comp_id]`.
-/
theorem comp_mulA {Z : Over S} (r : Z ⟶ A) (n : ℕ) : r ≫ mulA A n = r ^ n := by
  rw [mulA, MonObj.comp_pow, Category.comp_id]

/- English proof (translation)
Rewrite using `[transl, MonObj.comp_one, _root_.one_mul]`.
-/
theorem transl_one : transl A 1 = 𝟙 A := by rw [transl, MonObj.comp_one, _root_.one_mul]

/- English proof (translation)
Rewrite using `[comp_transl, toBaseOver_unique (toBaseOver _) (fst (baseOver S) A)]`. Both sides reduce to the same expression.
-/
theorem snd_transl (x : baseOver S ⟶ A) : snd (baseOver S) A ≫ transl A x = translPt A x := by
  rw [comp_transl, toBaseOver_unique (toBaseOver _) (fst (baseOver S) A)]; rfl

def unitInv : A ⟶ baseOver S ⊗ A := lift (toBaseOver A) (𝟙 A)

omit [GrpObj A] in
/- English proof (translation)
The claim follows from `lift_snd _ _`.
-/
theorem unitInv_snd : unitInv A ≫ snd (baseOver S) A = 𝟙 A := lift_snd _ _

omit [GrpObj A] in
instance : IsIso (unitInv A) :=
  ⟨snd (baseOver S) A, unitInv_snd A, CartesianMonoidalCategory.hom_ext _ _ (toBaseOver_unique _ _)
    (by rw [Category.assoc, unitInv_snd, Category.comp_id, Category.id_comp])⟩

/- English proof (translation)
The claim follows from `CartesianMonoidalCategory.hom_ext _ _ (toBaseOver_unique _ _) (by rw [Category.assoc, Category.assoc, unitInv_snd, mulT, lift_snd, MonObj.comp_pow, unitInv_snd, Category.comp_id])`.
-/
theorem unitInv_mulT (n : ℕ) : unitInv A ≫ mulT A (baseOver S) n = mulA A n ≫ unitInv A :=
  CartesianMonoidalCategory.hom_ext _ _ (toBaseOver_unique _ _) (by
    rw [Category.assoc, Category.assoc, unitInv_snd, mulT, lift_snd, MonObj.comp_pow, unitInv_snd, Category.comp_id])

/- English proof (translation)
The claim follows from `lift_snd _ _`.
-/
theorem ptSecT_snd {T : Over S} (q : T ⟶ A) : ptSecT A q ≫ snd T A = q := lift_snd _ _

/- English proof (translation)
Establish `e : ptSecT A q ≫ translPt A x = x * q`. Use `(MonObj.comp_mul (ptSecT A q) (fst T A ≫ x) (snd T A)).trans ?_` and prove the remaining obligations. Rewrite using `[ptSecT, lift_fst_assoc, lift_snd, Category.id_comp]`. Rewrite using `[translT, comp_lift, e, ptSecT, lift_fst, ptSecT]`.
-/
theorem ptSecT_translT {T : Over S} (q x : T ⟶ A) : ptSecT A q ≫ translT A x = ptSecT A (x * q) := by
  have e : ptSecT A q ≫ translPt A x = x * q := by
    refine (MonObj.comp_mul (ptSecT A q) (fst T A ≫ x) (snd T A)).trans ?_
    rw [ptSecT, lift_fst_assoc, lift_snd, Category.id_comp]
  rw [translT, comp_lift, e, ptSecT, lift_fst, ptSecT]

/- English proof (translation)
Rewrite using `[mulT, comp_lift, MonObj.comp_pow, ptSecT_snd, ptSecT, lift_fst, ptSecT]`.
-/
theorem ptSecT_mulT {T : Over S} (q : T ⟶ A) (n : ℕ) : ptSecT A q ≫ mulT A T n = ptSecT A (q ^ n) := by
  rw [mulT, comp_lift, MonObj.comp_pow, ptSecT_snd, ptSecT, lift_fst, ptSecT]

variable [IsCommMonObj A]

/- English proof (translation)
Rewrite using `[comp_transl, transl, transl, MonObj.comp_mul, ← _root_.mul_assoc, mul_comm (toBaseOver A ≫ y)]`.
-/
theorem transl_comp (x y : baseOver S ⟶ A) : transl A x ≫ transl A y = transl A (x * y) := by
  rw [comp_transl, transl, transl, MonObj.comp_mul, ← _root_.mul_assoc, mul_comm (toBaseOver A ≫ y)]

/- English proof (translation)
Rewrite using `[comp_transl, comp_mulA, transl, mul_pow, MonObj.comp_pow]`.
-/
theorem transl_mulA (x : baseOver S ⟶ A) (n : ℕ) : transl A x ≫ mulA A n = mulA A n ≫ transl A (x ^ n) := by
  rw [comp_transl, comp_mulA, transl, mul_pow, MonObj.comp_pow]

end Group

section Values

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

def powVal {a : ℤ} (s : LB.Sec (LPow A L a T)) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    Z.presheaf.stalk z :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J

/- English proof (translation)
Set `j : Fin 2 → L.ι` to `fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)`. Establish `hm : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j` using `hJ.mem _ r`. Establish `e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left`. Rewrite using `[← Over.comp_left, translT, lift_snd]`. Establish `le` using `chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j`.

Use `⟨_, ((gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (h j)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) rfl ((gs_res r z le hm _).trans ((gs_pull r (translT A θ.pt).left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (le hm) _).trans ?_))))))⟩` and prove the remaining obligations. Conclude with `(sval_of (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)).symm`.
-/
theorem powVal_act {k : ℤ} {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : IsActOf A L k θ s s')
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    ∃ c, powVal s' r z J = c * powVal s (r ≫ (translT A θ.pt).left) z J := by
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hm : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have le := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j
  refine ⟨_, ((gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (h j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) rfl ((gs_res r z le hm _).trans ((gs_pull r (translT A θ.pt).left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (le hm) _).trans ?_))))))⟩
  exact (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ z J (fun _ => j 1)
    (fun _ => by rw [Category.assoc, e]; rfl)).symm

/- English proof (translation)
Set `j : Fin 1 → L.ι` to `fun _ => J ((ptSecT A x).left ≫ (snd T A).left)`. Establish `e : (ptSecT A x).left ≫ (snd T A).left = x.left` using `by rw [← Over.comp_left, ptSecT_snd]`. Establish `hm : (𝟙 T.left : T.left ⟶ T.left) z ∈ LB.wchart L (fun _ : Fin 1 => x.left) j` using `Set.mem_iInter.2 fun _ => by`. Use `hJ ((ptSecT A x).left ≫ (snd T A).left)` as an intermediate fact. Rewrite `this` using `[show ((ptSecT A x).left ≫ (snd T A).left) z = x.left z by rw [e]]`.

Conclude with `this`. Establish `le` using `val_le A L x j`. Establish `e₁` using `((gs_res (𝟙 T.left) z le hm _).trans (gs_pull (𝟙 T.left) _ z _ (le hm) _)).symm.trans ((congrArg (gs (𝟙 T.left) z _) (h j)).trans ((gs_mul (𝟙 T.left) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 T.left) z le_top hm _) (gs_unit (𝟙 T.left) z _ hm _))))`. Rewrite `e₁` using `[Category.id_comp]`. Take `⟨v, rfl⟩` from `hv`.

Rewrite `e₁` using `[gs_unit _ z ⊤ trivial]`. Conclude with `(congrArg IsUnit e₁).mpr ((Units.isUnit _).mul (Units.isUnit _))`.
-/
theorem isUnit_powVal {k : ℤ} {s : LB.Sec (LPow A L k T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))} {v : Γ(T.left, ⊤)}
    (h : IsValueAt A L k s x τ v) (hv : IsUnit v) {z : T.left} {J : (T.left ⟶ A.left) → L.ι} (hJ : Good L z J) :
    IsUnit (powVal s (ptSecT A x).left z J) := by
  let j : Fin 1 → L.ι := fun _ => J ((ptSecT A x).left ≫ (snd T A).left)
  have e : (ptSecT A x).left ≫ (snd T A).left = x.left := by rw [← Over.comp_left, ptSecT_snd]
  have hm : (𝟙 T.left : T.left ⟶ T.left) z ∈ LB.wchart L (fun _ : Fin 1 => x.left) j :=
    Set.mem_iInter.2 fun _ => by
      have := hJ ((ptSecT A x).left ≫ (snd T A).left)
      rw [show ((ptSecT A x).left ≫ (snd T A).left) z = x.left z by rw [e]] at this
      exact this
  have le := val_le A L x j
  have e₁ := ((gs_res (𝟙 T.left) z le hm _).trans (gs_pull (𝟙 T.left) _ z _ (le hm) _)).symm.trans
    ((congrArg (gs (𝟙 T.left) z _) (h j)).trans ((gs_mul (𝟙 T.left) z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 T.left) z le_top hm _) (gs_unit (𝟙 T.left) z _ hm _))))
  rw [Category.id_comp] at e₁
  obtain ⟨v, rfl⟩ := hv
  rw [gs_unit _ z ⊤ trivial] at e₁
  exact (congrArg IsUnit e₁).mpr ((Units.isUnit _).mul (Units.isUnit _))

/- English proof (translation)
Establish `e : (ptSecT A x).left ≫ (snd T A).left = x.left` using `by rw [← Over.comp_left, ptSecT_snd]`. Set `f : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => x.left) j)` to `fun j => (T.left.presheaf.map (homOfLE (val_le A L x j)).op).hom (((ptSecT A x).left.app _).hom (s.f j))`. Establish `v : ∀ j y, y ∈ LB.wchart L (fun _ : Fin 1 => x.left) j → gs (𝟙 T.left) y _ (f j) = gs (ptSecT A x).left y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j)` using `fun j y hy => ((gs_res (𝟙 T.left) y (val_le A L x j) hy _).trans (gs_pull (𝟙 T.left) (ptSecT A x).left y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (val_le A L x j hy) _)).trans (by rw [Category.id_comp])`. Establish `hu : ∀ j, IsUnit (f j)` using `fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by`. Take `rfl : y = z` from `Subsingleton.elim (α := T.left) _ _`.

Establish `e₁` using `(v j y hy).trans (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (ptSecT A x).left y (val_le A L x j hy) (hJ.mem _ _))`. Conclude with `(congrArg IsUnit ((gs_eq (𝟙 T.left) y _ hy _).symm.trans e₁)).mpr ((Units.isUnit _).mul h)`. Use `⟨⟨fun j => (hu j).unit⟩, fun j j' => Units.ext (fn_ext fun y hy => ?_), fun j => ?_⟩` and prove the remaining obligations. Use `((gs_res _ y _ hy _).trans (v j y hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 T.left) y j j' hy.1 hy.2))) ((gs_res _ y _ hy _).trans (v j' y hy.2)))).symm)` and prove the remaining obligations. Use `(sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (ptSecT A x).left y (val_le A L x j hy.1) (val_le A L x j' hy.2)).trans ?_` and prove the remaining obligations.

Simplify using `only [trF, e, Category.id_comp]`. Rewrite using `[map_one, _root_.one_mul]`. Both sides reduce to the same expression.
-/
theorem exists_frame_of_isUnit [Subsingleton T.left] {k : ℤ} (s : LB.Sec (LPow A L k T)) (x : T ⟶ A)
    {z : T.left} {J : (T.left ⟶ A.left) → L.ι} (hJ : Good L z J) (h : IsUnit (powVal s (ptSecT A x).left z J)) :
    ∃ τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k)),
      τ.IsGen ∧ IsValueAt A L k s x τ 1 := by
  have e : (ptSecT A x).left ≫ (snd T A).left = x.left := by rw [← Over.comp_left, ptSecT_snd]
  let f : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => x.left) j) := fun j =>
    (T.left.presheaf.map (homOfLE (val_le A L x j)).op).hom (((ptSecT A x).left.app _).hom (s.f j))
  have v : ∀ j y, y ∈ LB.wchart L (fun _ : Fin 1 => x.left) j → gs (𝟙 T.left) y _ (f j) =
      gs (ptSecT A x).left y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) := fun j y hy =>
    ((gs_res (𝟙 T.left) y (val_le A L x j) hy _).trans (gs_pull (𝟙 T.left) (ptSecT A x).left y
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (val_le A L x j hy) _)).trans (by rw [Category.id_comp])
  have hu : ∀ j, IsUnit (f j) := fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain rfl : y = z := Subsingleton.elim (α := T.left) _ _
    have e₁ := (v j y hy).trans (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
      (ptSecT A x).left y (val_le A L x j hy) (hJ.mem _ _))
    exact (congrArg IsUnit ((gs_eq (𝟙 T.left) y _ hy _).symm.trans e₁)).mpr ((Units.isUnit _).mul h)
  refine ⟨⟨fun j => (hu j).unit⟩, fun j j' => Units.ext (fn_ext fun y hy => ?_), fun j => ?_⟩
  · refine ((gs_res _ y _ hy _).trans (v j y hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 T.left) y j j' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (v j' y hy.2)))).symm)
    refine (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
      (ptSecT A x).left y (val_le A L x j hy.1) (val_le A L x j' hy.2)).trans ?_
    simp only [trF, e, Category.id_comp]
  · rw [map_one, _root_.one_mul]; rfl

def vanishing (L : LB A.left) (k : ℤ) (B : Set (T ⟶ A)) : Submodule Γ(T.left, ⊤) (SecM A L k T) where
  carrier := {f | ∀ q ∈ B, ∀ z J, Good L z J →
    powVal (SecM.toSec A f) (ptSecT A q).left z J ∈ IsLocalRing.maximalIdeal _}
  add_mem' := fun {f g} hf hg q hq z J hJ =>
    (congrArg (· ∈ IsLocalRing.maximalIdeal _) (gs_add _ z _ (hJ.mem (fun _ : Fin 1 => (snd T A).left) _) _ _)).mpr
      (Ideal.add_mem _ (hf q hq z J hJ) (hg q hq z J hJ))
  zero_mem' := fun q _ z J _ =>
    (congrArg (· ∈ IsLocalRing.maximalIdeal _) (gs_zero _ z _)).mpr (Ideal.zero_mem _)
  smul_mem' := fun c f hf q hq z J hJ =>
    (congrArg (· ∈ IsLocalRing.maximalIdeal _) (gs_mul _ z _ (hJ.mem (fun _ : Fin 1 => (snd T A).left) _) _ _)).mpr
      (Ideal.mul_mem_left _ _ (hf q hq z J hJ))

end Values

section Field

variable {K : Type} [Field K]

/- English proof (translation)
Use `P.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected` as an intermediate fact. Establish `: IsIntegral P.A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom`. Set `_` to `(isField_of_universallyClosed K P.A.hom).toField`.

Set `e : Spec (CommRingCat.of K) ⟶ P.A.left` to `η[P.A].left`. Establish `he : e ≫ P.A.hom = 𝟙 _` using `Over.w η[P.A]`. Introduce `a`. Use `⟨e.appTop.hom a, e.appTop.hom.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]`.

Simplify using the standard rewrite rules.
-/
theorem surjective_appTop (P : PolAV (Spec (CommRingCat.of K))) : Function.Surjective P.A.hom.appTop.hom := by
  have := P.isAb.smooth
  have := P.isAb.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
    P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let _ := (isField_of_universallyClosed K P.A.hom).toField
  let e : Spec (CommRingCat.of K) ⟶ P.A.left := η[P.A].left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  intro a
  refine ⟨e.appTop.hom a, e.appTop.hom.injective ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
  simp

variable [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) [Etale (mulA P.A n).left]
  [Surjective (mulA P.A n).left]

/- English proof (translation)
Take `⟨y, -⟩` from `(pullback.snd (mulA P.A n).left a.left).surjective (IsLocalRing.closedPoint K)`. Take `⟨s, hs, -⟩` from `exists_section_of_etale (K := K) (pullback.snd (mulA P.A n).left a.left) y`. Establish `e : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `(congrArg (· ≫ a.left) hs).trans (Category.id_comp _)`.

Use `⟨Over.homMk (s ≫ pullback.fst (mulA P.A n).left a.left) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w (mulA P.A n), ← Category.assoc]`. Conclude with `(congrArg (· ≫ P.A.hom) e).trans (Over.w a)`. Rewrite using `[← comp_mulA]`. Conclude with `Over.OverMorphism.ext e`.
-/
theorem exists_pow_eq (a : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) :
    ∃ b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, b ^ n = a := by
  obtain ⟨y, -⟩ := (pullback.snd (mulA P.A n).left a.left).surjective (IsLocalRing.closedPoint K)
  obtain ⟨s, hs, -⟩ := exists_section_of_etale (K := K) (pullback.snd (mulA P.A n).left a.left) y
  have e : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ a.left) hs).trans (Category.id_comp _)
  refine ⟨Over.homMk (s ≫ pullback.fst (mulA P.A n).left a.left) ?_, ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc]
    exact (congrArg (· ≫ P.A.hom) e).trans (Over.w a)
  · rw [← comp_mulA]
    exact Over.OverMorphism.ext e

/- English proof (translation)
Substitute `hk` using the available equality. Set `t : (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) → (P.A.left ⟶ P.A.left)` to `fun x => (transl P.A x).left`. Establish `tM : ∀ a, t a ≫ (mulA P.A n).left = (mulA P.A n).left ≫ t (a ^ n)` using `fun a => congrArg (fun q => q.left) (transl_mulA P.A a n)`. Establish `e₀ : (unitInv P.A).left ≫ (snd _ P.A).left = 𝟙 P.A.left` using `congrArg (fun q => q.left) (unitInv_snd P.A)`. Establish `e₁ : (unitInv P.A).left ≫ (translPt P.A θ.pt).left = t θ.pt`.

Rewrite using `[← snd_transl, Over.comp_left, ← Category.assoc, e₀, Category.id_comp]`. Take `⟨u, hu, -⟩` from `exists_gen P.isLB (φ' := fun k => (mulA P.A n).left ≫ ![t (θ.pt ^ n), 𝟙 _] k) (ε' := ![1, -1]) (fun U _ h => by`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, Fintype.prod_sum_type, e₀, e₁, tM, -Over.snd_left]`. Use the proof step `abel)`.

Use the proof step `(LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (t θ.pt)) (LB.pullGen P.L _ _ θ.φ (unitInv P.A).left))))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ θ.isGen _))))`. Take `⟨U, hU, hinv⟩` from `exists_invariant_gen P.isLB t (congrArg (fun q => q.left) (transl_one P.A)) (fun a b => congrArg (fun q => q.left) (transl_comp P.A a b)) P.A.hom (fun a => Over.w _) (surjective_appTop P) _ n tM θ.pt u hu`. Take `⟨c, hc⟩` from `exists_gen_descend P.isLB (mulA P.A n).left (I := {w : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // w ^ n = 1}) (fun w => t w.1) (fun w => by`. Rewrite using `[tM, w.2]`.

Conclude with `(congrArg (fun q => _ ≫ q.left) (transl_one P.A)).trans (Category.comp_id _))`. Use the proof step `(fun V f hf => (existsUnique_descend_of_torsion_invariant P.A n V f fun y hy e => hf ⟨y, hy⟩ e).exists)`. Use `_ _ U hU (fun w => hinv w.1 w.2)`. Use `P.ktriv K (𝟙 _) _ fun p => ⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Use `gen_chartPull (chartPullOut P.L _ _ _ _ fun k => ?_) _ (DVR.pullGen_isGen _ _ _ c hc (Scheme.Opens.ι _ ≫ (snd _ P.A).left))` and prove the remaining obligations.

Rewrite using `[Category.assoc]`. Use `congrArg (_ ≫ ·) ?_` and prove the remaining obligations. Use `fin_cases k`. Conclude with `congrArg (fun q => q.left) (snd_transl P.A _)`. Conclude with `Category.comp_id _`.
-/
theorem thetaGrp_pt_pow [QuasiCompact (mulA P.A n).left]
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1])) (hα : α.IsGen)
    {k : ℤ} (hk : k = (n : ℤ) ^ 2) (θ : ThetaGrp P.A P.L k (baseOver (Spec (CommRingCat.of K)))) :
    (θ.pt ^ n) ^ n = 1 := by
  subst hk
  let t : (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) → (P.A.left ⟶ P.A.left) := fun x => (transl P.A x).left
  have tM : ∀ a, t a ≫ (mulA P.A n).left = (mulA P.A n).left ≫ t (a ^ n) := fun a =>
    congrArg (fun q => q.left) (transl_mulA P.A a n)
  have e₀ : (unitInv P.A).left ≫ (snd _ P.A).left = 𝟙 P.A.left := congrArg (fun q => q.left) (unitInv_snd P.A)
  have e₁ : (unitInv P.A).left ≫ (translPt P.A θ.pt).left = t θ.pt := by
    rw [← snd_transl, Over.comp_left, ← Category.assoc, e₀, Category.id_comp]
  obtain ⟨u, hu, -⟩ := exists_gen P.isLB (φ' := fun k => (mulA P.A n).left ≫ ![t (θ.pt ^ n), 𝟙 _] k)
    (ε' := ![1, -1]) (fun U _ h => by
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, e₀, e₁, tM, -Over.snd_left]
      abel)
    (LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (t θ.pt))
      (LB.pullGen P.L _ _ θ.φ (unitInv P.A).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ θ.isGen _))))
  obtain ⟨U, hU, hinv⟩ := exists_invariant_gen P.isLB t (congrArg (fun q => q.left) (transl_one P.A))
    (fun a b => congrArg (fun q => q.left) (transl_comp P.A a b)) P.A.hom (fun a => Over.w _)
    (surjective_appTop P) _ n tM θ.pt u hu
  obtain ⟨c, hc⟩ := exists_gen_descend P.isLB (mulA P.A n).left
    (I := {w : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // w ^ n = 1}) (fun w => t w.1)
    (fun w => by
      rw [tM, w.2]
      exact (congrArg (fun q => _ ≫ q.left) (transl_one P.A)).trans (Category.comp_id _))
    (fun V f hf => (existsUnique_descend_of_torsion_invariant P.A n V f fun y hy e => hf ⟨y, hy⟩ e).exists)
    _ _ U hU (fun w => hinv w.1 w.2)
  refine P.ktriv K (𝟙 _) _ fun p => ⟨⊤, trivial, ?_⟩
  refine gen_chartPull (chartPullOut P.L _ _ _ _ fun k => ?_) _
    (DVR.pullGen_isGen _ _ _ c hc (Scheme.Opens.ι _ ≫ (snd _ P.A).left))
  rw [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  fin_cases k
  · exact congrArg (fun q => q.left) (snd_transl P.A _)
  · exact Category.comp_id _

end Field

/- English proof (translation)
Introduce `hirr hpull hmul hgen K _ _ P n hn hnK th hth a`. Take `⟨h1, -, h3, h4⟩` from `hmul _ P n (by omega)`. Establish `: Etale (mulA P.A n).left` using `h4 (by`. Simplify using `using (Ne.isUnit hnK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)`. Establish `hs : Subsingleton (baseOver (Spec (CommRingCat.of K))).left` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`.

Establish `z : (baseOver (Spec (CommRingCat.of K))).left` using `IsLocalRing.closedPoint K`. Take `⟨α, hα⟩` from `hpull _ P n`. Take `⟨b, rfl⟩` from `exists_pow_eq P n a`. Assume the negation of the conclusion as `hcon`. Establish `h4 : 4 ≤ n * n` using `by nlinarith`.

Establish `hk : ((n * n : ℕ) : ℤ) = (n : ℤ) ^ 2` using `by push_cast; ring`. Establish `em : (mulT P.A (baseOver (Spec (CommRingCat.of K))) n).left ≫ (snd _ P.A).left = (snd _ P.A).left ≫ (mulA P.A n).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, comp_mulA, mulT, lift_snd]`. Take `⟨s₁, hs₁⟩` from `exists_sec P.isLB (φ' := fun _ : Fin 1 => (snd (baseOver (Spec (CommRingCat.of K))) P.A).left) (ε' := fun _ => ((n * n : ℕ) : ℤ)) (fun U _ h => by`. Rewrite using `[hk]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, Fintype.prod_sum_type, em, -Over.snd_left])`. Use the proof step `(pullMulSec (L := P.L) (φ := fun _ : Fin 1 => (snd (baseOver (Spec (CommRingCat.of K))) P.A).left) (ε := fun _ => 1) th (mulT P.A (baseOver _) n).left (LB.pullGen P.L _ _ α (snd _ P.A).left) (DVR.pullGen_isGen _ _ _ _ hα _))`. Establish `hv : ∀ (Z : Scheme.{0}) r (y : Z) J, Good P.L y J → ∃ c : (Z.presheaf.stalk y)ˣ, powVal (a` using `((n * n : ℕ) : ℤ)) s₁ r y J = powVal th (r ≫ (mulT P.A (baseOver _) n).left) y J * c.val := fun Z r y J hJ => ⟨_, (hs₁ Z r y J hJ).trans (sval_pullMulSec _ _ _ _ r y hJ)⟩`. Set `B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)` to `{q | ∃ w, (w ^ n) ^ n = 1 ∧ q = b * w}`.

Break down `hirr K P (n * n) (Or.inr h4) (by push_cast; exact mul_ne_zero hnK hnK) (vanishing P.L _ B) (fun θ s s' h hsB q ⟨w, hw, hq⟩ y J hJ => by` into its components or cases. Take `⟨c, hc⟩` from `powVal_act h (ptSecT P.A q).left hJ`. Rewrite `hc` using `[← Over.comp_left, ptSecT_translT]`. Use `(congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr (Ideal.mul_mem_left _ _ (hsB _ ⟨θ.pt * w, ?_, ?_⟩ y J hJ))` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow, hw, thetaGrp_pt_pow P n α hα hk θ, _root_.one_mul]`.

Rewrite using `[hq, mul_left_comm]) with h | h`. Establish `hm : SecM.ofSec P.A (a` using `((n * n : ℕ) : ℤ)) s₁ ∈ vanishing P.L _ B := by`. Introduce and unpack `q ⟨w, hw, rfl⟩ y J hJ`. Take `⟨c, hc⟩` from `hv _ (ptSecT P.A (b * w)).left y J hJ`. Rewrite `hc` using `[← Over.comp_left, ptSecT_mulT, mul_pow]`.

Use `(congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr (Ideal.mul_mem_right _ _ fun hu => hcon ?_)` and prove the remaining obligations. Take `⟨τ, hτ, hval⟩` from `exists_frame_of_isUnit th (b ^ n * w ^ n) hJ hu`. Establish `: Nonempty (⊤ : (baseOver (Spec (CommRingCat.of K))).left.Opens)` using `⟨⟨z, trivial⟩⟩`. Conclude with `⟨w ^ n, hw, τ, 1, hτ, hval, one_ne_zero⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`.

Use `hth (Subtype.ext (funext fun j => ?_))` and prove the remaining obligations. Establish `: IsIso (unitInv P.A).left` using `inferInstanceAs (IsIso ((Over.forget _).map (unitInv P.A)))`. Use `sec_eq_zero_of_flat P.isLB ((mulA P.A n).left ≫ (unitInv P.A).left) th (fun y J hJ => ?_) j` and prove the remaining obligations. Take `⟨c, hc⟩` from `hv _ (unitInv P.A).left y J hJ`. Rewrite `hc` using `[← Over.comp_left, unitInv_mulT, Over.comp_left]`.

Use `(Units.mul_left_eq_zero c).1 (hc.symm.trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (gs _ y _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ y _)`. Take `⟨s, τ, v, -, hval, hv⟩` from `hgen _ P K (𝟙 _) (n * n) (by omega) b choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ z)`. Establish `hm : SecM.ofSec P.A s ∈ vanishing P.L _ B` using `by rw [h]; trivial`. Conclude with `hm b ⟨1, by rw [one_pow, one_pow], (_root_.mul_one b).symm⟩ z J hJ (isUnit_powVal hval hv hJ)`.
-/
theorem goodPt_of_irred_of_mulPull :
    IrredSt → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v) → GoodPtSt := by
  intro hirr hpull hmul hgen K _ _ P n hn hnK th hth a
  obtain ⟨h1, -, h3, h4⟩ := hmul _ P n (by omega)
  have : Etale (mulA P.A n).left := h4 (by
    simpa using (Ne.isUnit hnK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have hs : Subsingleton (baseOver (Spec (CommRingCat.of K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have z : (baseOver (Spec (CommRingCat.of K))).left := IsLocalRing.closedPoint K
  obtain ⟨α, hα⟩ := hpull _ P n
  obtain ⟨b, rfl⟩ := exists_pow_eq P n a
  by_contra hcon
  have h4 : 4 ≤ n * n := by nlinarith
  have hk : ((n * n : ℕ) : ℤ) = (n : ℤ) ^ 2 := by push_cast; ring
  have em : (mulT P.A (baseOver (Spec (CommRingCat.of K))) n).left ≫ (snd _ P.A).left =
      (snd _ P.A).left ≫ (mulA P.A n).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_mulA, mulT, lift_snd]
  obtain ⟨s₁, hs₁⟩ := exists_sec P.isLB
    (φ' := fun _ : Fin 1 => (snd (baseOver (Spec (CommRingCat.of K))) P.A).left) (ε' := fun _ => ((n * n : ℕ) : ℤ))
    (fun U _ h => by
      rw [hk]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, em, -Over.snd_left])
    (pullMulSec (L := P.L) (φ := fun _ : Fin 1 => (snd (baseOver (Spec (CommRingCat.of K))) P.A).left)
      (ε := fun _ => 1) th (mulT P.A (baseOver _) n).left (LB.pullGen P.L _ _ α (snd _ P.A).left)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have hv : ∀ (Z : Scheme.{0}) r (y : Z) J, Good P.L y J → ∃ c : (Z.presheaf.stalk y)ˣ,
      powVal (a := ((n * n : ℕ) : ℤ)) s₁ r y J = powVal th (r ≫ (mulT P.A (baseOver _) n).left) y J * c.val :=
    fun Z r y J hJ => ⟨_, (hs₁ Z r y J hJ).trans (sval_pullMulSec _ _ _ _ r y hJ)⟩
  let B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := {q | ∃ w, (w ^ n) ^ n = 1 ∧ q = b * w}
  rcases hirr K P (n * n) (Or.inr h4) (by push_cast; exact mul_ne_zero hnK hnK) (vanishing P.L _ B)
    (fun θ s s' h hsB q ⟨w, hw, hq⟩ y J hJ => by
      obtain ⟨c, hc⟩ := powVal_act h (ptSecT P.A q).left hJ
      rw [← Over.comp_left, ptSecT_translT] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr (Ideal.mul_mem_left _ _ (hsB _ ⟨θ.pt * w, ?_, ?_⟩ y J hJ))
      · rw [mul_pow, mul_pow, hw, thetaGrp_pt_pow P n α hα hk θ, _root_.one_mul]
      · rw [hq, mul_left_comm]) with h | h
  · have hm : SecM.ofSec P.A (a := ((n * n : ℕ) : ℤ)) s₁ ∈ vanishing P.L _ B := by
      rintro q ⟨w, hw, rfl⟩ y J hJ
      obtain ⟨c, hc⟩ := hv _ (ptSecT P.A (b * w)).left y J hJ
      rw [← Over.comp_left, ptSecT_mulT, mul_pow] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr (Ideal.mul_mem_right _ _ fun hu => hcon ?_)
      obtain ⟨τ, hτ, hval⟩ := exists_frame_of_isUnit th (b ^ n * w ^ n) hJ hu
      have : Nonempty (⊤ : (baseOver (Spec (CommRingCat.of K))).left.Opens) := ⟨⟨z, trivial⟩⟩
      exact ⟨w ^ n, hw, τ, 1, hτ, hval, one_ne_zero⟩
    rw [h, Submodule.mem_bot] at hm
    refine hth (Subtype.ext (funext fun j => ?_))
    have : IsIso (unitInv P.A).left := inferInstanceAs (IsIso ((Over.forget _).map (unitInv P.A)))
    refine sec_eq_zero_of_flat P.isLB ((mulA P.A n).left ≫ (unitInv P.A).left) th (fun y J hJ => ?_) j
    obtain ⟨c, hc⟩ := hv _ (unitInv P.A).left y J hJ
    rw [← Over.comp_left, unitInv_mulT, Over.comp_left] at hc
    refine (Units.mul_left_eq_zero c).1 (hc.symm.trans ?_)
    exact (congrArg (gs _ y _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ y _)
  · obtain ⟨s, τ, v, -, hval, hv⟩ := hgen _ P K (𝟙 _) (n * n) (by omega) b
    choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ z)
    have hm : SecM.ofSec P.A s ∈ vanishing P.L _ B := by rw [h]; trivial
    exact hm b ⟨1, by rw [one_pow, one_pow], (_root_.mul_one b).symm⟩ z J hJ (isUnit_powVal hval hv hJ)

/- English proof (translation)
Introduce `_ hirr _ _` and use `goodPt_of_irred_of_mulPull hirr`.
-/
theorem goodPt_of_irred :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → IrredSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v) → GoodPtSt :=
  fun _ hirr _ _ => goodPt_of_irred_of_mulPull hirr

end GlobalTheory.GoodPoint
