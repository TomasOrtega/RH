import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsReducedCombination
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace Regular

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`.

Establish `hfin : {v | ¬ (0 : ℝ) ≤ q v}.Finite` using `Filter.eventually_cofinite.1 (h.eventually_ge_atTop 0)`. Establish `hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x`. Introduce `a b hab`. Use `smul_left_injective ℤ hx0 hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_le, QuadraticMap.map_smul, zsmul_eq_mul]`. Use `mul_neg_of_pos_of_neg ?_ hx` and prove the remaining obligations. Check the signs of the components of the expression.
-/
theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hx
  push_neg at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hfin : {v | ¬ (0 : ℝ) ≤ q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_ge_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_le, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_neg_of_pos_of_neg ?_ hx
  positivity

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
Unfold `ThetaSys.FF`. Use `finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_` and prove the remaining obligations. Conclude with `mul_mem (S.R.algebraMap_mem _) (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))`.
-/
theorem FF_mem (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _) (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

/- English proof (translation)
Introduce `_ ha x hx` and use `ha x (h hx)`.
-/
theorem perp_anti (S : ThetaSys o Ω) {H H' : AddSubgroup S.Gam} (h : H ≤ H') : S.perp H' ≤ S.perp H :=
  fun _ ha x hx => ha x (h hx)

variable {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}

/- English proof (translation)
The claim follows from `map_pow (RatModel.valHomOf y z h) ⟨a, ha⟩ n`.
-/
theorem val_pow (h : ∀ w, y w ⤳ z) {a : Ω} (ha : a ∈ M.O z) (n : ℕ) : M.val y (a ^ n) = M.val y a ^ n :=
  map_pow (RatModel.valHomOf y z h) ⟨a, ha⟩ n

/- English proof (translation)
Use `map_prod (RatModel.valHomOf y z h) (fun i => ⟨a i, ha i⟩) s` as an intermediate fact. Rewrite `this` using `[RatModel.valHomOf_apply, SubmonoidClass.coe_finset_prod]`. Conclude with `this`.
-/
theorem val_prod (h : ∀ w, y w ⤳ z) {I : Type} (s : Finset I) {a : I → Ω} (ha : ∀ i, a i ∈ M.O z) :
    M.val y (∏ i ∈ s, a i) = ∏ i ∈ s, M.val y (a i) := by
  have := map_prod (RatModel.valHomOf y z h) (fun i => ⟨a i, ha i⟩) s
  rw [RatModel.valHomOf_apply, SubmonoidClass.coe_finset_prod] at this
  exact this

/- English proof (translation)
Use `RatModel.val_mul h ha ha'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ h0, RatModel.val_one]`. Conclude with `left_ne_zero_of_mul_eq_one this.symm`.
-/
theorem val_ne_zero (h : ∀ w, y w ⤳ z) {a : Ω} (h0 : a ≠ 0) (ha : a ∈ M.O z) (ha' : a⁻¹ ∈ M.O z) :
    M.val y a ≠ 0 := by
  have := RatModel.val_mul h ha ha'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  exact left_ne_zero_of_mul_eq_one this.symm

/- English proof (translation)
Distinguish the cases in `h0 : b = 0`. Simplify using `[h0, RatModel.val_zero]`. Use `RatModel.val_mul h hb hb'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ h0, RatModel.val_one]`. Rewrite using `[div_eq_mul_inv, RatModel.val_mul h ha hb', div_eq_mul_inv, eq_inv_of_mul_eq_one_right this.symm]`.
-/
theorem val_div (h : ∀ w, y w ⤳ z) {a b : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb' : b⁻¹ ∈ M.O z) :
    M.val y (a / b) = M.val y a / M.val y b := by
  by_cases h0 : b = 0
  · simp [h0, RatModel.val_zero]
  have := RatModel.val_mul h hb hb'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  rw [div_eq_mul_inv, RatModel.val_mul h ha hb', div_eq_mul_inv, eq_inv_of_mul_eq_one_right this.symm]

/- English proof (translation)
Rewrite using `[mul_div_cancel_left₀ _ hδ.ne', div_le_one (by positivity)]`. Establish `h1 : f' / δ ≤ Real.exp (-a')` using `by rwa [div_le_iff₀' hδ]`. Establish `h2 : ∏ x, t x / δ ≤ Real.exp (-∑ x, v x)`. Rewrite using `[← Finset.sum_neg_distrib, Real.exp_sum]`. Use `Finset.prod_le_prod (fun x _ => div_nonneg (ht0 x) hδ.le) fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀' hδ]`. Conclude with `ht x`. Establish `h3 : 0 ≤ ∏ x, t x / δ` using `Finset.prod_nonneg fun x _ => div_nonneg (ht0 x) hδ.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ratio_le_one {I : Type} [Fintype I] {δ a a' f' : ℝ} {t v : I → ℝ} (hδ : 0 < δ) (hf0 : 0 ≤ f')
    (hf : f' ≤ δ * Real.exp (-a')) (ht0 : ∀ x, 0 ≤ t x) (ht : ∀ x, t x ≤ δ * Real.exp (-(v x))) {j C : ℕ}
    (h : j * a ≤ (j + 1) * a' + C * ∑ x, v x) :
    (f' / δ) ^ (j + 1) * (∏ x, t x / δ) ^ C / (δ * Real.exp (-a) / δ) ^ j ≤ 1 := by
  rw [mul_div_cancel_left₀ _ hδ.ne', div_le_one (by positivity)]
  have h1 : f' / δ ≤ Real.exp (-a') := by rwa [div_le_iff₀' hδ]
  have h2 : ∏ x, t x / δ ≤ Real.exp (-∑ x, v x) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun x _ => div_nonneg (ht0 x) hδ.le) fun x _ => ?_
    rw [div_le_iff₀' hδ]
    exact ht x
  have h3 : 0 ≤ ∏ x, t x / δ := Finset.prod_nonneg fun x _ => div_nonneg (ht0 x) hδ.le
  calc _ ≤ Real.exp (-a') ^ (j + 1) * Real.exp (-∑ x, v x) ^ C := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      push_cast
      linarith

end Regular

open Regular in

/- English proof (translation)
Introduce `o Ω _ _ _ _ S M U₀ hO hLL hT h0 hI h01 h11 h12 z ξ c c' k k' hz hξ hcc hk hk' x₀ hx₀ j hj`. Establish `hN : 1 ≤ S.N` using `le_trans one_le_two S.N_ge`. Establish `hr` using `S.r_pos`. Use `haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩`. Use `haveI : Fintype (S.supI M ξ) := Fintype.ofFinite _`.

Use `⟨j * (j + 1) * Fintype.card (S.supI M ξ) * S.N * (S.r * S.N) ^ 2, ?_⟩` and prove the remaining obligations. Rewrite using `[← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]`. Establish `hth : ∀ x, S.th x ∈ M.ringOn U₀` using `fun x => hO.le (S.th_mem x)`. Establish `hx0 : (S.th x₀)⁻¹ ∈ M.ringOn U₀` using `hO.th_unit _ hx₀.1`. Establish `hf : S.FF _ c k ∈ M.ringOn U₀` using `hO.le (FF_mem S _ c k)`.

Establish `hf' : S.FF _ c' k' ∈ M.ringOn U₀` using `hO.le (FF_mem S _ c' k')`. Establish `hfi : (S.FF _ c k)⁻¹ ∈ M.ringOn U₀` using `hO.FF_unit _ c k (hI.1 z).1 hk.1`. Establish `e1 : S.FF _ c' k' / S.th x₀ ∈ M.ringOn U₀`. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem hf' hx0`.

Establish `e2 : ∀ x, S.th x / S.th x₀ ∈ M.ringOn U₀` using `fun x => by`. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem (hth x) hx0`. Establish `e3 : S.FF _ c k / S.th x₀ ∈ M.ringOn U₀`. Rewrite using `[div_eq_mul_inv]`.

Conclude with `mul_mem hf hx0`. Establish `e4 : ((S.FF _ c k / S.th x₀) ^ j)⁻¹ ∈ M.ringOn U₀`. Rewrite using `[← inv_pow, inv_div, div_eq_mul_inv]`. Conclude with `pow_mem (mul_mem (hth _) hfi) j`. Establish `e5 : ∏ x : S.supI M ξ, S.th x / S.th x₀ ∈ M.ringOn U₀` using `prod_mem fun x _ => e2 x`.

Use `(hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ fun p _ y hy => ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem (mul_mem (pow_mem e1 _) (pow_mem e5 _)) e4`. Take `⟨y₀, hAt, hint, ⟨τ⟩⟩` from `hT z p y hy`. Take `⟨hsup, hH⟩` from `h0 z p y y₀ τ hy hAt`.

Use `set w₀ := (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw₀`. Establish `hs : ∀ w, (gPt p ≫ y) w ⤳ w₀` using `RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)`. Establish `hle : M.ringOn U₀ ≤ M.O w₀` using `RatModel.ringOn_le_O (hy.2 ⟨_, rfl⟩)`. Establish `hTz : S.TT M z = S.perp τ.yy.ker` using `by rw [ThetaSys.TT, hH]`. Establish `hTT : S.TT M ξ ≤ S.TT M z` using `perp_anti S (AddSubgroup.closure_mono (hI.2.1 ξ z hξ))`.

Establish `hTξ : S.TT M ξ ≤ S.perp τ.yy.ker` using `hTT.trans hTz.le`. Take `⟨α, hα, hwα⟩` from `(h01 p y₀ τ).1 (c.comp (AddSubgroup.inclusion hTz.ge))`. Establish `hcα : ∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩` using `fun t h₁ h₂ => by rw [hwα]; rfl`. Establish `hvf` using `h12 z p y y₀ τ hy hAt c k α hk hα hcα`. Take `⟨β, -, hcβ, hvf'⟩` from `(h11 p y₀ τ hint _ c' k' (FF_mem S _ c' k') (hI.1 ξ).1).2 hTξ`.

Rewrite `hvf'` using `[hAt]`. Establish `hex : ∀ x : S.Gam, ∃ w : τ.X, τ.yy x = QuotientAddGroup.mk w ∧ (x ∈ S.supI M ξ → ‖M.val (gPt p ≫ y) (S.th x)‖ ≤ τ.δ * Real.exp (-(τ.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2)))`. Introduce `x`. Distinguish the cases in `hx : x ∈ S.supI M ξ`. Take `⟨w, h1, h2⟩` from `τ.tx x (by`.

Rewrite using `[hAt]`. Conclude with `val_ne_zero hs hx.1 (hle (hth x)) (hle (hO.th_unit x hx.1)))`. Rewrite `h2` using `[hAt]`. Conclude with `⟨w, h1, fun _ => h2⟩`. Take `⟨w, hw⟩` from `QuotientAddGroup.mk_surjective (τ.yy x)`.

Conclude with `⟨w, hw.symm, fun h => absurd h hx⟩`. Use `choose w hw hwv using hex`. Establish `hmem` using `((h01 p y₀ τ).2 _ (hI.1 ξ).1 hTξ w hw (S.supI M ξ) (hI.1 ξ).2.symm (α - β)).1 (fun t h₂ h₁ => by`. Rewrite using `[map_sub, AddMonoidHom.sub_apply, ← hcβ t h₁ h₂, ← hcα t (hTT h₁) h₂, hcc t (hTT h₁) h₁, sub_self])`. Rewrite `hmem` using `[Set.image_eq_range]`.

Establish `hNpos : (0 : ℝ) < S.N` using `by exact_mod_cast hN`. Establish `hN'pos : (0 : ℝ) < ((S.r * S.N : ℕ) : ℝ)` using `by exact_mod_cast NeZero.pos _`. Take `⟨v₁, hv₁⟩` from `lattice_inequality τ.X τ.q (nonneg_of_tendsto τ.q τ.pos) (S.supI M ξ) S.N (S.r * S.N) j hN (dvd_mul_left _ _) hj (fun x => w x) (fun x => w x) (fun x => τ.q (w x) / ((S.r * S.N : ℕ) : ℝ) ^ 2) β α (τ.q β / S.N) (fun x => ⟨0, by simp⟩) (fun x => by rw [mul_div_cancel₀ _ (by positiv …`. Establish `hfin` using `le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hα v₁) hNpos.le) (Nat.cast_nonneg j)) hv₁`. Use `ratio_le_one τ.δ_pos (norm_nonneg _) hvf' (fun x : S.supI M ξ => norm_nonneg _) (fun x => hwv x x.2) hfin` as an intermediate fact.

Rewrite using `[val_div hs (hle (mul_mem (pow_mem e1 _) (pow_mem e5 _))) (hle (pow_mem e3 _)) (hle e4), RatModel.val_mul hs (hle (pow_mem e1 _)) (hle (pow_mem e5 _)), val_pow hs (hle e1), val_pow hs (hle e5), val_pow hs (hle e3), val_prod hs _ (fun x : S.supI M ξ => hle (e2 x)), val_div hs (hle …`. Simplify using `only [fun x => val_div hs (hle (hth x)) (hle (hth _)) (hle hx0), norm_div, norm_mul, norm_pow, norm_prod]`. Rewrite using `[(hsup x₀).1 hx₀, hvf]`. Conclude with `this`.
-/
theorem comparison_function_regular : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT h0 hI h01 h11 h12 z ξ c c' k k' hz hξ hcc hk hk' x₀ hx₀ j hj
  have hN : 1 ≤ S.N := le_trans one_le_two S.N_ge
  have hr := S.r_pos
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  haveI : Fintype (S.supI M ξ) := Fintype.ofFinite _
  refine ⟨j * (j + 1) * Fintype.card (S.supI M ξ) * S.N * (S.r * S.N) ^ 2, ?_⟩
  rw [← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]
  have hth : ∀ x, S.th x ∈ M.ringOn U₀ := fun x => hO.le (S.th_mem x)
  have hx0 : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit _ hx₀.1
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FF_mem S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (FF_mem S _ c' k')
  have hfi : (S.FF _ c k)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c k (hI.1 z).1 hk.1
  have e1 : S.FF _ c' k' / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf' hx0
  have e2 : ∀ x, S.th x / S.th x₀ ∈ M.ringOn U₀ := fun x => by
    rw [div_eq_mul_inv]; exact mul_mem (hth x) hx0
  have e3 : S.FF _ c k / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf hx0
  have e4 : ((S.FF _ c k / S.th x₀) ^ j)⁻¹ ∈ M.ringOn U₀ := by
    rw [← inv_pow, inv_div, div_eq_mul_inv]; exact pow_mem (mul_mem (hth _) hfi) j
  have e5 : ∏ x : S.supI M ξ, S.th x / S.th x₀ ∈ M.ringOn U₀ := prod_mem fun x _ => e2 x
  refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ fun p _ y hy => ?_
  · rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (pow_mem e1 _) (pow_mem e5 _)) e4
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
  obtain ⟨hsup, hH⟩ := h0 z p y y₀ τ hy hAt
  set w₀ := (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw₀
  have hs : ∀ w, (gPt p ≫ y) w ⤳ w₀ :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hle : M.ringOn U₀ ≤ M.O w₀ := RatModel.ringOn_le_O (hy.2 ⟨_, rfl⟩)
  have hTz : S.TT M z = S.perp τ.yy.ker := by rw [ThetaSys.TT, hH]
  have hTT : S.TT M ξ ≤ S.TT M z := perp_anti S (AddSubgroup.closure_mono (hI.2.1 ξ z hξ))
  have hTξ : S.TT M ξ ≤ S.perp τ.yy.ker := hTT.trans hTz.le
  obtain ⟨α, hα, hwα⟩ := (h01 p y₀ τ).1 (c.comp (AddSubgroup.inclusion hTz.ge))
  have hcα : ∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩ :=
    fun t h₁ h₂ => by rw [hwα]; rfl
  have hvf := h12 z p y y₀ τ hy hAt c k α hk hα hcα
  obtain ⟨β, -, hcβ, hvf'⟩ := (h11 p y₀ τ hint _ c' k' (FF_mem S _ c' k') (hI.1 ξ).1).2 hTξ
  rw [hAt] at hvf'
  have hex : ∀ x : S.Gam, ∃ w : τ.X, τ.yy x = QuotientAddGroup.mk w ∧ (x ∈ S.supI M ξ →
      ‖M.val (gPt p ≫ y) (S.th x)‖ ≤ τ.δ * Real.exp (-(τ.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
    intro x
    by_cases hx : x ∈ S.supI M ξ
    · obtain ⟨w, h1, h2⟩ := τ.tx x (by
        rw [hAt]
        exact val_ne_zero hs hx.1 (hle (hth x)) (hle (hO.th_unit x hx.1)))
      rw [hAt] at h2
      exact ⟨w, h1, fun _ => h2⟩
    · obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
      exact ⟨w, hw.symm, fun h => absurd h hx⟩
  choose w hw hwv using hex
  have hmem := ((h01 p y₀ τ).2 _ (hI.1 ξ).1 hTξ w hw (S.supI M ξ) (hI.1 ξ).2.symm (α - β)).1
    (fun t h₂ h₁ => by
      rw [map_sub, AddMonoidHom.sub_apply, ← hcβ t h₁ h₂, ← hcα t (hTT h₁) h₂, hcc t (hTT h₁) h₁, sub_self])
  rw [Set.image_eq_range] at hmem
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast hN
  have hN'pos : (0 : ℝ) < ((S.r * S.N : ℕ) : ℝ) := by exact_mod_cast NeZero.pos _
  obtain ⟨v₁, hv₁⟩ := lattice_inequality τ.X τ.q (nonneg_of_tendsto τ.q τ.pos) (S.supI M ξ) S.N (S.r * S.N) j hN
    (dvd_mul_left _ _) hj (fun x => w x) (fun x => w x) (fun x => τ.q (w x) / ((S.r * S.N : ℕ) : ℝ) ^ 2) β α
    (τ.q β / S.N) (fun x => ⟨0, by simp⟩) (fun x => by rw [mul_div_cancel₀ _ (by positivity)])
    (by rw [mul_div_cancel₀ _ hNpos.ne']) hmem
  have hfin := le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hα v₁) hNpos.le)
    (Nat.cast_nonneg j)) hv₁
  have := ratio_le_one τ.δ_pos (norm_nonneg _) hvf' (fun x : S.supI M ξ => norm_nonneg _)
    (fun x => hwv x x.2) hfin
  rw [val_div hs (hle (mul_mem (pow_mem e1 _) (pow_mem e5 _))) (hle (pow_mem e3 _)) (hle e4),
    RatModel.val_mul hs (hle (pow_mem e1 _)) (hle (pow_mem e5 _)), val_pow hs (hle e1), val_pow hs (hle e5),
    val_pow hs (hle e3), val_prod hs _ (fun x : S.supI M ξ => hle (e2 x)),
    val_div hs (hle hf') (hle (hth _)) (hle hx0), val_div hs (hle hf) (hle (hth _)) (hle hx0)]
  simp only [fun x => val_div hs (hle (hth x)) (hle (hth _)) (hle hx0), norm_div, norm_mul, norm_pow, norm_prod]
  rw [(hsup x₀).1 hx₀, hvf]
  exact this

end GlobalTheory.ZH
