import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Close
variable {k : Type} [Field k]

/- English proof (translation)
Simplify using `[vv]`.
-/
theorem vv_alg : vv k = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := by
  simp [vv]

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V]

omit [Module k V] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨x, hx, by simp⟩`.
-/
theorem mem_sh_of (a : ℕ) (N : Submodule k⟦X⟧ V) {x : V} (hx : x ∈ N) : vv k ^ a • x ∈ sh a N :=
  ⟨x, hx, by simp⟩

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
omit [Module k V] in
/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `_root_.GlobalTheory.PhiGam.mem_sh_iff_exists.mp hx`. Simplify `h y hy` using `[zpow_natCast]`.
-/
theorem _root_.GlobalTheory.PhiGam.Close.sh_le {a : ℕ} {N N' : Submodule k⟦X⟧ V}
    (h : ∀ x ∈ N, _root_.GlobalTheory.PhiGam.vv k ^ a • x ∈ N') :
    _root_.GlobalTheory.PhiGam.sh a N ≤ N' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.mp hx
  simpa [zpow_natCast] using h y hy

omit [Module k V] in
/- English proof (translation)
Use extensionality with `x`. Simplify using `[sh]`.
-/
theorem sh_zero (N : Submodule k⟦X⟧ V) : sh (-0) N = N := by
  ext x; simp [sh]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.PhiGam.vv_eq_coe_X, map_pow]`.
-/
private lemma laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma (n : ℕ) :
    _root_.GlobalTheory.PhiGam.vv k ^ n = HahnSeries.ofPowerSeries ℤ k (PowerSeries.X ^ n) := by
  rw [_root_.GlobalTheory.PhiGam.vv_eq_coe_X, map_pow]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
omit [Module k V] in
/- English proof (translation)
Establish `key : _root_.GlobalTheory.PhiGam.vv k ^ b • x = (PowerSeries.X ^ (b - a) : k⟦X⟧) • (_root_.GlobalTheory.PhiGam.vv k ^ a • x)`. Rewrite using `[← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ (b - a) : k⟦X⟧) (_root_.GlobalTheory.PhiGam.vv k ^ a • x), LaurentSeries.coe_algebraMap, ← laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, smul_smul, ← pow_add, Nat.sub_add_cancel hab]`. Rewrite using `[key]`. Conclude with `N.smul_mem _ h`.
-/
theorem _root_.GlobalTheory.PhiGam.Close.pow_smul_mem {N : Submodule k⟦X⟧ V} {a b : ℕ} (hab : a ≤ b) {x : V}
    (h : _root_.GlobalTheory.PhiGam.vv k ^ a • x ∈ N) :
    _root_.GlobalTheory.PhiGam.vv k ^ b • x ∈ N := by
  have key : _root_.GlobalTheory.PhiGam.vv k ^ b • x =
      (PowerSeries.X ^ (b - a) : k⟦X⟧) • (_root_.GlobalTheory.PhiGam.vv k ^ a • x) := by
    rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ (b - a) : k⟦X⟧) (_root_.GlobalTheory.PhiGam.vv k ^ a • x),
      LaurentSeries.coe_algebraMap, ← laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, smul_smul,
      ← pow_add, Nat.sub_add_cancel hab]
  rw [key]
  exact N.smul_mem _ h

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
/- English proof (translation)
Establish `e` using `c.single_order_mul_powerSeriesPart`. Generalize the expression as in `c.order = t at e ⊢`. Generalize the expression as in `c.powerSeriesPart = p at e`. Substitute `e` using the available equality. Use `⟨(-t).toNat, PowerSeries.X ^ (t + (-t).toNat).toNat * p, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, HahnSeries.ofPowerSeries_X_pow, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul]`. Establish `h : (((t + ((-t).toNat : ℤ)).toNat : ℕ) : ℤ) = ((-t).toNat : ℤ) + t` using `by omega`. Rewrite using `[h]`.
-/
private lemma exists_laurentVariable_pow_mul_eq_ofPowerSeries_lemma_2 (c : k⸨X⸩) :
    ∃ (b : ℕ) (p : k⟦X⟧), _root_.GlobalTheory.PhiGam.vv k ^ b * c = HahnSeries.ofPowerSeries ℤ k p := by
  have e := c.single_order_mul_powerSeriesPart
  generalize c.order = t at e ⊢
  generalize c.powerSeriesPart = p at e
  subst e
  refine ⟨(-t).toNat, PowerSeries.X ^ (t + (-t).toNat).toNat * p, ?_⟩
  rw [map_mul, laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, HahnSeries.ofPowerSeries_X_pow,
    HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
  have h : (((t + ((-t).toNat : ℤ)).toNat : ℕ) : ℤ) = ((-t).toNat : ℤ) + t := by omega
  rw [h]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
/- English proof (translation)
Establish `hq` using `Nat.lt_mul_div_succ m hl`. Generalize the expression as in `m / l = q at hq ⊢`. Distinguish the cases in `hc0 : c = 0`. Conclude with `⟨0, by simp [hc0]⟩`. Establish `hp0 : PowerSeries.constantCoeff c.powerSeriesPart ≠ 0`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff]`. Simplify using `using (mt HahnSeries.coeff_order_eq_zero.mp hc0)`. Establish `e` using `c.single_order_mul_powerSeriesPart`. Generalize the expression as in `c.order = t at e`. Generalize the expression as in `c.powerSeriesPart = p at e hp0`.

Substitute `e` using the available equality. Distinguish the cases in `ht : -(q : ℤ) ≤ t`. Use `⟨PowerSeries.X ^ ((q : ℤ) + t).toNat * p, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, HahnSeries.ofPowerSeries_X_pow, laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul]`. Establish `h : ((((q : ℤ) + t).toNat : ℕ) : ℤ) = (q : ℤ) + t` using `by omega`.

Rewrite using `[h]`. It suffices to derive a contradiction. Use `push_neg at ht`. Take `⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = -t` from `⟨(-t).toNat, by omega⟩`. Establish `hms : m < l * s` using `lt_of_lt_of_le hq (Nat.mul_le_mul_left l (by omega))`.

Take `⟨b, hb⟩` from `R.φ_int p`. Take `⟨b', hb'⟩` from `R.φ_int p⁻¹`. Establish `hbb : b * b' = 1` using `(HahnSeries.ofPowerSeries_injective : Function.Injective (HahnSeries.ofPowerSeries ℤ k)) (by`. Rewrite using `[map_mul, ← hb, ← hb', ← map_mul, ← map_mul, PowerSeries.mul_inv_cancel _ hp0, map_one, map_one])`. Establish `hb0 : PowerSeries.constantCoeff b ≠ 0` using `fun h0 => by`.

Use `congrArg PowerSeries.constantCoeff hbb` as an intermediate fact. Simplify using `[h0] at this`. Take `⟨u, hu⟩` from `R.φ_v`. Take `⟨q', hq'⟩` from `hc`. Establish `e1 : _root_.GlobalTheory.PhiGam.vv k ^ s * ((HahnSeries.single t) 1 * (HahnSeries.ofPowerSeries ℤ k) p) = HahnSeries.ofPowerSeries ℤ k p`.

Rewrite using `[laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul, hs, neg_add_cancel]`. Conclude with `one_mul _`. Establish `e2 : (HahnSeries.ofPowerSeries ℤ k (u : k⟦X⟧) * _root_.GlobalTheory.PhiGam.vv k ^ l) ^ s * R.φ ((HahnSeries.single t) 1 * (HahnSeries.ofPowerSeries ℤ k) p) = HahnSeries.ofPowerSeries ℤ k b`. Rewrite using `[← hu, ← map_pow, ← map_mul, e1, hb]`. Establish `rhs : HahnSeries.ofPowerSeries ℤ k ((u : k⟦X⟧) ^ s * PowerSeries.X ^ (l * s - m) * q') = (HahnSeries.ofPowerSeries ℤ k (u : k⟦X⟧)) ^ s * _root_.GlobalTheory.PhiGam.vv k ^ (l * s - m) * HahnSeries.ofPowerSeries ℤ k q'`.

Rewrite using `[laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, map_mul, map_mul, map_pow]`. Establish `split : _root_.GlobalTheory.PhiGam.vv k ^ (l * s) = _root_.GlobalTheory.PhiGam.vv k ^ (l * s - m) * _root_.GlobalTheory.PhiGam.vv k ^ m`. Rewrite using `[← pow_add, Nat.sub_add_cancel hms.le]`. Establish `e3 : HahnSeries.ofPowerSeries ℤ k b = HahnSeries.ofPowerSeries ℤ k ((u : k⟦X⟧) ^ s * PowerSeries.X ^ (l * s - m) * q')`. Rewrite using `[← e2, rhs, hq', mul_pow, ← pow_mul, split]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e4` using `congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective e3)`. Establish `hpos : 0 < l * s - m` using `by omega`. Simplify using `[PowerSeries.constantCoeff_X, zero_pow hpos.ne'] at e4`. Conclude with `hb0 e4`.
-/
private lemma laurentVariable_pow_mul_mem_of_frobenius_lemma_3 {l : ℕ} (hl : 0 < l) (R : _root_.GlobalTheory.PhiGam.RingPG k l) (m : ℕ) (c : k⸨X⸩)
    (hc : _root_.GlobalTheory.PhiGam.vv k ^ m * R.φ c ∈ Set.range (HahnSeries.ofPowerSeries ℤ k)) :
    _root_.GlobalTheory.PhiGam.vv k ^ (m / l) * c ∈ Set.range (HahnSeries.ofPowerSeries ℤ k) := by
  have hq := Nat.lt_mul_div_succ m hl
  generalize m / l = q at hq ⊢
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  have hp0 : PowerSeries.constantCoeff c.powerSeriesPart ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff]
    simpa using (mt HahnSeries.coeff_order_eq_zero.mp hc0)
  have e := c.single_order_mul_powerSeriesPart
  generalize c.order = t at e
  generalize c.powerSeriesPart = p at e hp0
  subst e
  by_cases ht : -(q : ℤ) ≤ t
  · refine ⟨PowerSeries.X ^ ((q : ℤ) + t).toNat * p, ?_⟩
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow, laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma,
      HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
    have h : ((((q : ℤ) + t).toNat : ℕ) : ℤ) = (q : ℤ) + t := by omega
    rw [h]
  exfalso
  push_neg at ht
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = -t := ⟨(-t).toNat, by omega⟩
  have hms : m < l * s := lt_of_lt_of_le hq (Nat.mul_le_mul_left l (by omega))
  obtain ⟨b, hb⟩ := R.φ_int p
  obtain ⟨b', hb'⟩ := R.φ_int p⁻¹
  have hbb : b * b' = 1 := (HahnSeries.ofPowerSeries_injective :
      Function.Injective (HahnSeries.ofPowerSeries ℤ k)) (by
    rw [map_mul, ← hb, ← hb', ← map_mul, ← map_mul, PowerSeries.mul_inv_cancel _ hp0, map_one, map_one])
  have hb0 : PowerSeries.constantCoeff b ≠ 0 := fun h0 => by
    have := congrArg PowerSeries.constantCoeff hbb
    simp [h0] at this
  obtain ⟨u, hu⟩ := R.φ_v
  obtain ⟨q', hq'⟩ := hc
  have e1 : _root_.GlobalTheory.PhiGam.vv k ^ s * ((HahnSeries.single t) 1 * (HahnSeries.ofPowerSeries ℤ k) p) =
      HahnSeries.ofPowerSeries ℤ k p := by
    rw [laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc,
      HahnSeries.single_mul_single, one_mul, hs, neg_add_cancel]
    exact one_mul _
  have e2 : (HahnSeries.ofPowerSeries ℤ k (u : k⟦X⟧) * _root_.GlobalTheory.PhiGam.vv k ^ l) ^ s *
      R.φ ((HahnSeries.single t) 1 * (HahnSeries.ofPowerSeries ℤ k) p) =
      HahnSeries.ofPowerSeries ℤ k b := by
    rw [← hu, ← map_pow, ← map_mul, e1, hb]
  have rhs : HahnSeries.ofPowerSeries ℤ k ((u : k⟦X⟧) ^ s * PowerSeries.X ^ (l * s - m) * q') =
      (HahnSeries.ofPowerSeries ℤ k (u : k⟦X⟧)) ^ s * _root_.GlobalTheory.PhiGam.vv k ^ (l * s - m) *
        HahnSeries.ofPowerSeries ℤ k q' := by
    rw [laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, map_mul, map_mul, map_pow]
  have split : _root_.GlobalTheory.PhiGam.vv k ^ (l * s) =
      _root_.GlobalTheory.PhiGam.vv k ^ (l * s - m) * _root_.GlobalTheory.PhiGam.vv k ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hms.le]
  have e3 : HahnSeries.ofPowerSeries ℤ k b =
      HahnSeries.ofPowerSeries ℤ k ((u : k⟦X⟧) ^ s * PowerSeries.X ^ (l * s - m) * q') := by
    rw [← e2, rhs, hq', mul_pow, ← pow_mul, split]
    ring
  have e4 := congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective e3)
  have hpos : 0 < l * s - m := by omega
  simp [PowerSeries.constantCoeff_X, zero_pow hpos.ne'] at e4
  exact hb0 e4

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in

/- English proof (translation)
Take `⟨hfg, hspan⟩` from `hN`. Establish `hf' : ∀ (a : k⸨X⸩) (y : V), f (a • y) = R.φ a • f y` using `hf`. Establish `smul_eq : ∀ (p : k⟦X⟧) (y : V), p • y = HahnSeries.ofPowerSeries ℤ k p • y` using `fun p y => by`. Rewrite using `[← LaurentSeries.coe_algebraMap, algebraMap_smul]`. Use `haveI : Module.Finite k⟦X⟧ N := Module.Finite.iff_fg.mpr hfg`.

Use `haveI : Module.IsTorsionFree k⟦X⟧ N := ⟨fun p hp y z hyz => by`. Establish `hp0 : HahnSeries.ofPowerSeries ℤ k p ≠ 0` using `fun h0 => hp.ne_zero ((HahnSeries.ofPowerSeries_injective : Function.Injective (HahnSeries.ofPowerSeries ℤ k)) (h0.trans (map_zero _).symm))`. Establish `h1` using `congrArg Subtype.val hyz`. Simplify using `only [Submodule.coe_smul] at h1`. Rewrite `h1` using `[smul_eq, smul_eq]`.

Conclude with `Subtype.ext (smul_right_injective V hp0 h1)⟩`. Use `haveI : Module.Free k⟦X⟧ N := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis k⟦X⟧ N`. Set `e : Module.Free.ChooseBasisIndex k⟦X⟧ N → V` to `fun i => (b i : V)`. Establish `mem_N : ∀ y ∈ N, ∃ g : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⟦X⟧, y = ∑ i, HahnSeries.ofPowerSeries ℤ k (g i) • e i`.

Introduce `y hy`. Use `⟨fun i => b.repr ⟨y, hy⟩ i, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Simplify using `only [e, ← smul_eq]`.

Conclude with `this.symm`. Establish `espan : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range e)`. Rewrite using `[← hspan]`. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `mem_N y hy`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `eindep : LinearIndependent k⸨X⸩ e`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hex` using `fun i => exists_laurentVariable_pow_mul_eq_ofPowerSeries_lemma_2 (k := k) (g i)`.

Use `choose a r hr using hex`. Use `set A := Finset.univ.sup a`. Establish `hA : ∀ i, _root_.GlobalTheory.PhiGam.vv k ^ A * g i = HahnSeries.ofPowerSeries ℤ k (PowerSeries.X ^ (A - a i) * r i)`. Introduce `i`. Rewrite using `[map_mul, ← laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, ← hr, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := a) (Finset.mem_univ i))]`.

Establish `hsum : ∑ i, (PowerSeries.X ^ (A - a i) * r i) • b i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]`. Simplify using `only [smul_eq, ← hA, ← smul_smul]`. Rewrite using `[← Finset.smul_sum]`.

Simplify using `only [e] at hg`. Rewrite using `[hg, smul_zero]`. Establish `hz` using `Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum`. Introduce `i`. Establish `h0 : _root_.GlobalTheory.PhiGam.vv k ^ A * g i = 0` using `by rw [hA, hz i, map_zero]`.

Conclude with `(mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (_root_.GlobalTheory.PhiGam.vv_ne_zero k))`. Set `eB` to `Module.Basis.mk eindep espan`. Establish `f_sum : ∀ c : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⸨X⸩, f (∑ i, c i • e i) = ∑ i, R.φ (c i) • f (e i)`. Introduce `c`. Rewrite using `[map_sum]`.

Simplify using `only [hf']`. Establish `fespan : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range (fun i => f (e i)))`. Rewrite using `[← het]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`.

Establish `hy : ∑ i, eB.repr y i • e i = y`. Simplify `eB.sum_repr y` using `only [eB, Module.Basis.mk_apply]`. Rewrite using `[← hy, f_sum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `findep : LinearIndependent k⸨X⸩ (fun i => f (e i))` using `linearIndependent_of_top_le_span_of_card_eq_finrank fespan (Module.finrank_eq_card_basis eB).symm`.

Set `fB` to `Module.Basis.mk findep fespan`. Establish `fB_repr : ∀ c : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⸨X⸩, fB.repr (∑ i, c i • f (e i)) = c`. Introduce `c`. Use `fB.repr_sum_self c` as an intermediate fact. Simplify using `only [fB, Module.Basis.mk_apply] at this`.

Conclude with `this`. Set `P : Submodule k⟦X⟧ V` to `{ carrier := {y | ∀ i, fB.repr y i ∈ Set.range (HahnSeries.ofPowerSeries ℤ k)} add_mem' := by`. Introduce and unpack `y z hy hz i`. Take `⟨p, hp⟩` from `hy i`. Take `⟨p', hp'⟩` from `hz i`.

Conclude with `⟨p + p', by simp [hp, hp']⟩`. Use the proof step `zero_mem' := fun i => ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `p y hy i`. Take `⟨p', hp'⟩` from `hy i`.

Use `⟨p * p', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hp', map_mul] }`. Establish `span_le : _root_.GlobalTheory.PhiGam.pull f N ≤ P`. Unfold `_root_.GlobalTheory.PhiGam.pull`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩ i`. Take `⟨g, rfl⟩` from `mem_N y hy`. Rewrite using `[f_sum, fB_repr]`. Take `⟨c, hc⟩` from `R.φ_int (g i)`. Conclude with `⟨c, hc.symm⟩`.

Establish `hx : ∑ i, eB.repr x i • e i = x`. Simplify `eB.sum_repr x` using `only [eB, Module.Basis.mk_apply]`. Establish `hP` using `span_le h`. Rewrite `hP` using `[← hx, f_sum, Finset.smul_sum]`. Simplify using `only [smul_smul] at hP`.

Establish `hcoef : ∀ i, _root_.GlobalTheory.PhiGam.vv k ^ (m / l) * eB.repr x i ∈ Set.range (HahnSeries.ofPowerSeries ℤ k)`. Introduce `i`. Use `hP i` as an intermediate fact. Rewrite `this` using `[fB_repr]`. Conclude with `laurentVariable_pow_mul_mem_of_frobenius_lemma_3 hl R m _ this`.

Use `choose r hr using hcoef`. Rewrite using `[← hx, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hr i, ← smul_eq]`. Conclude with `Submodule.smul_mem _ _ (b i).2`.
-/
theorem _root_.GlobalTheory.PhiGam.Close.key {l : ℕ} (hl : 0 < l)
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) [FiniteDimensional k⸨X⸩ V] (f : V →ₗ[k] V)
    (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (het : Submodule.span k⸨X⸩ (Set.range f) = ⊤) (N : Submodule k⟦X⟧ V)
    (hN : _root_.GlobalTheory.PhiGam.IsLat N) (m : ℕ) (x : V)
    (h : _root_.GlobalTheory.PhiGam.vv k ^ m • f x ∈ _root_.GlobalTheory.PhiGam.pull f N) :
    _root_.GlobalTheory.PhiGam.vv k ^ (m / l) • x ∈ N := by
  obtain ⟨hfg, hspan⟩ := hN
  have hf' : ∀ (a : k⸨X⸩) (y : V), f (a • y) = R.φ a • f y := hf
  have smul_eq : ∀ (p : k⟦X⟧) (y : V), p • y = HahnSeries.ofPowerSeries ℤ k p • y := fun p y => by
    rw [← LaurentSeries.coe_algebraMap, algebraMap_smul]
  haveI : Module.Finite k⟦X⟧ N := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree k⟦X⟧ N := ⟨fun p hp y z hyz => by
    have hp0 : HahnSeries.ofPowerSeries ℤ k p ≠ 0 := fun h0 =>
      hp.ne_zero ((HahnSeries.ofPowerSeries_injective :
        Function.Injective (HahnSeries.ofPowerSeries ℤ k)) (h0.trans (map_zero _).symm))
    have h1 := congrArg Subtype.val hyz
    simp only [Submodule.coe_smul] at h1
    rw [smul_eq, smul_eq] at h1
    exact Subtype.ext (smul_right_injective V hp0 h1)⟩
  haveI : Module.Free k⟦X⟧ N := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis k⟦X⟧ N
  let e : Module.Free.ChooseBasisIndex k⟦X⟧ N → V := fun i => (b i : V)
  have mem_N : ∀ y ∈ N, ∃ g : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⟦X⟧,
      y = ∑ i, HahnSeries.ofPowerSeries ℤ k (g i) • e i := by
    intro y hy
    refine ⟨fun i => b.repr ⟨y, hy⟩ i, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [e, ← smul_eq]
    exact this.symm
  have espan : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range e) := by
    rw [← hspan]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨g, rfl⟩ := mem_N y hy
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have eindep : LinearIndependent k⸨X⸩ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hex := fun i => exists_laurentVariable_pow_mul_eq_ofPowerSeries_lemma_2 (k := k) (g i)
    choose a r hr using hex
    set A := Finset.univ.sup a
    have hA : ∀ i, _root_.GlobalTheory.PhiGam.vv k ^ A * g i =
        HahnSeries.ofPowerSeries ℤ k (PowerSeries.X ^ (A - a i) * r i) := by
      intro i
      rw [map_mul, ← laurentSeriesVariableV_pow_eq_ofPowerSeries_lemma, ← hr, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := a) (Finset.mem_univ i))]
    have hsum : ∑ i, (PowerSeries.X ^ (A - a i) * r i) • b i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      simp only [smul_eq, ← hA, ← smul_smul]
      rw [← Finset.smul_sum]
      simp only [e] at hg
      rw [hg, smul_zero]
    have hz := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum
    intro i
    have h0 : _root_.GlobalTheory.PhiGam.vv k ^ A * g i = 0 := by rw [hA, hz i, map_zero]
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (_root_.GlobalTheory.PhiGam.vv_ne_zero k))
  let eB := Module.Basis.mk eindep espan
  have f_sum : ∀ c : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⸨X⸩,
      f (∑ i, c i • e i) = ∑ i, R.φ (c i) • f (e i) := by
    intro c
    rw [map_sum]
    simp only [hf']
  have fespan : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range (fun i => f (e i))) := by
    rw [← het]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    have hy : ∑ i, eB.repr y i • e i = y := by
      simpa only [eB, Module.Basis.mk_apply] using eB.sum_repr y
    rw [← hy, f_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have findep : LinearIndependent k⸨X⸩ (fun i => f (e i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank fespan (Module.finrank_eq_card_basis eB).symm
  let fB := Module.Basis.mk findep fespan
  have fB_repr : ∀ c : Module.Free.ChooseBasisIndex k⟦X⟧ N → k⸨X⸩,
      fB.repr (∑ i, c i • f (e i)) = c := by
    intro c
    have := fB.repr_sum_self c
    simp only [fB, Module.Basis.mk_apply] at this
    exact this
  let P : Submodule k⟦X⟧ V :=
    { carrier := {y | ∀ i, fB.repr y i ∈ Set.range (HahnSeries.ofPowerSeries ℤ k)}
      add_mem' := by
        rintro y z hy hz i
        obtain ⟨p, hp⟩ := hy i
        obtain ⟨p', hp'⟩ := hz i
        exact ⟨p + p', by simp [hp, hp']⟩
      zero_mem' := fun i => ⟨0, by simp⟩
      smul_mem' := by
        rintro p y hy i
        obtain ⟨p', hp'⟩ := hy i
        refine ⟨p * p', ?_⟩
        rw [smul_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hp', map_mul] }
  have span_le : _root_.GlobalTheory.PhiGam.pull f N ≤ P := by
    unfold _root_.GlobalTheory.PhiGam.pull
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ i
    obtain ⟨g, rfl⟩ := mem_N y hy
    rw [f_sum, fB_repr]
    obtain ⟨c, hc⟩ := R.φ_int (g i)
    exact ⟨c, hc.symm⟩
  have hx : ∑ i, eB.repr x i • e i = x := by
    simpa only [eB, Module.Basis.mk_apply] using eB.sum_repr x
  have hP := span_le h
  rw [← hx, f_sum, Finset.smul_sum] at hP
  simp only [smul_smul] at hP
  have hcoef : ∀ i, _root_.GlobalTheory.PhiGam.vv k ^ (m / l) * eB.repr x i ∈
      Set.range (HahnSeries.ofPowerSeries ℤ k) := by
    intro i
    have := hP i
    rw [fB_repr] at this
    exact laurentVariable_pow_mul_mem_of_frobenius_lemma_3 hl R m _ this
  choose r hr using hcoef
  rw [← hx, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_smul, ← hr i, ← smul_eq]
  exact Submodule.smul_mem _ _ (b i).2

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
omit [Module k V] in

/- English proof (translation)
Set `S : Submodule k⸨X⸩ V` to `{ carrier := {x | ∃ a : ℕ, _root_.GlobalTheory.PhiGam.vv k ^ a • x ∈ N'} add_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨max a b, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Conclude with `N'.add_mem (_root_.GlobalTheory.PhiGam.Close.pow_smul_mem (le_max_left a b) ha) (_root_.GlobalTheory.PhiGam.Close.pow_smul_mem (le_max_right a b) hb)`.

Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, ha⟩`. Take `⟨b, p, hp⟩` from `exists_laurentVariable_pow_mul_eq_ofPowerSeries_lemma_2 c`. Use `⟨b + a, ?_⟩` and prove the remaining obligations.

Establish `e : _root_.GlobalTheory.PhiGam.vv k ^ (b + a) * c = (_root_.GlobalTheory.PhiGam.vv k ^ b * c) * _root_.GlobalTheory.PhiGam.vv k ^ a` using `by ring`. Rewrite using `[smul_smul, e, ← smul_smul, hp, ← LaurentSeries.coe_algebraMap, algebraMap_smul]`. Conclude with `N'.smul_mem p ha }`. Establish `hS : ∀ x : V, x ∈ S`. Introduce `x`.

Establish `hle : Submodule.span k⸨X⸩ (N' : Set V) ≤ S` using `Submodule.span_le.mpr (fun y hy => ⟨0, by simpa using hy⟩)`. Rewrite `hle` using `[hN']`. Conclude with `hle Submodule.mem_top`. Use `choose f hf using hS`. Take `⟨s, hs⟩` from `hN`.

Use `⟨s.sup f, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact _root_.GlobalTheory.PhiGam.Close.pow_smul_mem (Finset.le_sup (f := f) hy) (hf y)`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `N'.add_mem hy hz`. Consider the case `smul p y _ hy`. Rewrite using `[← algebraMap_smul k⸨X⸩ p y, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]`. Conclude with `N'.smul_mem p hy`.
-/
theorem _root_.GlobalTheory.PhiGam.Close.exists_pow {N N' : Submodule k⟦X⟧ V} (hN : N.FG)
    (hN' : Submodule.span k⸨X⸩ (N' : Set V) = ⊤) :
    ∃ a : ℕ, ∀ x ∈ N, _root_.GlobalTheory.PhiGam.vv k ^ a • x ∈ N' := by
  let S : Submodule k⸨X⸩ V :=
    { carrier := {x | ∃ a : ℕ, _root_.GlobalTheory.PhiGam.vv k ^ a • x ∈ N'}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨max a b, ?_⟩
        rw [smul_add]
        exact N'.add_mem (_root_.GlobalTheory.PhiGam.Close.pow_smul_mem (le_max_left a b) ha)
          (_root_.GlobalTheory.PhiGam.Close.pow_smul_mem (le_max_right a b) hb)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        obtain ⟨b, p, hp⟩ := exists_laurentVariable_pow_mul_eq_ofPowerSeries_lemma_2 c
        refine ⟨b + a, ?_⟩
        have e : _root_.GlobalTheory.PhiGam.vv k ^ (b + a) * c = (_root_.GlobalTheory.PhiGam.vv k ^ b * c) * _root_.GlobalTheory.PhiGam.vv k ^ a := by ring
        rw [smul_smul, e, ← smul_smul, hp, ← LaurentSeries.coe_algebraMap, algebraMap_smul]
        exact N'.smul_mem p ha }
  have hS : ∀ x : V, x ∈ S := by
    intro x
    have hle : Submodule.span k⸨X⸩ (N' : Set V) ≤ S :=
      Submodule.span_le.mpr (fun y hy => ⟨0, by simpa using hy⟩)
    rw [hN'] at hle
    exact hle Submodule.mem_top
  choose f hf using hS
  obtain ⟨s, hs⟩ := hN
  refine ⟨s.sup f, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact _root_.GlobalTheory.PhiGam.Close.pow_smul_mem (Finset.le_sup (f := f) hy) (hf y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N'.add_mem hy hz
  | smul p y _ hy =>
    rw [← algebraMap_smul k⸨X⸩ p y, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact N'.smul_mem p hy

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] in
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] in

/- English proof (translation)
Unfold `_root_.GlobalTheory.PhiGam.sg`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Establish `hsum` using `_root_.GlobalTheory.PhiGam.summable_sg (l := l) (by omega) h i`. Establish `step : ∀ J : ℕ, ∀ i : ZMod n, (a i : ℝ) ≤ a (i + J) / (l : ℝ) ^ J + ∑ j ∈ Finset.range J, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)`. Introduce `J`.

Proceed by induction on `J with`. Consider the case `zero => intro i`. Simplify using the standard rewrite rules. Consider the case `succ J ih`. Introduce `i`.

Establish `h1` using `ih i`. Establish `h2 : ((l * a (i + J) : ℕ) : ℝ) ≤ ((a (i + J + 1) + h (i + J + 1) : ℕ) : ℝ)` using `by exact_mod_cast ha (i + J)`. Move the coercions through the operations in `at h2`. Establish `e : i + ((J + 1 : ℕ) : ZMod n) = i + (J : ZMod n) + 1` using `by push_cast; ring`. Rewrite using `[Finset.sum_range_succ, e]`.

Establish `hp : (0 : ℝ) < (l : ℝ) ^ (J + 1)` using `by positivity`. Establish `h3 : (a (i + J) : ℝ) / (l : ℝ) ^ J ≤ a (i + J + 1) / (l : ℝ) ^ (J + 1) + h (i + J + 1) / (l : ℝ) ^ (J + 1)`. Rewrite using `[← add_div, le_div_iff₀ hp, pow_succ, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Nat.le_floor` to reduce the goal to its premises. Use `set S := ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)`. Use `set M : ℝ := ∑ j, (a j : ℝ)`. Establish `bound : ∀ J : ℕ, (a i : ℝ) ≤ M / (l : ℝ) ^ J + S`. Introduce `J`.

Establish `hM : (a (i + J) : ℝ) ≤ M` using `Finset.single_le_sum (f := fun j => (a j : ℝ)) (fun j _ => by positivity) (Finset.mem_univ _)`. Establish `hpart : ∑ j ∈ Finset.range J, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) ≤ S` using `hsum.sum_le_tsum _ (fun j _ => by positivity)`. Use `step J i` as an intermediate fact. Establish `: (a (i + J) : ℝ) / (l : ℝ) ^ J ≤ M / (l : ℝ) ^ J` using `div_le_div_of_nonneg_right hM (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `lim : Filter.Tendsto (fun J : ℕ => M / (l : ℝ) ^ J + S) Filter.atTop (nhds (0 + S))` using `(tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hl))).add tendsto_const_nhds`. Rewrite `lim` using `[zero_add]`. Conclude with `ge_of_tendsto' lim bound`.
-/
theorem _root_.GlobalTheory.PhiGam.Close.le_sg {l : ℕ} (hl : 1 < l) {n : ℕ} [NeZero n]
    (h a : ZMod n → ℕ) (ha : ∀ i, l * a i ≤ a (i + 1) + h (i + 1)) (i : ZMod n) :
    a i ≤ _root_.GlobalTheory.PhiGam.sg l h i := by
  unfold _root_.GlobalTheory.PhiGam.sg
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hsum := _root_.GlobalTheory.PhiGam.summable_sg (l := l) (by omega) h i
  have step : ∀ J : ℕ, ∀ i : ZMod n, (a i : ℝ) ≤ a (i + J) / (l : ℝ) ^ J +
      ∑ j ∈ Finset.range J, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    intro J
    induction J with
    | zero => intro i; simp
    | succ J ih =>
      intro i
      have h1 := ih i
      have h2 : ((l * a (i + J) : ℕ) : ℝ) ≤ ((a (i + J + 1) + h (i + J + 1) : ℕ) : ℝ) := by exact_mod_cast ha (i + J)
      push_cast at h2
      have e : i + ((J + 1 : ℕ) : ZMod n) = i + (J : ZMod n) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, e]
      have hp : (0 : ℝ) < (l : ℝ) ^ (J + 1) := by positivity
      have h3 : (a (i + J) : ℝ) / (l : ℝ) ^ J ≤ a (i + J + 1) / (l : ℝ) ^ (J + 1) + h (i + J + 1) / (l : ℝ) ^ (J + 1) := by
        rw [← add_div, le_div_iff₀ hp, pow_succ, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
        linarith
      linarith
  apply Nat.le_floor
  set S := ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)
  set M : ℝ := ∑ j, (a j : ℝ)
  have bound : ∀ J : ℕ, (a i : ℝ) ≤ M / (l : ℝ) ^ J + S := by
    intro J
    have hM : (a (i + J) : ℝ) ≤ M :=
      Finset.single_le_sum (f := fun j => (a j : ℝ)) (fun j _ => by positivity) (Finset.mem_univ _)
    have hpart : ∑ j ∈ Finset.range J, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) ≤ S :=
      hsum.sum_le_tsum _ (fun j _ => by positivity)
    have := step J i
    have : (a (i + J) : ℝ) / (l : ℝ) ^ J ≤ M / (l : ℝ) ^ J :=
      div_le_div_of_nonneg_right hM (by positivity)
    linarith
  have lim : Filter.Tendsto (fun J : ℕ => M / (l : ℝ) ^ J + S) Filter.atTop (nhds (0 + S)) :=
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hl))).add
      tendsto_const_nhds
  rw [zero_add] at lim
  exact ge_of_tendsto' lim bound

/- English proof (translation)
Introduce `k _ l hl _ R n _ V _ _ _ _ _ _ _ _ D h N₁ N₂ h₁ h₂ c₁ c₂ i`. Establish `hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i` using `fun i => exists_pow (h₁ i).1 (h₂ i).2`. Establish `hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l`. Introduce `i`. Use `Nat.find_min' _ fun x hx => ?_` and prove the remaining obligations.

Use `key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_` and prove the remaining obligations. Establish `e1 : D.φ i x ∈ N₁ i`. Use `(c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩)` as an intermediate fact. Rewrite `this` using `[sh_zero]`. Then use the resulting hypothesis. Establish `e2` using `(c₂ i).2 (mem_sh_of (h i) _ (Nat.find_spec (hex i) _ e1))`.

Rewrite `e2` using `[← mul_smul, ← pow_add, add_comm]`. Then use the resulting hypothesis. Establish `hle` using `le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by`. Use `hrec (i + 1)` as an intermediate fact. Simplify using `only [add_sub_cancel_right] at this`. Conclude with `(Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i`.

Conclude with `sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)`.
-/
theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (h : ZMod n → ℕ) (N₁ N₂ : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ (fun _ => 0) (fun i => h i) N₁ → CondAB D.φ (fun _ => 0) (fun i => h i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  intro k _ l hl _ R n _ V _ _ _ _ _ _ _ _ D h N₁ N₂ h₁ h₂ c₁ c₂ i
  classical
  have hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i := fun i => exists_pow (h₁ i).1 (h₂ i).2
  have hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l := by
    intro i
    refine Nat.find_min' _ fun x hx => ?_
    refine key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_
    have e1 : D.φ i x ∈ N₁ i := by
      have := (c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
      rwa [sh_zero] at this
    have e2 := (c₂ i).2 (mem_sh_of (h i) _ (Nat.find_spec (hex i) _ e1))
    rwa [← mul_smul, ← pow_add, add_comm] at e2
  have hle := le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by
    have := hrec (i + 1)
    simp only [add_sub_cancel_right] at this
    exact (Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i
  exact sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)

end GlobalTheory.PhiGam.Close
