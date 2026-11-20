import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData

open GlobalTheory.CompanionTheory.Ar.Num
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

/- English proof (translation)
Establish `hvw : v w ≠ 0` using `(Valuation.ne_zero_iff v).2 hw0`. Establish `hvw' : 0 < v w` using `pos_iff_ne_zero.2 hvw`. Establish `hle : ∀ a : RC, v (a : C) ≤ 1` using `fun a => (hv _).1 a.2`. Establish `htw : v (p / w) ≤ v w` using `by rw [map_div₀, div_le_iff₀ hvw']; exact hpw`. Set `t : RC` to `⟨p / w, (hv _).2 (htw.trans hw1.le)⟩`.

Establish `hint : ∀ x : I → C, (∀ l ∈ AF, v (∑ j, (l j : C) * x j) ≤ 1) → ∀ m, w * x m ∈ RC` using `fun x hx m => by`. Use `hx _ (h0 (Pi.single m 1))` as an intermediate fact. Rewrite `this` using `[Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_mul, hc] at this`. Rewrite using `[hv, map_mul]`.

Conclude with `this`. Establish `hev : ∀ (f : (Fin g → C) →ₗ[C] C) (x : I → C), f (Hm.map (algebraMap RC C) *ᵥ x) = ∑ m, x m * f fun j => (Hm j m : C)` using `fun f x => by`. Establish `: Hm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun j => (Hm j m : C)`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[this, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Establish `key : ∀ x : I → C, (∀ m, w * x m ∈ RC) → ∃ u : Fin g → RC, ∀ k, q (Pm.map (algebraMap RC C) *ᵥ x) k = evs k (Hm.map (algebraMap RC C) *ᵥ x) - (t : C) * evs k fun j => (u j : C)`. Introduce `x hx`.

Use `choose U hU using hq`. Use `⟨∑ m, (⟨_, hx m⟩ : RC) • U m, fun k => ?_⟩` and prove the remaining obligations. Establish `e1 : Pm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun i => (Pm i m : C)`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `e2 : (fun j => (((∑ m, (⟨_, hx m⟩ : RC) • U m) j : RC) : C)) = ∑ m, (w * x m) • fun j => (U m j : C)`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]`. Rewrite using `[hev, e1, e2, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `e3 : (t : C) * w = p` using `div_mul_cancel₀ p hw0`. Take the linear combination `(-x m) * hU m k + (x m * evs k fun j => (U m j : C)) * e3`. Establish `hPJ' : ∀ u : Fin n → C, Pm.map (algebraMap RC C) *ᵥ (Jm.map (algebraMap RC C) *ᵥ u) = u` using `fun u => by`.

Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hPJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Establish `hdot : ∀ {K : Type} [Fintype K] (l : I → RC) (M : Matrix I K RC) (x : K → C), ∑ j, (l j : C) * (M.map (algebraMap RC C) *ᵥ x) j = ∑ j, ((l ᵥ* M) j : C) * x j` using `fun l M x => by`. Simplify using `only [Matrix.mulVec, Matrix.vecMul, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Finset.mul_sum, Finset.sum_mul, Matrix.map_apply, mul_assoc]`. Conclude with `Finset.sum_comm`. Use `⟨le_antisymm ?_ ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨u₀, hu₀, rfl⟩`. Establish `hu` using `(hhh u₀).1 hu₀`. Take `⟨u, e⟩` from `key _ (hint _ fun l hl => (hv _).1 (hu l hl))`. Rewrite `e` using `[hPJ']`. Use `(hom _).2 ⟨(fun j => ⟨_, hu _ (h1 j)⟩) - t • u, fun k => (e k).trans ?_⟩` and prove the remaining obligations.

Rewrite using `[← smul_eq_mul, ← map_smul, ← map_sub]`. Both sides reduce to the same expression. Set `N : Submodule RC (Fin g → RC)` to `{ carrier := {u | ∃ x ∈ hh, ∀ k, q x k = evs k fun j => (u j : C)} add_mem' := by`. Introduce and unpack `a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩`. Use `⟨x + y, hh.add_mem hx hy, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, Pi.add_apply, ha, hb, ← map_add]`. Both sides reduce to the same expression. Use the proof step `zero_mem' := ⟨0, hh.zero_mem, fun k => by rw [map_zero]; exact (map_zero (evs k)).symm⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a b ⟨x, hx, hb⟩`.

Use `⟨(a : C) • x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `RC.mul_mem a.2 ((hhh _).1 hx l hl) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]`. Rewrite using `[map_smul, Pi.smul_apply, hb, ← map_smul]`. Use `rfl }`.

Establish `hjac : Ideal.span {t} ≤ (⊥ : Ideal RC).jacobson`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]`. Introduce `y`. Establish `h1 : v ((t * y + 1 : RC) : C) = 1`. Rewrite using `[add_comm]`.

Use `v.map_one_add_of_lt ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v ((t : C) * y) < 1`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le (htw.trans_lt hw1) (hle y)`. Establish `h0 : ((t * y + 1 : RC) : C) ≠ 0` using `fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1`.

Use `IsUnit.of_mul_eq_one ⟨((t * y + 1 : RC) : C)⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_` and prove the remaining obligations. Conclude with `Subtype.ext (mul_inv_cancel₀ h0)`. Establish `hN : (⊤ : Submodule RC (Fin g → RC)) ≤ N`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun u _ => ?_` and prove the remaining obligations. Take `⟨x, hx, hxu⟩` from `h4 u`.

Take `⟨u', e⟩` from `key x (hint x hx)`. Use `Submodule.mem_sup.2 ⟨u - t • u', ⟨Pm.map (algebraMap RC C) *ᵥ x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩, t • u', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top, sub_add_cancel _ _⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hdot]`. Conclude with `(hv _).2 (hx _ (hst l hl))`. Rewrite using `[e, hxu, ← smul_eq_mul, ← map_smul, ← map_sub]`.

Both sides reduce to the same expression. Introduce `z hz`. Take `⟨u, hu⟩` from `(hom z).1 hz`. Take `⟨x, hx, e⟩` from `hN (Submodule.mem_top (x := u))`. Conclude with `⟨x, hx, funext fun k => (e k).trans (hu k).symm⟩`.

Establish `est : ∀ a : Fin r → C, w • a ∈ W → ∀ y : I → RC, (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j ∈ RC ↔ v (∑ k, (w • a) k * evr k fun j => ((Hm *ᵥ y) j : C)) ≤ v w)`. Introduce `a ha y`. Take `⟨z, hz, e⟩` from `hcl _ ha`. Establish `hz' : ∀ k, z k ∈ RC` using `fun k => hz k (Set.mem_univ k)`. Establish `e1 : w • hb a = i' (w • a) + w • z`.

Rewrite using `[← map_smul hb, ← sub_eq_iff_eq_add', ← e]`. Both sides reduce to the same expression. Establish `e2 : w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j + w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j`. Use `congrArg (fun x => ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ x) j) e1` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_left_comm _ w, ← Finset.mul_sum]`.

Establish `e3 : v (w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j) ≤ v w`. Rewrite using `[map_mul]`. Use `mul_le_of_le_one_right zero_le ((hv _).1 ?_)` and prove the remaining obligations. Rewrite using `[hdot]`. Conclude with `RC.sum_mem fun j _ => RC.mul_mem (Subtype.prop _) (hz' j)`.

Establish `e4 : ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j + ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) = ∑ m, (y m : C) * (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) m' + ∑ k, (w • a) k * evr k fun j => (Hm j m : C))`. Establish `: (fun j => ((Hm *ᵥ y) j : C)) = Hm.map (algebraMap RC C) *ᵥ fun m => (y m : C)`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Matrix.map_apply]`. Both sides reduce to the same expression.

Rewrite using `[this, ← hdot]`. Simplify using `only [hev, mul_add, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [mul_left_comm]`. Establish `e5 : v (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j + ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C))) ≤ v w`. Rewrite using `[e4]`. Use `v.map_sum_le fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `(mul_le_of_le_one_left zero_le (hle _)).trans (hdual _ ha m)`. Establish `e6` using `v.map_add_le e5 e3`. Rewrite `e6` using `[add_right_comm, ← e2]`. Rewrite using `[hv, ← mul_le_mul_iff_right₀ hvw', mul_one, ← map_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Simplify using `using v.map_sub_le e6 h`. Introduce `h`. Simplify using `using v.map_sub_le e6 h`. Establish `hlin : ∀ (a : Fin r → C) (b : RC) (u : Fin g → RC), ∑ k, a k * evr k (fun j => ((b • u) j : C)) = (b : C) * ∑ k, a k * evr k (fun j => (u j : C))` using `fun a b u => by`.

Establish `: (fun j => ((b • u) j : C)) = (b : C) • fun j => (u j : C)` using `rfl`. Simplify using `only [this, map_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `hb a ∈ hh ↔ w • a ∈ lie`. Rewrite using `[hhh]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `ha : w • a ∈ W`. Rewrite using `[← hW]`. Introduce `k _`.

Establish `h5` using `(hv _).1 (h _ (h0 (Pm k)))`. Establish `h6 : ∑ j, ((c • Pm k) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = (c : C) * hb a k` using `by conv_rhs => rw [← hPJ' (hb a)]`. Generalize the expression as in `Jm.map (algebraMap RC C) *ᵥ hb a = x`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Finset.mul_sum, mul_assoc, Matrix.map_apply]`. Both sides reduce to the same expression.

Rewrite `h5` using `[h6, map_mul, hc, ← map_mul]`. Express the relevant statement in the definitionally equal form `hb (w • a) k ∈ RC`. Rewrite using `[map_smul]`. Conclude with `(hv _).2 h5`. Use `(hlie _).2 fun u => ?_` and prove the remaining obligations.

Take `⟨y, u', hy, e⟩` from `h3 u`. Establish `h5` using `(est a ha y).1 (h _ hy)`. Establish `h6 : ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) = (c : C) * ∑ k, (w • a) k * evr k (fun j => (u j : C)) + (p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))`. Establish `: (fun j => ((c • u + P • u') j : C)) = (fun j => ((c • u) j : C)) + fun j => ((P • u') j : C)` using `rfl`. Rewrite using `[e, this]`.

Simplify using `only [map_add, mul_add, Finset.sum_add_distrib, hlin, hP]`. Use `congr 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc w, ← Finset.mul_sum]`. Clear the denominators using the available nonvanishing facts. Establish `h7 : v ((p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))) ≤ v w`.

Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 (hWl _ ha) u'))).trans htw`. Rewrite `h5` using `[h6]`. Establish `h8` using `v.map_sub_le h5 h7`. Rewrite `h8` using `[add_sub_cancel_right, map_mul, hc]`.

Rewrite using `[hv]`. Conclude with `(mul_le_iff_le_one_right hvw').1 h8`. Introduce `h l hl`. Establish `hl' : (l ᵥ* Ei) ᵥ* Eg = l` using `by rw [Matrix.vecMul_vecMul, hEi, Matrix.vecMul_one]`. Rewrite `hl`, the goal using `[← hl']`.

Take `⟨u, e⟩` from `h2 _ hl`. Rewrite using `[est a (hlW h), e, hlin, map_mul, hc]`. Conclude with `mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 h u))`.
-/
theorem typed {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal)
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (p w : C) (hw0 : w ≠ 0) (hw1 : v w < 1) (hpw : v p ≤ v w * v w) (c P : RC)
    (hc : v (c : C) = v w) (hP : (P : C) = p)
    {I : Type} [Fintype I] [DecidableEq I] {g n r s : ℕ} (AF : Submodule RC (I → RC))
    (Hm : Matrix (Fin g) I RC) (Eg Ei : Matrix I I RC) (hEi : Ei * Eg = 1)
    (h0 : ∀ l, c • l ∈ AF) (h1 : ∀ k, Hm k ∈ AF) (h2 : ∀ y, y ᵥ* Eg ∈ AF → ∃ u, Hm *ᵥ y = c • u)
    (h3 : ∀ u : Fin g → RC, ∃ (y : I → RC) (u' : Fin g → RC), y ᵥ* Eg ∈ AF ∧ Hm *ᵥ y = c • u + P • u')
    (h4 : ∀ u : Fin g → RC, ∃ x : I → C, (∀ l ∈ AF, v (∑ j, algebraMap RC C (l j) * x j) ≤ 1) ∧
      Hm.map (algebraMap RC C) *ᵥ x = fun k => algebraMap RC C (u k))
    (Pm : Matrix (Fin n) I RC) (Jm : Matrix I (Fin n) RC) (hPJ : Pm * Jm = 1)
    (hst : ∀ l ∈ AF, l ᵥ* (Jm * Pm) ∈ AF) (hh : AddSubgroup (Fin n → C))
    (hhh : ∀ u, u ∈ hh ↔ ∀ l ∈ AF, (∑ j, (l j : C) * (Jm.map (algebraMap RC C)).mulVec u j) ∈ RC)
    (evs : Fin s → ((Fin g → C) →ₗ[C] C)) (evr : Fin r → ((Fin g → C) →ₗ[C] C))
    (om : AddSubgroup (Fin s → C)) (lie W : AddSubgroup (Fin r → C))
    (hom : ∀ z, z ∈ om ↔ ∃ u : Fin g → RC, ∀ k, z k = evs k fun j => (u j : C))
    (hlie : ∀ a, a ∈ lie ↔ ∀ u : Fin g → RC, ∑ k, a k * evr k (fun j => (u j : C)) ∈ RC)
    (hlW : lie ≤ W) (hWl : ∀ a ∈ W, w • a ∈ lie)
    (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (hq : ∀ m, ∃ u : Fin g → RC, ∀ k,
      evs k (fun j => (Hm j m : C)) - q (fun i => (Pm i m : C)) k = p * evs k fun j => (u j : C))
    (i' hb : (Fin r → C) →ₗ[C] (Fin n → C))
    (hdual : ∀ a ∈ W, ∀ m, v (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' a) m' +
      ∑ k, a k * evr k fun j => (Hm j m : C)) ≤ v w)
    (hW : (stdLat RC _).comap hb.toAddMonoidHom = W) (hcl : ∀ a ∈ W, hb a - i' a ∈ mulLat w (stdLat RC _)) :
    hh.map q.toAddMonoidHom = om ∧ hh.comap hb.toAddMonoidHom = divLat w lie := by
  have hvw : v w ≠ 0 := (Valuation.ne_zero_iff v).2 hw0
  have hvw' : 0 < v w := pos_iff_ne_zero.2 hvw
  have hle : ∀ a : RC, v (a : C) ≤ 1 := fun a => (hv _).1 a.2
  have htw : v (p / w) ≤ v w := by rw [map_div₀, div_le_iff₀ hvw']; exact hpw
  let t : RC := ⟨p / w, (hv _).2 (htw.trans hw1.le)⟩
  have hint : ∀ x : I → C, (∀ l ∈ AF, v (∑ j, (l j : C) * x j) ≤ 1) → ∀ m, w * x m ∈ RC := fun x hx m => by
    have := hx _ (h0 (Pi.single m 1))
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_mul, hc] at this
    rw [hv, map_mul]
    exact this
  have hev : ∀ (f : (Fin g → C) →ₗ[C] C) (x : I → C),
      f (Hm.map (algebraMap RC C) *ᵥ x) = ∑ m, x m * f fun j => (Hm j m : C) := fun f x => by
    have : Hm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun j => (Hm j m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  have key : ∀ x : I → C, (∀ m, w * x m ∈ RC) → ∃ u : Fin g → RC, ∀ k,
      q (Pm.map (algebraMap RC C) *ᵥ x) k = evs k (Hm.map (algebraMap RC C) *ᵥ x) - (t : C) * evs k fun j => (u j : C) := by
    intro x hx
    choose U hU using hq
    refine ⟨∑ m, (⟨_, hx m⟩ : RC) • U m, fun k => ?_⟩
    have e1 : Pm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun i => (Pm i m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : (fun j => (((∑ m, (⟨_, hx m⟩ : RC) • U m) j : RC) : C)) = ∑ m, (w * x m) • fun j => (U m j : C) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [hev, e1, e2, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have e3 : (t : C) * w = p := div_mul_cancel₀ p hw0
    linear_combination (-x m) * hU m k + (x m * evs k fun j => (U m j : C)) * e3
  have hPJ' : ∀ u : Fin n → C, Pm.map (algebraMap RC C) *ᵥ (Jm.map (algebraMap RC C) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hdot : ∀ {K : Type} [Fintype K] (l : I → RC) (M : Matrix I K RC) (x : K → C),
      ∑ j, (l j : C) * (M.map (algebraMap RC C) *ᵥ x) j = ∑ j, ((l ᵥ* M) j : C) * x j := fun l M x => by
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.map_apply, mul_assoc]
    exact Finset.sum_comm
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨u₀, hu₀, rfl⟩
    have hu := (hhh u₀).1 hu₀
    obtain ⟨u, e⟩ := key _ (hint _ fun l hl => (hv _).1 (hu l hl))
    rw [hPJ'] at e
    refine (hom _).2 ⟨(fun j => ⟨_, hu _ (h1 j)⟩) - t • u, fun k => (e k).trans ?_⟩
    rw [← smul_eq_mul, ← map_smul, ← map_sub]
    rfl
  · let N : Submodule RC (Fin g → RC) :=
      { carrier := {u | ∃ x ∈ hh, ∀ k, q x k = evs k fun j => (u j : C)}
        add_mem' := by
          rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
          refine ⟨x + y, hh.add_mem hx hy, fun k => ?_⟩
          rw [map_add, Pi.add_apply, ha, hb, ← map_add]
          rfl
        zero_mem' := ⟨0, hh.zero_mem, fun k => by rw [map_zero]; exact (map_zero (evs k)).symm⟩
        smul_mem' := by
          rintro a b ⟨x, hx, hb⟩
          refine ⟨(a : C) • x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩
          · convert RC.mul_mem a.2 ((hhh _).1 hx l hl) using 1
            simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
          · rw [map_smul, Pi.smul_apply, hb, ← map_smul]
            rfl }
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal RC).jacobson := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]
      intro y
      have h1 : v ((t * y + 1 : RC) : C) = 1 := by
        rw [add_comm]
        refine v.map_one_add_of_lt ?_
        change v ((t : C) * y) < 1
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (htw.trans_lt hw1) (hle y)
      have h0 : ((t * y + 1 : RC) : C) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
      refine IsUnit.of_mul_eq_one ⟨((t * y + 1 : RC) : C)⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_
      exact Subtype.ext (mul_inv_cancel₀ h0)
    have hN : (⊤ : Submodule RC (Fin g → RC)) ≤ N := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun u _ => ?_
      obtain ⟨x, hx, hxu⟩ := h4 u
      obtain ⟨u', e⟩ := key x (hint x hx)
      refine Submodule.mem_sup.2 ⟨u - t • u', ⟨Pm.map (algebraMap RC C) *ᵥ x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩,
        t • u', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top, sub_add_cancel _ _⟩
      · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hdot]
        exact (hv _).2 (hx _ (hst l hl))
      · rw [e, hxu, ← smul_eq_mul, ← map_smul, ← map_sub]
        rfl
    intro z hz
    obtain ⟨u, hu⟩ := (hom z).1 hz
    obtain ⟨x, hx, e⟩ := hN (Submodule.mem_top (x := u))
    exact ⟨x, hx, funext fun k => (e k).trans (hu k).symm⟩
  · have est : ∀ a : Fin r → C, w • a ∈ W → ∀ y : I → RC,
        (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j ∈ RC ↔
          v (∑ k, (w • a) k * evr k fun j => ((Hm *ᵥ y) j : C)) ≤ v w) := by
      intro a ha y
      obtain ⟨z, hz, e⟩ := hcl _ ha
      have hz' : ∀ k, z k ∈ RC := fun k => hz k (Set.mem_univ k)
      have e1 : w • hb a = i' (w • a) + w • z := by
        rw [← map_smul hb, ← sub_eq_iff_eq_add', ← e]; rfl
      have e2 : w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j =
          ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
            w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j := by
        have := congrArg (fun x => ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ x) j) e1
        simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, mul_left_comm _ w, ← Finset.mul_sum] using this
      have e3 : v (w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j) ≤ v w := by
        rw [map_mul]
        refine mul_le_of_le_one_right zero_le ((hv _).1 ?_)
        rw [hdot]
        exact RC.sum_mem fun j _ => RC.mul_mem (Subtype.prop _) (hz' j)
      have e4 : ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          ∑ m, (y m : C) * (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) m' +
            ∑ k, (w • a) k * evr k fun j => (Hm j m : C)) := by
        have : (fun j => ((Hm *ᵥ y) j : C)) = Hm.map (algebraMap RC C) *ᵥ fun m => (y m : C) := by
          funext j
          simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Matrix.map_apply]
          rfl
        rw [this, ← hdot]
        simp only [hev, mul_add, Finset.sum_add_distrib]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
      have e5 : v (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C))) ≤ v w := by
        rw [e4]
        refine v.map_sum_le fun m _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left zero_le (hle _)).trans (hdual _ ha m)
      have e6 := v.map_add_le e5 e3
      rw [add_right_comm, ← e2] at e6
      rw [hv, ← mul_le_mul_iff_right₀ hvw', mul_one, ← map_mul]
      constructor
      · intro h
        simpa using v.map_sub_le e6 h
      · intro h
        simpa using v.map_sub_le e6 h
    have hlin : ∀ (a : Fin r → C) (b : RC) (u : Fin g → RC), ∑ k, a k * evr k (fun j => ((b • u) j : C)) =
        (b : C) * ∑ k, a k * evr k (fun j => (u j : C)) := fun a b u => by
      have : (fun j => ((b • u) j : C)) = (b : C) • fun j => (u j : C) := rfl
      simp only [this, map_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    ext a
    change hb a ∈ hh ↔ w • a ∈ lie
    rw [hhh]
    constructor
    · intro h
      have ha : w • a ∈ W := by
        rw [← hW]
        intro k _
        have h5 := (hv _).1 (h _ (h0 (Pm k)))
        have h6 : ∑ j, ((c • Pm k) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = (c : C) * hb a k := by
          conv_rhs => rw [← hPJ' (hb a)]
          generalize Jm.map (algebraMap RC C) *ᵥ hb a = x
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Finset.mul_sum,
            mul_assoc, Matrix.map_apply]
          rfl
        rw [h6, map_mul, hc, ← map_mul] at h5
        change hb (w • a) k ∈ RC
        rw [map_smul]
        exact (hv _).2 h5
      refine (hlie _).2 fun u => ?_
      obtain ⟨y, u', hy, e⟩ := h3 u
      have h5 := (est a ha y).1 (h _ hy)
      have h6 : ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          (c : C) * ∑ k, (w • a) k * evr k (fun j => (u j : C)) +
            (p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C)) := by
        have : (fun j => ((c • u + P • u') j : C)) = (fun j => ((c • u) j : C)) + fun j => ((P • u') j : C) := rfl
        rw [e, this]
        simp only [map_add, mul_add, Finset.sum_add_distrib, hlin, hP]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc w, ← Finset.mul_sum]
        field_simp
      have h7 : v ((p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))) ≤ v w := by
        rw [map_mul]
        exact (mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 (hWl _ ha) u'))).trans htw
      rw [h6] at h5
      have h8 := v.map_sub_le h5 h7
      rw [add_sub_cancel_right, map_mul, hc] at h8
      rw [hv]
      exact (mul_le_iff_le_one_right hvw').1 h8
    · intro h l hl
      have hl' : (l ᵥ* Ei) ᵥ* Eg = l := by rw [Matrix.vecMul_vecMul, hEi, Matrix.vecMul_one]
      rw [← hl'] at hl ⊢
      obtain ⟨u, e⟩ := h2 _ hl
      rw [est a (hlW h), e, hlin, map_mul, hc]
      exact mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 h u))

end PositivityTheory.Xgn.TestGroupPoint
