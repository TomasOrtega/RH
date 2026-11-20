import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmodEqIffDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.SatMod

/- English proof (translation)
Establish `step : ∀ y : {y // mem y}, ∃ (c : Fin n → S) (y' : {y // mem y}), ∀ i, y.1 i = (Y *ᵥ fun a => ev (c a)) i + (l : A) * y'.1 i`. Introduce and unpack `⟨y, hy⟩`. Take `⟨c, hc⟩` from `hgen y hy`. Use `choose y' hy' using hc`. Use `⟨c, ⟨y', hsat _ ?_⟩, fun i => by simp only; linear_combination hy' i⟩` and prove the remaining obligations.

Use `hadd _ _ hy (hsm (-1) _ (hY c))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, map_neg, map_one]`. Take the linear combination `- hy' i`.

Use `choose c nx hnx using step`. Set `ys : ℕ → {y // mem y}` to `fun k => nx^[k] ⟨y, hy⟩`. Set `f : ℕ → Fin n → S` to `fun k a => ∑ j ∈ Finset.range k, (l : S) ^ j * c (ys j) a`. Establish `hf : ∀ k i, y i = (Y *ᵥ fun a => ev (f k a)) i + (l : A) ^ k * (ys k).1 i`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro i`. Simplify using `[f, ys, mulVec, dotProduct]`. Consider the case `succ k ih`. Introduce `i`.

Establish `h1` using `hnx (ys k) i`. Establish `h2 : ys (k + 1) = nx (ys k)` using `Function.iterate_succ_apply' _ _ _`. Establish `h3 : (Y *ᵥ fun a => ev (f (k + 1) a)) i = (Y *ᵥ fun a => ev (f k a)) i + (l : A) ^ k * (Y *ᵥ fun a => ev (c (ys k) a)) i`. Simplify using `only [f, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast, mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => by ring` and prove the remaining obligations.

Rewrite using `[h3, h2]`. Take the linear combination `ih i + (l : A) ^ k * h1`. Establish `hz : ∀ a, ∃ z, ∀ k, (l : S) ^ k ∣ z - f k a` using `fun a => hS (fun k => f k a) fun k => by simp [f, Finset.sum_range_succ]`. Use `choose z hz using hz`. Use `⟨z, funext fun i => sub_eq_zero.1 (hA _ fun k => ?_)⟩` and prove the remaining obligations.

Establish `h4 : (l : A) ^ k ∣ (Y *ᵥ fun a => ev (z a)) i - (Y *ᵥ fun a => ev (f k a)) i`. Simplify using `only [mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub, ← map_sub]`. Use `Finset.dvd_sum fun a _ => Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Simplify using `using map_dvd ev (hz a k)`. Take `⟨q, hq⟩` from `h4`.

Conclude with `⟨(ys k).1 i - q, by linear_combination hf k i - hq⟩`.
-/
theorem approx {S A : Type} [CommRing S] [CommRing A] (l : ℕ) (ev : S →+* A) {d n : ℕ}
    (mem : (Fin d → A) → Prop) (hadd : ∀ y z, mem y → mem z → mem (y + z))
    (hsm : ∀ (c : S) y, mem y → mem (fun a => ev c * y a))
    (hsat : ∀ y, mem (fun a => (l : A) * y a) → mem y)
    (hA : ∀ x : A, (∀ k : ℕ, (l : A) ^ k ∣ x) → x = 0)
    (hS : ∀ f : ℕ → S, (∀ k, (l : S) ^ k ∣ f (k + 1) - f k) → ∃ z, ∀ k, (l : S) ^ k ∣ z - f k)
    (Y : Matrix (Fin d) (Fin n) A) (hY : ∀ c : Fin n → S, mem (Y *ᵥ fun a => ev (c a)))
    (hgen : ∀ y, mem y → ∃ c : Fin n → S, ∀ i, (l : A) ∣ y i - (Y *ᵥ fun a => ev (c a)) i)
    (y : Fin d → A) (hy : mem y) : ∃ c : Fin n → S, y = Y *ᵥ fun a => ev (c a) := by
  have step : ∀ y : {y // mem y}, ∃ (c : Fin n → S) (y' : {y // mem y}),
      ∀ i, y.1 i = (Y *ᵥ fun a => ev (c a)) i + (l : A) * y'.1 i := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := hgen y hy
    choose y' hy' using hc
    refine ⟨c, ⟨y', hsat _ ?_⟩, fun i => by simp only; linear_combination hy' i⟩
    have := hadd _ _ hy (hsm (-1) _ (hY c))
    convert this using 1
    funext i
    simp only [Pi.add_apply, map_neg, map_one]
    linear_combination - hy' i
  choose c nx hnx using step
  let ys : ℕ → {y // mem y} := fun k => nx^[k] ⟨y, hy⟩
  let f : ℕ → Fin n → S := fun k a => ∑ j ∈ Finset.range k, (l : S) ^ j * c (ys j) a
  have hf : ∀ k i, y i = (Y *ᵥ fun a => ev (f k a)) i + (l : A) ^ k * (ys k).1 i := by
    intro k
    induction k with
    | zero => intro i; simp [f, ys, mulVec, dotProduct]
    | succ k ih =>
      intro i
      have h1 := hnx (ys k) i
      have h2 : ys (k + 1) = nx (ys k) := Function.iterate_succ_apply' _ _ _
      have h3 : (Y *ᵥ fun a => ev (f (k + 1) a)) i =
          (Y *ᵥ fun a => ev (f k a)) i + (l : A) ^ k * (Y *ᵥ fun a => ev (c (ys k) a)) i := by
        simp only [f, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast, mulVec, dotProduct,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [h3, h2]
      linear_combination ih i + (l : A) ^ k * h1
  have hz : ∀ a, ∃ z, ∀ k, (l : S) ^ k ∣ z - f k a := fun a =>
    hS (fun k => f k a) fun k => by simp [f, Finset.sum_range_succ]
  choose z hz using hz
  refine ⟨z, funext fun i => sub_eq_zero.1 (hA _ fun k => ?_)⟩
  have h4 : (l : A) ^ k ∣ (Y *ᵥ fun a => ev (z a)) i - (Y *ᵥ fun a => ev (f k a)) i := by
    simp only [mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub, ← map_sub]
    refine Finset.dvd_sum fun a _ => Dvd.dvd.mul_left ?_ _
    simpa using map_dvd ev (hz a k)
  obtain ⟨q, hq⟩ := h4
  exact ⟨(ys k).1 i - q, by linear_combination hf k i - hq⟩

/- English proof (translation)
Establish `h1 : LinearIndependent A C.col`. Rewrite using `[← Matrix.mulVec_injective_iff]`. Introduce `v w hvw`. Establish `: (Y * C) *ᵥ (v - w) = 0`. Rewrite using `[← mulVec_mulVec, mulVec_sub, hvw, sub_self, mulVec_zero]`.

Conclude with `sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero h this)`. Simplify using `using h1.fintype_card_le_finrank`.
-/
theorem le_of_det_ne_zero {A : Type} [CommRing A] [IsDomain A] {d n : ℕ} (Y : Matrix (Fin d) (Fin n) A)
    (C : Matrix (Fin n) (Fin d) A) (h : (Y * C).det ≠ 0) : d ≤ n := by
  have h1 : LinearIndependent A C.col := by
    rw [← Matrix.mulVec_injective_iff]
    intro v w hvw
    have : (Y * C) *ᵥ (v - w) = 0 := by
      rw [← mulVec_mulVec, mulVec_sub, hvw, sub_self, mulVec_zero]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero h this)
  simpa using h1.fintype_card_le_finrank

/- English proof (translation)
Set `L : Submodule R (Fin d → R)` to `{ carrier := {r | ∃ y, mem y ∧ (P *ᵥ fun a => cc (y a)) = fun a => eb (r a)} zero_mem' := ⟨0, h0, by ext i; simp [mulVec, dotProduct]⟩ add_mem' := by`. Introduce and unpack `r r' ⟨y, hy, h⟩ ⟨y', hy', h'⟩`. Use `⟨y + y', hadd _ _ hy hy', funext fun i => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun h i`. Establish `e'` using `congrFun h' i`.

Simplify using `only [mulVec, dotProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib] at e e' ⊢`. Rewrite using `[e, e']`. Use the proof step `smul_mem' := by`. Introduce and unpack `t r ⟨y, hy, h⟩`. Take `⟨s, rfl⟩` from `hred t`.

Use `⟨_, hsm s y hy, funext fun i => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun h i`. Simplify using `only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, hc] at e ⊢`. Rewrite using `[← e, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring }`.

Take `⟨n, b⟩` from `Submodule.basisOfPid (Pi.basisFun R (Fin d)) L`. Establish `hli : LinearIndependent R fun j => (b j : Fin d → R)` using `b.linearIndependent.map' L.subtype L.ker_subtype`. Establish `hnd : n ≤ d` using `by simpa using hli.fintype_card_le_finrank`. Establish `hb : ∀ j, ∃ y, mem y ∧ (P *ᵥ fun a => cc (y a)) = fun a => eb ((b j : Fin d → R) a)` using `fun j => (b j).2`. Use `choose yb hyb hyb' using hb`.

Set `Y : Matrix (Fin d) (Fin n) A` to `Matrix.of fun i j => yb j i`. Set `B : Matrix (Fin d) (Fin n) R` to `Matrix.of fun i j => (b j : Fin d → R) i`. Establish `hPY : P * Y.map cc = B.map eb`. Use extensionality with `i j`. Conclude with `congrFun (hyb' j) i`.

Establish `hY : ∀ c : Fin n → S, mem (Y *ᵥ fun a => ev (c a))`. Introduce `c`. Establish `: ∀ T : Finset (Fin n), mem (∑ j ∈ T, fun i => ev (c j) * yb j i)` using `fun T => Finset.sum_induction _ mem hadd h0 fun j _ => hsm _ _ (hyb j)`. Use `this Finset.univ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `[mulVec, dotProduct, Y, Finset.sum_apply, mul_comm]`. Establish `hgen : ∀ y, mem y → ∃ c : Fin n → S, ∀ i, (l : A) ∣ y i - (Y *ᵥ fun a => ev (c a)) i`. Introduce `y hy`. Take `⟨r, hr⟩` from `hPm y hy`. Use `choose c hc' using fun j => hred (b.repr ⟨r, y, hy, hr⟩ j)`.

Use `⟨c, fun i => hcc _ ?_⟩` and prove the remaining obligations. Establish `e1 : r = B *ᵥ fun j => red (c j)`. Use `congrArg (fun x : L => (x : Fin d → R)) (b.sum_repr ⟨r, y, hy, hr⟩)` as an intermediate fact. Use function extensionality and compare the values at `i`. Use `congrFun this i` as an intermediate fact.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[← this]`. Simplify using `[mulVec, dotProduct, B, hc', mul_comm]`. Establish `e2 : P *ᵥ ((fun a => cc (y a)) - Y.map cc *ᵥ fun j => eb (red (c j))) = 0`. Rewrite using `[mulVec_sub, mulVec_mulVec, hPY, hr, e1]`.

Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct]`. Establish `e3` using `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP e2) i`. Simplify `e3` using `[mulVec, dotProduct, hc]`. Establish `hall` using `approx l ev mem hadd hsm hsat hA hS Y hY hgen`.

Establish `hdn : d ≤ n` using `by choose C hC using fun j => hall _ (hm1 (Pi.single j 1))`. Use `le_of_det_ne_zero Y (Matrix.of fun a j => ev (C j a)) ?_` and prove the remaining obligations. Use `hY1 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Use `congrFun (hC j) i` as an intermediate fact.

Simplify using `only [mulVec, dotProduct, Pi.single_apply, apply_ite ev, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Rewrite using `[this]`. Both sides reduce to the same expression. Take `rfl : n = d` from `le_antisymm hnd hdn`. Use `⟨Y, fun h => ?_, fun y => ⟨hall y, fun ⟨c, hc⟩ => hc ▸ hY c⟩⟩` and prove the remaining obligations.

Establish `hB : B.det ≠ 0`. Introduce `hB`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hB`. Establish `: Function.Injective B.mulVec` using `Matrix.mulVec_injective_iff.2 hli`. Conclude with `hv (this (by rw [hv0, mulVec_zero]))`.

Use `congrArg Matrix.det hPY` as an intermediate fact. Rewrite `this` using `[det_mul, h, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hB (heb (by rw [← this, map_zero]))`.
-/
theorem abstract {S R A F : Type} [CommRing S] [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field F] (l : ℕ) (ev : S →+* A) (red : S →+* R) (hred : Function.Surjective red)
    (cc : A →+* F) (eb : R →+* F) (heb : Function.Injective eb) (hc : ∀ s, cc (ev s) = eb (red s))
    (hcc : ∀ x, cc x = 0 → (l : A) ∣ x) {d : ℕ}
    (mem : (Fin d → A) → Prop) (h0 : mem 0) (hadd : ∀ y z, mem y → mem z → mem (y + z))
    (hsm : ∀ (c : S) y, mem y → mem (fun a => ev c * y a))
    (hsat : ∀ y, mem (fun a => (l : A) * y a) → mem y)
    (hA : ∀ x : A, (∀ k : ℕ, (l : A) ^ k ∣ x) → x = 0)
    (hS : ∀ f : ℕ → S, (∀ k, (l : S) ^ k ∣ f (k + 1) - f k) → ∃ z, ∀ k, (l : S) ^ k ∣ z - f k)
    (Y1 : Matrix (Fin d) (Fin d) A) (hY1 : Y1.det ≠ 0) (hm1 : ∀ c : Fin d → S, mem (Y1 *ᵥ fun a => ev (c a)))
    (P : Matrix (Fin d) (Fin d) F) (hP : P.det ≠ 0)
    (hPm : ∀ y, mem y → ∃ r : Fin d → R, (P *ᵥ fun a => cc (y a)) = fun a => eb (r a)) :
    ∃ Y : Matrix (Fin d) (Fin d) A, (Y.map cc).det ≠ 0 ∧
      ∀ y, mem y ↔ ∃ c : Fin d → S, y = Y *ᵥ fun a => ev (c a) := by
  classical
  let L : Submodule R (Fin d → R) :=
    { carrier := {r | ∃ y, mem y ∧ (P *ᵥ fun a => cc (y a)) = fun a => eb (r a)}
      zero_mem' := ⟨0, h0, by ext i; simp [mulVec, dotProduct]⟩
      add_mem' := by
        rintro r r' ⟨y, hy, h⟩ ⟨y', hy', h'⟩
        refine ⟨y + y', hadd _ _ hy hy', funext fun i => ?_⟩
        have e := congrFun h i
        have e' := congrFun h' i
        simp only [mulVec, dotProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib] at e e' ⊢
        rw [e, e']
      smul_mem' := by
        rintro t r ⟨y, hy, h⟩
        obtain ⟨s, rfl⟩ := hred t
        refine ⟨_, hsm s y hy, funext fun i => ?_⟩
        have e := congrFun h i
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, hc] at e ⊢
        rw [← e, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin d)) L
  have hli : LinearIndependent R fun j => (b j : Fin d → R) := b.linearIndependent.map' L.subtype L.ker_subtype
  have hnd : n ≤ d := by simpa using hli.fintype_card_le_finrank
  have hb : ∀ j, ∃ y, mem y ∧ (P *ᵥ fun a => cc (y a)) = fun a => eb ((b j : Fin d → R) a) := fun j => (b j).2
  choose yb hyb hyb' using hb
  let Y : Matrix (Fin d) (Fin n) A := Matrix.of fun i j => yb j i
  let B : Matrix (Fin d) (Fin n) R := Matrix.of fun i j => (b j : Fin d → R) i
  have hPY : P * Y.map cc = B.map eb := by
    ext i j
    exact congrFun (hyb' j) i
  have hY : ∀ c : Fin n → S, mem (Y *ᵥ fun a => ev (c a)) := by
    intro c
    have : ∀ T : Finset (Fin n), mem (∑ j ∈ T, fun i => ev (c j) * yb j i) := fun T =>
      Finset.sum_induction _ mem hadd h0 fun j _ => hsm _ _ (hyb j)
    convert this Finset.univ using 1
    funext i
    simp [mulVec, dotProduct, Y, Finset.sum_apply, mul_comm]
  have hgen : ∀ y, mem y → ∃ c : Fin n → S, ∀ i, (l : A) ∣ y i - (Y *ᵥ fun a => ev (c a)) i := by
    intro y hy
    obtain ⟨r, hr⟩ := hPm y hy
    choose c hc' using fun j => hred (b.repr ⟨r, y, hy, hr⟩ j)
    refine ⟨c, fun i => hcc _ ?_⟩
    have e1 : r = B *ᵥ fun j => red (c j) := by
      have := congrArg (fun x : L => (x : Fin d → R)) (b.sum_repr ⟨r, y, hy, hr⟩)
      funext i
      have := congrFun this i
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      rw [← this]
      simp [mulVec, dotProduct, B, hc', mul_comm]
    have e2 : P *ᵥ ((fun a => cc (y a)) - Y.map cc *ᵥ fun j => eb (red (c j))) = 0 := by
      rw [mulVec_sub, mulVec_mulVec, hPY, hr, e1]
      funext i
      simp [mulVec, dotProduct]
    have e3 := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP e2) i
    simpa [mulVec, dotProduct, hc] using e3
  have hall := approx l ev mem hadd hsm hsat hA hS Y hY hgen
  have hdn : d ≤ n := by
    choose C hC using fun j => hall _ (hm1 (Pi.single j 1))
    refine le_of_det_ne_zero Y (Matrix.of fun a j => ev (C j a)) ?_
    convert hY1 using 2
    ext i j
    have := congrFun (hC j) i
    simp only [mulVec, dotProduct, Pi.single_apply, apply_ite ev, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [this]; rfl
  obtain rfl : n = d := le_antisymm hnd hdn
  refine ⟨Y, fun h => ?_, fun y => ⟨hall y, fun ⟨c, hc⟩ => hc ▸ hY c⟩⟩
  have hB : B.det ≠ 0 := by
    intro hB
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hB
    have : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 hli
    exact hv (this (by rw [hv0, mulVec_zero]))
  have := congrArg Matrix.det hPY
  rw [det_mul, h, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact hB (heb (by rw [← this, map_zero]))

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ModularLimit.exists_limit`. Consider the case `exact _root_.GlobalTheory.ModularLimit.exists_limit`. Consider the case `(apply _root_.GlobalTheory.ModularLimit.exists_limit <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ModularLimit.exists_limit <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ModularLimit.exists_limit <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ModularLimit.exists_limit ..)`.
-/
theorem lim_of_complete {W : Type} [CommRing W] (x : W) [h : IsPrecomplete (Ideal.span {x}) W] (f : ℕ → W)
    (hf : ∀ k, x ^ k ∣ f (k + 1) - f k) : ∃ z, ∀ k, x ^ k ∣ z - f k := by
  first
  | exact @_root_.GlobalTheory.ModularLimit.exists_limit
  | exact _root_.GlobalTheory.ModularLimit.exists_limit
  | (apply _root_.GlobalTheory.ModularLimit.exists_limit <;> assumption)
  | (intros; apply _root_.GlobalTheory.ModularLimit.exists_limit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ModularLimit.exists_limit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ModularLimit.exists_limit ..)

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP`. Establish `hC : ∀ k, (l : bk.S) ^ k = C ((l : Wq l bk.a) ^ k)` using `fun k => by rw [map_pow, map_natCast]`. Establish `: ∀ i, ∃ z, ∀ k, (l : Wq l bk.a) ^ k ∣ z - coeff i (f k)` using `fun i => lim_of_complete _ _ fun k => by`. Take `⟨q, hq⟩` from `hf k`. Conclude with `⟨coeff i q, by rw [← map_sub, hq, hC, coeff_C_mul]⟩`.

Use `choose z hz using this`. Use `⟨PowerSeries.mk z, fun k => ?_⟩` and prove the remaining obligations. Use `choose q hq using fun i => hz i k`. Conclude with `⟨PowerSeries.mk q, PowerSeries.ext fun i => by rw [map_sub, coeff_mk, hq, hC, coeff_C_mul, coeff_mk]⟩`.
-/
theorem lim_S (f : ℕ → bk.S) (hf : ∀ k, (l : bk.S) ^ k ∣ f (k + 1) - f k) :
    ∃ z, ∀ k, (l : bk.S) ^ k ∣ z - f k := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hC : ∀ k, (l : bk.S) ^ k = C ((l : Wq l bk.a) ^ k) := fun k => by rw [map_pow, map_natCast]
  have : ∀ i, ∃ z, ∀ k, (l : Wq l bk.a) ^ k ∣ z - coeff i (f k) := fun i =>
    lim_of_complete _ _ fun k => by
      obtain ⟨q, hq⟩ := hf k
      exact ⟨coeff i q, by rw [← map_sub, hq, hC, coeff_C_mul]⟩
  choose z hz using this
  refine ⟨PowerSeries.mk z, fun k => ?_⟩
  choose q hq using fun i => hz i k
  exact ⟨PowerSeries.mk q, PowerSeries.ext fun i => by rw [map_sub, coeff_mk, hq, hC, coeff_C_mul, coeff_mk]⟩

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := WittVector.isAdicCompleteIdealSpanP`. Use `IsHausdorff.haus' (I := Ideal.span {(l : Ainf l)}) x fun k => ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero, Ideal.mem_span_singleton]`. Conclude with `hx k`.
-/
theorem sep_A (x : Ainf l) (hx : ∀ k : ℕ, (l : Ainf l) ^ k ∣ x) : x = 0 := by
  haveI : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := WittVector.isAdicCompleteIdealSpanP
  refine IsHausdorff.haus' (I := Ideal.span {(l : Ainf l)}) x fun k => ?_
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero, Ideal.mem_span_singleton]
  exact hx k

def red : bk.S →+* (Fq l bk.a)⟦X⟧ := PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a))

/- English proof (translation)
Introduce `v` and use `⟨PowerSeries.mk fun n => WittVector.teichmuller l (coeff n v), by ext n simp [red, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩`.
-/
theorem red_surj : Function.Surjective (red bk) := fun v =>
  ⟨PowerSeries.mk fun n => WittVector.teichmuller l (coeff n v), by
    ext n
    simp [red, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨y, rfl⟩ := dvd_of_map_eq_zero l bk.a x hx rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`.
-/
theorem ker_red_le : RingHom.ker (red bk) ≤ RingHom.ker bk.evRed := fun x hx => by
  obtain ⟨y, rfl⟩ := dvd_of_map_eq_zero l bk.a x hx
  rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def eo : (Fq l bk.a)⟦X⟧ →+* OCb l := (red bk).liftOfSurjective (red_surj bk) ⟨bk.evRed, ker_red_le bk⟩

/- English proof (translation)
The claim follows from `(red bk).liftOfRightInverse_comp_apply _ _ _ s`.
-/
theorem eo_red (s : bk.S) : eo bk (red bk s) = bk.evRed s :=
  (red bk).liftOfRightInverse_comp_apply _ _ _ s

/- English proof (translation)
Rewrite using `[← bk.evRed_X, ← eo_red, red, PowerSeries.map_X]`.
-/
theorem eo_X : eo bk X = bk.flat := by
  rw [← bk.evRed_X, ← eo_red, red, PowerSeries.map_X]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Take `⟨s, rfl⟩` from `red_surj bk r`. Rewrite `hr` using `[eo_red]`. Take `⟨y, rfl⟩` from `bk.dvd_of_evRed_eq_zero s hr`.

Rewrite using `[map_mul, map_natCast, ← map_natCast (C : Fq l bk.a →+* _), CharP.cast_eq_zero, map_zero, zero_mul]`.
-/
theorem eo_injective : Function.Injective (eo bk) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨s, rfl⟩ := red_surj bk r
  rw [eo_red] at hr
  obtain ⟨y, rfl⟩ := bk.dvd_of_evRed_eq_zero s hr
  rw [map_mul, map_natCast, ← map_natCast (C : Fq l bk.a →+* _), CharP.cast_eq_zero, map_zero, zero_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro o r h; exact ⟨r, by simpa using h⟩`. Consider the case `succ m ih`. Introduce `o r h`. Establish `hX : X ∣ r`.

Rewrite using `[X_dvd_iff]`. Assume the negation of the conclusion as `h0`. Establish `hu : IsUnit (eo bk r)` using `(isUnit_iff_constantCoeff.2 (Ne.isUnit h0)).map _`. Rewrite `hu` using `[← h, pow_succ', mul_assoc]`. Conclude with `AinfDiv.flat_not_unit bk (isUnit_of_mul_isUnit_left hu)`.

Take `⟨r', rfl⟩` from `hX`. Use `ih o r' (mul_left_cancel₀ bk.flat_ne_zero ?_)` and prove the remaining obligations. Rewrite `h` using `[map_mul, eo_X]`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_range_eo (m : ℕ) : ∀ (o : OCb l) (r : (Fq l bk.a)⟦X⟧), bk.flat ^ m * o = eo bk r → ∃ r', o = eo bk r' := by
  induction m with
  | zero => intro o r h; exact ⟨r, by simpa using h⟩
  | succ m ih =>
    intro o r h
    have hX : X ∣ r := by
      rw [X_dvd_iff]
      by_contra h0
      have hu : IsUnit (eo bk r) := (isUnit_iff_constantCoeff.2 (Ne.isUnit h0)).map _
      rw [← h, pow_succ', mul_assoc] at hu
      exact AinfDiv.flat_not_unit bk (isUnit_of_mul_isUnit_left hu)
    obtain ⟨r', rfl⟩ := hX
    refine ih o r' (mul_left_cancel₀ bk.flat_ne_zero ?_)
    rw [map_mul, eo_X] at h
    rw [← h]; ring

/- English proof (translation)
Use `haveI := GlobalTheory.FrobInt.valuationRing_tilt l`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := OCb l) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `: ∃ c, b ∣ bk.flat ^ c`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hb0 (AinfDiv.flat_haus bk b fun n => (ValuationRing.dvd_total _ _).resolve_right (h n))`. Take `⟨c, q, hq⟩` from `this`. Use `⟨c, q * a, ?_⟩` and prove the remaining obligations. Establish `hb1 : algebraMap (OCb l) (Cb l) b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0`.

Rewrite using `[← map_pow, hq, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_pow_mul (x : Cb l) : ∃ (c : ℕ) (o : OCb l),
    algebraMap (OCb l) (Cb l) bk.flat ^ c * x = algebraMap (OCb l) (Cb l) o := by
  haveI := GlobalTheory.FrobInt.valuationRing_tilt l
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have : ∃ c, b ∣ bk.flat ^ c := by
    by_contra h
    push_neg at h
    exact hb0 (AinfDiv.flat_haus bk b fun n => (ValuationRing.dvd_total _ _).resolve_right (h n))
  obtain ⟨c, q, hq⟩ := this
  refine ⟨c, q * a, ?_⟩
  have hb1 : algebraMap (OCb l) (Cb l) b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  rw [← map_pow, hq, map_mul, map_mul]
  field_simp

end GlobalTheory.BSP.SatMod

open GlobalTheory.BSP.SatMod in

/- English proof (translation)
Introduce `l _ K bk d mem h0 hadd hsm hsat _ Y1 Y' hY1 hY' hm1 hOE`. Set `al` to `algebraMap (OCb l) (Cb l)`. Establish `hal : Function.Injective al` using `IsFractionRing.injective _ _`. Set `cW` to `WittVector.constantCoeff (p := l) (R := Cb l)`. Set `cA` to `WittVector.constantCoeff (p := l) (R := OCb l)`.

Establish `hcc : ∀ x, cW (inclW l x) = al (cA x)` using `fun x => by`. Simplify using `[cW, cA, al, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]`. Take `⟨U, rfl⟩` from `hY'`. Set `Q : Matrix (Fin d) (Fin d) (Cb l)` to `(↑U⁻¹ : Matrix (Fin d) (Fin d) (WCb l)).map cW`. Establish `hQ : Q.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 ((U⁻¹).isUnit.map cW.mapMatrix)).ne_zero`.

Use `choose c o ho using fun p : Fin d × Fin d => exists_pow_mul bk (Q p.1 p.2)`. Set `N` to `Finset.univ.sup c`. Establish `hf : al bk.flat ≠ 0` using `(map_ne_zero_iff _ hal).2 bk.flat_ne_zero`. Establish `hP : ∀ i j, ∃ o', al bk.flat ^ N * Q i j = al o'` using `fun i j => by`. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := c) (Finset.mem_univ (i, j)))`.

Use `⟨bk.flat ^ e * o (i, j), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, ← ho (i, j), show N = c (i, j) + e from he]`. Expand and normalize the polynomial expressions, which then agree. Use `choose o' ho' using hP`. Take `⟨Y, hY, hYm⟩` from `abstract l bk.ev (red bk) (red_surj bk) (al.comp cA) (al.comp (eo bk)) (hal.comp (eo_injective bk)) (fun s => by rw [RingHom.comp_apply, RingHom.comp_apply, eo_red]; rfl) (fun x hx => (AinfDiv.dvd_iff x).2 (hal (by rw [map_zero]; exact hx))) mem h0 hadd hsm hsat sep_A (lim_S bk) …`.

Take `⟨w, hw, hyw⟩` from `hOE y hy`. Establish `e1 : (↑U⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) *ᵥ (fun a => inclW l (y a)) = w`. Rewrite using `[hyw, mulVec_mulVec, Units.inv_mul, one_mulVec]`. Establish `: ∀ i, ∃ r, ((al bk.flat ^ N • Q) *ᵥ fun a => (al.comp cA) (y a)) i = al (eo bk r)` using `fun i => by`. Establish `e2 : (Q *ᵥ fun a => (al.comp cA) (y a)) i = cW (w i)`.

Rewrite using `[← e1]`. Simplify using `[mulVec, dotProduct, Q, hcc]`. Establish `e3 : ((al bk.flat ^ N • Q) *ᵥ fun a => (al.comp cA) (y a)) i = al (∑ a, o' i a * cA (y a))`. Simplify using `[mulVec, dotProduct, ho']`. Take `⟨m, s, hs⟩` from `((GlobalTheory.BSP.oe_mod_l l K bk).1 (cW (w i))).1 ⟨w i, hw i, rfl⟩`.

Establish `e4 : bk.flat ^ m * (∑ a, o' i a * cA (y a)) = eo bk (X ^ N * red bk s)`. Apply `hal` to reduce the goal to its premises. Rewrite using `[map_mul, ← e3, smul_mulVec, Pi.smul_apply, e2, map_mul, map_pow, map_pow, eo_X, eo_red, map_mul, map_pow, smul_eq_mul, mul_left_comm, hs]`. Both sides reduce to the same expression. Take `⟨r, hr⟩` from `mem_range_eo bk m _ _ e4`.

Conclude with `⟨r, by rw [e3, hr]⟩`. Use `choose r hr using this`. Conclude with `⟨r, funext hr⟩)`. Use `⟨Y, ?_, hYm⟩` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`.

Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `cW _ ≠ 0`. Rewrite using `[RingHom.map_det]`. Establish `e : cW.mapMatrix (Y.map (inclW l)) = Y.map (al.comp cA)` using `Matrix.ext fun i j => hcc _`. Rewrite using `[e]`.

Conclude with `hY`.
-/
theorem GlobalTheory.BSP.saturated_module_free : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (mem : (Fin d → Ainf l) → Prop), mem 0 → (∀ y z, mem y → mem z → mem (y + z)) → (∀ (c : bk.S) y, mem y → mem (fun a => bk.ev c * y a)) → (∀ y, mem (fun a => (l : Ainf l) * y a) → mem y) → (∀ y : ℕ → Fin d → Ainf l, (∀ n, mem (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → mem z) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d) (Fin d) (WCb l)), (Y1.map (inclW l)).det ≠ 0 → IsUnit Y' → (∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a))) → (∀ y, mem y → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w) → ∃ Y : Matrix (Fin d) (Fin d) (Ainf l), IsUnit (Y.map (inclW l)) ∧ ∀ y, mem y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk d mem h0 hadd hsm hsat _ Y1 Y' hY1 hY' hm1 hOE
  classical
  let al := algebraMap (OCb l) (Cb l)
  have hal : Function.Injective al := IsFractionRing.injective _ _
  let cW := WittVector.constantCoeff (p := l) (R := Cb l)
  let cA := WittVector.constantCoeff (p := l) (R := OCb l)
  have hcc : ∀ x, cW (inclW l x) = al (cA x) := fun x => by
    simp [cW, cA, al, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]
  obtain ⟨U, rfl⟩ := hY'
  let Q : Matrix (Fin d) (Fin d) (Cb l) := (↑U⁻¹ : Matrix (Fin d) (Fin d) (WCb l)).map cW
  have hQ : Q.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 ((U⁻¹).isUnit.map cW.mapMatrix)).ne_zero
  choose c o ho using fun p : Fin d × Fin d => exists_pow_mul bk (Q p.1 p.2)
  let N := Finset.univ.sup c
  have hf : al bk.flat ≠ 0 := (map_ne_zero_iff _ hal).2 bk.flat_ne_zero
  have hP : ∀ i j, ∃ o', al bk.flat ^ N * Q i j = al o' := fun i j => by
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := c) (Finset.mem_univ (i, j)))
    refine ⟨bk.flat ^ e * o (i, j), ?_⟩
    rw [map_mul, map_pow, ← ho (i, j), show N = c (i, j) + e from he]
    ring
  choose o' ho' using hP
  obtain ⟨Y, hY, hYm⟩ := abstract l bk.ev (red bk) (red_surj bk) (al.comp cA) (al.comp (eo bk))
    (hal.comp (eo_injective bk)) (fun s => by rw [RingHom.comp_apply, RingHom.comp_apply, eo_red]; rfl)
    (fun x hx => (AinfDiv.dvd_iff x).2 (hal (by rw [map_zero]; exact hx))) mem h0 hadd hsm hsat sep_A (lim_S bk)
    Y1 (fun h => hY1 (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero])) hm1
    (al bk.flat ^ N • Q) (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hf)) hQ)
    (fun y hy => by
      obtain ⟨w, hw, hyw⟩ := hOE y hy
      have e1 : (↑U⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) *ᵥ (fun a => inclW l (y a)) = w := by
        rw [hyw, mulVec_mulVec, Units.inv_mul, one_mulVec]
      have : ∀ i, ∃ r, ((al bk.flat ^ N • Q) *ᵥ fun a => (al.comp cA) (y a)) i = al (eo bk r) := fun i => by
        have e2 : (Q *ᵥ fun a => (al.comp cA) (y a)) i = cW (w i) := by
          rw [← e1]
          simp [mulVec, dotProduct, Q, hcc]
        have e3 : ((al bk.flat ^ N • Q) *ᵥ fun a => (al.comp cA) (y a)) i = al (∑ a, o' i a * cA (y a)) := by
          simp [mulVec, dotProduct, ho']
        obtain ⟨m, s, hs⟩ := ((GlobalTheory.BSP.oe_mod_l l K bk).1 (cW (w i))).1 ⟨w i, hw i, rfl⟩
        have e4 : bk.flat ^ m * (∑ a, o' i a * cA (y a)) = eo bk (X ^ N * red bk s) := by
          apply hal
          rw [map_mul, ← e3, smul_mulVec, Pi.smul_apply, e2, map_mul, map_pow, map_pow, eo_X, eo_red, map_mul,
            map_pow, smul_eq_mul, mul_left_comm, hs]
          rfl
        obtain ⟨r, hr⟩ := mem_range_eo bk m _ _ e4
        exact ⟨r, by rw [e3, hr]⟩
      choose r hr using this
      exact ⟨r, funext hr⟩)
  refine ⟨Y, ?_, hYm⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change cW _ ≠ 0
  rw [RingHom.map_det]
  have e : cW.mapMatrix (Y.map (inclW l)) = Y.map (al.comp cA) := Matrix.ext fun i j => hcc _
  rw [e]
  exact hY
