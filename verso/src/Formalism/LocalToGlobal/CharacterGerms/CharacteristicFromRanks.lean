import Formalism.LocalToGlobal.CharacterGerms.Interface
import Formalism.LocalToGlobal.CharacterGerms.ExistsStrictMonoMinor

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace CharacteristicFromRanks

variable {C : Type} [Field C]

def pT {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (G g).ty (Sum.inl c) = b).card

def CHProp {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ) (big : Fin 2 → ZMod d → Prop) : Prop :=
  ∀ g a, big g a → ∀ u : Fin n → I g → C, IsSat V u →
    (∀ c x, (G g).ty (Sum.inl x) ≠ a → u c x = 0) →
    ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      ((Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, big g a) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

/- English proof (translation)
The claim follows from `X.CH`.
-/
example {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) : CHProp X.G X.n X.j X.j' X.big := X.CH

def intR (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' {_ _} ha hb := VF.Ge.mul_int (V := V) ha hb
  one_mem' := VF.Ge.one (V := V)
  add_mem' {_ _} ha hb := VF.Ge.add (V := V) ha hb
  zero_mem' := VF.Ge.zero (V := V) 0
  neg_mem' {_} ha := VF.Ge.neg (V := V) ha

def vR (V : VF C) : AddValuation (intR V) (WithTop ℝ) := V.v.comap (intR V).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vR_apply (V : VF C) (x : intR V) : vR V x = V.v (x : C) := rfl

/- English proof (translation)
Introduce `x`. Rewrite using `[vR_apply]`. Establish `h : V.Ge 0 (x : C)` using `x.2`. Unfold `VF.Ge at h`. Simplify using `using h`.
-/
theorem vR_nonneg (V : VF C) : ∀ x, 0 ≤ vR V x := by
  intro x
  rw [vR_apply]
  have h : V.Ge 0 (x : C) := x.2
  unfold VF.Ge at h
  simpa using h

/- English proof (translation)
Rewrite using `[show ((M.det : intR V) : C) = (intR V).subtype M.det from rfl, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem coe_det (V : VF C) {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m (intR V)) :
    ((M.det : intR V) : C) = (Matrix.of fun i k => (M i k : C)).det := by
  rw [show ((M.det : intR V) : C) = (intR V).subtype M.det from rfl, RingHom.map_det]
  rfl

/- English proof (translation)
Unfold `S4.lenCoker`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[vR_apply, coe_det]`. Both sides reduce to the same expression.
-/
theorem lenCoker_coe (V : VF C) {m h : ℕ} (α : Matrix (Fin m) (Fin h) (intR V)) :
    S4.lenCoker (vR V) α = S4.lenCoker V.v (Matrix.of fun i k => (α i k : C)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vR_apply, coe_det]
  rfl

/- English proof (translation)
Rewrite using `[show (∑ c, F (e c)) = ∑ s : {x // P x}, F s from Equiv.sum_comp e (fun s => F s), ← Finset.sum_subtype (Finset.univ.filter P) (by simp) F, Finset.sum_filter_of_ne]`. Introduce `x _ hx`. Assume the negation of the conclusion as `hP`. Conclude with `hx (hF x hP)`.
-/
theorem sum_type {ι : Type} [Fintype ι] (P : ι → Prop) {m : ℕ} (e : Fin m ≃ {x // P x})
    (F : ι → C) (hF : ∀ x, ¬ P x → F x = 0) : ∑ c, F (e c) = ∑ x, F x := by
  rw [show (∑ c, F (e c)) = ∑ s : {x // P x}, F s from Equiv.sum_comp e (fun s => F s),
    ← Finset.sum_subtype (Finset.univ.filter P) (by simp) F, Finset.sum_filter_of_ne]
  intro x _ hx
  by_contra hP
  exact hx (hF x hP)

/- English proof (translation)
Take `⟨hu_int, w, hw_int, huw⟩` from `hu`. Use `⟨Matrix.of fun c i => ⟨ht i (e c), ht_int i _⟩, Matrix.of fun c k => ⟨u c (e k), hu_int c _⟩, Matrix.of fun k c => ⟨w (e k) c, hw_int _ c⟩, ?_, fun c i => rfl, fun f => ?_⟩` and prove the remaining obligations. Use extensionality with `c c'`. Establish `hs` using `sum_type P e (fun x => u c x * w x c') (fun x hx => by rw [hsupp c x hx, zero_mul])`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]`.

Use `push_cast`. Rewrite using `[hs, huw]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[vR_apply, coe_det]`. Use `congr 2`.

Use extensionality with `k c`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply]`. Use `push_cast`. Establish `hs` using `sum_type P e (fun x => ht (f k) x * u c x) (fun x hx => by rw [hsupp c x hx, mul_zero])`. Rewrite using `[← hs]`.

Conclude with `Finset.sum_congr rfl fun x _ => mul_comm _ _`.
-/
theorem pick (V : VF C) {ι : Type} [Fintype ι] (P : ι → Prop) {p n h : ℕ}
    (e : Fin p ≃ {x // P x}) (u : Fin n → ι → C) (hu : IsSat V u)
    (hsupp : ∀ c x, ¬ P x → u c x = 0) (ht : Fin h → ι → C) (ht_int : ∀ i x, V.Ge 0 (ht i x)) :
    ∃ (αR : Matrix (Fin p) (Fin h) (intR V)) (SR : Matrix (Fin n) (Fin p) (intR V))
      (WR : Matrix (Fin p) (Fin n) (intR V)), SR * WR = 1 ∧
      (∀ c i, (αR c i : C) = ht i (e c)) ∧
      ∀ f : Fin n → Fin h, vR V (Matrix.of fun k c => (SR * αR) c (f k)).det =
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht (f ρ) x * u c x).det := by
  obtain ⟨hu_int, w, hw_int, huw⟩ := hu
  refine ⟨Matrix.of fun c i => ⟨ht i (e c), ht_int i _⟩, Matrix.of fun c k => ⟨u c (e k), hu_int c _⟩,
    Matrix.of fun k c => ⟨w (e k) c, hw_int _ c⟩, ?_, fun c i => rfl, fun f => ?_⟩
  · ext c c'
    have hs := sum_type P e (fun x => u c x * w x c') (fun x hx => by rw [hsupp c x hx, zero_mul])
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    push_cast
    rw [hs, huw]
    split_ifs <;> simp
  · rw [vR_apply, coe_det]
    congr 2
    ext k c
    simp only [Matrix.of_apply, Matrix.mul_apply]
    push_cast
    have hs := sum_type P e (fun x => ht (f k) x * u c x) (fun x hx => by rw [hsupp c x hx, mul_zero])
    rw [← hs]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/- English proof (translation)
Use `MvPowerSeries.ext fun m => ?_` and prove the remaining obligations. Use `show ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = MvPowerSeries.coeff m 1`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Rewrite using `[zero_pow hk, map_zero, zero_div]`. Introduce `h`. Simplify using `at h`.
-/
theorem mvExp_zero {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  refine MvPowerSeries.ext fun m => ?_
  show ∑ k ∈ Finset.range (m.degree + 1),
      MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = MvPowerSeries.coeff m 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
  · intro h
    simp at h

/- English proof (translation)
Rewrite using `[← MvPolynomial.coe_one, MvPowerSeries.subst_coe, map_one]`.
-/
theorem subst_one' {σ τ : Type} (a : σ → MvPowerSeries τ C) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPolynomial.coe_one, MvPowerSeries.subst_coe, map_one]

/- English proof (translation)
Use `⟨1, fun μ => ?_, (subst_one' _).symm⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `VF.Ge.one (V := V)`. Conclude with `VF.Ge.zero (V := V) 0`.
-/
theorem one_mem_IntGerm {V : VF C} {I : Fin 2 → Type} (t : ∀ g, I g → MvPowerSeries (I g) C) :
    (1 : MvPowerSeries (WV I) C) ∈ IntGerm V t := by
  refine ⟨1, fun μ => ?_, (subst_one' _).symm⟩
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact VF.Ge.one (V := V)
  · exact VF.Ge.zero (V := V) 0

/- English proof (translation)
Simplify using `only [zero_smul, Finset.sum_const_zero, mvExp_zero]`. Unfold `upG`. Rewrite using `[subst_one']`. Conclude with `one_mem_IntGerm t`.
-/
theorem zero_germ {V : VF C} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (g : Fin 2)
    (t : ∀ g, I g → MvPowerSeries (I g) C) :
    upG g (mvExp (∑ x : I g, (0 : C) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
      IntGerm V t := by
  simp only [zero_smul, Finset.sum_const_zero, mvExp_zero]
  unfold upG
  rw [subst_one']
  exact one_mem_IntGerm t

/- English proof (translation)
Establish `hd2 : 2 ≤ d`. Take `⟨k, hk⟩` from `hd`. Use `NeZero.ne d` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `haveI : Fact (1 < d) := ⟨by omega⟩`.

Rewrite using `[ZMod.val_add, ZMod.val_one]`. Establish `hb` using `ZMod.val_lt b`. Break down `Nat.lt_or_ge (b.val + 1) d with h | h` into its components or cases. Rewrite using `[Nat.mod_eq_of_lt h, Nat.even_add_one]`. Establish `heq : b.val + 1 = d` using `by omega`.

Rewrite using `[heq, Nat.mod_self]`. Use `iff_of_true ⟨0, rfl⟩ fun hbe => ?_` and prove the remaining obligations. Establish `h2 : Even (b.val + 1)` using `by rw [heq]; exact hd`. Rewrite `h2` using `[Nat.even_add_one]`. Conclude with `h2 hbe`.
-/
theorem even_val_succ {d : ℕ} [NeZero d] (hd : Even d) (b : ZMod d) :
    Even (b + 1).val ↔ ¬ Even b.val := by
  have hd2 : 2 ≤ d := by
    obtain ⟨k, hk⟩ := hd
    have := NeZero.ne d
    omega
  haveI : Fact (1 < d) := ⟨by omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  have hb := ZMod.val_lt b
  rcases Nat.lt_or_ge (b.val + 1) d with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.even_add_one]
  · have heq : b.val + 1 = d := by omega
    rw [heq, Nat.mod_self]
    refine iff_of_true ⟨0, rfl⟩ fun hbe => ?_
    have h2 : Even (b.val + 1) := by rw [heq]; exact hd
    rw [Nat.even_add_one] at h2
    exact h2 hbe

/- English proof (translation)
Introduce `b`. Establish `h0 : ∀ a, big 0 a ↔ Even a.val` using `hA.2`. Establish `h1 : ∀ a, big 1 a ↔ ¬ big 0 a` using `fun a => by simpa using big_compl 0 a`. Use `fin_cases g`. Use `show big 0 (b + 1) ↔ ¬ big 0 b`.

Rewrite using `[h0, h0, even_val_succ hA.1]`. Use `show big 1 (b + 1) ↔ ¬ big 1 b`. Rewrite using `[h1, h1, h0, h0, even_val_succ hA.1]`.
-/
theorem alt_step {d : ℕ} [NeZero d] (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (hA : Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) (g : Fin 2) :
    ∀ b, big g (b + 1) ↔ ¬ big g b := by
  intro b
  have h0 : ∀ a, big 0 a ↔ Even a.val := hA.2
  have h1 : ∀ a, big 1 a ↔ ¬ big 0 a := fun a => by simpa using big_compl 0 a
  fin_cases g
  · show big 0 (b + 1) ↔ ¬ big 0 b
    rw [h0, h0, even_val_succ hA.1]
  · show big 1 (b + 1) ↔ ¬ big 1 b
    rw [h1, h1, h0, h0, even_val_succ hA.1]

/- English proof (translation)
Introduce `hall`. Conclude with `((alt_step big big_compl hA g 0).1 (hall _)) (hall 0)`.
-/
theorem alt_not_allBig {d : ℕ} [NeZero d] (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (hA : Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) (g : Fin 2) : ¬ ∀ b, big g b := by
  intro hall
  exact ((alt_step big big_compl hA g 0).1 (hall _)) (hall 0)

/- English proof (translation)
Unfold `CHProp`. Introduce `g a hbig u hu hsupp`. Take `⟨e, hL1, hL2⟩` from `hLen g a hbig`. Take `⟨αR, SR, WR, hSW, hα, hdet⟩` from `pick V (fun x => (G g).ty (Sum.inl x) = a) e u hu (fun c x hx => hsupp c x hx) (ht g) (ht_int g)`. Establish `hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c))`.

Rewrite using `[lenCoker_coe]`. Use `congr 1`. Use extensionality with `c i`. Simplify using `only [Matrix.of_apply, hα]`. Establish `key : ∀ x : ℝ, S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ (x : WithTop ℝ) → ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧ (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X …`.

Introduce `x hx`. Rewrite `hx` using `[← hcoe]`. Take `⟨f, -, hf, -⟩` from `S4.ch_minor (vR V) (vR_nonneg V) SR WR hSW αR x hx`. Use `⟨fun ρ => ht g (f ρ), fun ρ x => ht_int g _ x, fun S t hT ρ => hGerm g (f ρ) S t hT, ?_⟩` and prove the remaining obligations. Use `show V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht g (f ρ) x * u c x).det ≤ _`.

Rewrite using `[← hdet f]`. Conclude with `hf.trans hx`. Distinguish the cases in `hA : Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)`. Take `⟨y, hy1, hy2, hy3⟩` from `key _ (hL1 hA)`. Conclude with `⟨y, hy1, hy2, fun _ => hy3, fun hall => absurd hall (alt_not_allBig big big_compl hA g)⟩`.

Distinguish the cases in `hall : ∀ b, big g b`. Take `⟨y, hy1, hy2, hy3⟩` from `key _ (hL2 hall)`. Conclude with `⟨y, hy1, hy2, fun h' => absurd h' hA, fun _ => hy3⟩`. Conclude with `⟨fun _ _ => 0, fun _ _ => VF.Ge.zero (V := V) 0, fun S t _ ρ => zero_germ g t, fun h' => absurd h' hA, fun h' => absurd h' hall⟩`.
-/
private theorem ch_core_lemma {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hLen : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  unfold CHProp
  intro g a hbig u hu hsupp
  obtain ⟨e, hL1, hL2⟩ := hLen g a hbig
  obtain ⟨αR, SR, WR, hSW, hα, hdet⟩ := pick V (fun x => (G g).ty (Sum.inl x) = a) e u hu
    (fun c x hx => hsupp c x hx) (ht g) (ht_int g)
  have hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) := by
    rw [lenCoker_coe]
    congr 1
    ext c i
    simp only [Matrix.of_apply, hα]
  have key : ∀ x : ℝ, S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ (x : WithTop ℝ) →
      ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
        (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
          ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
            IntGerm V t) ∧
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤ (x : WithTop ℝ) := by
    intro x hx
    rw [← hcoe] at hx
    obtain ⟨f, -, hf, -⟩ := S4.ch_minor (vR V) (vR_nonneg V) SR WR hSW αR x hx
    refine ⟨fun ρ => ht g (f ρ), fun ρ x => ht_int g _ x, fun S t hT ρ => hGerm g (f ρ) S t hT, ?_⟩
    show V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht g (f ρ) x * u c x).det ≤ _
    rw [← hdet f]
    exact hf.trans hx
  by_cases hA : Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)
  · obtain ⟨y, hy1, hy2, hy3⟩ := key _ (hL1 hA)
    exact ⟨y, hy1, hy2, fun _ => hy3, fun hall => absurd hall (alt_not_allBig big big_compl hA g)⟩
  · by_cases hall : ∀ b, big g b
    · obtain ⟨y, hy1, hy2, hy3⟩ := key _ (hL2 hall)
      exact ⟨y, hy1, hy2, fun h' => absurd h' hA, fun _ => hy3⟩
    · exact ⟨fun _ _ => 0, fun _ _ => VF.Ge.zero (V := V) 0, fun S t _ ρ => zero_germ g t,
        fun h' => absurd h' hA, fun h' => absurd h' hall⟩

/- English proof (translation)
Establish `hlodd : Odd V.l` using `V.l_prime.odd_of_ne_two l_odd`. Use `ch_core_lemma G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm` and prove the remaining obligations. Take `⟨e, hAe⟩` from `hAiii g a hb`. Establish `hrh : rh ≤ j'`. Establish `h1` using `rk_fil g a`.

Rewrite `h1` using `[rk_big g a hb]`. Use linear arithmetic over natural numbers and integers. Establish `hn : n ≤ pT G g a` using `by rw [rk_big g a hb]; omega`. Set `αR : Matrix (Fin (pT G g a)) (Fin (h g)) (intR V)` to `fun c i => ⟨ht g i (e c), ht_int g i _⟩`. Establish `hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c))` using `lenCoker_coe V αR`.

Establish `hAR : S4.ThmAiii (vR V) αR (l1 g a)`. Unfold `S4.ThmAiii`. Rewrite using `[hcoe]`. Conclude with `hAe`. Set `S : Matrix (Fin n) (Fin (pT G g a)) (intR V)` to `Matrix.of fun i k => if (k : ℕ) = i then 1 else 0`.

Set `W : Matrix (Fin (pT G g a)) (Fin n) (intR V)` to `Matrix.of fun k i => if (k : ℕ) = i then 1 else 0`. Establish `hSW : S * W = 1`. Use extensionality with `i i'`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, S, W]`. Rewrite using `[Finset.sum_eq_single (Fin.castLE hn i)]`.

Simplify using `[Fin.ext_iff]`. Introduce `k _ hk`. Establish `hki : (k : ℕ) ≠ i` using `fun hk' => hk (Fin.ext (by simp [hk']))`. Simplify using `[hki]`. Simplify using the standard rewrite rules.

Use `⟨e, fun hA => ?_, fun hall => ?_⟩` and prove the remaining obligations. Establish `H` using `S4.ch_inert (vR V) (vR_nonneg V) hA.1 V.l V.l_prime hlodd r n j j' rh (h g) r_eq (hh g) hrh (big g) (alt_step big big_compl hA g) (pT G g) (rk_big g) (rk_small g) a hb αR S W hSW (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR`. Rewrite using `[← hcoe]`. Conclude with `H.1.1.trans (WithTop.coe_le_coe.2 H.1.2.2)`. Establish `H` using `S4.ch_split (vR V) (vR_nonneg V) (NeZero.ne d) V.l V.l_prime hlodd r n j j' rh (h g) (n + j) (by omega) (hh g) hrh (pT G g) (fun τ => rk_big g τ (hall τ)) a αR S W hSW (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR`.

Rewrite using `[← hcoe]`. Conclude with `H.1.1.trans (WithTop.coe_le_coe.2 H.1.2)`.
-/
theorem characteristic_of_rank_split {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ)
    (r_eq : r = n + j + j') (big : Fin 2 → ZMod d → Prop)
    (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (rk_fil : ∀ g a, (Finset.univ.filter fun κ : J g => (G g).ty (Sum.inr κ) = a).card + rh +
      pT G g a = r)
    (l_odd : V.l ≠ 2)
    (h : Fin 2 → ℕ) (hh : ∀ g, h g + rh = r)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (l1 l2 : Fin 2 → ZMod d → ℝ)
    (hDET : ∀ g a, big g a → S4.CorDET V.l (pT G g) (l1 g) (l2 g) a)
    (hAi : ∀ g a, big g a → S4.ThmAi V.l r rh (pT G g) (l2 g) a)
    (hAiii : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      S4.ThmAiii V.v (Matrix.of fun c i => ht g i (e c)) (l1 g a))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  have hlodd : Odd V.l := V.l_prime.odd_of_ne_two l_odd
  refine ch_core_lemma G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm
  obtain ⟨e, hAe⟩ := hAiii g a hb
  have hrh : rh ≤ j' := by
    have h1 := rk_fil g a
    rw [rk_big g a hb] at h1
    omega
  have hn : n ≤ pT G g a := by rw [rk_big g a hb]; omega
  let αR : Matrix (Fin (pT G g a)) (Fin (h g)) (intR V) := fun c i => ⟨ht g i (e c), ht_int g i _⟩
  have hcoe : S4.lenCoker (vR V) αR = S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) :=
    lenCoker_coe V αR
  have hAR : S4.ThmAiii (vR V) αR (l1 g a) := by
    unfold S4.ThmAiii
    rw [hcoe]
    exact hAe
  let S : Matrix (Fin n) (Fin (pT G g a)) (intR V) := Matrix.of fun i k => if (k : ℕ) = i then 1 else 0
  let W : Matrix (Fin (pT G g a)) (Fin n) (intR V) := Matrix.of fun k i => if (k : ℕ) = i then 1 else 0
  have hSW : S * W = 1 := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, S, W]
    rw [Finset.sum_eq_single (Fin.castLE hn i)]
    · simp [Fin.ext_iff]
    · intro k _ hk
      have hki : (k : ℕ) ≠ i := fun hk' => hk (Fin.ext (by simp [hk']))
      simp [hki]
    · simp
  refine ⟨e, fun hA => ?_, fun hall => ?_⟩
  · have H := S4.ch_inert (vR V) (vR_nonneg V) hA.1 V.l V.l_prime hlodd r n j j' rh (h g) r_eq (hh g)
      hrh (big g) (alt_step big big_compl hA g) (pT G g) (rk_big g) (rk_small g) a hb αR S W hSW
      (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR
    rw [← hcoe]
    exact H.1.1.trans (WithTop.coe_le_coe.2 H.1.2.2)
  · have H := S4.ch_split (vR V) (vR_nonneg V) (NeZero.ne d) V.l V.l_prime hlodd r n j j' rh (h g)
      (n + j) (by omega) (hh g) hrh (pT G g) (fun τ => rk_big g τ (hall τ)) a αR S W hSW
      (l1 g) (l2 g) (hDET g a hb) (hAi g a hb) hAR
    rw [← hcoe]
    exact H.1.1.trans (WithTop.coe_le_coe.2 H.1.2)

/- English proof (translation)
Conclude with `ch_core_lemma G n j j' big big_compl h ht ht_int hLen hGerm`.
-/
theorem CH_of_lenCoker {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hLen : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  exact ch_core_lemma G n j j' big big_compl h ht ht_int hLen hGerm

def upB (l rp rm : ℕ) (w : ℝ) : ℝ := ((rp : ℝ) - rm) * w + (rm : ℝ) / ((l : ℝ) - 1)

/- English proof (translation)
Establish `hl' : (1 : ℝ) < l` using `by exact_mod_cast hl`. Unfold `gam`. Rewrite using `[div_le_div_iff₀ (by nlinarith) (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gam_le {l : ℕ} (hl : 1 < l) : gam l ≤ 1 / ((l : ℝ) - 1) := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  unfold gam
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/- English proof (translation)
Establish `hl' : (1 : ℝ) < l` using `by exact_mod_cast hl`. Unfold `gam`. Conclude with `div_nonneg (by linarith) (by nlinarith)`.
-/
theorem gam_nonneg {l : ℕ} (hl : 1 < l) : 0 ≤ gam l := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  unfold gam
  exact div_nonneg (by linarith) (by nlinarith)

/- English proof (translation)
Establish `h1` using `gam_le hl`. Establish `h0` using `gam_nonneg hl`. Establish `hL : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `upB`. Use `push_cast`. Rewrite using `[div_eq_mul_one_div ((j : ℝ) + j') ((l : ℝ) - 1), div_eq_mul_one_div (j' : ℝ) ((l : ℝ) - 1)]`. Establish `hq : 0 ≤ 1 / ((l : ℝ) - 1)` using `by positivity`. Establish `hj : (j : ℝ) * gam l ≤ j * (1 / ((l : ℝ) - 1))` using `mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j)`.

Establish `hj' : 0 ≤ (j' : ℝ) * gam l` using `mul_nonneg (Nat.cast_nonneg _) h0`. Establish `hj0 : 0 ≤ (j : ℝ) * (1 / ((l : ℝ) - 1))` using `mul_nonneg (Nat.cast_nonneg _) hq`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma upB_le_bounds {l : ℕ} (hl : 1 < l) (n j j' : ℕ) :
    upB l (n + j) j' (gam l) ≤ (n : ℝ) * gam l + ((j : ℝ) + j') / ((l : ℝ) - 1) ∧
      upB l (n + j) j' 0 ≤ ((j : ℝ) + j') / ((l : ℝ) - 1) := by
  have h1 := gam_le hl
  have h0 := gam_nonneg hl
  have hL : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  unfold upB
  push_cast
  rw [div_eq_mul_one_div ((j : ℝ) + j') ((l : ℝ) - 1), div_eq_mul_one_div (j' : ℝ) ((l : ℝ) - 1)]
  have hq : 0 ≤ 1 / ((l : ℝ) - 1) := by positivity
  have hj : (j : ℝ) * gam l ≤ j * (1 / ((l : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j)
  have hj' : 0 ≤ (j' : ℝ) * gam l := mul_nonneg (Nat.cast_nonneg _) h0
  have hj0 : 0 ≤ (j : ℝ) * (1 / ((l : ℝ) - 1)) := mul_nonneg (Nat.cast_nonneg _) hq
  constructor
  · nlinarith
  · nlinarith

/- English proof (translation)
Establish `hl1 : 1 < V.l` using `V.l_prime.one_lt`. Take `⟨hb1, hb2⟩` from `upB_le_bounds hl1 n j j'`. Use `CH_of_lenCoker G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm` and prove the remaining obligations. Take `⟨e, h1, h2⟩` from `hUP g a hb`. Conclude with `⟨e, fun hA => (h1 hA).trans (WithTop.coe_le_coe.2 hb1), fun hall => (h2 hall).trans (WithTop.coe_le_coe.2 hb2)⟩`.
-/
theorem CH_of_UP {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g)) (n j j' : ℕ)
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (hUP : ∀ g a, big g a → ∃ e : Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a},
      ((Even d ∧ ∀ b : ZMod d, (big 0 b ↔ Even b.val)) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤
          ((upB V.l (n + j) j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
      ((∀ b, big g b) →
        S4.lenCoker V.v (Matrix.of fun c i => ht g i (e c)) ≤ ((upB V.l (n + j) j' 0 : ℝ) : WithTop ℝ)))
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  have hl1 : 1 < V.l := V.l_prime.one_lt
  obtain ⟨hb1, hb2⟩ := upB_le_bounds hl1 n j j'
  refine CH_of_lenCoker G n j j' big big_compl h ht ht_int (fun g a hb => ?_) hGerm
  obtain ⟨e, h1, h2⟩ := hUP g a hb
  exact ⟨e, fun hA => (h1 hA).trans (WithTop.coe_le_coe.2 hb1),
    fun hall => (h2 hall).trans (WithTop.coe_le_coe.2 hb2)⟩

end CharacteristicFromRanks

end Formalism.L2.FormalSeriesBounds
