import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.Dual

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

def twE {A : Type*} [Ring A] (E : Fin n → Fin n → A) (a b : Fin n) : A := -E b a

/- English proof (translation)
Introduce `a b c d`. Use `h b a d c` as an intermediate fact. Simplify using `only [twE, neg_mul_neg]`. Rewrite using `[this]`. Use `clear this`.

Establish `k1 : (a = d) ↔ (d = a)` using `eq_comm`. Establish `k2 : (c = b) ↔ (b = c)` using `eq_comm`. Simplify using `only [k1, k2]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel`.
-/
theorem glRel_twE {A : Type*} [Ring A] {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (twE E) := by
  intro a b c d
  have := h b a d c
  simp only [twE, neg_mul_neg]
  rw [this]
  clear this
  have k1 : (a = d) ↔ (d = a) := eq_comm
  have k2 : (c = b) ↔ (b = c) := eq_comm
  simp only [k1, k2]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel

/- English proof (translation)
Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[capEntry, twE, add_comm]`. Simplify using `[capEntry, twE, h, Ne.symm h]`.
-/
theorem capEntry_twE {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
    capEntry (twE E) y a b = -capEntry E (-y) b a := by
  by_cases h : a = b
  · subst h; simp [capEntry, twE, add_comm]
  · simp [capEntry, twE, h, Ne.symm h]

/- English proof (translation)
Introduce `p`. Proceed by induction on `p with`. Consider the case `zero => intro f`. Simplify using the standard rewrite rules. Consider the case `succ p ih`.

Introduce `f`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]`. Apply the tactic sequence `rcases neg_one_pow_eq_or A p with h | h <;> simp [h, pow_succ]`.
-/
theorem ofFn_neg_prod {A : Type*} [Ring A] : ∀ {p : ℕ} (f : Fin p → A),
    (List.ofFn fun j => -f j).prod = (-1) ^ p * (List.ofFn f).prod := by
  intro p
  induction p with
  | zero => intro f; simp
  | succ p ih =>
    intro f
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]
    rcases neg_one_pow_eq_or A p with h | h <;> simp [h, pow_succ]

/- English proof (translation)
Unfold `capelliC`. Rewrite using `[cminor_eq_rminor E hE]`. Unfold `cminor rminor`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `have e : (fun j : Fin n => capEntry (twE E) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) = fun j : Fin n => -capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j) (id (σ j)) := by`. Use function extensionality and compare the values at `j`. Rewrite using `[capEntry_twE]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, ofFn_neg_prod, mul_smul_comm]`.
-/
theorem capelliC_twE {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (hE : GlRelR E) (x : ℂ) :
    capelliC (twE E) x = (-1) ^ n * capelliC E ((n : ℂ) - 1 - x) := by
  unfold capelliC
  rw [cminor_eq_rminor E hE]
  unfold cminor rminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : (fun j : Fin n => capEntry (twE E) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      fun j : Fin n => -capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j) (id (σ j)) := by
    funext j
    rw [capEntry_twE]
    congr 2
    ring
  rw [e, ofFn_neg_prod, mul_smul_comm]

def tw (X : GMod n) : GMod n := ⟨X.V, twE X.E, glRel_twE X.gl⟩

/- English proof (translation)
Unfold `Formalism.QuantumDeterminants.capP`. Establish `: ∀ s : Fin n, Y + (-χ) s = (-1) * (-Y + χ s)` using `fun s => by simp; ring`. Simplify using `only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem capelliPoly_neg (χ : Fin n → ℂ) (Y : ℂ) : Formalism.QuantumDeterminants.capP (-χ) Y = (-1) ^ n * Formalism.QuantumDeterminants.capP χ (-Y) := by
  unfold Formalism.QuantumDeterminants.capP
  have : ∀ s : Fin n, Y + (-χ) s = (-1) * (-Y + χ s) := fun s => by simp; ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Use `⟨k, fun Y => ?_⟩` and prove the remaining obligations. Establish `h0` using `hk (-Y)`. Use `show (qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V)) ^ k = 0`. Establish `e : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V) = (-1 : Module.End ℂ X.V) ^ n * (qdet X.E (-Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ (-Y) • (1 : Module.End ℂ X.V))`.

Establish `h1 : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) = (-1 : Module.End ℂ X.V) ^ n * qdet X.E (-Y + ((n : ℂ) - 1) / 2)`. Rewrite using `[qdet_eq_capelliC, qdet_eq_capelliC]`. Use `capelliC_twE X.E X.gl (Y + ((n : ℂ) - 1) / 2)` as an intermediate fact. Establish `e2 : (n : ℂ) - 1 - (Y + ((n : ℂ) - 1) / 2) = -Y + ((n : ℂ) - 1) / 2` using `by ring`. Rewrite `this` using `[e2]`.

Conclude with `this`. Rewrite using `[h1, capelliPoly_neg, mul_sub]`. Use `congr 1`. Apply the tactic sequence `rcases Nat.even_or_odd n with h | h <;> simp [h.neg_one_pow]`. Rewrite using `[e, ((Commute.neg_one_left _).pow_left n).mul_pow, h0, mul_zero]`.
-/
theorem hasChar_tw {X : GMod n} {χ : Fin n → ℂ} (h : HasChar X χ) : HasChar (tw X) (-χ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  have h0 := hk (-Y)
  show (qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V)) ^ k = 0
  have e : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V) =
      (-1 : Module.End ℂ X.V) ^ n *
        (qdet X.E (-Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ (-Y) • (1 : Module.End ℂ X.V)) := by
    have h1 : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) =
        (-1 : Module.End ℂ X.V) ^ n * qdet X.E (-Y + ((n : ℂ) - 1) / 2) := by
      rw [qdet_eq_capelliC, qdet_eq_capelliC]
      have := capelliC_twE X.E X.gl (Y + ((n : ℂ) - 1) / 2)
      have e2 : (n : ℂ) - 1 - (Y + ((n : ℂ) - 1) / 2) = -Y + ((n : ℂ) - 1) / 2 := by ring
      rw [e2] at this
      exact this
    rw [h1, capelliPoly_neg, mul_sub]
    congr 1
    rcases Nat.even_or_odd n with h | h <;> simp [h.neg_one_pow]
  rw [e, ((Commute.neg_one_left _).pow_left n).mul_pow, h0, mul_zero]

/- English proof (translation)
Unfold `capelliC cminor`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_list_prod, List.map_ofFn]`. Apply the tactic sequence `have e : (⇑φ ∘ fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) = fun j : Fin n => capEntry (fun a b => φ (E a b)) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j) := by`.

Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp, capEntry, map_add]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`.
-/
theorem capelliC_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (x : ℂ) : φ (capelliC E x) = capelliC (fun a b => φ (E a b)) x := by
  unfold capelliC cminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_zsmul, map_list_prod, List.map_ofFn]
  have e : (⇑φ ∘ fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      fun j : Fin n => capEntry (fun a b => φ (E a b)) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j) := by
    funext j
    simp only [Function.comp, capEntry, map_add]
    split_ifs <;> simp
  rw [e]

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Take `⟨k, hk⟩` from `hX`. Use `⟨k, fun Y => ?_⟩` and prove the remaining obligations. Set `φ : Module.End ℂ X.V →ₐ[ℂ] Module.End ℂ X'.V` to `(LinearEquiv.conjAlgEquiv ℂ e).toAlgHom`. Establish `hE : (fun a b => φ (X.E a b)) = X'.E`.

Use function extensionality and compare the values at `a b`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `he a b (e.symm y)` as an intermediate fact. Simplify `this` using `[φ, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply]`. Establish `h1 : ∀ x : ℂ, qdet X'.E x = φ (qdet X.E x)` using `fun x => by`.

Rewrite using `[qdet_eq_capelliC, qdet_eq_capelliC, capelliC_map φ, hE]`. Use `congrArg φ (hk Y)` as an intermediate fact. Simplify `this` using `[map_pow, map_sub, h1]`.
-/
theorem hasChar_of_iso {X X' : GMod n} {χ : Fin n → ℂ} (h : Iso X X') (hX : HasChar X χ) : HasChar X' χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun Y => ?_⟩
  let φ : Module.End ℂ X.V →ₐ[ℂ] Module.End ℂ X'.V := (LinearEquiv.conjAlgEquiv ℂ e).toAlgHom
  have hE : (fun a b => φ (X.E a b)) = X'.E := by
    funext a b
    refine LinearMap.ext fun y => ?_
    have := he a b (e.symm y)
    simpa [φ, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply] using this
  have h1 : ∀ x : ℂ, qdet X'.E x = φ (qdet X.E x) := fun x => by
    rw [qdet_eq_capelliC, qdet_eq_capelliC, capelliC_map φ, hE]
  have := congrArg φ (hk Y)
  simpa [map_pow, map_sub, h1] using this

/- English proof (translation)
Use `LinearMap.ext fun (u : Fin n → X.V) => funext fun b => ?_` and prove the remaining obligations. Use `show ∑ a, (-X.E b a) (u a) = eeVd X.E u b`. Rewrite using `[eeVd_apply']`. Simplify using the standard rewrite rules.
-/
theorem om_tw (X : GMod n) : om (tw X) = omD X := by
  refine LinearMap.ext fun (u : Fin n → X.V) => funext fun b => ?_
  show ∑ a, (-X.E b a) (u a) = eeVd X.E u b
  rw [eeVd_apply']
  simp

/- English proof (translation)
Unfold `stepSub backSub`. Rewrite using `[om_tw]`. Both sides reduce to the same expression.
-/
theorem stepSub_tw (X : GMod n) (z : ℂ) : stepSub (tw X) (-z) = backSub X z := by
  unfold stepSub backSub
  rw [om_tw]
  rfl

/- English proof (translation)
Take `⟨K, hK⟩` from `GlobalTheory.T.CayleyHamiltonHk n (tw X) (-χ) (hasChar_tw h)`. Use `⟨K, ?_⟩` and prove the remaining obligations. Establish `e : (fun t : Fin n => om (tw X) - ((-χ) t - cn n) • (1 : Module.End ℂ (Fin n → (tw X).V))) = fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))`. Use function extensionality and compare the values at `t`. Rewrite using `[om_tw]`.

Both sides reduce to the same expression. Rewrite `hK` using `[e]`. Conclude with `hK`.
-/
theorem dual_cayley (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) :
    ∃ K : ℕ, ((List.ofFn fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))).prod) ^ K = 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.T.CayleyHamiltonHk n (tw X) (-χ) (hasChar_tw h)
  refine ⟨K, ?_⟩
  have e : (fun t : Fin n => om (tw X) - ((-χ) t - cn n) • (1 : Module.End ℂ (Fin n → (tw X).V))) =
      fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V)) := by
    funext t
    rw [om_tw]
    rfl
  rw [e] at hK
  exact hK

/- English proof (translation)
Use `GlobalTheory.T.HeckeNonVanishing n (tw X) (-χ) s (hasChar_tw h) hne (fun r e => hfree r (by` as an intermediate fact. Simplify using `only [Pi.neg_apply] at e`. Take the linear combination `-e))`. Establish `t : stepSub (tw X) (-χ s) ≠ ⊥` using `this`. Rewrite `t` using `[stepSub_tw]`.

Conclude with `t`.
-/
theorem dual_nonvan (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) (s : Fin n) (hne : Nontrivial X.V)
    (hfree : ∀ r, χ r ≠ χ s - 1) : backSub X (χ s) ≠ ⊥ := by
  have := GlobalTheory.T.HeckeNonVanishing n (tw X) (-χ) s (hasChar_tw h) hne (fun r e => hfree r (by
    simp only [Pi.neg_apply] at e
    linear_combination -e))
  have t : stepSub (tw X) (-χ s) ≠ ⊥ := this
  rw [stepSub_tw] at t
  exact t

/- English proof (translation)
Establish `e3 : ∀ p q : X.V, -(-p + q) = p - q` using `fun p q => by abel`. Use function extensionality and compare the values at `i`. Rewrite using `[ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd_apply']`. Conclude with `e3 (X.E a b (y i)) (if i = b then y a else 0)`.
-/
theorem tw_tens (X : GMod n) (a b : Fin n) (y : Fin n → X.V) :
    -(tensE (tw X) b a y) = ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b y := by
  have e3 : ∀ p q : X.V, -(-p + q) = p - q := fun p q => by abel
  funext i
  rw [ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd_apply']
  exact e3 (X.E a b (y i)) (if i = b then y a else 0)

set_option maxHeartbeats 200000 in
/- English proof (translation)
Set `S : Submodule ℂ (Fin n → X.V)` to `stepSub (tw X) (-z)`. Set `e : ↥S ≃ₗ[ℂ] ↥(backSub X z)` to `LinearEquiv.ofEq S (backSub X z) (stepSub_tw X z)`. Establish `l0 : ∀ w : ↥S, Subtype.val (e w) = Subtype.val w` using `fun w => LinearEquiv.coe_ofEq_apply _ w`. Use `⟨e, ?_⟩` and prove the remaining obligations. Introduce `a b x`.

Apply `Subtype.ext` to reduce the goal to its premises. Set `y : Fin n → X.V` to `Subtype.val (show ↥S from x)`. Establish `l1 : Subtype.val (show ↥S from (tw (step (tw X) (-z))).E a b x) = -(tensE (tw X) b a y)` using `rfl`. Establish `r1 : ∀ w : ↥(backSub X z), Subtype.val ((back X z hB).E a b w) = ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b w.val` using `fun _ => rfl`. Conclude with `(l0 _).trans (l1.trans ((tw_tens X a b y).trans ((congrArg (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b) (l0 x).symm).trans (r1 (e x)).symm)))`.
-/
theorem iso_back (X : GMod n) (z : ℂ) (hB : ∀ a b, ∀ x ∈ backSub X z, (tensD X).E a b x ∈ backSub X z) :
    Iso (tw (step (tw X) (-z))) (back X z hB) := by
  let S : Submodule ℂ (Fin n → X.V) := stepSub (tw X) (-z)
  let e : ↥S ≃ₗ[ℂ] ↥(backSub X z) := LinearEquiv.ofEq S (backSub X z) (stepSub_tw X z)
  have l0 : ∀ w : ↥S, Subtype.val (e w) = Subtype.val w := fun w => LinearEquiv.coe_ofEq_apply _ w
  refine ⟨e, ?_⟩
  intro a b x
  apply Subtype.ext
  let y : Fin n → X.V := Subtype.val (show ↥S from x)
  have l1 : Subtype.val (show ↥S from (tw (step (tw X) (-z))).E a b x) = -(tensE (tw X) b a y) := rfl
  have r1 : ∀ w : ↥(backSub X z), Subtype.val ((back X z hB).E a b w) =
      ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b w.val := fun _ => rfl
  exact (l0 _).trans (l1.trans ((tw_tens X a b y).trans
    ((congrArg (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b) (l0 x).symm).trans (r1 (e x)).symm)))

/- English proof (translation)
Establish `hT : HasChar (tw (step (tw X) (-χ s))) (-(-χ + Pi.single s 1))` using `hasChar_tw (GlobalTheory.T.InfinitesimalCharacterStatement n (tw X) (-χ) s (hasChar_tw h))`. Establish `e : -(-χ + Pi.single s 1) = χ - Pi.single s 1`. Rewrite using `[neg_add, neg_neg, sub_eq_add_neg]`. Rewrite `hT` using `[e]`. Conclude with `hasChar_of_iso (iso_back X (χ s) hB) hT`.
-/
theorem dual_char (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) (s : Fin n)
    (hB : ∀ a b, ∀ x ∈ backSub X (χ s), (tensD X).E a b x ∈ backSub X (χ s)) :
    HasChar (back X (χ s) hB) (χ - Pi.single s 1) := by
  have hT : HasChar (tw (step (tw X) (-χ s))) (-(-χ + Pi.single s 1)) :=
    hasChar_tw (GlobalTheory.T.InfinitesimalCharacterStatement n (tw X) (-χ) s (hasChar_tw h))
  have e : -(-χ + Pi.single s 1) = χ - Pi.single s 1 := by
    rw [neg_add, neg_neg, sub_eq_add_neg]
  rw [e] at hT
  exact hasChar_of_iso (iso_back X (χ s) hB) hT

/- English proof (translation)
Introduce `_ X χ h` and use `⟨dual_cayley X χ h, fun s hB => dual_char X χ h s hB, fun s hne hf => dual_nonvan X χ h s hne hf⟩`.
-/
theorem dualFacts : DualFacts := fun _ X χ h =>
  ⟨dual_cayley X χ h, fun s hB => dual_char X χ h s hB, fun s hne hf => dual_nonvan X χ h s hne hf⟩

end GlobalTheory.CompanionTheory.RgExhHecke.Dual
