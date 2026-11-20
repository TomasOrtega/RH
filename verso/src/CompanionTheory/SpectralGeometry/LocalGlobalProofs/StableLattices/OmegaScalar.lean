import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement

noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def evAt (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) fun a => (Algebra.commutes u a).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evAt_apply (u : ℂ) (p : A[X]) : evAt u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A v) else 0) + C (E a b)

/- English proof (translation)
Unfold `tmPoly Tm`. Apply the tactic sequence `by_cases h : a = b <;> simp [h, evAt_apply, map_sub]`.
-/
theorem evAt_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v u : ℂ) (a b : Fin n) :
    evAt u (tmPoly E v a b) = Tm E (u - v) a b := by
  unfold tmPoly Tm
  by_cases h : a = b <;> simp [h, evAt_apply, map_sub]

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A[X]) *
    (List.ofFn fun k : Fin n => tmPoly E ((k : ℕ) : ℂ) (σ k) k).prod

/- English proof (translation)
Unfold `qdet qminor qdetPoly`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Simplify using `[Function.comp_def, evAt_tmPoly]`.
-/
theorem evAt_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by
  unfold qdet qminor qdetPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  simp [Function.comp_def, evAt_tmPoly]

end Poly

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `φ`. Use `set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr`. Establish `hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h)`. Introduce `u`.

Establish `e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h`. Rewrite using `[evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]`. Both sides reduce to the same expression.

Rewrite using `[e1, hr]`. Simplify using `[eval_finsetSum, map_sum, eval_monomial, mul_comm]`. Establish `hz : r = 0`. Use `eq_zero_of_infinite_isRoot r ?_` and prove the remaining obligations. Use `Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl` and prove the remaining obligations.

Introduce `u hu`. Establish `hu' : u ≠ b` using `hu`. Express the relevant statement in the definitionally equal form `r.eval u = 0`. Rewrite using `[hev, H u hu', sub_self, map_zero]`. Rewrite using `[← hev, hz, eval_zero]`.
-/
theorem cont {M : Type*} [AddCommGroup M] [Module ℂ M] (p : (Module.End ℂ M)[X]) (q : ℂ[X]) (h : M) (b : ℂ)
    (H : ∀ u, u ≠ b → evAt u p h = q.eval u • h) : evAt b p h = q.eval b • h := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr
  have hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h) := by
    intro u
    have e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h := by
      rw [evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]
      rfl
    rw [e1, hr]
    simp [eval_finsetSum, map_sum, eval_monomial, mul_comm]
  have hz : r = 0 := by
    refine eq_zero_of_infinite_isRoot r ?_
    refine Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl
    intro u hu
    have hu' : u ≠ b := hu
    change r.eval u = 0
    rw [hev, H u hu', sub_self, map_zero]
  rw [← hev, hz, eval_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[LinearMap.compLeft_apply]`.
-/
theorem compLeft_smul_one {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by
  funext i
  simp [LinearMap.compLeft_apply]

/- English proof (translation)
Establish `hq : qdet X.E u = Formalism.QuantumDeterminants.capP χ (u - cn n) • (1 : Module.End ℂ X.V)`. Use `hS (u - cn n)` as an intermediate fact. Rewrite `this` using `[show u - cn n + ((n : ℂ) - 1) / 2 = u by unfold cn; ring]`. Then use the resulting hypothesis. Establish `h` using `LinearMap.congr_fun (GlobalTheory.T.QuantumDeterminantTensor n X u) w`. Rewrite `h` using `[hq]`.

Simplify `h` using `[Module.End.mul_apply, compLeft_smul_one]`.
-/
theorem tens_apply {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (hS : ScalChar X χ) (u : ℂ) (w : Fin n → X.V) :
    qdet (tensE X) u (u • w + om X w) =
      Formalism.QuantumDeterminants.capP χ (u - cn n) • ((u + 1) • w + om X w) := by
  have hq : qdet X.E u = Formalism.QuantumDeterminants.capP χ (u - cn n) • (1 : Module.End ℂ X.V) := by
    have := hS (u - cn n)
    rwa [show u - cn n + ((n : ℂ) - 1) / 2 = u by unfold cn; ring] at this
  have h := LinearMap.congr_fun (GlobalTheory.T.QuantumDeterminantTensor n X u) w
  rw [hq] at h
  simpa [Module.End.mul_apply, compLeft_smul_one] using h

/- English proof (translation)
Use `set a : ℂ := χ s - cn n with ha`. Use `set h : Fin n → X.V := om X g - a • g with hh`. Use `set ct : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) with hct`. Establish `hc : ∀ u, Formalism.QuantumDeterminants.capP χ (u - cn n) = (u + a) * ct u`. Introduce `u`.

Use `Finset.mul_prod_erase univ (fun t => u - cn n + χ t) (mem_univ s)` as an intermediate fact. Simplify using `only [Formalism.QuantumDeterminants.capP, hct]`. Rewrite using `[← this, ha]`. Put the polynomial expressions in normal form. Use `set q : ℂ[X] := (∏ t ∈ univ.erase s, (Polynomial.X - C (cn n) + C (χ t))) * (Polynomial.X + C (a + 1)) with hq`.

Establish `hqe : ∀ u, q.eval u = ct u * (u + (a + 1))`. Introduce `u`. Simplify using `[hq, hct, eval_prod]`. Establish `hne : ∀ u, u ≠ -a → evAt u (qdetPoly (tensE X)) h = q.eval u • h`. Introduce `u hu`.

Establish `hw : u + a ≠ 0` using `fun e => hu (eq_neg_of_add_eq_zero_left e)`. Establish `e` using `tens_apply X χ hS u h`. Rewrite `e` using `[h2, hc]`. Rewrite using `[evAt_qdetPoly, hqe]`. Establish `e1 : u • h + a • h = (u + a) • h` using `(add_smul _ _ _).symm`.

Establish `e2 : (u + 1) • h + a • h = (u + (a + 1)) • h` using `by rw [← add_smul]; ring_nf`. Rewrite `e` using `[e1, e2, map_smul, smul_smul, mul_assoc, ← smul_smul]`. Conclude with `smul_right_injective _ hw e`. Establish `hb` using `cont _ q h (-a) hne`. Rewrite `hb` using `[evAt_qdetPoly, hqe]`.

Establish `hzero : qdet (tensE X) (-a) h = 0`. Establish `e` using `tens_apply X χ hS (-a) g`. Rewrite `e` using `[hc]`. Establish `e0 : (-a) • g + om X g = h` using `by rw [hh, neg_smul]; abel`. Rewrite `e` using `[e0]`.

Rewrite using `[e]`. Simplify using the standard rewrite rules. Rewrite `hb` using `[hzero]`. Establish `hct0 : ct (-a) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun t ht => ?_` and prove the remaining obligations.

Establish `ht' : t ≠ s` using `Finset.ne_of_mem_erase ht`. Establish `: -a - cn n + χ t = χ t - χ s` using `by rw [ha]; ring`. Rewrite using `[this]`. Conclude with `sub_ne_zero.2 (hs t ht')`. Establish `hfin : ct (-a) • h = 0`.

Establish `: ct (-a) * (-a + (a + 1)) = ct (-a)` using `by ring`. Rewrite `hb` using `[this]`. Conclude with `hb.symm`. Conclude with `(smul_eq_zero.1 hfin).resolve_left hct0`.
-/
theorem core {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hS : ScalChar X χ)
    (hs : ∀ r, r ≠ s → χ r ≠ χ s) (g : Fin n → X.V)
    (h2 : om X (om X g - (χ s - cn n) • g) = (χ s - cn n) • (om X g - (χ s - cn n) • g)) :
    om X g - (χ s - cn n) • g = 0 := by
  set a : ℂ := χ s - cn n with ha
  set h : Fin n → X.V := om X g - a • g with hh
  set ct : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) with hct
  have hc : ∀ u, Formalism.QuantumDeterminants.capP χ (u - cn n) = (u + a) * ct u := by
    intro u
    have := Finset.mul_prod_erase univ (fun t => u - cn n + χ t) (mem_univ s)
    simp only [Formalism.QuantumDeterminants.capP, hct]
    rw [← this, ha]
    ring_nf
  set q : ℂ[X] := (∏ t ∈ univ.erase s, (Polynomial.X - C (cn n) + C (χ t))) * (Polynomial.X + C (a + 1)) with hq
  have hqe : ∀ u, q.eval u = ct u * (u + (a + 1)) := by
    intro u
    simp [hq, hct, eval_prod]
  have hne : ∀ u, u ≠ -a → evAt u (qdetPoly (tensE X)) h = q.eval u • h := by
    intro u hu
    have hw : u + a ≠ 0 := fun e => hu (eq_neg_of_add_eq_zero_left e)
    have e := tens_apply X χ hS u h
    rw [h2, hc] at e
    rw [evAt_qdetPoly, hqe]
    have e1 : u • h + a • h = (u + a) • h := (add_smul _ _ _).symm
    have e2 : (u + 1) • h + a • h = (u + (a + 1)) • h := by rw [← add_smul]; ring_nf
    rw [e1, e2, map_smul, smul_smul, mul_assoc, ← smul_smul] at e
    exact smul_right_injective _ hw e
  have hb := cont _ q h (-a) hne
  rw [evAt_qdetPoly, hqe] at hb
  have hzero : qdet (tensE X) (-a) h = 0 := by
    have e := tens_apply X χ hS (-a) g
    rw [hc] at e
    have e0 : (-a) • g + om X g = h := by rw [hh, neg_smul]; abel
    rw [e0] at e
    rw [e]
    simp
  rw [hzero] at hb
  have hct0 : ct (-a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    have ht' : t ≠ s := Finset.ne_of_mem_erase ht
    have : -a - cn n + χ t = χ t - χ s := by rw [ha]; ring
    rw [this]
    exact sub_ne_zero.2 (hs t ht')
  have hfin : ct (-a) • h = 0 := by
    have : ct (-a) * (-a + (a + 1)) = ct (-a) := by ring
    rw [this] at hb
    exact hb.symm
  exact (smul_eq_zero.1 hfin).resolve_left hct0

/- English proof (translation)
Introduce `n X χ s hS hs f hf`. Use `set T : Module.End ℂ (Fin n → X.V) := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hT`. Establish `hTa : ∀ w, T w = om X w - (χ s - cn n) • w` using `fun w => by simp [hT]`. Establish `key : ∀ k : ℕ, (T ^ (k + 1)) f = 0 → T f = 0`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Introduce `hk`. Use `ih ?_` and prove the remaining obligations.

Establish `h2 : T (T ((T ^ k) f)) = 0`. Rewrite using `[← hk, pow_succ' T (k + 1), pow_succ' T k]`. Both sides reduce to the same expression. Establish `h3` using `core X χ s hS hs ((T ^ k) f) (by`. Rewrite `h2` using `[hTa]`.

Rewrite using `[← hTa]`. Conclude with `sub_eq_zero.1 h2)`. Rewrite `h3` using `[← hTa]`. Rewrite using `[pow_succ' T k]`. Conclude with `h3`.

Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hf`. Establish `hk' : (T ^ (k + 1)) f = 0`. Rewrite using `[pow_succ' T k, Module.End.mul_apply]`. Establish `: (T ^ k) f = 0` using `hk`. Rewrite using `[this, map_zero]`.

Use `key k hk'` as an intermediate fact. Rewrite `this` using `[hTa]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem omScal : OmScal := by
  intro n X χ s hS hs f hf
  set T : Module.End ℂ (Fin n → X.V) := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hT
  have hTa : ∀ w, T w = om X w - (χ s - cn n) • w := fun w => by simp [hT]
  have key : ∀ k : ℕ, (T ^ (k + 1)) f = 0 → T f = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      refine ih ?_
      have h2 : T (T ((T ^ k) f)) = 0 := by
        rw [← hk, pow_succ' T (k + 1), pow_succ' T k]
        rfl
      have h3 := core X χ s hS hs ((T ^ k) f) (by
        rw [hTa] at h2
        rw [← hTa]
        exact sub_eq_zero.1 h2)
      rw [← hTa] at h3
      rw [pow_succ' T k]
      exact h3
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have hk' : (T ^ (k + 1)) f = 0 := by
    rw [pow_succ' T k, Module.End.mul_apply]
    have : (T ^ k) f = 0 := hk
    rw [this, map_zero]
  have := key k hk'
  rw [hTa] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
