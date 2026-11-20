import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ColmezLift

variable {A : Type} [CommRing A]

/- English proof (translation)
Establish `h1 : a ^ l - b ^ l ∈ Ideal.span {p} ^ (n + 1 + 1)` using `GlobalTheory.LTTilt.pow_l_sub_mem _ hl (by omega) (by rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact h)`. Establish `h2` using `GlobalTheory.LTTilt.pow_sub_mem _ h1 (l ^ (f - 1))`. Rewrite `h2` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul, ← pow_mul, ← pow_succ']`. Rewrite `h2` using `[show f - 1 + 1 = f by omega]`. Then use the resulting hypothesis.
-/
theorem pow_q_dvd {l : ℕ} [Fact l.Prime] {p : A} (hl : (l : A) ∈ Ideal.span {p}) {f : ℕ} (hf : 1 ≤ f)
    {a b : A} {n : ℕ} (h : p ^ (n + 1) ∣ a - b) : p ^ (n + 1 + 1) ∣ a ^ l ^ f - b ^ l ^ f := by
  have h1 : a ^ l - b ^ l ∈ Ideal.span {p} ^ (n + 1 + 1) :=
    GlobalTheory.LTTilt.pow_l_sub_mem _ hl (by omega) (by rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact h)
  have h2 := GlobalTheory.LTTilt.pow_sub_mem _ h1 (l ^ (f - 1))
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  rwa [show f - 1 + 1 = f by omega] at h2

def phi (p : A) (ψ : A ≃+* A) (q : ℕ) (y : A) : A := ψ.symm (p * y + y ^ q)

/- English proof (translation)
Establish `hsp : ψ.symm p = p` using `(ψ.symm_apply_eq).2 hψp.symm`. Establish `hsd : ∀ {n : ℕ} {a : A}, p ^ n ∣ a → p ^ n ∣ ψ.symm a` using `fun {n a} ⟨c, hc⟩ => ⟨ψ.symm c, by rw [hc, map_mul, map_pow, hsp]⟩`. Establish `hΦ : ∀ (n : ℕ) (a b : A), p ^ (n + 1) ∣ a - b → p ^ (n + 1 + 1) ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b`. Introduce `n a b h`. Establish `e : phi p ψ (l ^ f) a - phi p ψ (l ^ f) b = ψ.symm (p * (a - b) + (a ^ l ^ f - b ^ l ^ f))`.

Rewrite using `[phi, phi, ← map_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hsd (dvd_add (by rw [pow_succ']; exact mul_dvd_mul_left p h) (pow_q_dvd hl hf h))`.

Establish `hΦ' : ∀ (n : ℕ) (a b : A), p ^ n ∣ a - b → p ^ n ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b`. Introduce `n a b h`. Consider the cases of `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `one_dvd _`.

Consider the case `succ k => exact (pow_dvd_pow p (by omega)).trans (hΦ k a b h)`. Establish `h1 : ∀ y, p ∣ phi p ψ (l ^ f) y - y`. Introduce `y`. Take `⟨c, hc⟩` from `hψ y`. Establish `e : phi p ψ (l ^ f) y - y = ψ.symm (p * (y - c))`.

Rewrite using `[phi, ← (ψ.symm_apply_apply y), ← map_sub, ψ.symm_apply_apply]`. Use `congr 1`. Take the linear combination `-hc`. Rewrite using `[e]`. Rewrite using `[map_mul, hsp]`.

Conclude with `dvd_mul_right p _`. Set `y : ℕ → A` to `fun n => (phi p ψ (l ^ f))^[n] y0`. Establish `hy : ∀ n, y (n + 1) = phi p ψ (l ^ f) (y n)` using `fun n => Function.iterate_succ_apply' _ n y0`. Establish `hstep : ∀ n, p ^ (n + 1) ∣ y (n + 1) - y n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => rw [zero_add, pow_one, hy]`. Conclude with `h1 _`. Consider the case `succ n ih => have h := hΦ n _ _ ih`. Rewrite `h` using `[← hy, ← hy]`. Then use the resulting hypothesis.

Establish `hcauchy : ∀ m k, p ^ m ∣ y m - y (m + k)`. Introduce `m k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `e : y m - y (m + (k + 1)) = (y m - y (m + k)) - (y (m + k + 1) - y (m + k))`. Rewrite using `[← add_assoc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_sub ih ((pow_dvd_pow p (by omega)).trans (hstep (m + k)))`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {p}) y fun {m n} hmn => by`. Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `hcauchy m k`. Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hL`.

Establish `hfix : phi p ψ (l ^ f) L = L`. Use `sub_eq_zero.1 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus p _ fun n => Ideal.mem_span_singleton.2 ?_)` and prove the remaining obligations. Establish `e : phi p ψ (l ^ f) L - L = (y (n + 1) - L) - (phi p ψ (l ^ f) (y n) - phi p ψ (l ^ f) L)`. Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `dvd_sub ((pow_dvd_pow p n.le_succ).trans (hL (n + 1))) (hΦ' n _ _ (hL n))`. Use `⟨L, ?_, ?_⟩` and prove the remaining obligations. Establish `e : L - y0 = (y 1 - y 0) - (y 1 - L)` using `by simp [y]`. Rewrite using `[e]`.

Conclude with `dvd_sub (by simpa using hstep 0) (by simpa using hL 1)`. Conclude with `((ψ.symm_apply_eq).1 hfix).symm`.
-/
theorem exists_fix (p : A) [IsAdicComplete (Ideal.span {p}) A] (l : ℕ) [Fact l.Prime]
    (hl : (l : A) ∈ Ideal.span {p}) (f : ℕ) (hf : 1 ≤ f) (ψ : A ≃+* A) (hψp : ψ p = p)
    (hψ : ∀ a, p ∣ ψ a - a ^ l ^ f) (y0 : A) : ∃ ω, p ∣ ω - y0 ∧ ψ ω = p * ω + ω ^ l ^ f := by
  have hsp : ψ.symm p = p := (ψ.symm_apply_eq).2 hψp.symm
  have hsd : ∀ {n : ℕ} {a : A}, p ^ n ∣ a → p ^ n ∣ ψ.symm a := fun {n a} ⟨c, hc⟩ =>
    ⟨ψ.symm c, by rw [hc, map_mul, map_pow, hsp]⟩
  have hΦ : ∀ (n : ℕ) (a b : A), p ^ (n + 1) ∣ a - b →
      p ^ (n + 1 + 1) ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b := by
    intro n a b h
    have e : phi p ψ (l ^ f) a - phi p ψ (l ^ f) b =
        ψ.symm (p * (a - b) + (a ^ l ^ f - b ^ l ^ f)) := by
      rw [phi, phi, ← map_sub]; congr 1; ring
    rw [e]
    exact hsd (dvd_add (by rw [pow_succ']; exact mul_dvd_mul_left p h) (pow_q_dvd hl hf h))
  have hΦ' : ∀ (n : ℕ) (a b : A), p ^ n ∣ a - b → p ^ n ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b := by
    intro n a b h
    cases n with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ k => exact (pow_dvd_pow p (by omega)).trans (hΦ k a b h)
  have h1 : ∀ y, p ∣ phi p ψ (l ^ f) y - y := by
    intro y
    obtain ⟨c, hc⟩ := hψ y
    have e : phi p ψ (l ^ f) y - y = ψ.symm (p * (y - c)) := by
      rw [phi, ← (ψ.symm_apply_apply y), ← map_sub, ψ.symm_apply_apply]
      congr 1
      linear_combination -hc
    rw [e]
    rw [map_mul, hsp]
    exact dvd_mul_right p _
  let y : ℕ → A := fun n => (phi p ψ (l ^ f))^[n] y0
  have hy : ∀ n, y (n + 1) = phi p ψ (l ^ f) (y n) := fun n => Function.iterate_succ_apply' _ n y0
  have hstep : ∀ n, p ^ (n + 1) ∣ y (n + 1) - y n := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, hy]; exact h1 _
    | succ n ih => have h := hΦ n _ _ ih; rwa [← hy, ← hy] at h
  have hcauchy : ∀ m k, p ^ m ∣ y m - y (m + k) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : y m - y (m + (k + 1)) = (y m - y (m + k)) - (y (m + k + 1) - y (m + k)) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_sub ih ((pow_dvd_pow p (by omega)).trans (hstep (m + k)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) y fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hL
  have hfix : phi p ψ (l ^ f) L = L := by
    refine sub_eq_zero.1 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus p _ fun n => Ideal.mem_span_singleton.2 ?_)
    have e : phi p ψ (l ^ f) L - L = (y (n + 1) - L) - (phi p ψ (l ^ f) (y n) - phi p ψ (l ^ f) L) := by
      rw [hy]; ring
    rw [e]
    exact dvd_sub ((pow_dvd_pow p n.le_succ).trans (hL (n + 1))) (hΦ' n _ _ (hL n))
  refine ⟨L, ?_, ?_⟩
  · have e : L - y0 = (y 1 - y 0) - (y 1 - L) := by simp [y]
    rw [e]
    exact dvd_sub (by simpa using hstep 0) (by simpa using hL 1)
  · exact ((ψ.symm_apply_eq).1 hfix).symm

open GlobalTheory.AinfK in

/- English proof (translation)
Introduce `l _ K π hπ x`. Use `haveI := complete_pi hπ`. Take `⟨ω, h1, h2⟩` from `exists_fix (inO K π) l (Ideal.mem_span_singleton.2 (dvd_l hπ)) (fK K) (NeZero.pos (fK K)) (RingEquiv.ofBijective (frobq K) (frobq_bijective K)) (frobq_inO K π) (dvd_frobq_sub hπ) (inA K (WittVector.teichmuller l x))`. Conclude with `⟨ω, ((red_eq_iff hπ _ _).2 h1).trans (red_teich x), h2⟩`.
-/
theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ x : OCb l,
    ∃ ω : AK K, red K ω = x ∧ frobq K ω = inO K π * ω + ω ^ l ^ fK K := by
  intro l _ K π hπ x
  haveI := complete_pi hπ
  obtain ⟨ω, h1, h2⟩ := exists_fix (inO K π) l (Ideal.mem_span_singleton.2 (dvd_l hπ)) (fK K)
    (NeZero.pos (fK K)) (RingEquiv.ofBijective (frobq K) (frobq_bijective K)) (frobq_inO K π)
    (dvd_frobq_sub hπ) (inA K (WittVector.teichmuller l x))
  exact ⟨ω, ((red_eq_iff hπ _ _).2 h1).trans (red_teich x), h2⟩

end GlobalTheory.ColmezLift
