import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

open Ideal WittVector

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp A R _ _ _ _ _ φ hp0 hsurj hker π hπ0 hπ hdiv`. Establish `hpp : p.Prime` using `hp.out`. Establish `: CharP (R ⧸ Ideal.span {(p : R)}) p` using `(inferInstance : CharP (ModP R p) p)`. Use `set g := (Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ with hg`. Establish `hf : ∀ n, φ (π (n + 1)) ^ p = φ (π n)` using `fun n => by rw [← map_pow, hπ]`.

Use `⟨ReciprocityTheory.PGsh.ofRoots (fun n => φ (π n)) hf, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.PGsh.untilt_ofRoots, hπ0, map_natCast]`. Introduce `c hc`. Establish `hz : ∀ x, g x = 0 ↔ (p : A) ∣ x` using `fun x => by`. Rewrite using `[← RingHom.mem_ker, hker, Ideal.mem_span_singleton]`.

Establish `hππ : ∀ n, π n ^ p ^ n = p`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [hπ0]`. Consider the case `succ n ih => rw [pow_succ', pow_mul, hπ, ih]`.

Establish `hcs : ∀ n, Perfection.coeff (ModP R p) p (n + 1) c ^ p = Perfection.coeff (ModP R p) p n c` using `fun n => Perfection.coeff_pow_p' c n`. Establish `hc0 : Perfection.coeff (ModP R p) p 0 c = 0` using `by rw [← PreTilt.coeff_def]; exact hc`. Establish `hcp : ∀ n, Perfection.coeff (ModP R p) p n c ^ p ^ n = 0`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using hc0`. Consider the case `succ n ih => rw [pow_succ', pow_mul, hcs, ih]`. Use `choose y hy using fun n => hsurj (show R ⧸ Ideal.span {(p : R)} from Perfection.coeff (ModP R p) p n c)`. Establish `hyp : ∀ n, (p : A) ∣ y n ^ p ^ n` using `fun n => (hz _).1 (by rw [map_pow, hy]; exact hcp n)`. Use `choose z hzy using fun n => hdiv n (y n) (hyp n)`.

Establish `compat : ∀ n, g (z (n + 2) ^ p) ^ p = g (z (n + 1) ^ p)`. Introduce `n`. Use `set b := z (n + 2) ^ p - z (n + 1) with hb`. Establish `h1 : π (n + 1) * b = y (n + 2) ^ p - y (n + 1)`. Rewrite using `[hzy (n + 2), hzy (n + 1), mul_pow, hπ (n + 1), hb]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : g (π (n + 1) * b) = 0`. Rewrite using `[h1, map_sub, map_pow, hy, hy]`. Conclude with `sub_eq_zero.2 (hcs (n + 1))`. Take `⟨w, hw⟩` from `(hz _).1 h2`.

Establish `e1 : π n * b ^ p = (p : A) ^ p * w ^ p` using `by rw [← hπ n, ← mul_pow, hw, mul_pow]`. Establish `hp2 : (p : A) ^ p = (p : A) ^ (p - 2) * (p : A) ^ 2`. Rewrite using `[← pow_add, Nat.sub_add_cancel hpp.two_le]`. Establish `hn1 : π n ^ p ^ n = π n ^ (p ^ n - 1) * π n`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hpp.pos)]`.

Establish `e2 : (p : A) * b ^ p = (p : A) * ((p : A) * ((p : A) ^ (p - 2) * w ^ p * π n ^ (p ^ n - 1)))`. Combine the equalities or inequalities in the displayed calculation. Establish `hbp : g (b ^ p) = 0` using `(hz _).2 ⟨_, mul_left_cancel₀ hp0 e2⟩`. Establish `hz2 : z (n + 2) ^ p = z (n + 1) + b` using `by rw [hb]; ring`. Rewrite using `[← map_pow, ← pow_mul, mul_comm, pow_mul, hz2, map_pow, map_add, add_pow_char, ← map_pow g b, hbp, add_zero, map_pow]`.

Set `d : PreTilt R p` to `⟨fun n => g (z (n + 1) ^ p), fun n => compat n⟩`. Use `⟨d, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Use `show Perfection.coeff (ModP R p) p n c = g (π n) * g (z (n + 1) ^ p)`. Rewrite using `[← map_mul, ← hπ n, ← mul_pow, ← hzy (n + 1), map_pow, hy, hcs]`.
-/
theorem pflat_dvd_of_roots : ∀ (p : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [IsDomain A] [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R] (φ : A →+* R), (p : A) ≠ 0 →
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) →
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) = Ideal.span {(p : A)} →
    ∀ π : ℕ → A, π 0 = p → (∀ n, π (n + 1) ^ p = π n) → (∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x) →
    ∃ pflat : PreTilt R p, PreTilt.untilt pflat = (p : R) ∧ ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c := by
  intro p hp A R _ _ _ _ _ φ hp0 hsurj hker π hπ0 hπ hdiv
  classical
  have hpp : p.Prime := hp.out
  have : CharP (R ⧸ Ideal.span {(p : R)}) p := (inferInstance : CharP (ModP R p) p)
  set g := (Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ with hg
  have hf : ∀ n, φ (π (n + 1)) ^ p = φ (π n) := fun n => by rw [← map_pow, hπ]
  refine ⟨ReciprocityTheory.PGsh.ofRoots (fun n => φ (π n)) hf, ?_, ?_⟩
  · rw [ReciprocityTheory.PGsh.untilt_ofRoots, hπ0, map_natCast]
  intro c hc
  have hz : ∀ x, g x = 0 ↔ (p : A) ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hππ : ∀ n, π n ^ p ^ n = p := by
    intro n
    induction n with
    | zero => simp [hπ0]
    | succ n ih => rw [pow_succ', pow_mul, hπ, ih]
  have hcs : ∀ n, Perfection.coeff (ModP R p) p (n + 1) c ^ p = Perfection.coeff (ModP R p) p n c :=
    fun n => Perfection.coeff_pow_p' c n
  have hc0 : Perfection.coeff (ModP R p) p 0 c = 0 := by rw [← PreTilt.coeff_def]; exact hc
  have hcp : ∀ n, Perfection.coeff (ModP R p) p n c ^ p ^ n = 0 := by
    intro n
    induction n with
    | zero => simpa using hc0
    | succ n ih => rw [pow_succ', pow_mul, hcs, ih]
  choose y hy using fun n => hsurj (show R ⧸ Ideal.span {(p : R)} from Perfection.coeff (ModP R p) p n c)
  have hyp : ∀ n, (p : A) ∣ y n ^ p ^ n := fun n => (hz _).1 (by rw [map_pow, hy]; exact hcp n)
  choose z hzy using fun n => hdiv n (y n) (hyp n)
  have compat : ∀ n, g (z (n + 2) ^ p) ^ p = g (z (n + 1) ^ p) := by
    intro n
    set b := z (n + 2) ^ p - z (n + 1) with hb
    have h1 : π (n + 1) * b = y (n + 2) ^ p - y (n + 1) := by
      rw [hzy (n + 2), hzy (n + 1), mul_pow, hπ (n + 1), hb]; ring
    have h2 : g (π (n + 1) * b) = 0 := by
      rw [h1, map_sub, map_pow, hy, hy]
      exact sub_eq_zero.2 (hcs (n + 1))
    obtain ⟨w, hw⟩ := (hz _).1 h2
    have e1 : π n * b ^ p = (p : A) ^ p * w ^ p := by rw [← hπ n, ← mul_pow, hw, mul_pow]
    have hp2 : (p : A) ^ p = (p : A) ^ (p - 2) * (p : A) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hpp.two_le]
    have hn1 : π n ^ p ^ n = π n ^ (p ^ n - 1) * π n := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hpp.pos)]
    have e2 : (p : A) * b ^ p = (p : A) * ((p : A) * ((p : A) ^ (p - 2) * w ^ p * π n ^ (p ^ n - 1))) := by
      calc (p : A) * b ^ p = π n ^ p ^ n * b ^ p := by rw [hππ]
        _ = π n ^ (p ^ n - 1) * (π n * b ^ p) := by rw [hn1]; ring
        _ = _ := by rw [e1, hp2]; ring
    have hbp : g (b ^ p) = 0 := (hz _).2 ⟨_, mul_left_cancel₀ hp0 e2⟩
    have hz2 : z (n + 2) ^ p = z (n + 1) + b := by rw [hb]; ring
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hz2, map_pow, map_add, add_pow_char, ← map_pow g b, hbp,
      add_zero, map_pow]
  let d : PreTilt R p := ⟨fun n => g (z (n + 1) ^ p), fun n => compat n⟩
  refine ⟨d, Perfection.ext fun n => ?_⟩
  show Perfection.coeff (ModP R p) p n c = g (π n) * g (z (n + 1) ^ p)
  rw [← map_mul, ← hπ n, ← mul_pow, ← hzy (n + 1), map_pow, hy, hcs]

end GlobalTheory
