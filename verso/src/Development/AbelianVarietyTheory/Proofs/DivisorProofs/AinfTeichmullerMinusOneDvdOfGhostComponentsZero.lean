import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.GhostKer

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius]`. Unfold `phiInv`. Use extensionality with `n`. Simplify using `only [WittVector.map_coeff]`. Conclude with `(_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _`.
-/
theorem phiInv_frobenius (b : Ainf p O) : phiInv p O (WittVector.frobenius b) = b := by
  rw [WittVector.frobenius_eq_map_frobenius]
  unfold phiInv
  ext n
  simp only [WittVector.map_coeff]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]`.
-/
theorem frobenius_iterate_teichmuller (k : ℕ) (x : PreTilt O p) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[k] (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

variable (p O) in

def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by rw [ghost, iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

/- English proof (translation)
Establish `h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1`. Rewrite using `[ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ', pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]`. Establish `h0` using `hε.zeta_zero`. Simplify using `only [zeta, Function.iterate_zero, id] at h0`. Rewrite using `[h0, one_pow]`.

Express the relevant statement in the definitionally equal form `ghostHom p O (k + 1) (xi ε) = p`. Unfold `xi`. Rewrite using `[map_sum]`. Simplify using `only [map_pow]`. Express the relevant statement in the definitionally equal form `∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p`.

Simplify using `[h]`.
-/
theorem ghost_succ_xi {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (k : ℕ) :
    ghost p O (k + 1) (xi ε) = p := by
  have h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1 := by
    rw [ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ',
      pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]
    have h0 := hε.zeta_zero
    simp only [zeta, Function.iterate_zero, id] at h0
    rw [h0, one_pow]
  change ghostHom p O (k + 1) (xi ε) = p
  unfold xi
  rw [map_sum]
  simp only [map_pow]
  change ∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p
  simp [h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nu_eq_mu_root (x : PreTilt O p) : nu x = mu (root x) := rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha`. Establish `h1 : IsPrimitiveRoot (root ε).untilt p` using `by simpa [zeta] using hε 1`. Establish `hp0 : (p : O) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (algebraMap O C) h`.

Rewrite `h2` using `[map_natCast, map_zero]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2`. Establish `key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro a _`. Conclude with `dvd_mul_right _ _`. Consider the case `succ n ih`. Introduce `a ha`. Establish `ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p)`.

Rewrite using `[RingHom.mem_ker]`. Conclude with `ha 0`. Rewrite `ha0` using `[GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton]`. Take `⟨b, rfl⟩` from `ha0`. Establish `hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0`.

Introduce `m`. Rewrite using `[ghost_frobenius]`. Establish `h3` using `ha (m + 1)`. Rewrite `h3` using `[ghost_mul, ghost_succ_xi hε]`. Conclude with `(mul_eq_zero.1 h3).resolve_left hp0`.

Take `⟨c, hc⟩` from `ih _ hb`. Establish `hc'` using `congrArg (phiInv p O) hc`. Establish `e : root (root^[n] ε) = root^[n + 1] ε` using `(Function.iterate_succ_apply' root n ε).symm`. Rewrite `hc'` using `[map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e]`. Use `⟨phiInv p O c, ?_⟩` and prove the remaining obligations.

Take the linear combination `xi ε * hc' + phiInv p O c * xi_mul_nu ε`. Conclude with `GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)`.
-/
theorem mu_dvd_of_ghost : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a := by
    intro n
    induction n with
    | zero => intro a _; exact dvd_mul_right _ _
    | succ n ih =>
      intro a ha
      have ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
        rw [RingHom.mem_ker]; exact ha 0
      rw [GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton] at ha0
      obtain ⟨b, rfl⟩ := ha0
      have hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0 := by
        intro m
        rw [ghost_frobenius]
        have h3 := ha (m + 1)
        rw [ghost_mul, ghost_succ_xi hε] at h3
        exact (mul_eq_zero.1 h3).resolve_left hp0
      obtain ⟨c, hc⟩ := ih _ hb
      have hc' := congrArg (phiInv p O) hc
      have e : root (root^[n] ε) = root^[n + 1] ε := (Function.iterate_succ_apply' root n ε).symm
      rw [map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e] at hc'
      refine ⟨phiInv p O c, ?_⟩
      linear_combination xi ε * hc' + phiInv p O c * xi_mul_nu ε
  exact GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)

end GlobalTheory.GhostKer
