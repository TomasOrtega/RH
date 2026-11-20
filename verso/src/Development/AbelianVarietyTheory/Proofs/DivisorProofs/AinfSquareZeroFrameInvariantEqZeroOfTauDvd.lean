import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TauUniq

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

/- English proof (translation)
Establish `h1` using `congrArg (algebraMap F.B F.Q) h`. Simplify using `only [map_mul, map_natCast] at h1`. Conclude with `F.frame.inj (F.frame.unit_p.mul_left_cancel h1)`.
-/
theorem p_cancel {b c : F.B} (h : (p : F.B) * b = p * c) : b = c := by
  have h1 := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h1
  exact F.frame.inj (F.frame.unit_p.mul_left_cancel h1)

/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`.
-/
theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

/- English proof (translation)
Apply `p_cancel F` to reduce the goal to its premises. Establish `hS : WittVector.frobenius (Sandwich.mu ε) = Sandwich.mu ε * ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i`. Unfold `Sandwich.mu`. Rewrite using `[map_sub, map_one, frob_teich, mul_comm, geom_sum_mul]`. Establish `hd : Sandwich.mu ε ∣ ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O)`.

Establish `: ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) = ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε ^ i - 1)`. Simplify using `[Finset.sum_sub_distrib]`. Rewrite using `[this]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `i _`.

Simplify `sub_dvd_pow_sub_pow (WittVector.teichmuller p ε) 1 i` using `[Sandwich.mu, one_pow]`. Establish `h0` using `(F.τ_mul _).2 hd`. Rewrite `h0` using `[map_sub, map_natCast]`. Establish `h1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε))`. Rewrite using `[← F.σ_a, ← F.p_τ, map_mul, map_natCast]`.

Rewrite using `[h1, hS, map_mul, ← F.p_τ]`. Take the linear combination `(p : F.B) * h0`.
-/
theorem sigma_tau : F.σ F.τ = p * F.τ := by
  apply p_cancel F
  have hS : WittVector.frobenius (Sandwich.mu ε) =
      Sandwich.mu ε * ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
    unfold Sandwich.mu
    rw [map_sub, map_one, frob_teich, mul_comm, geom_sum_mul]
  have hd : Sandwich.mu ε ∣ ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) := by
    have : ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) =
        ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    apply Finset.dvd_sum
    intro i _
    simpa [Sandwich.mu, one_pow] using sub_dvd_pow_sub_pow (WittVector.teichmuller p ε) 1 i
  have h0 := (F.τ_mul _).2 hd
  rw [map_sub, map_natCast] at h0
  have h1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  rw [h1, hS, map_mul, ← F.p_τ]
  linear_combination (p : F.B) * h0

/- English proof (translation)
The claim follows from `mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])`.
-/
theorem theta_tau [IsDomain O] : F.θ F.τ = 0 :=
  mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Take `⟨x, y, rfl⟩` from `F.gen c`. Conclude with `⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩`.
-/
theorem dvd_tau {b : F.B} (h : F.τ ∣ b) : ∃ x, b = F.τ * F.a x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨x, y, rfl⟩ := F.gen c
  exact ⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩

/- English proof (translation)
Use `choose x y h using fun i j => F.gen (M i j)`. Conclude with `⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩`.
-/
theorem lift_exists {ι : Type} (M : Matrix ι ι F.B) :
    ∃ m : Matrix ι ι (Ainf p O), ∀ i j, F.τ ∣ M i j - F.a (m i j) := by
  choose x y h using fun i j => F.gen (M i j)
  exact ⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩

/- English proof (translation)
Establish `hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Simplify using `only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢`. Establish `hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) = Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j)))`.

Introduce `j`. Rewrite using `[← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]`.
-/
theorem step {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (u : ι → F.B) (u' : ι → Ainf p O)
    (hu : ∀ j, F.τ ∣ u j - F.a (u' j)) (i : ι) :
    F.τ ∣ M.mulVec (fun j => F.σ (u j)) i -
      F.a (m.mulVec (fun j => WittVector.frobenius (u' j)) i) := by
  have hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢
  have hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) =
      Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j))) := by
    intro j
    rw [← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]

/- English proof (translation)
Proceed by induction on `n generalizing i with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `step F M m hm _ _ ih i`.
-/
theorem iter {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (w : ι → Ainf p O) (n : ℕ) (i : ι) :
    F.τ ∣ (fun v : ι → F.B => M.mulVec fun j => F.σ (v j))^[n] (fun j => F.a (w j)) i -
      F.a ((fun v : ι → Ainf p O => m.mulVec fun j => WittVector.frobenius (v j))^[n] w i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step F M m hm _ _ ih i

/- English proof (translation)
Take `⟨N, hN⟩` from `hM`. Use `⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `iter F M m hm w N i`. Rewrite `hc` using `[sub_eq_iff_eq_add]`. Rewrite using `[hc, map_add, map_mul, theta_tau, zero_mul, zero_add, F.θ_a]`.

Conclude with `hu`.
-/
theorem nil_lift [IsDomain O] {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (hM : IsNil F.θ F.σ M) :
    IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) m := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩
  obtain ⟨c, hc⟩ := iter F M m hm w N i
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_mul, theta_tau, zero_mul, zero_add, F.θ_a]
  exact hu

/- English proof (translation)
Take `⟨m, hm⟩` from `lift_exists F M`. Establish `key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i`. Introduce `i`. Rewrite using `[← F.τ_mul, map_sub, mul_sub, hz i]`. Take `⟨c, hc⟩` from `step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i`.

Rewrite `hc` using `[sub_eq_iff_eq_add]`. Rewrite using `[hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]`. Conclude with `(F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)`.
-/
theorem core (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    [Algebra O C] [IsDomain O] (hv : v.Integers O) (hε : IsPrimitiveSystem ε) {ι : Type} [Fintype ι]
    (M : Matrix ι ι F.B) (hM : IsNil F.θ F.σ M) (z : ι → Ainf p O)
    (hz : ∀ i, F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i) (i : ι) :
    F.τ * F.a (z i) = 0 := by
  obtain ⟨m, hm⟩ := lift_exists F M
  have key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i := by
    intro i
    rw [← F.τ_mul, map_sub, mul_sub, hz i]
    obtain ⟨c, hc⟩ := step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]
  exact (F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)

/- English proof (translation)
Apply `p_cancel F` to reduce the goal to its premises. Establish `e` using `hg i`. Simplify using `only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e`. Rewrite using `[← e]`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem vec_eq {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (g : ι → F.B) (z : ι → Ainf p O)
    (hz : ∀ i, g i = F.τ * F.a (z i))
    (hg : ∀ i, M.mulVec (fun j => F.σ (g j)) i = (p : F.B) * g i) (i : ι) :
    F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i := by
  apply p_cancel F
  have e := hg i
  simp only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem blk_mul_blk (d k : ℕ) (R : Type) [CommRing R] (u : R) :
    blk d k 1 u * blk d k u 1 = u • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  rw [blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2`. Establish `hdet : IsUnit U.transpose.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.isUnit_iff_isUnit_det U).1 hU`. Use `⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩` and prove the remaining obligations.

Use `choose z hz using fun i c => dvd_tau F (hdiv i c)`. Establish `hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y`. Rewrite using `[hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)), ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]`. Use extensionality with `i c`. Rewrite using `[hz i c, Matrix.zero_apply]`.

Use `core F C v hv hε _ hN1 (fun j => z j c) (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i` and prove the remaining obligations. Establish `e` using `congrArg (fun X => X i c) hM`. Simplify `e` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use `choose z hz using fun i => dvd_tau F (hdiv i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[hz i, Pi.zero_apply]`. Conclude with `core F C v hv hε _ hN2 z (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i`.
-/
theorem eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2
  have hdet : IsUnit U.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det U).1 hU
  refine ⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩
  · choose z hz using fun i c => dvd_tau F (hdiv i c)
    have hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)),
        ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul]
    ext i c
    rw [hz i c, Matrix.zero_apply]
    refine core F C v hv hε _ hN1 (fun j => z j c)
      (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i
    have e := congrArg (fun X => X i c) hM
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using e
  · choose z hz using fun i => dvd_tau F (hdiv i)
    funext i
    rw [hz i, Pi.zero_apply]
    exact core F C v hv hε _ hN2 z
      (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i

end GlobalTheory.TauUniq
