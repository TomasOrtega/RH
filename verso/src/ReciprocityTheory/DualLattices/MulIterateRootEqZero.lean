import Mathlib
import ReciprocityTheory.DualLattices.CyclicRecursionStatement

noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Use extensionality with `n`. Establish `h'` using `congrArg (fun z => WittVector.coeff z n) h`. Simplify using `only [WittVector.coeff_frobenius_charP] at h'`.

Apply `(frobeniusEquiv R p).injective` to reduce the goal to its premises. Rewrite using `[_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]`. Conclude with `h'`. Introduce `x`. Use `⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩` and prove the remaining obligations.

Use extensionality with `n`. Rewrite using `[WittVector.coeff_frobenius_charP, WittVector.coeff_mk]`. Establish `h` using `(frobeniusEquiv R p).apply_symm_apply (x.coeff n)`. Rewrite `h` using `[_root_.frobeniusEquiv_apply, frobenius_def]`. Then use the resulting hypothesis.
-/
private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Rewrite using `[← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]`. Introduce `hx`.

Take `⟨y, hy⟩` from `(frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))`. Use `Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← WittVector.verschiebung_frobenius, hy]`. Use extensionality with `n`. Consider the cases of `n with`.

Consider the case `zero => rw [WittVector.verschiebung_coeff_zero, hx]`. Consider the case `succ n => exact WittVector.verschiebung_coeff_succ _ n`.
-/
lemma mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n

/- English proof (translation)
Rewrite `h` using `[← WittVector.verschiebung_frobenius]`. Establish `h2 : WittVector.frobenius x = 0`. Use extensionality with `n`. Establish `h3` using `congrArg (fun z => WittVector.coeff z n.succ) h`. Simplify `h3` using `only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff]`.

Apply `(frob_bij (p := p) (R := R)).1` to reduce the goal to its premises. Rewrite using `[h2, map_zero]`.
-/
lemma p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by
  rw [← WittVector.verschiebung_frobenius] at h
  have h2 : WittVector.frobenius x = 0 := by
    ext n
    have h3 := congrArg (fun z => WittVector.coeff z n.succ) h
    simpa only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff] using h3
  apply (frob_bij (p := p) (R := R)).1
  rw [h2, map_zero]

/- English proof (translation)
The claim follows from `mem_nonZeroDivisors_iff.mpr ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩`.
-/
lemma p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩

/- English proof (translation)
Establish `hr : ((frobeniusEquiv R p).symm y) ^ p = y`. Establish `h1` using `(frobeniusEquiv R p).apply_symm_apply y`. Rewrite `h1` using `[_root_.frobeniusEquiv_apply, frobenius_def]`. Then use the resulting hypothesis. Establish `hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0`. Rewrite using `[mul_pow, hr]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]`. Use `_ = 0 := by rw [h, mul_zero]`. Apply `(frobeniusEquiv R p).injective` to reduce the goal to its premises. Rewrite using `[map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]`.
-/
private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `mul_root_eq_zero w _ ih`.
-/
private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih

end Witt

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Establish `hu0 : (0 : PreTilt O p).untilt = 0`. Establish `h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt`. Rewrite using `[← hpf, ← map_mul, mul_zero]`. Establish `hJ` using `IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))`. Rewrite `hJ` using `[Ideal.mem_jacobson_bot]`.

Establish `h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0`. Take the linear combination `h1`. Conclude with `((hJ (-1)).mul_right_eq_zero).mp h2`. Establish `hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0`. Introduce `y hy`.

Establish `h1 : (p : O) * y.untilt = 0` using `by rw [← hpf, ← map_mul, hy, hu0]`. Rewrite using `[← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]`. Establish `hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0` using `mul_iterate_root_eq_zero pflat x hx`. Establish `hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm` using `fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]`. Apply `Perfection.ext` to reduce the goal to its premises.

Introduce `n`. Establish `key` using `Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p) ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n`. Rewrite `key` using `[zero_add]`. Use `erw [hli.iterate n x] at key`. Conclude with `key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)`.
-/
lemma pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)

end Tilt

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Introduce `pflat hpf`. Use `⟨p_mem_nonZeroDivisors, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_span_p_iff]`. Rewrite `hx` using `[WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero]`.

Conclude with `pflat_mul_eq_zero hO pflat hpf _ hx`. Introduce `htop`. Establish `h1 : (1 : WittVector p (PreTilt O p)) ∈ span {(p : WittVector p (PreTilt O p)), teichmuller p pflat}`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Take `⟨c, e, hce⟩` from `Ideal.mem_span_pair.mp h1`. Establish `h2` using `congrArg (fun z => WittVector.coeff z 0) hce`. Simplify using `only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2`. Establish `hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0`. Rewrite using `[← mem_span_p_iff]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h2` using `[hp0, mul_zero, zero_add, mul_comm]`. Establish `hu : IsUnit pflat` using `⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩`. Establish `h3` using `hu.map (PreTilt.untilt (O := O) (p := p))`. Rewrite `h3` using `[hpf]`.

Conclude with `(Fact.out : ¬IsUnit (p : O)) h3`.
-/
theorem regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by
  intro pflat hpf
  refine ⟨p_mem_nonZeroDivisors, ?_, ?_⟩
  · intro x hx
    rw [mem_span_p_iff] at hx ⊢
    rw [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at hx
    exact pflat_mul_eq_zero hO pflat hpf _ hx
  · intro htop
    have h1 : (1 : WittVector p (PreTilt O p)) ∈
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
    have h2 := congrArg (fun z => WittVector.coeff z 0) hce
    simp only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
    have hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0 := by
      rw [← mem_span_p_iff]; exact Ideal.mem_span_singleton_self _
    rw [hp0, mul_zero, zero_add, mul_comm] at h2
    have hu : IsUnit pflat := ⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    have h3 := hu.map (PreTilt.untilt (O := O) (p := p))
    rw [hpf] at h3
    exact (Fact.out : ¬IsUnit (p : O)) h3

end Main

end ReciprocityTheory.PGsh
