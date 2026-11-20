import ReciprocityTheory.DualLattices.Imports
import ReciprocityTheory.DualLattices.ATowerInh

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev A := WittVector p (PreTilt O p)

def root (ε : PreTilt O p) (k : ℕ) : PreTilt O p := (frobeniusEquiv (PreTilt O p) p).symm^[k] ε

def xi (ε : PreTilt O p) : A p O := ∑ i ∈ Finset.range p, teichmuller p (root p O ε 1) ^ i

def nu (ε : PreTilt O p) : A p O := teichmuller p (root p O ε 1) - 1

/- English proof (translation)
Establish `hsp : ∀ x : PreTilt O p, ((frobeniusEquiv (PreTilt O p) p).symm x) ^ p = x` using `fun x => by`. Rewrite using `[← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]`. Proceed by induction on `k with`. Consider the case `zero => simp [root]`. Consider the case `succ k ih`.

Simplify using `only [root] at ih ⊢`. Rewrite using `[Function.iterate_succ_apply', pow_succ', pow_mul, hsp]`. Conclude with `ih`.
-/
lemma root_pow (ε : PreTilt O p) (k : ℕ) : root p O ε k ^ p ^ k = ε := by
  have hsp : ∀ x : PreTilt O p, ((frobeniusEquiv (PreTilt O p) p).symm x) ^ p = x := fun x => by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  induction k with
  | zero => simp [root]
  | succ k ih =>
    simp only [root] at ih ⊢
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, hsp]
    exact ih

/- English proof (translation)
Establish `h'` using `congrArg (algebraMap O C) h`. Rewrite `h'` using `[map_mul, map_pow, map_natCast, map_zero]`. Establish `hpC : (p : C) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`. Establish `h0 : algebraMap O C a = 0` using `(mul_eq_zero.1 h').resolve_right (pow_ne_zero _ hpC)`. Conclude with `hv.hom_inj (by rw [h0, map_zero])`.
-/
lemma torsion_free (hv : v.Integers O) (n : ℕ) (a : O) (h : a * (p : O) ^ n = 0) : a = 0 := by
  have h' := congrArg (algebraMap O C) h
  rw [map_mul, map_pow, map_natCast, map_zero] at h'
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h0 : algebraMap O C a = 0 := (mul_eq_zero.1 h').resolve_right (pow_ne_zero _ hpC)
  exact hv.hom_inj (by rw [h0, map_zero])

/- English proof (translation)
Introduce `x`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos`. Establish `hvy : v y ≤ 1`. Establish `h1 : v y ^ p ≤ 1`.

Rewrite using `[← map_pow, hy]`. Conclude with `hv.map_le_one x`. Conclude with `(pow_le_one_iff_of_nonneg (by positivity) hp.out.ne_zero).1 h1`. Take `⟨z, rfl⟩` from `hv.exists_of_le_one hvy`. Use `⟨Ideal.Quotient.mk _ z, ?_⟩` and prove the remaining obligations.

Rewrite using `[frobenius_def, ← map_pow]`. Use `congr 1`. Conclude with `hv.hom_inj (by rw [map_pow, hy])`.
-/
lemma frob_surj (hv : v.Integers O) : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  have hvy : v y ≤ 1 := by
    have h1 : v y ^ p ≤ 1 := by
      rw [← map_pow, hy]
      exact hv.map_le_one x
    exact (pow_le_one_iff_of_nonneg (by positivity) hp.out.ne_zero).1 h1
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvy
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact hv.hom_inj (by rw [map_pow, hy])

/- English proof (translation)
The claim follows from `surjective_fontaineTheta (frob_surj p O hv)`.
-/
lemma theta_surj (hv : v.Integers O) : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frob_surj p O hv)

/- English proof (translation)
Use `haveI : Nontrivial O := ⟨⟨(0 : O), (1 : O), fun h => by`. Establish `h2` using `congrArg (algebraMap O C) h`. Simplify using `at h2⟩⟩`. Establish `hu : ∀ y : O, v (algebraMap O C y) = 1 → IsUnit y` using `fun y hy => hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by`. Rewrite `hy` using `[h0, map_zero]`.

Conclude with `zero_ne_one hy) hy`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Break down `(hv.map_le_one x).lt_or_eq with hlt | heq` into its components or cases. Use `right`. Apply `hu` to reduce the goal to its premises.

Rewrite using `[map_sub, map_one]`. Conclude with `Valuation.map_one_sub_of_lt v hlt`. Use `left`. Conclude with `hu x heq`.
-/
lemma O_local (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O :=
    ⟨⟨(0 : O), (1 : O), fun h => by
      have h2 := congrArg (algebraMap O C) h
      simp at h2⟩⟩
  have hu : ∀ y : O, v (algebraMap O C y) = 1 → IsUnit y := fun y hy =>
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by
      rw [h0, map_zero] at hy
      exact zero_ne_one hy) hy
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases (hv.map_le_one x).lt_or_eq with hlt | heq
  · right
    apply hu
    rw [map_sub, map_one]
    exact Valuation.map_one_sub_of_lt v hlt
  · left
    exact hu x heq

/- English proof (translation)
Apply `IsHausdorff.haus' (I := span {(p : O)})` to reduce the goal to its premises. Introduce `n`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Consider the cases of `n with`. Consider the case `zero => simp`.

Consider the case `succ k => exact SModEq.zero.2 (h k)`.
-/
lemma sepO (a : O) (h : ∀ n : ℕ, a ∈ span {(p : O) ^ (n + 1)}) : a = 0 := by
  apply IsHausdorff.haus' (I := span {(p : O)})
  intro n
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  cases n with
  | zero => simp
  | succ k => exact SModEq.zero.2 (h k)

/- English proof (translation)
The claim follows from `Ideal.Quotient.nontrivial_iff.2 hI`.
-/
lemma quot_nontrivial {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.2 hI

/- English proof (translation)
Use `haveI : Nontrivial S := hf.nontrivial`. Establish `key : ∀ y : S, IsUnit (f y) → IsUnit y`. Introduce `y hy`. Take `⟨u, hu⟩` from `hy`. Take `⟨z, hz⟩` from `hf (↑u⁻¹ : T)`.

Establish `hker : y * z - 1 ∈ RingHom.ker f`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hu, Units.mul_inv, sub_self]`. Establish `hsq` using `hk _ hker`. Establish `h1 : y * (z * (1 - (y * z - 1))) = 1` using `by linear_combination -hsq`. Conclude with `⟨⟨y, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩`.

Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self (f x) with h | h` into its components or cases. Conclude with `Or.inl (key x h)`. Conclude with `Or.inr (key (1 - x) (by rwa [map_sub, map_one]))`.
-/
lemma local_of_surj_sq {S T : Type} [CommRing S] [CommRing T] [IsLocalRing T] (f : S →+* T)
    (hf : Function.Surjective f) (hk : ∀ k ∈ RingHom.ker f, k * k = 0) : IsLocalRing S := by
  haveI : Nontrivial S := hf.nontrivial
  have key : ∀ y : S, IsUnit (f y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ := hy
    obtain ⟨z, hz⟩ := hf (↑u⁻¹ : T)
    have hker : y * z - 1 ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hu, Units.mul_inv, sub_self]
    have hsq := hk _ hker
    have h1 : y * (z * (1 - (y * z - 1))) = 1 := by linear_combination -hsq
    exact ⟨⟨y, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (f x) with h | h
  · exact Or.inl (key x h)
  · exact Or.inr (key (1 - x) (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

/- English proof (translation)
Take `⟨pflat, hpf⟩` from `exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)`. Establish `hX` using `xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε`. Simplify using `only [xi, nu, root, Function.iterate_one] at *`. Conclude with `(hX.2.2.2 pflat hpf).1`.
-/
lemma ker_theta : RingHom.ker (fontaineTheta O p) = span {xi p O ε} := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  exact (hX.2.2.2 pflat hpf).1

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, ker_theta p O hv ε hε]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
lemma theta_xi : fontaineTheta O p (xi p O ε) = 0 := by
  rw [← RingHom.mem_ker, ker_theta p O hv ε hε]
  exact Ideal.mem_span_singleton_self _

/- English proof (translation)
Take `⟨pflat, hpf⟩` from `exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)`. Establish `hK` using `(kerTheta (p := p) (C := C) (O := O) (v := v) hv) pflat hpf`. Establish `hX` using `xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε`. Simplify using `only [xi, nu, root, Function.iterate_one] at *`. Take `⟨u, hu⟩` from `(hX.2.2.2 pflat hpf).2`.

Rewrite `hy` using `[hu, ← mul_assoc]`. Establish `h1 : y * ↑u = 0` using `(mem_nonZeroDivisors_iff.1 hK.2.1).2 _ hy`. Establish `h2 : y * ↑u * ↑u⁻¹ = 0` using `by rw [h1, zero_mul]`. Rewrite `h2` using `[mul_assoc, Units.mul_inv, mul_one]`. Then use the resulting hypothesis.
-/
lemma xi_nzd (y : A p O) (hy : y * xi p O ε = 0) : y = 0 := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hK := (kerTheta (p := p) (C := C) (O := O) (v := v) hv) pflat hpf
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  obtain ⟨u, hu⟩ := (hX.2.2.2 pflat hpf).2
  rw [hu, ← mul_assoc] at hy
  have h1 : y * ↑u = 0 := (mem_nonZeroDivisors_iff.1 hK.2.1).2 _ hy
  have h2 : y * ↑u * ↑u⁻¹ = 0 := by rw [h1, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h2

/- English proof (translation)
Establish `hX` using `xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε`. Simplify using `only [xi, nu, root, Function.iterate_one] at *`. Take the linear combination `hX.1`.
-/
lemma teich_eps : teichmuller p ε = 1 + nu p O ε * xi p O ε := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  linear_combination hX.1

/- English proof (translation)
Establish `hX` using `xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε`. Simplify using `only [xi, nu, root, Function.iterate_one] at *`. Rewrite using `[hX.2.1]`. Conclude with `sub_ne_zero.2 (hε.ne_one hp.out.one_lt)`.
-/
lemma theta_nu : fontaineTheta O p (nu p O ε) ≠ 0 := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  rw [hX.2.1]
  exact sub_ne_zero.2 (hε.ne_one hp.out.one_lt)

/- English proof (translation)
Establish `he : ε = ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ p`. Rewrite using `[← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]`. Rewrite using `[he, map_pow, hε.pow_eq_one]`.
-/
lemma untilt_eps : ε.untilt = 1 := by
  have he : ε = ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ p := by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  rw [he, map_pow, hε.pow_eq_one]

end Ainf

end ReciprocityTheory.PGsh
