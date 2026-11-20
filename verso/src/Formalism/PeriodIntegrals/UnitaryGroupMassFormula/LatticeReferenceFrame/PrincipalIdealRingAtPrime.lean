import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.ScRefExists.ApP

open PI.ScRefExists.Sk

abbrev Pz (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

/- English proof (translation)
The claim follows from `(Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)`.
-/
theorem pz_prime {p : ℕ} (hp : p.Prime) : (Pz p).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)

instance pz_isPrime (p : ℕ) [hp : Fact p.Prime] : (Pz p).IsPrime := pz_prime hp.out

/- English proof (translation)
Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions.
-/
theorem pz_ne_bot {p : ℕ} (hp : p.Prime) : Pz p ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton]`. Introduce `h`. Establish `h1 : p ∣ s` using `Int.natCast_dvd_natCast.mp h`. Establish `h2 : p ∣ Nat.gcd s p` using `Nat.dvd_gcd h1 dvd_rfl`. Rewrite `h2` using `[Nat.Coprime.gcd_eq_one hs]`.

Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp h2)`.
-/
theorem natCast_not_mem {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : (s : ℤ) ∉ Pz p := by
  rw [Ideal.mem_span_singleton]
  intro h
  have h1 : p ∣ s := Int.natCast_dvd_natCast.mp h
  have h2 : p ∣ Nat.gcd s p := Nat.dvd_gcd h1 dvd_rfl
  rw [Nat.Coprime.gcd_eq_one hs] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[algebraMap_int_eq, eq_intCast]`. Conclude with `map_intCast (algebraMap (𝓞 I.E) I.E) n`.
-/
private theorem coe_algebraMap_int_ringOfIntegers (n : ℤ) :
    ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) = (n : I.E) := by
  rw [algebraMap_int_eq, eq_intCast]
  exact map_intCast (algebraMap (𝓞 I.E) I.E) n

/- English proof (translation)
Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn (dvd_zero _)`. Establish `hE : (n : I.E) ≠ 0` using `Int.cast_ne_zero.mpr hn0`. Establish `hcop : Nat.Coprime n.natAbs p`.

Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]`. Introduce `h`. Conclude with `hn (Int.natCast_dvd.mpr h)`. Use `(mem_Ap_lemma I p _).mpr ⟨n.natAbs, hcop, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq n with h | h` into its components or cases.

Establish `h' : (n.natAbs : ℤ) = n` using `by linarith`. Establish `e : (n.natAbs : I.E) = (n : I.E)` using `by rw [← Int.cast_natCast, h']`. Conclude with `⟨1, by rw [e, mul_inv_cancel₀ hE]; simp⟩`. Establish `h' : (n.natAbs : ℤ) = -n` using `by linarith`. Establish `e : (n.natAbs : I.E) = -(n : I.E)` using `by rw [← Int.cast_natCast, h', Int.cast_neg]`.

Conclude with `⟨-1, by rw [e, neg_mul, mul_inv_cancel₀ hE]; simp⟩`.
-/
theorem inv_mem {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : ((n : I.E))⁻¹ ∈ Ap I p := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  have hE : (n : I.E) ≠ 0 := Int.cast_ne_zero.mpr hn0
  have hcop : Nat.Coprime n.natAbs p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact hn (Int.natCast_dvd.mpr h)
  refine (mem_Ap_lemma I p _).mpr ⟨n.natAbs, hcop, ?_⟩
  rcases Int.natAbs_eq n with h | h
  · have h' : (n.natAbs : ℤ) = n := by linarith
    have e : (n.natAbs : I.E) = (n : I.E) := by rw [← Int.cast_natCast, h']
    exact ⟨1, by rw [e, mul_inv_cancel₀ hE]; simp⟩
  · have h' : (n.natAbs : ℤ) = -n := by linarith
    have e : (n.natAbs : I.E) = -(n : I.E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
    exact ⟨-1, by rw [e, neg_mul, mul_inv_cancel₀ hE]; simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Take `⟨n, hn, rfl⟩` from `hy`. Establish `hnd : ¬ (p : ℤ) ∣ n` using `fun h => hn (Ideal.mem_span_singleton.mpr h)`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hnd (dvd_zero _)`. Use `isUnit_iff_exists_inv.mpr ⟨⟨((n : I.E))⁻¹, inv_mem I hpf.out hnd⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) * (n : I.E)⁻¹ = 1`. Rewrite using `[coe_algebraMap_int_ringOfIntegers]`. Conclude with `mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn0)`. Introduce `z`. Take `⟨s, hs, a, ha⟩` from `(mem_Ap_lemma I p z).mp z.2`.

Use `⟨(a, ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨(s : ℤ), natCast_not_mem hpf.out hs⟩ : (Pz p).primeCompl)⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (z : I.E) * ((algebraMap ℤ (𝓞 I.E) (s : ℤ) : 𝓞 I.E) : I.E) = (a : I.E)`. Rewrite using `[coe_algebraMap_int_ringOfIntegers]`. Use `push_cast`.

Take the linear combination `ha`. Introduce `x y h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h2 : (x : I.E) = y`. Establish `h3` using `congrArg (fun z : Ap I p => (z : I.E)) h`.

Conclude with `h3`. Establish `hxy : x = y` using `NumberField.RingOfIntegers.ext h2`. Substitute `hxy` using the available equality. Both sides reduce to the same expression.
-/
theorem isLoc {p : ℕ} [hpf : Fact p.Prime] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) := by
  constructor
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := hy
    have hnd : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨((n : I.E))⁻¹, inv_mem I hpf.out hnd⟩, ?_⟩
    apply Subtype.ext
    show ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) * (n : I.E)⁻¹ = 1
    rw [coe_algebraMap_int_ringOfIntegers]
    exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn0)
  · intro z
    obtain ⟨s, hs, a, ha⟩ := (mem_Ap_lemma I p z).mp z.2
    refine ⟨(a, ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨(s : ℤ), natCast_not_mem hpf.out hs⟩ : (Pz p).primeCompl)⟩), ?_⟩
    apply Subtype.ext
    show (z : I.E) * ((algebraMap ℤ (𝓞 I.E) (s : ℤ) : 𝓞 I.E) : I.E) = (a : I.E)
    rw [coe_algebraMap_int_ringOfIntegers]
    push_cast
    linear_combination ha
  · intro x y h
    refine ⟨1, ?_⟩
    have h2 : (x : I.E) = y := by
      have h3 := congrArg (fun z : Ap I p => (z : I.E)) h
      exact h3
    have hxy : x = y := NumberField.RingOfIntegers.ext h2
    subst hxy
    rfl

/- English proof (translation)
Introduce and unpack `_ ⟨n, hn, rfl⟩`. Apply `mem_nonZeroDivisors_of_ne_zero` to reduce the goal to its premises. Introduce `h`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hn (Pz p).zero_mem`. Apply `hn0` to reduce the goal to its premises. Establish `h2` using `congrArg ((↑) : 𝓞 I.E → I.E) h`. Rewrite `h2` using `[coe_algebraMap_int_ringOfIntegers]`. Simplify using `using h2`.
-/
private theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (p : ℕ) [Fact p.Prime] :
    Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl ≤ nonZeroDivisors (𝓞 I.E) := by
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Pz p).zero_mem
  apply hn0
  have h2 := congrArg ((↑) : 𝓞 I.E → I.E) h
  rw [coe_algebraMap_int_ringOfIntegers] at h2
  simpa using h2

/- English proof (translation)
Use `haveI := isLoc I (p := p)`. Conclude with `IsLocalization.isDedekindDomain (𝓞 I.E) (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors I p) (Ap I p)`.
-/
theorem isDedekind {p : ℕ} [Fact p.Prime] : IsDedekindDomain (Ap I p) := by
  haveI := isLoc I (p := p)
  exact IsLocalization.isDedekindDomain (𝓞 I.E) (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors I p) (Ap I p)

/- English proof (translation)
Introduce `I p hp`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI := isLoc I (p := p)`. Use `haveI := isDedekind I (p := p)`. Conclude with `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 I.E) (Pz p) (pz_ne_bot hp)`.
-/
theorem principal_ideal_ring_at_prime : ApPID := by
  intro I p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLoc I (p := p)
  haveI := isDedekind I (p := p)
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 I.E) (Pz p) (pz_ne_bot hp)

/- English proof (translation)
Use `haveI := isLoc I (p := p)`. Conclude with `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) I.E`.
-/
theorem isFrac {p : ℕ} [Fact p.Prime] : IsFractionRing (Ap I p) I.E := by
  haveI := isLoc I (p := p)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) I.E

end PI.ScRefExists.ApP

end
