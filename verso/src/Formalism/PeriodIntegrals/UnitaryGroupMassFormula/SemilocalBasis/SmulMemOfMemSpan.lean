import Mathlib
import Formalism.PeriodIntegrals.LocBasisSemi

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocBasisSemi

variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

abbrev T : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl

/- English proof (translation)
The claim follows from `algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (Ideal.primeCompl_le_nonZeroDivisors _)`.
-/
theorem T_le : T K p ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    (Ideal.primeCompl_le_nonZeroDivisors _)

abbrev A : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (T K p) (T_le K p)

variable {K p}

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `Submonoid.mem_map.mp ht`. Establish `hz' : ¬ (p : ℤ) ∣ z` using `fun h => hz (Ideal.mem_span_singleton.mpr h)`. Take `⟨n, hn⟩ : ∃ n : ℕ, z = n ∨ z = -n` from `⟨z.natAbs, Int.natAbs_eq z⟩`. Establish `hcop : Nat.Coprime n p`. Use `Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hz' ?_)` and prove the remaining obligations.

Establish `h' : (p : ℤ) ∣ (n : ℤ)` using `Int.natCast_dvd_natCast.mpr h`. Apply the tactic sequence `rcases hn with hn | hn <;> rw [hn]`. Conclude with `h'`. Conclude with `(dvd_neg).mpr h'`. Use `⟨n, hcop, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rcases hn with hn | hn <;> subst hn`. Conclude with `⟨1, by simp⟩`. Conclude with `⟨-1, by simp⟩`.
-/
theorem mem_T {t : 𝓞 K} (ht : t ∈ T K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 K, (s : 𝓞 K) = u * t := by
  obtain ⟨z, hz, rfl⟩ := Submonoid.mem_map.mp ht
  have hz' : ¬ (p : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z = n ∨ z = -n := ⟨z.natAbs, Int.natAbs_eq z⟩
  have hcop : Nat.Coprime n p := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hz' ?_)
    have h' : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr h
    rcases hn with hn | hn <;> rw [hn]
    · exact h'
    · exact (dvd_neg).mpr h'
  refine ⟨n, hcop, ?_⟩
  rcases hn with hn | hn <;> subst hn
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

/- English proof (translation)
Take `⟨⟨x, t⟩, h⟩` from `IsLocalization.surj (T K p) a`. Establish `hK : (a : K) * ((t : 𝓞 K) : K) = (x : K)` using `congrArg (fun b : A K p => (b : K)) h`. Take `⟨s, hs, u, hu⟩` from `mem_T t.2`. Use `⟨s, hs, u * x, ?_⟩` and prove the remaining obligations. Establish `hu' : (s : K) = (u : K) * ((t : 𝓞 K) : K)`.

Use `congrArg (fun y : 𝓞 K => (y : K)) hu` as an intermediate fact. Simplify using `using this`. Rewrite using `[hu', show ((u * x : 𝓞 K) : K) = (u : K) * (x : K) from rfl, ← hK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem surjK (a : A K p) : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : 𝓞 K, (s : K) * (a : K) = (x : K) := by
  obtain ⟨⟨x, t⟩, h⟩ := IsLocalization.surj (T K p) a
  have hK : (a : K) * ((t : 𝓞 K) : K) = (x : K) := congrArg (fun b : A K p => (b : K)) h
  obtain ⟨s, hs, u, hu⟩ := mem_T t.2
  refine ⟨s, hs, u * x, ?_⟩
  have hu' : (s : K) = (u : K) * ((t : 𝓞 K) : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hu
    simpa using this
  rw [hu', show ((u * x : 𝓞 K) : K) = (u : K) * (x : K) from rfl, ← hK]
  ring

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (T K p) c`. Use `choose x hx using hb`. Take `⟨s, hs, u, hu⟩` from `mem_T b.2`. Use `⟨s, hs, fun i => u * x i, fun i => ?_⟩` and prove the remaining obligations. Establish `hK : ((x i : 𝓞 K) : K) = ((b : 𝓞 K) : K) * (c i : K)` using `congrArg (fun y : A K p => (y : K)) (hx i)`.

Establish `hu' : (s : K) = (u : K) * ((b : 𝓞 K) : K)`. Use `congrArg (fun y : 𝓞 K => (y : K)) hu` as an intermediate fact. Simplify using `using this`. Rewrite using `[hu', show ((u * x i : 𝓞 K) : K) = (u : K) * (x i : K) from rfl, hK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem common_denom {ι : Type*} [Fintype ι] (c : ι → A K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : ι → 𝓞 K, ∀ i, (s : K) * (c i : K) = (x i : K) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (T K p) c
  choose x hx using hb
  obtain ⟨s, hs, u, hu⟩ := mem_T b.2
  refine ⟨s, hs, fun i => u * x i, fun i => ?_⟩
  have hK : ((x i : 𝓞 K) : K) = ((b : 𝓞 K) : K) * (c i : K) :=
    congrArg (fun y : A K p => (y : K)) (hx i)
  have hu' : (s : K) = (u : K) * ((b : 𝓞 K) : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hu
    simpa using this
  rw [hu', show ((u * x i : 𝓞 K) : K) = (u : K) * (x i : K) from rfl, hK]
  ring

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hnat : ∀ (n : ℕ) {w : V}, w ∈ Y → (n : K) • w ∈ Y` using `fun n w hw => by`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `Y.nsmul_mem hw n`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩` and prove the remaining obligations.

Establish `e : ((s * t : ℕ) : K) • (x + y) = (t : K) • ((s : K) • x) + (s : K) • ((t : K) • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : K) (s : K)]`. Rewrite using `[e]`. Conclude with `Y.add_mem (hnat t hsx) (hnat s hty)`. Consider the case `smul a x _ hx`.

Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, y, hy⟩` from `surjK a`. Use `⟨t * s, Nat.Coprime.mul_left ht hs, ?_⟩` and prove the remaining obligations. Establish `e : ((t * s : ℕ) : K) • (a • x) = y • ((s : K) • x)`. Rewrite using `[Subalgebra.smul_def, smul_smul, ← algebraMap_smul K y, smul_smul, Nat.cast_mul, ← RingOfIntegers.coe_eq_algebraMap, ← hy]`.

Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `Y.smul_mem y hsx`.
-/
theorem smul_mem_of_mem_span (Y : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span (A K p) (Y : Set V)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • v ∈ Y := by
  have hnat : ∀ (n : ℕ) {w : V}, w ∈ Y → (n : K) • w ∈ Y := fun n w hw => by
    rw [Nat.cast_smul_eq_nsmul]
    exact Y.nsmul_mem hw n
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : K) • (x + y) = (t : K) • ((s : K) • x) + (s : K) • ((t : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : K) (s : K)]
    rw [e]
    exact Y.add_mem (hnat t hsx) (hnat s hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, y, hy⟩ := surjK a
    refine ⟨t * s, Nat.Coprime.mul_left ht hs, ?_⟩
    have e : ((t * s : ℕ) : K) • (a • x) = y • ((s : K) • x) := by
      rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K y, smul_smul, Nat.cast_mul,
        ← RingOfIntegers.coe_eq_algebraMap, ← hy]
      ring_nf
    rw [e]
    exact Y.smul_mem y hsx

end PI.UnitaryGroupMassFormula.LocBasisSemi
