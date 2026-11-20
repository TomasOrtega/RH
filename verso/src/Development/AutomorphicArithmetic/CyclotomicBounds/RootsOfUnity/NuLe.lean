import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostApprox

open NumberField Formalism.HC KStar.Tree

/- English proof (translation)
Introduce `φ H l _ Ω _ _ _ n hn hq hd`. Establish `hQS0 : H.QS ≠ 0` using `H.QS_pos.ne'`. Take `⟨u, hu1, hun⟩` from `exists_unit_not_dvd l H.QS n hQS0 H.two_dvd_QS hn`. Apply `nuOf_le_of_approx l (cyc l H.E Ω) n _ u _ hun` to reduce the goal to its premises. Establish `hN : H.condN = H.QS * H.q * H.d` using `rfl`.

Establish `hfac : H.condN.factorization l = H.QS.factorization l`. Establish `hq0 : H.q ≠ 0` using `H.q_prime.ne_zero`. Establish `hd0 : H.d ≠ 0` using `H.d_prime.ne_zero`. Rewrite using `[hN, Nat.factorization_mul (mul_ne_zero hQS0 hq0) hd0, Nat.factorization_mul hQS0 hq0]`. Simplify using `only [Finsupp.add_apply]`.

Rewrite using `[H.q_prime.factorization, H.d_prime.factorization]`. Simplify using `[Finsupp.single_apply, Ne.symm hq, Ne.symm hd]`. Establish `h2 : 2 ≤ H.condN`. Use `Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.two_dvd_condN` as an intermediate fact. Conclude with `this`.

Use `haveI : Fact (1 < H.condN) := ⟨by omega⟩`. Introduce `k`. Apply `UpperTheory.Mu.hostApprox φ H l Ω 1 (map_one _) u _ k` to reduce the goal to its premises. Rewrite using `[hfac]`. Simplify `hu1` using `[ZMod.val_one]`.
-/
theorem UpperTheory.Mu.nuLe :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → l ≠ H.q → l ≠ H.d → nuOf l (cyc l H.E Ω) n ≤ H.QS.factorization l + (if l ∣ H.QS then n.factorization l else 0) := by
  intro φ H l _ Ω _ _ _ n hn hq hd
  have hQS0 : H.QS ≠ 0 := H.QS_pos.ne'
  obtain ⟨u, hu1, hun⟩ := exists_unit_not_dvd l H.QS n hQS0 H.two_dvd_QS hn
  apply nuOf_le_of_approx l (cyc l H.E Ω) n _ u _ hun
  have hN : H.condN = H.QS * H.q * H.d := rfl
  have hfac : H.condN.factorization l = H.QS.factorization l := by
    have hq0 : H.q ≠ 0 := H.q_prime.ne_zero
    have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
    rw [hN, Nat.factorization_mul (mul_ne_zero hQS0 hq0) hd0, Nat.factorization_mul hQS0 hq0]
    simp only [Finsupp.add_apply]
    rw [H.q_prime.factorization, H.d_prime.factorization]
    simp [Finsupp.single_apply, Ne.symm hq, Ne.symm hd]
  have h2 : 2 ≤ H.condN := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.two_dvd_condN
    exact this
  haveI : Fact (1 < H.condN) := ⟨by omega⟩
  intro k
  apply UpperTheory.Mu.hostApprox φ H l Ω 1 (map_one _) u _ k
  rw [hfac]
  simpa [ZMod.val_one] using hu1
