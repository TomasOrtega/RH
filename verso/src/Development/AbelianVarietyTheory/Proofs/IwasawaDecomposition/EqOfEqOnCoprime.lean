import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.QuadPrim

def IsPrimQuad (L : ℕ) (f : ℕ → ℂ) : Prop :=
  (∃ ψ : DirichletCharacter ℂ L, ψ.IsPrimitive ∧ ∀ a : ℕ, ψ (a : ZMod L) = f a) ∧
    ∀ a : ℕ, f a = 0 ∨ f a = 1 ∨ f a = -1

/- English proof (translation)
Use `DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm (a := (a : ℤ)) (Nat.isCoprime_iff_coprime.mpr ha)` as an intermediate fact. Simplify using `using this`.
-/
theorem changeLevel_nat {n m : ℕ} (χ : DirichletCharacter ℂ n) (hm : n ∣ m) {a : ℕ}
    (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hm χ (a : ZMod m) = χ (a : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm (a := (a : ℤ))
    (Nat.isCoprime_iff_coprime.mpr ha)
  simpa using this

/- English proof (translation)
The claim follows from `χ.map_nonunit (fun h => ha ((ZMod.isUnit_iff_coprime a n).mp h))`.
-/
theorem apply_nat_eq_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {a : ℕ} (ha : ¬ a.Coprime n) :
    χ (a : ZMod n) = 0 :=
  χ.map_nonunit (fun h => ha ((ZMod.isUnit_iff_coprime a n).mp h))

/- English proof (translation)
Establish `: NeZero (m * n)` using `⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩`. Use `set A := DirichletCharacter.changeLevel (dvd_mul_right m n) α with hA`. Use `set B := DirichletCharacter.changeLevel (dvd_mul_left n m) β with hB`. Establish `cA : A.conductor = m`. Rewrite using `[hA, DirichletCharacter.conductor_changeLevel]`.

Conclude with `hα`. Establish `cB : B.conductor = n`. Rewrite using `[hB, DirichletCharacter.conductor_changeLevel]`. Conclude with `hβ`. Establish `h1` using `DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) B⁻¹`.

Establish `h2` using `DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) A⁻¹`. Rewrite `h1` using `[mul_inv_cancel_right, DirichletCharacter.conductor_inv, cA, cB]`. Rewrite `h2` using `[mul_inv_cancel_comm, DirichletCharacter.conductor_inv, cA, cB]`. Establish `h3 : m ∣ DirichletCharacter.conductor (A * B)` using `h.dvd_of_dvd_mul_right (h1.trans (Nat.lcm_dvd_mul _ _))`. Establish `h4 : n ∣ DirichletCharacter.conductor (A * B)` using `h.symm.dvd_of_dvd_mul_right (h2.trans (Nat.lcm_dvd_mul _ _))`.

Conclude with `Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) (h.mul_dvd_of_dvd_of_dvd h3 h4)`.
-/
theorem isPrimitive_mul {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) :
    DirichletCharacter.IsPrimitive
      (DirichletCharacter.changeLevel (dvd_mul_right m n) α *
        DirichletCharacter.changeLevel (dvd_mul_left n m) β) := by
  have : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right m n) α with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left n m) β with hB
  have cA : A.conductor = m := by
    rw [hA, DirichletCharacter.conductor_changeLevel]; exact hα
  have cB : B.conductor = n := by
    rw [hB, DirichletCharacter.conductor_changeLevel]; exact hβ
  have h1 := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
  have h2 := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv, cA, cB] at h1
  rw [mul_inv_cancel_comm, DirichletCharacter.conductor_inv, cA, cB] at h2
  have h3 : m ∣ DirichletCharacter.conductor (A * B) :=
    h.dvd_of_dvd_mul_right (h1.trans (Nat.lcm_dvd_mul _ _))
  have h4 : n ∣ DirichletCharacter.conductor (A * B) :=
    h.symm.dvd_of_dvd_mul_right (h2.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _)
    (h.mul_dvd_of_dvd_of_dvd h3 h4)

/- English proof (translation)
Establish `: NeZero (N * L * M)` using `⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne L)) hM⟩`. Establish `hN : N ∣ N * L * M` using `(dvd_mul_right N L).mul_right M`. Establish `hL : L ∣ N * L * M` using `(dvd_mul_left L N).mul_right M`. Establish `key : DirichletCharacter.changeLevel hN χ = DirichletCharacter.changeLevel hL ψ`. Apply `MulChar.ext` to reduce the goal to its premises.

Introduce `u`. Establish `hu` using `ZMod.val_coe_unit_coprime u`. Rewrite using `[← ZMod.natCast_zmod_val (u : ZMod (N * L * M)), changeLevel_nat χ hN hu, changeLevel_nat ψ hL hu]`. Conclude with `h _ (hu.coprime_dvd_right (dvd_mul_left M _))`. Establish `hNL : N = L`.

Use `congrArg DirichletCharacter.conductor key` as an intermediate fact. Rewrite `this` using `[DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel]`. Conclude with `hχ.symm.trans (this.trans hψ)`. Substitute `hNL` using the available equality. Use `⟨rfl, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[DirichletCharacter.changeLevel_injective hN key]`.
-/
theorem eq_of_eqOn_coprime {N L M : ℕ} [NeZero N] [NeZero L] (hM : M ≠ 0)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ L)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (h : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = ψ (a : ZMod L)) :
    N = L ∧ ∀ a : ℕ, χ (a : ZMod N) = ψ (a : ZMod L) := by
  have : NeZero (N * L * M) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne L)) hM⟩
  have hN : N ∣ N * L * M := (dvd_mul_right N L).mul_right M
  have hL : L ∣ N * L * M := (dvd_mul_left L N).mul_right M
  have key : DirichletCharacter.changeLevel hN χ = DirichletCharacter.changeLevel hL ψ := by
    apply MulChar.ext
    intro u
    have hu := ZMod.val_coe_unit_coprime u
    rw [← ZMod.natCast_zmod_val (u : ZMod (N * L * M)), changeLevel_nat χ hN hu,
      changeLevel_nat ψ hL hu]
    exact h _ (hu.coprime_dvd_right (dvd_mul_left M _))
  have hNL : N = L := by
    have := congrArg DirichletCharacter.conductor key
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at this
    exact hχ.symm.trans (this.trans hψ)
  subst hNL
  refine ⟨rfl, fun a => ?_⟩
  rw [DirichletCharacter.changeLevel_injective hN key]

/- English proof (translation)
Establish `: NeZero m` using `⟨hm⟩`. Establish `: NeZero n` using `⟨hn⟩`. Take `⟨⟨α, hα, hαf⟩, hf⟩` from `hf`. Take `⟨⟨β, hβ, hβg⟩, hg⟩` from `hg`. Use `⟨⟨_, isPrimitive_mul h α β hα hβ, fun a => ?_⟩, fun a => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `ha : a.Coprime (m * n)`. Rewrite using `[MulChar.mul_apply, changeLevel_nat _ _ ha, changeLevel_nat _ _ ha, hαf, hβg]`. Rewrite using `[apply_nat_eq_zero _ ha]`. Rewrite `ha` using `[Nat.coprime_mul_iff_right, not_and_or]`. Use `beta_reduce`.

Break down `ha with ha | ha` into its components or cases. Rewrite using `[← hαf, apply_nat_eq_zero _ ha, zero_mul]`. Rewrite using `[← hβg, apply_nat_eq_zero _ ha, mul_zero]`. Apply the tactic sequence `rcases hf a with h1 | h1 | h1 <;> rcases hg a with h2 | h2 | h2 <;> simp [h1, h2]`.
-/
theorem IsPrimQuad.mul {m n : ℕ} {f g : ℕ → ℂ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n)
    (hf : IsPrimQuad m f) (hg : IsPrimQuad n g) : IsPrimQuad (m * n) (fun a => f a * g a) := by
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  obtain ⟨⟨α, hα, hαf⟩, hf⟩ := hf
  obtain ⟨⟨β, hβ, hβg⟩, hg⟩ := hg
  refine ⟨⟨_, isPrimitive_mul h α β hα hβ, fun a => ?_⟩, fun a => ?_⟩
  · by_cases ha : a.Coprime (m * n)
    · rw [MulChar.mul_apply, changeLevel_nat _ _ ha, changeLevel_nat _ _ ha, hαf, hβg]
    · rw [apply_nat_eq_zero _ ha]
      rw [Nat.coprime_mul_iff_right, not_and_or] at ha
      beta_reduce
      rcases ha with ha | ha
      · rw [← hαf, apply_nat_eq_zero _ ha, zero_mul]
      · rw [← hβg, apply_nat_eq_zero _ ha, mul_zero]
  · rcases hf a with h1 | h1 | h1 <;> rcases hg a with h2 | h2 | h2 <;> simp [h1, h2]

/- English proof (translation)
Use `fin_cases k`. Use `show IsPrimQuad 1 (fun a => f a ^ 0)`. Use `⟨⟨1, DirichletCharacter.isPrimitive_one_level_one, fun a => ?_⟩, fun a => by simp⟩` and prove the remaining obligations. Rewrite using `[MulChar.one_apply (isUnit_of_subsingleton _)]`. Simplify using the standard rewrite rules.

Simplify using `using hf`.
-/
theorem IsPrimQuad.pow {m : ℕ} {f : ℕ → ℂ} (hf : IsPrimQuad m f) (k : Fin 2) :
    IsPrimQuad (m ^ k.1) (fun a => f a ^ k.1) := by
  fin_cases k
  · show IsPrimQuad 1 (fun a => f a ^ 0)
    refine ⟨⟨1, DirichletCharacter.isPrimitive_one_level_one, fun a => ?_⟩, fun a => by simp⟩
    rw [MulChar.one_apply (isUnit_of_subsingleton _)]
    simp
  · simpa using hf

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Use `⟨⟨(quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ), ?_, fun a => ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Break down `(Nat.dvd_prime hp).mp (DirichletCharacter.conductor_dvd_level ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[← DirichletCharacter.eq_one_iff_conductor_eq_one, MulChar.ringHomComp_eq_one_iff (RingHom.injective_int _)]`.

Conclude with `quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]) h`. Conclude with `h`. Use `beta_reduce`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym]`. Simplify using the standard rewrite rules.

Apply the tactic sequence `rcases jacobiSym.trichotomy (a : ℤ) p with h | h | h <;> simp [h]`.
-/
theorem isPrimQuad_jacobi {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsPrimQuad p (fun a => ((jacobiSym (a : ℤ) p : ℤ) : ℂ)) := by
  have := Fact.mk hp
  refine ⟨⟨(quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ), ?_, fun a => ?_⟩,
    fun a => ?_⟩
  · rcases (Nat.dvd_prime hp).mp (DirichletCharacter.conductor_dvd_level
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) with h | h
    · exfalso
      rw [← DirichletCharacter.eq_one_iff_conductor_eq_one,
        MulChar.ringHomComp_eq_one_iff (RingHom.injective_int _)] at h
      exact quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]) h
    · exact h
  · beta_reduce
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp
  · rcases jacobiSym.trichotomy (a : ℤ) p with h | h | h <;> simp [h]

/- English proof (translation)
Use `⟨⟨ZMod.χ₈.ringHomComp (Int.castRingHom ℂ), ?_, fun a => by simp⟩, fun a => ?_⟩` and prove the remaining obligations. Use `set χ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ) with hχ`. Assume the negation of the conclusion as `hne`. Establish `hd` using `DirichletCharacter.conductor_dvd_level χ`. Establish `h4 : χ.conductor ∣ 4`.

Establish `hle` using `Nat.le_of_dvd (by norm_num) hd`. Establish `hne' : χ.conductor ≠ 8` using `hne`. Generalize the expression as in `χ.conductor = c at hd hle hne'`. Apply the tactic sequence `interval_cases c <;> simp_all`. Take `⟨h48, χ₀, h0⟩` from `(DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (show 4 ∣ 8 by norm_num)).mpr h4`.

Establish `e1 : χ ((5 : ℕ) : ZMod 8) = χ₀ ((5 : ℕ) : ZMod 4)`. Rewrite using `[h0]; exact changeLevel_nat χ₀ h48 (by norm_num)`. Establish `e2 : ((5 : ℕ) : ZMod 4) = 1` using `by decide`. Establish `e3 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1` using `by decide`. Rewrite `e1` using `[e2, map_one, hχ, MulChar.ringHomComp_apply, e3]`.

Evaluate the numerical expressions using `at e1`. Apply the tactic sequence `rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h <;> simp [h]`.
-/
theorem isPrimQuad_chi8 :
    IsPrimQuad 8 (fun a => ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ)) := by
  refine ⟨⟨ZMod.χ₈.ringHomComp (Int.castRingHom ℂ), ?_, fun a => by simp⟩, fun a => ?_⟩
  · set χ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ) with hχ
    by_contra hne
    have hd := DirichletCharacter.conductor_dvd_level χ
    have h4 : χ.conductor ∣ 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      have hne' : χ.conductor ≠ 8 := hne
      generalize χ.conductor = c at hd hle hne'
      interval_cases c <;> simp_all
    obtain ⟨h48, χ₀, h0⟩ := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ
      (show 4 ∣ 8 by norm_num)).mpr h4
    have e1 : χ ((5 : ℕ) : ZMod 8) = χ₀ ((5 : ℕ) : ZMod 4) := by
      rw [h0]; exact changeLevel_nat χ₀ h48 (by norm_num)
    have e2 : ((5 : ℕ) : ZMod 4) = 1 := by decide
    have e3 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
    rw [e2, map_one, hχ, MulChar.ringHomComp_apply, e3] at e1
    norm_num at e1
  · rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h <;> simp [h]

/- English proof (translation)
Introduce `q d hq hd hq4 hd4 hqd i j k hij N _ χ hχ`. Take `⟨hK, hK2⟩` from `GlobalTheory.kronSym_neg_eq_jacobiSym_and_two`. Establish `hq2 : q ≠ 2` using `by omega`. Establish `hd2 : d ≠ 2` using `by omega`. Establish `c8 : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.Coprime 8 p` using `fun p hp h2 => Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp).mpr h2.symm)`.

Establish `cdq : Nat.Coprime d q` using `(Nat.coprime_primes hd hq).mpr hqd.symm`. Establish `n8 : (8 : ℕ) ^ k.1 ≠ 0` using `pow_ne_zero _ (by norm_num)`. Establish `nd : d ^ j.1 ≠ 0` using `pow_ne_zero _ hd.ne_zero`. Establish `nq : q ^ i.1 ≠ 0` using `pow_ne_zero _ hq.ne_zero`. Establish `hP` using `((isPrimQuad_chi8.pow k).mul n8 nd (Nat.Coprime.pow _ _ (c8 d hd hd2)) ((isPrimQuad_jacobi hd hd2).pow j)).mul (mul_ne_zero n8 nd) nq (Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (c8 q hq hq2)) (Nat.Coprime.pow _ _ cdq)) ((isPrimQuad_jacobi hq hq2).pow i)`.

Take `⟨⟨ψ, hψ, hψf⟩, htri⟩` from `hP`. Establish `: NeZero (8 ^ k.1 * d ^ j.1 * q ^ i.1)` using `⟨mul_ne_zero (mul_ne_zero n8 nd) nq⟩`. Establish `hch : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.chDir d a = ((jacobiSym (a : ℤ) d : ℤ) : ℂ)`. Introduce `a ha`. Rewrite using `[GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, hK d a hd4 ha]`.

Establish `hps : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.psDir q a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ)`. Introduce `a ha`. Rewrite using `[GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, hK q a hq4 ha]`. Take `⟨hN, hval⟩` from `eq_of_eqOn_coprime (M := 8 * q * d) (mul_ne_zero (mul_ne_zero (by norm_num) hq.ne_zero) hd.ne_zero) χ ψ hχ.1 hψ (by`. Introduce `a ha`.

Establish `hodd : Odd a`. Establish `: a.Coprime 2` using `ha.coprime_dvd_right (((show 2 ∣ 8 by norm_num).mul_right q).mul_right d)`. Conclude with `Nat.coprime_two_right.mp this`. Rewrite using `[hχ.2 a ha, hψf]`. Use `beta_reduce`.

Rewrite using `[hch a hodd.pos, hps a hodd.pos, GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, hK2 a hodd])`. Establish `hquad : χ.IsQuadratic`. Introduce `x`. Rewrite using `[← ZMod.natCast_zmod_val x, hval, hψf]`. Conclude with `htri _`.

Use `⟨hN, hquad.sq_eq_one, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h1`. Establish `hc : N = 1` using `hχ.1.symm.trans (DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1)`. Rewrite `hN` using `[hc]`. Establish `h2` using `Nat.eq_one_of_mul_eq_one_left hN.symm`.

Establish `h3` using `Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hN.symm)`. Rewrite `h2`, `h3` using `[Nat.pow_eq_one]`. Use linear arithmetic over natural numbers and integers. Introduce `x`. Apply the tactic sequence `rcases hquad x with h | h | h <;> simp [h]`.

Introduce `a ha hk`. Rewrite using `[hval, hψf, hch a ha, hps a ha]`. Simplify using `[hk]`.
-/
theorem main : ∀ q d : ℕ, q.Prime → d.Prime → q % 4 = 3 → d % 4 = 3 → q ≠ d → ∀ (i j k : Fin 2), (i.1 + j.1 ≠ 0) → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a ^ j.1 * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) → N = 8 ^ k.1 * d ^ j.1 * q ^ i.1 ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ GlobalTheoryTheory.IsRealChar χ ∧ ∀ a : ℕ, 0 < a → (k.1 = 0 → χ (a : ZMod N) = GlobalTheoryTheory.chDir d a ^ j.1 * GlobalTheoryTheory.psDir q a ^ i.1) := by
  intro q d hq hd hq4 hd4 hqd i j k hij N _ χ hχ
  obtain ⟨hK, hK2⟩ := GlobalTheory.kronSym_neg_eq_jacobiSym_and_two
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have c8 : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.Coprime 8 p := fun p hp h2 =>
    Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp).mpr h2.symm)
  have cdq : Nat.Coprime d q := (Nat.coprime_primes hd hq).mpr hqd.symm
  have n8 : (8 : ℕ) ^ k.1 ≠ 0 := pow_ne_zero _ (by norm_num)
  have nd : d ^ j.1 ≠ 0 := pow_ne_zero _ hd.ne_zero
  have nq : q ^ i.1 ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hP := ((isPrimQuad_chi8.pow k).mul n8 nd (Nat.Coprime.pow _ _ (c8 d hd hd2))
    ((isPrimQuad_jacobi hd hd2).pow j)).mul (mul_ne_zero n8 nd) nq
    (Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (c8 q hq hq2)) (Nat.Coprime.pow _ _ cdq))
    ((isPrimQuad_jacobi hq hq2).pow i)
  obtain ⟨⟨ψ, hψ, hψf⟩, htri⟩ := hP
  have : NeZero (8 ^ k.1 * d ^ j.1 * q ^ i.1) := ⟨mul_ne_zero (mul_ne_zero n8 nd) nq⟩
  have hch : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.chDir d a = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) := by
    intro a ha
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, hK d a hd4 ha]
  have hps : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.psDir q a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) := by
    intro a ha
    rw [GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, hK q a hq4 ha]
  obtain ⟨hN, hval⟩ := eq_of_eqOn_coprime (M := 8 * q * d)
    (mul_ne_zero (mul_ne_zero (by norm_num) hq.ne_zero) hd.ne_zero) χ ψ hχ.1 hψ (by
      intro a ha
      have hodd : Odd a := by
        have : a.Coprime 2 := ha.coprime_dvd_right
          (((show 2 ∣ 8 by norm_num).mul_right q).mul_right d)
        exact Nat.coprime_two_right.mp this
      rw [hχ.2 a ha, hψf]
      beta_reduce
      rw [hch a hodd.pos, hps a hodd.pos, GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, hK2 a hodd])
  have hquad : χ.IsQuadratic := by
    intro x
    rw [← ZMod.natCast_zmod_val x, hval, hψf]
    exact htri _
  refine ⟨hN, hquad.sq_eq_one, ?_, ?_, ?_⟩
  · intro h1
    have hc : N = 1 := hχ.1.symm.trans (DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1)
    rw [hc] at hN
    have h2 := Nat.eq_one_of_mul_eq_one_left hN.symm
    have h3 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hN.symm)
    rw [Nat.pow_eq_one] at h2 h3
    omega
  · intro x
    rcases hquad x with h | h | h <;> simp [h]
  · intro a ha hk
    rw [hval, hψf, hch a ha, hps a ha]
    simp [hk]

end GlobalTheory.QuadPrim
