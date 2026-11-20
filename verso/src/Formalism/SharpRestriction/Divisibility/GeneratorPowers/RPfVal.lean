import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RStatement
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Pj.Crude Formalism.MainNotions.ModuliIntegralCharts.H1

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Establish `h : (a : K) = algebraMap (𝓞 K) K a` using `rfl`. Rewrite using `[vLa, h, HeightOneSpectrum.valuation_of_algebraMap, (la.intValuation_eq_one_iff_mem_primeCompl _).2 ha]`. Simplify using the standard rewrite rules.
-/
theorem vLa_int_not_mem {a : 𝓞 K} (ha : a ∉ la.asIdeal) : vLa la (a : K) = 0 := by
  have h : (a : K) = algebraMap (𝓞 K) K a := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 ha]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hm`. Assume the negation of the conclusion as `hne`. Establish `hl` using `resCharOf_prime la`. Establish `hnd : ¬ resCharOf la ∣ p` using `fun hd => hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 hd)`.

Conclude with `crv_not_mem la hnd hm`. Introduce `h`. Rewrite using `[← h]`. Conclude with `crv_char_mem la`.
-/
theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hl := resCharOf_prime la
    have hnd : ¬ resCharOf la ∣ p := fun hd =>
      hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `padicValNat_self`. Establish `: Fact p.Prime` using `⟨hp⟩`. Conclude with `padicValNat_primes h`.
-/
theorem padic_prime (l : ℕ) [Fact l.Prime] {p : ℕ} (hp : p.Prime) :
    padicValNat l p = if l = p then 1 else 0 := by
  split_ifs with h
  · subst h; exact padicValNat_self
  · have : Fact p.Prime := ⟨hp⟩
    exact padicValNat_primes h

/- English proof (translation)
Establish `hl` using `resCharOf_prime la`. Establish `: Fact (resCharOf la).Prime` using `⟨hl⟩`. Establish `h2 : (Q ^ a : ℕ) ≠ 0` using `pow_ne_zero _ hQ`. Establish `hq' : (q ^ b : ℕ) ≠ 0` using `pow_ne_zero _ hq.ne_zero`. Establish `hd' : (d ^ c : ℕ) ≠ 0` using `pow_ne_zero _ hd.ne_zero`.

Rewrite using `[crv_vLa_natCast la (Nat.mul_ne_zero (Nat.mul_ne_zero h2 hq') hd')]`. Use `congr 2`. Establish `e1 : padicValNat (resCharOf la) (Q ^ a) = a * padicValNat (resCharOf la) Q`. Rewrite using `[padicValNat.pow]`. Establish `e2 : padicValNat (resCharOf la) (q ^ b) = b * padicValNat (resCharOf la) q`.

Rewrite using `[padicValNat.pow]`. Establish `e3 : padicValNat (resCharOf la) (d ^ c) = c * padicValNat (resCharOf la) d`. Rewrite using `[padicValNat.pow]`. Rewrite using `[padicValNat.mul (Nat.mul_ne_zero h2 hq') hd', padicValNat.mul h2 hq', e1, e2, e3, padic_prime _ hq, padic_prime _ hd]`.
-/
theorem vLa_pPow {Q q d : ℕ} (hQ : Q ≠ 0) (hq : q.Prime) (hd : d.Prime) (a b c : ℕ) :
    vLa la (((Q ^ a * q ^ b * d ^ c : ℕ) : ℕ) : K) =
      (((a * padicValNat (resCharOf la) Q + b * (if resCharOf la = q then 1 else 0) +
        c * (if resCharOf la = d then 1 else 0)) * ramOverZ la : ℕ) : ℤ) := by
  have hl := resCharOf_prime la
  have : Fact (resCharOf la).Prime := ⟨hl⟩
  have h2 : (Q ^ a : ℕ) ≠ 0 := pow_ne_zero _ hQ
  have hq' : (q ^ b : ℕ) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hd' : (d ^ c : ℕ) ≠ 0 := pow_ne_zero _ hd.ne_zero
  rw [crv_vLa_natCast la (Nat.mul_ne_zero (Nat.mul_ne_zero h2 hq') hd')]
  congr 2
  have e1 : padicValNat (resCharOf la) (Q ^ a) = a * padicValNat (resCharOf la) Q := by
    rw [padicValNat.pow]
  have e2 : padicValNat (resCharOf la) (q ^ b) = b * padicValNat (resCharOf la) q := by
    rw [padicValNat.pow]
  have e3 : padicValNat (resCharOf la) (d ^ c) = c * padicValNat (resCharOf la) d := by
    rw [padicValNat.pow]
  rw [padicValNat.mul (Nat.mul_ne_zero h2 hq') hd', padicValNat.mul h2 hq', e1, e2, e3,
    padic_prime _ hq, padic_prime _ hd]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hm`. Assume the negation of the conclusion as `hnd`. Conclude with `crv_not_mem la hnd hm`. Introduce and unpack `⟨k, rfl⟩`.

Use `push_cast`. Conclude with `la.asIdeal.mul_mem_right _ (crv_char_mem la)`.
-/
theorem nat_mem_iff (n : ℕ) : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la ∣ n := by
  constructor
  · intro hm
    by_contra hnd
    exact crv_not_mem la hnd hm
  · rintro ⟨k, rfl⟩
    push_cast
    exact la.asIdeal.mul_mem_right _ (crv_char_mem la)

variable {D : D7} {j : ℕ}

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h` using `EX.piG_norm i`. Use `push_cast`. Conclude with `h`.
-/
theorem piG_mul_bar (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply RingOfIntegers.coe_injective
  have h := EX.piG_norm i
  push_cast
  exact h

/- English proof (translation)
Establish `hπ : ∀ i, iE D hinj B (EX.piG i) ∉ la.asIdeal ∧ iE D hinj B (piBarO EX i) ∉ la.asIdeal`. Introduce `i`. Establish `hn : iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 B.KO)`. Rewrite using `[← map_mul, piG_mul_bar, map_natCast]`. Conclude with `⟨fun hm => hg i (hn ▸ la.asIdeal.mul_mem_right _ hm), fun hm => hg i (hn ▸ la.asIdeal.mul_mem_left _ hm)⟩`.

Establish `: nnW B hinj EX w ∈ la.asIdeal.primeCompl`. Unfold `nnW`. Conclude with `Submonoid.prod_mem _ fun i _ => Submonoid.mul_mem _ (Submonoid.pow_mem _ (hπ i).1 _) (Submonoid.pow_mem _ (hπ i).2 _)`. Conclude with `this`.
-/
theorem nnW_not_mem (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    nnW B hinj EX w ∉ la.asIdeal := by
  have hπ : ∀ i, iE D hinj B (EX.piG i) ∉ la.asIdeal ∧ iE D hinj B (piBarO EX i) ∉ la.asIdeal := by
    intro i
    have hn : iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 B.KO) := by
      rw [← map_mul, piG_mul_bar, map_natCast]
    exact ⟨fun hm => hg i (hn ▸ la.asIdeal.mul_mem_right _ hm),
      fun hm => hg i (hn ▸ la.asIdeal.mul_mem_left _ hm)⟩
  have : nnW B hinj EX w ∈ la.asIdeal.primeCompl := by
    unfold nnW
    exact Submonoid.prod_mem _ fun i _ =>
      Submonoid.mul_mem _ (Submonoid.pow_mem _ (hπ i).1 _) (Submonoid.pow_mem _ (hπ i).2 _)
  exact this

/- English proof (translation)
Establish `hq : D.host.q.Prime` using `D.host.hyp.1`. Establish `hd : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hq8 : D.host.q % 8 = 3` using `D.host.hyp.2.2.1`. Establish `hd16 : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Establish `hq2 : D.host.q ≠ 2` using `by omega`.

Establish `hd2 : D.host.d ≠ 2` using `by omega`. Establish `hqd : D.host.q ≠ D.host.d` using `by omega`. Establish `hnn` using `nnW_not_mem B hinj EX w la hg`. Establish `hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0` using `fun h => hnn ((NumberField.RingOfIntegers.coe_eq_zero_iff.1 h) ▸ la.asIdeal.zero_mem)`. Establish `hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w` using `rfl`.

Establish `hN0 : ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) ≠ 0`. Rewrite using `[hP]`. Conclude with `Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hd.ne_zero)` after adjusting the coercions. Establish `hc : (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) = ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO)` using `by show algebraMap (𝓞 B.KO) B.KO _ = _`. Rewrite using `[map_mul, map_natCast]`.

Use `show ((vLa la _ : ℤ) : ℝ) = _`. Rewrite using `[hc, crv_vLa_mul la hnn0 hN0, vLa_int_not_mem la hnn, hP, vLa_pPow la D.host.QS_pos.ne' hq hd]`. Unfold `clOf`. Rewrite using `[show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]`. Simplify using `only [nat_mem_iff la D.host.QS, prime_mem_iff la hq, prime_mem_iff la hd]`.

Distinguish the cases in `hS : resCharOf la ∣ D.host.QS`. Establish `h1 : resCharOf la ≠ D.host.q` using `fun h => D.host.q_not_dvd_QS (h ▸ hS)`. Establish `h2 : resCharOf la ≠ D.host.d` using `fun h => D.host.d_not_dvd_QS (h ▸ hS)`. Rewrite using `[if_pos hS, if_neg h1, if_neg h2]`. Generalize the expression as in `padicValNat (resCharOf la) D.host.QS = m`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `rw [if_neg hS, padicValNat.eq_zero_of_not_dvd hS] split_ifs <;> (try (exfalso; omega)) <;> (try (exfalso; tauto)) <;> push_cast <;> ring`.
-/
theorem vAdd_sW (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    ((vAdd la (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) : ℤ) : ℝ) =
      (ramOverZ la : ℝ) * clOf w la := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hq2 : D.host.q ≠ 2 := by omega
  have hd2 : D.host.d ≠ 2 := by omega
  have hqd : D.host.q ≠ D.host.d := by omega
  have hnn := nnW_not_mem B hinj EX w la hg
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn ((NumberField.RingOfIntegers.coe_eq_zero_iff.1 h) ▸ la.asIdeal.zero_mem)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN0 : ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) ≠ 0 := by
    rw [hP]
    exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  have hc : (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO _ = _
    rw [map_mul, map_natCast]
  show ((vLa la _ : ℤ) : ℝ) = _
  rw [hc, crv_vLa_mul la hnn0 hN0, vLa_int_not_mem la hnn, hP, vLa_pPow la D.host.QS_pos.ne' hq hd]
  unfold clOf
  rw [show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
  simp only [nat_mem_iff la D.host.QS, prime_mem_iff la hq, prime_mem_iff la hd]
  by_cases hS : resCharOf la ∣ D.host.QS
  · have h1 : resCharOf la ≠ D.host.q := fun h => D.host.q_not_dvd_QS (h ▸ hS)
    have h2 : resCharOf la ≠ D.host.d := fun h => D.host.d_not_dvd_QS (h ▸ hS)
    rw [if_pos hS, if_neg h1, if_neg h2]
    generalize padicValNat (resCharOf la) D.host.QS = m
    push_cast; ring
  · rw [if_neg hS, padicValNat.eq_zero_of_not_dvd hS]
    split_ifs <;> (try (exfalso; omega)) <;> (try (exfalso; tauto)) <;> push_cast <;> ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal
