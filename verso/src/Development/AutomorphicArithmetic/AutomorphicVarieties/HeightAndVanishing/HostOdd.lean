import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Establish `hc : Nat.Coprime (2 ^ k) m` using `Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)`. Establish `h3 : orderOf x ∣ Nat.gcd (2 ^ k) m` using `Nat.dvd_gcd h1 h2`. Rewrite `h3` using `[hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff]`. Conclude with `h3`.
-/
private theorem eq_one_of_odd {Γ : Type} [Monoid Γ] {x : Γ} {k m : ℕ} (h1 : orderOf x ∣ 2 ^ k) (h2 : orderOf x ∣ m)
    (hm : Odd m) : x = 1 := by
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h3 : orderOf x ∣ Nat.gcd (2 ^ k) m := Nat.dvd_gcd h1 h2
  rw [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

/- English proof (translation)
Establish `hN : h.N ≠ 0` using `NeZero.ne _`. Take `⟨-, -, -, -, -, hpf, hpow, hq1, hd, -⟩` from `hostIndex h`. Rewrite using `[(compCond O h.N ψ 2 Nat.prime_two).2.2.2.2.2 h.q h.q_dvd]`. Introduce `p hp`. Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors hp`.

Establish `hpN : p ∣ h.N` using `Nat.dvd_of_mem_primeFactors hp`. Take `⟨hcond, hone, -⟩` from `compCond O h.N ψ p hpp`. Establish `c1 : comp p ψ = 1 → (comp p ψ).conductor = 1` using `fun e => by`. Rewrite using `[hcond, Nat.factorization_eq_zero_of_not_dvd (hone.mp e), pow_zero]`. Distinguish the cases in `h2p : p = 2`.

Substitute `h2p` using the available equality. Rewrite using `[c1 h2]`. Conclude with `one_dvd _`. Establish `hf : ψ.conductor.factorization p ≤ h.N.factorization p` using `(Nat.factorization_le_iff_dvd ψ.conductor_ne_zero hN).mpr ψ.conductor_dvd_level p`. Establish `hdvdp : (comp p ψ).conductor ∣ p ^ h.N.factorization p`.

Rewrite using `[hcond]`. Conclude with `Nat.pow_dvd_pow p hf`. Establish `key : p = h.q1 ∨ p = h.d → (comp p ψ).conductor ∣ h.q`. Introduce `hpe`. Establish `hpp1 : p ^ h.N.factorization p = p`.

Break down `hpe with rfl | rfl` into its components or cases. Use `exacts [hq1, hd]`. Rewrite `hdvdp` using `[hpp1]`. Distinguish the cases in `hpq : p ∣ h.q`. Conclude with `hdvdp.trans hpq`.

Take `⟨m, hm, hmd⟩` from `ho p hpp hpe`. Establish `hsq : comp p ψ ^ 2 = 1` using `((hostComp h O ψ hψ).2.2 p hpp h2p).2.2.1 hpq`. Establish `e : comp p ψ = 1` using `eq_one_of_odd (k := 1) (by simpa using orderOf_dvd_of_pow_eq_one hsq) hmd hm`. Rewrite using `[c1 e]`. Conclude with `one_dvd _`.

Distinguish the cases in `hpe : p = h.q1 ∨ p = h.d`. Conclude with `key hpe`. Use `push_neg at hpe`. Break down `(hpf p hpp).mp hpN with h2' | hpq | hq1' | hd'` into its components or cases. Conclude with `absurd h2' h2p`.

Rewrite `hdvdp` using `[hpow p hpp h2p hpe.1 hpe.2]`. Conclude with `hdvdp.trans (Nat.ordProj_dvd _ _)`. Conclude with `absurd hq1' hpe.1`. Conclude with `absurd hd' hpe.2`.
-/
private theorem cond_dvd (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    (h2 : comp 2 ψ = 1) (ho : ∀ p, p.Prime → p = h.q1 ∨ p = h.d → ∃ m, Odd m ∧ orderOf (comp p ψ) ∣ m) :
    ψ.conductor ∣ h.q := by
  have hN : h.N ≠ 0 := NeZero.ne _
  obtain ⟨-, -, -, -, -, hpf, hpow, hq1, hd, -⟩ := hostIndex h
  rw [(compCond O h.N ψ 2 Nat.prime_two).2.2.2.2.2 h.q h.q_dvd]
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpN : p ∣ h.N := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨hcond, hone, -⟩ := compCond O h.N ψ p hpp
  have c1 : comp p ψ = 1 → (comp p ψ).conductor = 1 := fun e => by
    rw [hcond, Nat.factorization_eq_zero_of_not_dvd (hone.mp e), pow_zero]
  by_cases h2p : p = 2
  · subst h2p
    rw [c1 h2]
    exact one_dvd _
  have hf : ψ.conductor.factorization p ≤ h.N.factorization p :=
    (Nat.factorization_le_iff_dvd ψ.conductor_ne_zero hN).mpr ψ.conductor_dvd_level p
  have hdvdp : (comp p ψ).conductor ∣ p ^ h.N.factorization p := by
    rw [hcond]
    exact Nat.pow_dvd_pow p hf
  have key : p = h.q1 ∨ p = h.d → (comp p ψ).conductor ∣ h.q := by
    intro hpe
    have hpp1 : p ^ h.N.factorization p = p := by
      rcases hpe with rfl | rfl
      exacts [hq1, hd]
    rw [hpp1] at hdvdp
    by_cases hpq : p ∣ h.q
    · exact hdvdp.trans hpq
    · obtain ⟨m, hm, hmd⟩ := ho p hpp hpe
      have hsq : comp p ψ ^ 2 = 1 := ((hostComp h O ψ hψ).2.2 p hpp h2p).2.2.1 hpq
      have e : comp p ψ = 1 :=
        eq_one_of_odd (k := 1) (by simpa using orderOf_dvd_of_pow_eq_one hsq) hmd hm
      rw [c1 e]
      exact one_dvd _
  by_cases hpe : p = h.q1 ∨ p = h.d
  · exact key hpe
  push_neg at hpe
  rcases (hpf p hpp).mp hpN with h2' | hpq | hq1' | hd'
  · exact absurd h2' h2p
  · rw [hpow p hpp h2p hpe.1 hpe.2] at hdvdp
    exact hdvdp.trans (Nat.ordProj_dvd _ _)
  · exact absurd hq1' hpe.1
  · exact absurd hd' hpe.2

/- English proof (translation)
Take `⟨k, hk⟩` from `(compOrd O N ψ 2 Nat.prime_two).2.1`. Establish `hd : orderOf (comp 2 ψ) ∣ orderOf ψ` using `((compAlg O N 2 Nat.prime_two).2.2.2.2.2.1 ψ).2.1`. Conclude with `eq_one_of_odd (k := k) (hk ▸ dvd_refl _) hd ho`.
-/
private theorem comp_two_eq_one (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N)
    (ho : Odd (orderOf ψ)) : comp 2 ψ = 1 := by
  obtain ⟨k, hk⟩ := (compOrd O N ψ 2 Nat.prime_two).2.1
  have hd : orderOf (comp 2 ψ) ∣ orderOf ψ := ((compAlg O N 2 Nat.prime_two).2.2.2.2.2.1 ψ).2.1
  exact eq_one_of_odd (k := k) (hk ▸ dvd_refl _) hd ho

/- English proof (translation)
Introduce `h O _ _ ψ hψ`. Take `⟨hord, hpos, -⟩` from `hostComp h O ψ hψ`. Use `⟨fun hodd => ?_, fun l hl hl2 hlq1 hld hodd => ?_⟩` and prove the remaining obligations. Establish `h2 : comp 2 ψ = 1` using `comp_two_eq_one O h.N ψ hodd`. Establish `hcd : ψ.conductor ∣ h.q` using `cond_dvd h O ψ hψ h2 (fun p hp _ => ⟨orderOf ψ, hodd, ((compAlg O h.N p hp).2.2.2.2.2.1 ψ).2.1⟩)`.

Take `⟨hc2eq, hone2, -⟩` from `compCond O h.N ψ 2 Nat.prime_two`. Establish `hnd : ¬ 2 ∣ ψ.conductor` using `hone2.mp h2`. Use `⟨?_, h2, ?_, ?_, hcd⟩` and prove the remaining obligations. Establish `hco : Nat.Coprime (orderOf ψ) (2 ^ (h.ex + 1))` using `Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)`. Establish `hdo : orderOf ψ ∣ h.o` using `hco.dvd_of_dvd_mul_left hord`.

Conclude with `Nat.dvd_ordCompl_of_dvd_not_dvd hdo (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])`. Use `show (comp 2 ψ).conductor.factorization 2 = 0`. Rewrite using `[hc2eq, Nat.factorization_eq_zero_of_not_dvd hnd]`. Simplify using the standard rewrite rules. Rewrite using `[← Nat.not_even_iff_odd, even_iff_two_dvd]` and apply the resulting hypothesis.

Take `⟨-, -, -, -, -, -, hc2chi, -, -, hcomp_eq, -⟩` from `hostTh1 h O ψ hψ l hl hl2`. Establish `hpsi : psi2 ψ = 1`. Rewrite using `[← hc2chi]`. Conclude with `comp_two_eq_one O h.N _ hodd`. Use `⟨cond_dvd h O ψ hψ hpsi ?_, hpsi⟩` and prove the remaining obligations.

Introduce `p hp hpe`. Establish `hpl : p ≠ l`. Break down `hpe with rfl | rfl` into its components or cases. Use `exacts [hlq1.symm, hld.symm]`. Take `⟨hkap, -⟩` from `partOrd _ l hl ψ hpos`.

Use `⟨orderOf (chiP l ψ) * l ^ (orderOf ψ).factorization l, Odd.mul hodd (Odd.pow (hl.odd_of_ne_two hl2)), ?_⟩` and prove the remaining obligations. Establish `e : comp p ψ = comp p (th0 l ψ) * comp p (kap l ψ)`. Rewrite using `[← (compAlg O h.N p hp).2.1, dirichletPrimeToLPart_mul_lPowerPart]`. Rewrite using `[e]`. Use `(Commute.all _ _).orderOf_mul_dvd_mul_orderOf.trans (Nat.mul_dvd_mul ?_ ?_)` and prove the remaining obligations.

Rewrite using `[← hcomp_eq p hp hpl]`. Conclude with `((compAlg O h.N p hp).2.2.2.2.2.1 _).2.1`. Establish `hk` using `((compAlg O h.N p hp).2.2.2.2.2.1 (kap l ψ)).2.1`. Rewrite `hk` using `[show kap l ψ = lPart l ψ from rfl, hkap]`. Conclude with `hk`.
-/
theorem UpperTheory.V.HV.hostOdd :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ →
      (Odd (orderOf ψ) → orderOf ψ ∣ ordCompl[2] h.o ∧ psi2 ψ = 1 ∧ c2 ψ = 0 ∧ Odd ψ.conductor ∧ ψ.conductor ∣ h.q) ∧
      ∀ l, l.Prime → l ≠ 2 → l ≠ h.q1 → l ≠ h.d → Odd (orderOf (chiP l ψ)) → ψ.conductor ∣ h.q ∧ psi2 ψ = 1 := by
  intro h O _ _ ψ hψ
  obtain ⟨hord, hpos, -⟩ := hostComp h O ψ hψ
  refine ⟨fun hodd => ?_, fun l hl hl2 hlq1 hld hodd => ?_⟩
  · have h2 : comp 2 ψ = 1 := comp_two_eq_one O h.N ψ hodd
    have hcd : ψ.conductor ∣ h.q := cond_dvd h O ψ hψ h2
      (fun p hp _ => ⟨orderOf ψ, hodd, ((compAlg O h.N p hp).2.2.2.2.2.1 ψ).2.1⟩)
    obtain ⟨hc2eq, hone2, -⟩ := compCond O h.N ψ 2 Nat.prime_two
    have hnd : ¬ 2 ∣ ψ.conductor := hone2.mp h2
    refine ⟨?_, h2, ?_, ?_, hcd⟩
    · have hco : Nat.Coprime (orderOf ψ) (2 ^ (h.ex + 1)) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
      have hdo : orderOf ψ ∣ h.o := hco.dvd_of_dvd_mul_left hord
      exact Nat.dvd_ordCompl_of_dvd_not_dvd hdo (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
    · show (comp 2 ψ).conductor.factorization 2 = 0
      rw [hc2eq, Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
    · rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
  · obtain ⟨-, -, -, -, -, -, hc2chi, -, -, hcomp_eq, -⟩ := hostTh1 h O ψ hψ l hl hl2
    have hpsi : psi2 ψ = 1 := by
      rw [← hc2chi]
      exact comp_two_eq_one O h.N _ hodd
    refine ⟨cond_dvd h O ψ hψ hpsi ?_, hpsi⟩
    intro p hp hpe
    have hpl : p ≠ l := by
      rcases hpe with rfl | rfl
      exacts [hlq1.symm, hld.symm]
    obtain ⟨hkap, -⟩ := partOrd _ l hl ψ hpos
    refine ⟨orderOf (chiP l ψ) * l ^ (orderOf ψ).factorization l,
      Odd.mul hodd (Odd.pow (hl.odd_of_ne_two hl2)), ?_⟩
    have e : comp p ψ = comp p (th0 l ψ) * comp p (kap l ψ) := by
      rw [← (compAlg O h.N p hp).2.1, dirichletPrimeToLPart_mul_lPowerPart]
    rw [e]
    refine (Commute.all _ _).orderOf_mul_dvd_mul_orderOf.trans (Nat.mul_dvd_mul ?_ ?_)
    · rw [← hcomp_eq p hp hpl]
      exact ((compAlg O h.N p hp).2.2.2.2.2.1 _).2.1
    · have hk := ((compAlg O h.N p hp).2.2.2.2.2.1 (kap l ψ)).2.1
      rw [show kap l ψ = lPart l ψ from rfl, hkap] at hk
      exact hk
