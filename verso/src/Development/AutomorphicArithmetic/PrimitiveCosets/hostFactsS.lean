import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Establish `h1 : ((H.toHostRaw.art u).1.2 : ℤ) = 1`. Rewrite using `[H.der.art_ch u, jacobi_congr hk, hj]`. Establish `h2 : (H.toHostRaw.art u).1.2 = 1` using `Units.ext h1`. Use `show Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.toHostRaw.art u).1.2) = 0`. Rewrite using `[Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_eq_zero_iff]`.

Conclude with `h2`.
-/
private lemma inPhi_of_jac {φ : Frame} (H : HostAx φ) (u : (ZMod H.toHostRaw.condN)ˣ) (k : ℕ)
    (hk : (u : ZMod H.toHostRaw.condN).val ≡ k [MOD H.d]) (hj : jacobiSym (k : ℤ) H.d = 1) :
    Formalism.D5.InPhi (Multiplicative.toAdd (recH H.toHostRaw u)) := by
  have h1 : ((H.toHostRaw.art u).1.2 : ℤ) = 1 := by
    rw [H.der.art_ch u, jacobi_congr hk, hj]
  have h2 : (H.toHostRaw.art u).1.2 = 1 := Units.ext h1
  show Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.toHostRaw.art u).1.2) = 0
  rw [Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_eq_zero_iff]
  exact h2

/- English proof (translation)
Establish `hd4` using `H.d_mod_four`. Break down `(H.dvd_QSq_iff hp).mp h with hQ | rfl` into its components or cases. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Conclude with `jac_two_d H.hyp`.

Establish `hodd : p % 2 = 1` using `hp.eq_two_or_odd.resolve_left h2`. Rewrite using `[← jacobi_neg_recip hd4 hodd]`. Conclude with `H.QS_split p hp h2 hQ`. Establish `hodd : H.q % 2 = 1`. Use `H.hyp.2.2.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← jacobi_neg_recip hd4 hodd]`. Conclude with `H.hyp.2.2.2.2`.
-/
private lemma jac_of_dvd {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    jacobiSym (p : ℤ) H.d = 1 := by
  have hd4 := H.d_mod_four
  rcases (H.dvd_QSq_iff hp).mp h with hQ | rfl
  · by_cases h2 : p = 2
    · subst h2
      exact jac_two_d H.hyp
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
      rw [← jacobi_neg_recip hd4 hodd]
      exact H.QS_split p hp h2 hQ
  · have hodd : H.q % 2 = 1 := by
      have := H.hyp.2.2.1
      omega
    rw [← jacobi_neg_recip hd4 hodd]
    exact H.hyp.2.2.2.2

/- English proof (translation)
Apply `Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN` to reduce the goal to its premises. Introduce `hpd`. Establish `hpe : p = H.d` using `(Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp hpd`. Conclude with `H.d_not_dvd_QSq (hpe ▸ h)`.
-/
private lemma d_dvd_ordCompl {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    H.d ∣ ordCompl[p] H.condN := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
  intro hpd
  have hpe : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp hpd
  exact H.d_not_dvd_QSq (hpe ▸ h)

/- English proof (translation)
Rewrite using `[(toE_bij φ).2.1]`. Both sides reduce to the same expression.
-/
private lemma toE_iod' (φ : Frame) : Multiplicative.toAdd (toE φ φ.iod) = sgc0 := by
  rw [(toE_bij φ).2.1]
  rfl

/- English proof (translation)
Introduce `φ H`. Use `haveI : NeZero H.toHostRaw.condN := ⟨H.toHostRaw.condN_ne_zero⟩`. Establish `hQq0 : H.QS * H.q ≠ 0` using `Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero`. Use `{ d_prime := H.d_prime two_mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_of_dvd_left H.two_dvd_QS _, hQq0⟩ q1_mem := Nat.mem_primeFactors.mpr ⟨H.q_prime, dvd_mul_left _ _, hQq0⟩ d_not_mem := fun hm => H.d_not_dvd_QSq (Nat.dvd_of_mem_primeFactors hm) unram := ?_ split_in …` and prove the remaining obligations. Introduce `p hp hpS hpd`.

Establish `hpN : ¬ p ∣ H.toHostRaw.condN`. Introduce `hdvd`. Break down `(Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1` into its components or cases. Conclude with `hpS (Nat.mem_primeFactors.mpr ⟨hp, h1, hQq0⟩)`. Conclude with `hpd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp h1)`.

Establish `hloc` using `(unramified_spec _ p H.toHostRaw.condN_ne_zero hp hpN).1`. Rewrite using `[AddSubgroup.eq_bot_iff_forall]`. Introduce `x hx`. Take `⟨u, hu, rfl⟩` from `(mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx`. Rewrite `hu` using `[hloc, Subgroup.mem_bot]`.

Substitute `hu` using the available equality. Simplify using the standard rewrite rules. Introduce `p hpS x hx`. Establish `hp` using `Nat.prime_of_mem_primeFactors hpS`. Establish `hdvd` using `Nat.dvd_of_mem_primeFactors hpS`.

Take `⟨u, hu, rfl⟩` from `(mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx`. Rewrite `hu` using `[mem_localUnits_iff]`. Conclude with `inPhi_of_jac H u 1 (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hu) (by simp)`. Introduce `p hpS`. Establish `hp` using `Nat.prime_of_mem_primeFactors hpS`.

Establish `hdvd` using `Nat.dvd_of_mem_primeFactors hpS`. Establish `hf` using `(frobUnit_modEq (N := H.toHostRaw.condN) hp).1`. Conclude with `inPhi_of_jac H _ p (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hf) (jac_of_dvd H.toHostRaw hp hdvd)`. Introduce `x`. Establish `hparts` using `parts_of_eq (N := H.toHostRaw.condN) (k := 1) (m := H.QS * H.q) H.d_prime (by show H.QS * H.q * H.d = _; ring) H.d_not_dvd_QSq hQq0`.

Use `(mem_inertia_iff H.q H.d (recH H.toHostRaw) H.d x).trans ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite `hu` using `[mem_localUnits_iff, hparts.2]`. Break down `H.art_d u hu with h | h` into its components or cases.

Use `left`. Simplify using `[recH, h]`. Use `right show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0`. Rewrite using `[h]`. Conclude with `toE_iod' φ`.

Introduce and unpack `(rfl | rfl)`. Conclude with `⟨1, Subgroup.one_mem _, by simp⟩`. Take `⟨u, hu1, hu2⟩` from `exists_unit_crt (N := H.toHostRaw.condN) (a := H.QS * H.q) (b := H.d)`. Use `rfl H.coprime_QSq_d (dvd_mul_right _ _) H.d_dvd_condN 1 (-1)`. Establish `hloc : (u : ZMod H.toHostRaw.condN).val ≡ 1 [MOD H.QS * H.q]` using `(unitsMap_eq_one_iff _ u).mp hu1`.

Use `⟨u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_localUnits_iff, hparts.2]`. Conclude with `hloc`. Establish `hcast : (((u : ZMod H.toHostRaw.condN).val : ℤ) : ZMod H.d) = ((-1 : ℤ) : ZMod H.d)`. Establish `h3` using `congrArg (fun v : (ZMod H.d)ˣ => (v : ZMod H.d)) hu2`.

Simplify using `only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_neg, Units.val_one] at h3`. Use `push_cast`. Rewrite using `[ZMod.natCast_val]`. Conclude with `h3`. Rewrite `hcast` using `[ZMod.intCast_eq_intCast_iff]`.

Establish `hjac : ((H.toHostRaw.art u).1.2 : ℤ) = -1`. Rewrite using `[H.der.art_ch u, jacobiSym.mod_left, show (((u : ZMod H.toHostRaw.condN).val : ℕ) : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) from hcast, ← jacobiSym.mod_left, jacobiSym.at_neg_one (H.d_prime.odd_of_ne_two H.d_ne_two), ZMod.χ₄_nat_three_mod_four H.d_mod_four]`. Break down `H.art_d u hloc with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hjac` using `[h]`.

Simplify using `at hjac`. Use `show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0`. Rewrite using `[h]`. Conclude with `toE_iod' φ`.
-/
private theorem hostFactsS_pf :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (H.QS * H.q).primeFactors := by
  intro φ H
  haveI : NeZero H.toHostRaw.condN := ⟨H.toHostRaw.condN_ne_zero⟩
  have hQq0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  refine
    { d_prime := H.d_prime
      two_mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_of_dvd_left H.two_dvd_QS _, hQq0⟩
      q1_mem := Nat.mem_primeFactors.mpr ⟨H.q_prime, dvd_mul_left _ _, hQq0⟩
      d_not_mem := fun hm => H.d_not_dvd_QSq (Nat.dvd_of_mem_primeFactors hm)
      unram := ?_
      split_inertia := ?_
      split_frob := ?_
      inertia_d := ?_ }
  · intro p hp hpS hpd
    have hpN : ¬ p ∣ H.toHostRaw.condN := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h1, hQq0⟩)
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp h1)
    have hloc := (unramified_spec _ p H.toHostRaw.condN_ne_zero hp hpN).1
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [hloc, Subgroup.mem_bot] at hu
    subst hu
    simp
  · intro p hpS x hx
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [mem_localUnits_iff] at hu
    exact inPhi_of_jac H u 1 (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hu) (by simp)
  · intro p hpS
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    have hf := (frobUnit_modEq (N := H.toHostRaw.condN) hp).1
    exact inPhi_of_jac H _ p (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hf)
      (jac_of_dvd H.toHostRaw hp hdvd)
  · intro x
    have hparts := parts_of_eq (N := H.toHostRaw.condN) (k := 1) (m := H.QS * H.q) H.d_prime
      (by show H.QS * H.q * H.d = _; ring) H.d_not_dvd_QSq hQq0
    refine (mem_inertia_iff H.q H.d (recH H.toHostRaw) H.d x).trans ?_
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mem_localUnits_iff, hparts.2] at hu
      rcases H.art_d u hu with h | h
      · left
        simp [recH, h]
      · right
        show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
        rw [h]
        exact toE_iod' φ
    · rintro (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by simp⟩
      · obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.toHostRaw.condN) (a := H.QS * H.q) (b := H.d)
          rfl H.coprime_QSq_d (dvd_mul_right _ _) H.d_dvd_condN 1 (-1)
        have hloc : (u : ZMod H.toHostRaw.condN).val ≡ 1 [MOD H.QS * H.q] :=
          (unitsMap_eq_one_iff _ u).mp hu1
        refine ⟨u, ?_, ?_⟩
        · rw [mem_localUnits_iff, hparts.2]
          exact hloc
        · have hcast : (((u : ZMod H.toHostRaw.condN).val : ℤ) : ZMod H.d) = ((-1 : ℤ) : ZMod H.d) := by
            have h3 := congrArg (fun v : (ZMod H.d)ˣ => (v : ZMod H.d)) hu2
            simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
              Units.val_neg, Units.val_one] at h3
            push_cast
            rw [ZMod.natCast_val]
            exact h3
          rw [ZMod.intCast_eq_intCast_iff] at hcast
          have hjac : ((H.toHostRaw.art u).1.2 : ℤ) = -1 := by
            rw [H.der.art_ch u, jacobiSym.mod_left,
              show (((u : ZMod H.toHostRaw.condN).val : ℕ) : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) from hcast,
              ← jacobiSym.mod_left, jacobiSym.at_neg_one (H.d_prime.odd_of_ne_two H.d_ne_two),
              ZMod.χ₄_nat_three_mod_four H.d_mod_four]
          rcases H.art_d u hloc with h | h
          · exfalso
            rw [h] at hjac
            simp at hjac
          · show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
            rw [h]
            exact toE_iod' φ

/- English proof (translation)
Introduce `φ H`. Establish `hset : insert H.q H.small = (H.QS * H.q).primeFactors`. Rewrite using `[Nat.primeFactors_mul H.QS_ne_zero H.q_prime.ne_zero, H.q_prime.primeFactors]`. Use `show insert H.q H.QS.primeFactors = _`. Use extensionality with `a`.

Simplify using `[or_comm]`. Rewrite using `[hset]`. Conclude with `hostFactsS_pf φ H`.
-/
theorem UpperTheory.Comparison₂.hostFactsS :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (insert H.q H.small) := by
  intro φ H
  have hset : insert H.q H.small = (H.QS * H.q).primeFactors := by
    rw [Nat.primeFactors_mul H.QS_ne_zero H.q_prime.ne_zero, H.q_prime.primeFactors]
    show insert H.q H.QS.primeFactors = _
    ext a
    simp [or_comm]
  rw [hset]
  exact hostFactsS_pf φ H
