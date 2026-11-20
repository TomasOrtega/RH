import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.FieldDatPf

/- English proof (translation)
Use `⟨GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp _ ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver hp).symm.trans hs), fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨h1, -, h3, -⟩` from `GlobalTheory.Mem.Chr.splitsC_main R H p hp hs P hP`. Conclude with `⟨h1, GlobalTheory.ToricDenom.splits_below H h3⟩`.
-/
theorem good_prime {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.Mem.Chr.SplitsC H.E p) :
    ¬ (p : ℤ) ∣ discr H.E ∧ ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal →
      Ideal.absNorm P.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below P) := by
  refine ⟨GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp _ ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver hp).symm.trans hs),
    fun P hP => ?_⟩
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs P hP
  exact ⟨h1, GlobalTheory.ToricDenom.splits_below H h3⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.HostSplit.split_of_one_mod R H p hp h).1`.
-/
theorem splitsC_of_mod {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (h : p % (H.QS * H.q * H.d) = 1) :
    GlobalTheory.Mem.Chr.SplitsC H.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod R H p hp h).1

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hv⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hne : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`. Conclude with `⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hv.over.symm⟩`.
-/
theorem exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), GlobalTheory.ToricDenom.below P = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  exact ⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hv.over.symm⟩

/- English proof (translation)
Use `show algebraMap (OF E) (𝓞 E) _ ∈ P.asIdeal ↔ _`. Rewrite using `[map_natCast]`.
-/
theorem natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  show algebraMap (OF E) (𝓞 E) _ ∈ P.asIdeal ↔ _
  rw [map_natCast]

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

open Classical in

/- English proof (translation)
Establish `key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S → ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u` using `fun S hS h => by`. Take `⟨u, hu, h⟩` from `(v.prime.dvd_finset_prod_iff _).1 h`. Establish `h2` using `v.prime.dvd_of_dvd_pow h`. Establish `: v = u` using `HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))`. Conclude with `hS (this ▸ hu)`.

Use `show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _`. Use `split_ifs with h`. Rewrite using `[← Finset.mul_prod_erase _ _ h]`. Use `multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_` and prove the remaining obligations. Rewrite `h'` using `[pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)]`.

Conclude with `key _ (Finset.notMem_erase _ _) h'`. Conclude with `multiplicity_eq_zero.2 (key _ h)`.
-/
theorem expIn_condF' (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    obtain ⟨u, hu, h⟩ := (v.prime.dvd_finset_prod_iff _).1 h
    have h2 := v.prime.dvd_of_dvd_pow h
    have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
    exact hS (this ▸ hu)
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero.2 (key _ h)

/- English proof (translation)
Establish `hE : 1 < LevelStarExponents.condE D`. Use `D.host.qd_big` as an intermediate fact. Unfold `LevelStarExponents.condE`. Establish `h1 : 1 ≤ D.host.QS` using `D.host.QS_pos`. Establish `h2 : 1 < D.host.q` using `by omega`.

Establish `h3 : 1 ≤ D.host.d` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Establish `hgood : ∀ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.bel …`. Establish `ofMod : ∀ p : ℕ, p.Prime → p % LevelStarExponents.condE D = 1 → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q)`. Introduce `p hp hm`.

Establish `h4 : p % 4 = 1`. Establish `: (4 : ℕ) ∣ LevelStarExponents.condE D` using `((dvd_trans (by norm_num) (UpperTheory.Ram.Rd.sixteen_dvd_QS D.host)).mul_right _).mul_right _`. Rewrite using `[← Nat.mod_mod_of_dvd p this, hm]`. Use `⟨hp, by omega, good_prime D.host hp (splitsC_of_mod D.host hp hm)⟩` and prove the remaining obligations. Establish `ofSplit : ∀ p : ℕ, p.Prime → p % 15 = 1 → ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits …`.

Introduce `p hp h15 hs`. Establish `hs' : GlobalTheory.Mem.Chr.SplitsC D.host.E p`. Establish `e` using `GlobalTheory.HostSplit.ncard_placesOver D.host.E hp`. Rewrite `e` using `[hs]`. Conclude with `e`.

Conclude with `⟨hp, by omega, good_prime D.host hp hs'⟩`. Introduce and unpack `p (rfl | rfl | rfl | rfl | rfl)`. Conclude with `ofMod _ (D.host.g_prime 0) (hg 0)`. Conclude with `ofMod _ (D.host.g_prime 1) (hg 1)`. Conclude with `ofSplit _ D.host.pde_prime D.host.pde_mod.1 hpde.1`.

Conclude with `ofSplit _ D.host.pde'_prime D.host.pde_mod.2 hpde.2`. Take `⟨hq, hqm, -⟩` from `leastSplitAuxiliaryPrimeThetaChain_spec D`. Use `ofMod _ hq ?_` and prove the remaining obligations. Rewrite using `[← Nat.mod_mod_of_dvd _ (dvd_mul_left (LevelStarExponents.condE D) (Formalism.MainNotions.rPrAv D)), hqm]`. Conclude with `Nat.mod_eq_of_lt hE`.

Establish `hexp : ∀ v : HeightOneSpectrum (OF D.host.E), v.asIdeal ∣ condF P → v ∈ P.S0`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Establish `e` using `expIn_condF' P v`. Rewrite `e` using `[if_neg h]`.

Use `multiplicity_eq_zero.1 e` as an intermediate fact. Conclude with `this hv`. Use `⟨?_, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot`. Introduce `e`.

Establish `h0 : P.v0 ∈ P.S0` using `P.mem_S0_of_sum_eq.2 (Or.inl rfl)`. Establish `e1` using `expIn_condF' P P.v0`. Rewrite `e1` using `[if_pos h0, condExp, if_pos rfl]`. Establish `e2 : expIn (condF P) P.v0 = 0`. Rewrite using `[e]`.

Conclude with `multiplicity_eq_zero.2 fun h => P.v0.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))`. Use linear arithmetic over natural numbers and integers. Establish `hS` using `hexp v hv`. Establish `hle : expIn (condF P) v ≤ 2`. Apply the tactic sequence `rw [expIn_condF', if_pos hS, condExp]; split_ifs <;> omega`.

Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hpv⟩ : ∃ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) ∧ (p : OF D.host.E) ∈ v.asIdeal := by`. Break down `P.mem_S0_of_sum_eq.1 hS with h | h` into its components or cases. Conclude with `⟨q0 D, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h ▸ P.basePlace_over_qZero⟩`. Break down `(S1_mem_OmF D).1 h with h | h | h | h` into its components or cases. Conclude with `⟨_, Or.inl rfl, h⟩`.

Conclude with `⟨_, Or.inr (Or.inl rfl), h⟩`. Conclude with `⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩`. Conclude with `⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩`. Take `⟨h1, h2, h3, h4⟩` from `hgood p hp`. Take `⟨Q, rfl⟩` from `exists_above v`.

Conclude with `⟨(h4 Q ((natCast_mem_below Q p).1 hpv)).2, hle, p, h1, h2, hpv, h3, fun Q' hQ' => (h4 Q' hQ').1⟩`.
-/
theorem isBaseCond_condF (P : Places L) (hg : ∀ i, D.host.g i % LevelStarExponents.condE D = 1)
    (hpde : ((Ideal.span {(D.host.pde : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      ((Ideal.span {(D.host.pde' : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    IsBaseCond (condF P) := by
  classical
  have hE : 1 < LevelStarExponents.condE D := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    have h1 : 1 ≤ D.host.QS := D.host.QS_pos
    have h2 : 1 < D.host.q := by omega
    have h3 : 1 ≤ D.host.d := by omega
    calc 1 < 1 * D.host.q * 1 := by omega
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr

  have hgood : ∀ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) →
      p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
        (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
    have ofMod : ∀ p : ℕ, p.Prime → p % LevelStarExponents.condE D = 1 → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp hm
      have h4 : p % 4 = 1 := by
        have : (4 : ℕ) ∣ LevelStarExponents.condE D := ((dvd_trans (by norm_num) (UpperTheory.Ram.Rd.sixteen_dvd_QS D.host)).mul_right _).mul_right _
        rw [← Nat.mod_mod_of_dvd p this, hm]
      refine ⟨hp, by omega, good_prime D.host hp (splitsC_of_mod D.host hp hm)⟩
    have ofSplit : ∀ p : ℕ, p.Prime → p % 15 = 1 →
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E →
        p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp h15 hs
      have hs' : GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
        have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
        rw [hs] at e
        exact e
      exact ⟨hp, by omega, good_prime D.host hp hs'⟩
    rintro p (rfl | rfl | rfl | rfl | rfl)
    · exact ofMod _ (D.host.g_prime 0) (hg 0)
    · exact ofMod _ (D.host.g_prime 1) (hg 1)
    · exact ofSplit _ D.host.pde_prime D.host.pde_mod.1 hpde.1
    · exact ofSplit _ D.host.pde'_prime D.host.pde_mod.2 hpde.2
    · obtain ⟨hq, hqm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
      refine ofMod _ hq ?_
      rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left (LevelStarExponents.condE D) (Formalism.MainNotions.rPrAv D)), hqm]
      exact Nat.mod_eq_of_lt hE
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E), v.asIdeal ∣ condF P → v ∈ P.S0 := by
    intro v hv
    by_contra h
    have e := expIn_condF' P v
    rw [if_neg h] at e
    have := multiplicity_eq_zero.1 e
    exact this hv
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  · intro e
    have h0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    have e1 := expIn_condF' P P.v0
    rw [if_pos h0, condExp, if_pos rfl] at e1
    have e2 : expIn (condF P) P.v0 = 0 := by
      rw [e]; exact multiplicity_eq_zero.2 fun h => P.v0.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
    omega
  · have hS := hexp v hv
    have hle : expIn (condF P) v ≤ 2 := by
      rw [expIn_condF', if_pos hS, condExp]; split_ifs <;> omega
    obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) ∧
        (p : OF D.host.E) ∈ v.asIdeal := by
      rcases P.mem_S0_of_sum_eq.1 hS with h | h
      · exact ⟨q0 D, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h ▸ P.basePlace_over_qZero⟩
      · rcases (S1_mem_OmF D).1 h with h | h | h | h
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
    obtain ⟨h1, h2, h3, h4⟩ := hgood p hp
    obtain ⟨Q, rfl⟩ := exists_above v
    exact ⟨(h4 Q ((natCast_mem_below Q p).1 hpv)).2, hle, p, h1, h2, hpv, h3, fun Q' hQ' => (h4 Q' hQ').1⟩

/- English proof (translation)
Take `⟨hcm, hsq⟩` from `GlobalTheory.LamTie.CMType.phi_cmType D.R D.host`. Establish `e : ∀ τ, cmPhi D τ = GlobalTheory.LamTie.phi D.host (D.eTau τ)` using `fun _ => rfl`. Use `⟨fun σ => ?_, fun τ τ' => by rw [e, e]; exact hsq _ _⟩` and prove the remaining obligations. Take `⟨g, hg, hu⟩` from `hcm σ`. Use `⟨D.eTau.symm g, ?_, fun τ hτ => ?_⟩` and prove the remaining obligations.

Simplify using `only [e, Equiv.apply_symm_apply]`. Conclude with `hg`. Establish `hτ' : σ = GlobalTheory.LamTie.phi D.host (D.eTau τ) ∨ σ = ComplexEmbedding.conjugate (GlobalTheory.LamTie.phi D.host (D.eTau τ))`. Simplify `hτ` using `only [e]`. Rewrite using `[← hu _ hτ', Equiv.symm_apply_apply]`.
-/
theorem isCMType_cmPhi (D : D7) : IsCMType (cmPhi D) ∧ ∀ τ τ', cmPhi D τ D.host.sqrtMinusD = cmPhi D τ' D.host.sqrtMinusD := by
  obtain ⟨hcm, hsq⟩ := GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  have e : ∀ τ, cmPhi D τ = GlobalTheory.LamTie.phi D.host (D.eTau τ) := fun _ => rfl
  refine ⟨fun σ => ?_, fun τ τ' => by rw [e, e]; exact hsq _ _⟩
  obtain ⟨g, hg, hu⟩ := hcm σ
  refine ⟨D.eTau.symm g, ?_, fun τ hτ => ?_⟩
  · simp only [e, Equiv.apply_symm_apply]
    exact hg
  · have hτ' : σ = GlobalTheory.LamTie.phi D.host (D.eTau τ) ∨ σ = ComplexEmbedding.conjugate (GlobalTheory.LamTie.phi D.host (D.eTau τ)) := by
      simpa only [e] using hτ
    rw [← hu _ hτ', Equiv.symm_apply_apply]

end GlobalTheory.SqTop.FieldDatPf

namespace GlobalTheory.SqTop

/- English proof (translation)
Use `⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨Pm, -, -⟩, -⟩` from `hR.size`. Take `⟨hcm, hsq⟩` from `FieldDatPf.isCMType_cmPhi D`. Establish `hd : 0 < D.host.d` using `D.host.hyp.2.1.pos`. Conclude with `⟨D.host.isCMField_hostE, GlobalTheory.ToricDenomBridge.host_isAbelianGalois D.host, GlobalTheory.ToricDenomBridge.isFieldData_host D.host hcm hsq, FieldDatPf.isBaseCond_condF G.pl Pm.g_mod Pm.pde_split, GlobalTheory.ToricDenom.ringPair D.host.d hd, GlobalTheory.ToricDenomBridge.i …`.
-/
theorem fieldDat : FieldDat := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  obtain ⟨hcm, hsq⟩ := FieldDatPf.isCMType_cmPhi D
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  exact ⟨D.host.isCMField_hostE, GlobalTheory.ToricDenomBridge.host_isAbelianGalois D.host,
    GlobalTheory.ToricDenomBridge.isFieldData_host D.host hcm hsq, FieldDatPf.isBaseCond_condF G.pl Pm.g_mod Pm.pde_split,
    GlobalTheory.ToricDenom.ringPair D.host.d hd,
    GlobalTheory.ToricDenomBridge.isIntLattice_of D.host.hyp.2.1 (by have := D.host.hyp.2.2.2.1; omega) rfl rfl⟩

end GlobalTheory.SqTop

end
