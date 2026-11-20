import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private count_norm_int count_chi count_pow count_trace from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
/- English proof (translation)
Introduce and unpack `⟨C, A, hnum⟩`. Use `⟨C, A, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut`. Establish `hlp : l ≠ p` using `fun h => hpS (h ▸ hD.l_mem)`. Take `⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩` from `ML.placeBasic Ω`.

Establish `hB : ML.Over (D.pl p) p` using `hD.pl_over p hp`. Take `⟨σ, hσ⟩` from `hfr _ p hp hB`. Take `⟨w, hw, -, hpw⟩` from `hpl _ p hp hB`. Establish `hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h => by`. Use `hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_` and prove the remaining obligations.

Establish `h1` using `(hw ((l : ℕ) : 𝓞 ℚ)).2 h`. Establish `e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω)` using `by simp`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hχ` using `count_chi c hlw hw hσ`.

Establish `h3 : (D.om⁻¹ * D.ξ) ^ k = 1` using `by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]`. Establish `h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1` using `by rw [mul_pow, h3, hψ, one_mul]`. Take `⟨NN, hNN, hlog, hX⟩` from `hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _ (count_pow c ι _ h1 σ) (count_pow c ι _ hψ σ) (count_pow c ι _ h3 σ)`. Use `replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ`. Rewrite `hX` using `[← count_trace D ι hχ]`.

Establish `hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits`. Introduce `r hr hi`. Take `⟨hlev, θ, hθ, hdual, -⟩` from `level D hD N hN hψN hξN hoN r hr`. Conclude with `⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩`. Establish `hne : D.AllIrr (fun r => D.aVal σ r ≠ 0)`.

Introduce `r hr hi`. Establish `h` using `(hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi) (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _ (Finset.mem_singleton_self _)`. Conclude with `sub_ne_zero.2 h`. Use `⟨σ, hne, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨-, Xi, hXi, hconj, hle⟩`.

Establish `hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits` using `fun r r' h => MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)`. Establish `h` using `(hX (Xi.image fun r => r.toHomUnits) (fun s hs => by`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hs`.

Take `⟨r', hr', rfl⟩` from `Finset.mem_image.1 hs'`. Rewrite using `[hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2`. Rewrite `h` using `[Finset.prod_image hinj.injOn]`. Express the relevant statement in the definitionally equal form `_ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h`. Establish `hN0 : 0 < ‖(NN : PadicAlgCl l)‖` using `norm_pos_iff.2 (by exact_mod_cast hNN)`.

Establish `h4` using `Real.log_le_log hN0 h`. Rewrite `h4` using `[Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)]`. Establish `h5` using `count_norm_int l NN hNN`. Establish `h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤ C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p`. Establish `: (Nat.totient k : ℝ) ≤ k` using `by exact_mod_cast Nat.totient_le k`.

Use `Real.log_natCast_nonneg p` as an intermediate fact. Use `gcongr`. Rewrite `hle` using `[Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound :
    _root_.UpperTheory.V.Af.NumberSp4Alt → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
  classical
  rintro ⟨C, A, hnum⟩
  refine ⟨C, A, ?_⟩
  intro Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut
  have hlp : l ≠ p := fun h => hpS (h ▸ hD.l_mem)
  obtain ⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  have hB : ML.Over (D.pl p) p := hD.pl_over p hp
  obtain ⟨σ, hσ⟩ := hfr _ p hp hB
  obtain ⟨w, hw, -, hpw⟩ := hpl _ p hp hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have hχ := count_chi c hlw hw hσ
  have h3 : (D.om⁻¹ * D.ξ) ^ k = 1 := by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]
  have h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1 := by rw [mul_pow, h3, hψ, one_mul]
  obtain ⟨NN, hNN, hlog, hX⟩ := hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _
    (count_pow c ι _ h1 σ) (count_pow c ι _ hψ σ) (count_pow c ι _ h3 σ)
  replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ
  rw [← count_trace D ι hχ] at hX
  have hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩
  have hne : D.AllIrr (fun r => D.aVal σ r ≠ 0) := by
    intro r hr hi
    have h := (hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi)
      (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _
      (Finset.mem_singleton_self _)
    exact sub_ne_zero.2 h
  refine ⟨σ, hne, ?_⟩
  rintro ⟨-, Xi, hXi, hconj, hle⟩
  have hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits := fun r r' h =>
    MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)
  have h := (hX (Xi.image fun r => r.toHomUnits) (fun s hs => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hs'
      rw [hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2
  rw [Finset.prod_image hinj.injOn] at h
  change _ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hNN)
  have h4 := Real.log_le_log hN0 h
  rw [Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)] at h4
  have h5 := count_norm_int l NN hNN
  have h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤
      C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p := by
    have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have := Real.log_natCast_nonneg p
    gcongr
  rw [Finset.sum_neg_distrib] at hle
  linarith
end
