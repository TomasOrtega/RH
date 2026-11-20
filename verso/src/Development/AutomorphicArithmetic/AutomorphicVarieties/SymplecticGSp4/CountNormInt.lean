import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.TeichNotLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Establish `hq : ((n : ℚ) : ℚ) ≠ 0` using `by exact_mod_cast hn`. Establish `hx : ‖(n : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l n : ℤ))`. Establish `hc : (((n : ℚ) : ℚ_[l]) : PadicAlgCl l) = (n : PadicAlgCl l)` using `by simp`. Rewrite using `[← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]`. Establish `h` using `padicNorm.eq_zpow_of_nonzero (p := l) hq`.

Rewrite `h` using `[padicValRat.of_int]`. Rewrite using `[h]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast hl.out.pos`.

Establish `hdvd : ((l : ℤ) ^ padicValInt l n) ∣ n` using `padicValInt_dvd n`. Establish `hle : ((l : ℤ) ^ padicValInt l n) ≤ |n|` using `Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)`. Establish `hle' : (l : ℝ) ^ padicValInt l n ≤ |(n : ℝ)|` using `by exact_mod_cast hle`. Rewrite using `[hx, Real.log_zpow]`. Use `push_cast`.

Rewrite using `[neg_mul, neg_neg, ← Real.log_pow]`. Conclude with `Real.log_le_log (pow_pos hl0 _) hle'`.
-/
private theorem count_norm_int (l : ℕ) [hl : Fact l.Prime] (n : ℤ) (hn : n ≠ 0) :
    -Real.log ‖(n : PadicAlgCl l)‖ ≤ Real.log |(n : ℝ)| := by
  have hq : ((n : ℚ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have hx : ‖(n : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l n : ℤ)) := by
    have hc : (((n : ℚ) : ℚ_[l]) : PadicAlgCl l) = (n : PadicAlgCl l) := by simp
    rw [← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
    have h := padicNorm.eq_zpow_of_nonzero (p := l) hq
    rw [padicValRat.of_int] at h
    rw [h]
    push_cast
    rfl
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hdvd : ((l : ℤ) ^ padicValInt l n) ∣ n := padicValInt_dvd n
  have hle : ((l : ℤ) ^ padicValInt l n) ≤ |n| :=
    Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
  have hle' : (l : ℝ) ^ padicValInt l n ≤ |(n : ℝ)| := by exact_mod_cast hle
  rw [hx, Real.log_zpow]
  push_cast
  rw [neg_mul, neg_neg, ← Real.log_pow]
  exact Real.log_le_log (pow_pos hl0 _) hle'

/- English proof (translation)
Establish `hz : (cycZ ℚ Ω l σ : ℤ_[l]) = (p : ℤ_[l])`. Apply `PadicInt.ext_of_toZModPow.mp` to reduce the goal to its premises. Introduce `n`. Conclude with `cycZ_toZModPow_eq hw hB hσ.2 n`. Simplify using `only [chiO, MonoidHom.comp_apply, Units.coe_map]`.

Rewrite using `[hz]`. Simplify using the standard rewrite rules.
-/
private theorem count_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    {p : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} {B : ValuationSubring Ω} (hw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    (hB : IsPlaceOver B w) {σ : G ℚ Ω} (hσ : IsFrob (F := ℚ) B p σ) :
    (((chiO ℚ Ω l c.O σ : c.Oˣ) : c.O) : PadicAlgCl l) = (p : PadicAlgCl l) := by
  have hz : (cycZ ℚ Ω l σ : ℤ_[l]) = (p : ℤ_[l]) := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact cycZ_toZModPow_eq hw hB hσ.2 n
  simp only [chiO, MonoidHom.comp_apply, Units.coe_map]
  rw [hz]
  simp

/- English proof (translation)
Establish `h1 : χ g ^ k = 1`. Rewrite using `[← MonoidHom.pow_apply, h, MonoidHom.one_apply]`. Rewrite using `[← map_pow]`. Establish `h2 : ((χ g : c.O) : PadicAlgCl l) ^ k = 1`. Rewrite using `[← Subalgebra.coe_pow, ← Units.val_pow_eq_pow_val, h1]`.

Both sides reduce to the same expression. Rewrite using `[h2, map_one]`.
-/
private theorem count_pow {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (c : Coef l) (ι : PadicAlgCl l ≃+* ℂ)
    (χ : Γ →* c.Oˣ) {k : ℕ} (h : χ ^ k = 1) (g : Γ) : ι ((χ g : c.O) : PadicAlgCl l) ^ k = 1 := by
  have h1 : χ g ^ k = 1 := by
    rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
  rw [← map_pow]
  have h2 : ((χ g : c.O) : PadicAlgCl l) ^ k = 1 := by
    rw [← Subalgebra.coe_pow, ← Units.val_pow_eq_pow_val, h1]
    rfl
  rw [h2, map_one]

/- English proof (translation)
Establish `htr : (D.r0E σ).trace = ∑ i, (((D.ps i σ : c.Oˣ) : c.O) : PadicAlgCl l)`. Simplify using `[Raw.r0E, Raw.r0, mapRep, diagRep, Matrix.trace]`. Rewrite using `[htr]`. Simplify using `only [Fin.sum_univ_four, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, Af.eis4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_natCast, MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply, Mono …`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem count_trace {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) {p : ℕ} {σ : G ℚ Ω}
    (hχ : (((chiO ℚ Ω l c.O σ : c.Oˣ) : c.O) : PadicAlgCl l) = (p : PadicAlgCl l)) :
    (D.r0E σ).trace = ι.symm (Af.eis4 p D.e (ι (((D.om⁻¹ * D.ξ * D.ψ) σ : c.O) : PadicAlgCl l))
      (ι ((D.ψ σ : c.O) : PadicAlgCl l)) (ι (((D.om⁻¹ * D.ξ) σ : c.O) : PadicAlgCl l))) := by
  have htr : (D.r0E σ).trace = ∑ i, (((D.ps i σ : c.Oˣ) : c.O) : PadicAlgCl l) := by
    simp [Raw.r0E, Raw.r0, mapRep, diagRep, Matrix.trace]
  rw [htr]
  simp only [Fin.sum_univ_four, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, Af.eis4, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_natCast, MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Subalgebra.coe_mul, Subalgebra.coe_one,
    Subalgebra.coe_pow, map_add, map_mul, map_pow, map_natCast, map_one, RingEquiv.symm_apply_apply, hχ]
  ring

/- English proof (translation)
Introduce and unpack `⟨C, A, hnum⟩`. Use `⟨C, A, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut`. Establish `hlp : l ≠ p` using `fun h => hpS (h ▸ hD.l_mem)`. Take `⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩` from `ML.placeBasic Ω`.

Establish `hB : ML.Over (D.pl p) p` using `hD.pl_over p hp`. Take `⟨σ, hσ⟩` from `hfr _ p hp hB`. Take `⟨w, hw, -, hpw⟩` from `hpl _ p hp hB`. Establish `hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h => by`. Use `hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_` and prove the remaining obligations.

Establish `h1` using `(hw ((l : ℕ) : 𝓞 ℚ)).2 h`. Establish `e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω)` using `by simp`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hχ` using `count_chi c hlw hw hσ`.

Establish `h3 : (D.om⁻¹ * D.ξ) ^ k = 1` using `by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]`. Establish `h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1` using `by rw [mul_pow, h3, hψ, one_mul]`. Take `⟨NN, hNN, hlog, hX⟩` from `hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _ (count_pow c ι _ h1 σ) (count_pow c ι _ hψ σ) (count_pow c ι _ h3 σ)`. Use `replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ`. Rewrite `hX` using `[← count_trace D ι hχ]`.

Establish `hadm : ∀ r, D.EPt r → Irr r → Af.AdmR ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits`. Introduce `r hr hi`. Take `⟨hlev, θ, hθ, hdual, -⟩` from `level D hD N hN hψN hξN hoN r hr`. Conclude with `⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, Or.inl (Lev.teichDvd D hD N hN hoN)⟩`. Establish `hne : D.AllIrr (fun r => D.aVal σ r ≠ 0)`.

Introduce `r hr hi`. Establish `h` using `(hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi) (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _ (Finset.mem_singleton_self _)`. Conclude with `sub_ne_zero.2 h`. Use `⟨σ, hne, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨-, Xi, hXi, hconj, hle⟩`.

Establish `hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits` using `fun r r' h => MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)`. Establish `h` using `(hX (Xi.image fun r => r.toHomUnits) (fun s hs => by`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hs`.

Take `⟨r', hr', rfl⟩` from `Finset.mem_image.1 hs'`. Rewrite using `[hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2`. Rewrite `h` using `[Finset.prod_image hinj.injOn]`. Express the relevant statement in the definitionally equal form `_ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h`. Establish `hN0 : 0 < ‖(NN : PadicAlgCl l)‖` using `norm_pos_iff.2 (by exact_mod_cast hNN)`.

Establish `h4` using `Real.log_le_log hN0 h`. Rewrite `h4` using `[Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)]`. Establish `h5` using `count_norm_int l NN hNN`. Establish `h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤ C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p`. Establish `: (Nat.totient k : ℝ) ≤ k` using `by exact_mod_cast Nat.totient_le k`.

Use `Real.log_natCast_nonneg p` as an intermediate fact. Use `gcongr`. Rewrite `hle` using `[Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.count :
    Af.NumberSp4 → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (Aut.IsAut4 ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
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
  have hadm : ∀ r, D.EPt r → Irr r → Af.AdmR ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, Or.inl (Lev.teichDvd D hD N hN hoN)⟩
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
