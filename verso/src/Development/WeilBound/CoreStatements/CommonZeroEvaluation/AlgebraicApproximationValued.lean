import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsRootAdicComplete
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsAlgebraicStd

open Formalism.L2.Pj

open Polynomial IsDedekindDomain

/- English proof (translation)
Use `set P := IsDiscreteValuationRing.maximalIdeal V with hP`. Establish `hb : (1 : NNReal) < 2` using `one_lt_two`. Use `letI nK : NormedField K := (P.adicAbv (K := K) hb).toNormedField`. Establish `hnorm : ∀ x : K, ‖x‖ = (WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (valV V x) : ℝ)` using `fun x => rfl`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)`.

Establish `hint : ∀ a : V, ‖algebraMap V K a‖ ≤ 1`. Introduce `a`. Rewrite using `[hnorm]`. Conclude with `(WithZeroMulInt.toNNReal_le_one_iff hb).mpr (P.valuation_le_one (K := K) a)` after adjusting the coercions. Establish `hintlt : ∀ a : V, ‖algebraMap V K a‖ < 1 ↔ a ∈ IsLocalRing.maximalIdeal V`.

Introduce `a`. Rewrite using `[hnorm]`. Establish `h` using `WithZeroMulInt.toNNReal_lt_one_iff (m := P.valuation K (algebraMap V K a)) hb`. Rewrite `h` using `[P.valuation_lt_one_iff_mem]`. Conclude with `h` after adjusting the coercions.

Establish `hmem : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : V, algebraMap V K a = x`. Introduce `x hx`. Establish `hv : P.valuation K x ≤ 1`. Rewrite `hx` using `[hnorm]`. Conclude with `(WithZeroMulInt.toNNReal_le_one_iff hb).mp (by exact_mod_cast hx)`.

Establish `huniq : ∀ w : HeightOneSpectrum V, w = P`. Introduce `w`. Use `ext1`. Conclude with `IsLocalRing.eq_maximalIdeal w.isMaximal`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one K x (fun w => by rw [huniq w]; exact hv)`.

Conclude with `⟨a, ha⟩`. Establish `hev : ∀ (q : Polynomial V) (a : V), Polynomial.eval (algebraMap V K a) (q.map (algebraMap V K)) = algebraMap V K (Polynomial.eval a q)`. Introduce `q a`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Establish `hH : ModelDimension.Alg.HenselN K`.

Introduce `h α hco hα hlt`. Choose the witnesses or unpack the hypotheses as in `⟨f, rfl⟩ : ∃ f : Polynomial V, f.map (algebraMap V K) = h := by`. Establish `hl : h ∈ Polynomial.lifts (algebraMap V K)` using `(Polynomial.lifts_iff_coeff_lifts h).mpr (fun k => hmem _ (hco k))`. Conclude with `Polynomial.mem_lifts h |>.mp hl`. Take `⟨a, rfl⟩` from `hmem α hα`.

Rewrite `hlt` using `[Polynomial.derivative_map, hev, hev]`. Rewrite using `[Polynomial.derivative_map, hev, hev]`. Use `set y := Polynomial.eval a f`. Use `set d := Polynomial.eval a (Polynomial.derivative f)`. Establish `hd : algebraMap V K d ≠ 0`.

Introduce `h0`. Rewrite `hlt` using `[h0, norm_zero]`. Use `norm_nonneg (algebraMap V K y)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hdpos : 0 < ‖algebraMap V K d‖ ^ 2` using `by positivity`.

Establish `hq : ‖algebraMap V K y / algebraMap V K d ^ 2‖ < 1`. Rewrite using `[norm_div, norm_pow, div_lt_one hdpos]`. Conclude with `hlt`. Take `⟨e, he⟩` from `hmem _ hq.le`. Establish `hem : e ∈ IsLocalRing.maximalIdeal V` using `(hintlt e).mp (by rw [he]; exact hq)`.

Establish `hy : y = d ^ 2 * e`. Apply `IsFractionRing.injective V K` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, he]`. Clear the denominators using the available nonvanishing facts. Take `⟨β, hβ, c, hc⟩` from `ModelDimension.Alg.exists_root f a e hem hy`.

Use `⟨algebraMap V K β, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev, hβ, map_zero]`. Rewrite using `[← map_sub, hc, map_mul, norm_mul, he, norm_div, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hint c`.

Use `_ = _ := mul_one _`. Take `⟨N, hN0, hNm, hNf⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : V) ∈ IsLocalRing.maximalIdeal V ∧ Finite (V ⧸ Ideal.span {(N : V)})` from `by haveI : CharP (IsLocalRing.ResidueField V) (ringChar (IsLocalRing.ResidueField V)) := ringChar.charP _`. Use `⟨ringChar (IsLocalRing.ResidueField V), CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`.

Establish `hne : Ideal.span {((ringChar (IsLocalRing.ResidueField V) : ℕ) : V)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ`.

Use `haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hT`. Establish `hfin` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal V)) k`. Rewrite `hfin` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hk]`. Conclude with `hfin`. Establish `hNK : ‖(N : K)‖ < 1`.

Use `(hintlt (N : V)).mpr hNm` as an intermediate fact. Simplify using `using this`. Establish `hNne : (N : K) ≠ 0` using `Nat.cast_ne_zero.mpr hN0`. Establish `hdense : Dense {x : K | IsAlgebraic ℤ x}`. Use `ModelDimension.Alg.dense_algebraic hH (fun z => ?_) N hN0 hNK (fun α hα => ?_)` and prove the remaining obligations.

Simplify using `using hint (z : V)`. Use `haveI := hNf`. Take `⟨m, hm⟩` from `ModelDimension.Alg.exists_monic (V := V) N`. Use `⟨m, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hmem α hα`.

Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hδ hNK`. Take `⟨Q, hQm, hQd, c, hc⟩` from `hm a k`. Use `⟨Q, hQm, hQd, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algebraMap_apply, hc, map_mul, norm_mul, map_pow, norm_pow, map_natCast]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hint c`. Use `_ < δ := by rw [mul_one]; exact hk`. Use `letI : Algebra F K := io.toAlgebra`. Establish `hdF : Dense {x : K | IsAlgebraic F x}` using `hdense.mono (fun x hx => IsAlgebraic.extendScalars (algebraMap ℤ F).injective_int hx)`. Set `ψa : R →ₐ[F] K` to `{ ψ with commutes' := fun r => by exact RingHom.congr_fun hψ r }`.

Establish `hFZ : Algebra.IsAlgebraic ℤ F` using `(IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hεn⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ d : K, ‖d‖ < ε → d = 0 ∨ (n : ℤ) ≤ vV V d := by`. Use `⟨(WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (WithZero.exp (-(n : ℤ))) : ℝ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `WithZeroMulInt.toNNReal_pos _ WithZero.exp_ne_zero` after adjusting the coercions. Introduce `d hd`.

Distinguish the cases in `h0 : d = 0`. Conclude with `Or.inl h0`. Use `right`. Rewrite `hd` using `[hnorm]`. Establish `hlt : valV V d < WithZero.exp (-(n : ℤ))` using `(WithZeroMulInt.toNNReal_strictMono hb).lt_iff_lt.mp (by exact_mod_cast hd)`.

Establish `hne : valV V d ≠ 0` using `(Valuation.ne_zero_iff _).mpr h0`. Rewrite `hlt` using `[← WithZero.exp_log hne, WithZero.exp_lt_exp]`. Use `show (n : ℤ) ≤ -(valV V d).log`. Use linear arithmetic over natural numbers and integers. Take `⟨ψ', h1, h2, h3⟩` from `ModelDimension.Alg.approx_smooth hH hNne hNK hdF ψa S ε hε g hg`.

Use `⟨ψ'.toRingHom, ?_, fun x => ?_, fun s hs => ?_, h3⟩` and prove the remaining obligations. Use extensionality with `r`. Conclude with `ψ'.commutes r`. Conclude with `(h1 x).restrictScalars ℤ`. Break down `hεn _ (h2 s hs) with h | h` into its components or cases.

Conclude with `Or.inl (sub_eq_zero.mp h)`. Conclude with `Or.inr h`.
-/
theorem ModelDimension.Alg.approx_dvr (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.Smooth F R] (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] [Field K] [Algebra V K] [IsFractionRing V K]
    (hT : Finite (IsLocalRing.ResidueField V)) (io : F →+* K) (ψ : R →+* K) (hψ : ψ.comp (algebraMap F R) = io)
    (S : Finset R) (n : ℕ) (g : R) (hg : g ≠ 0) : ∃ ψ' : R →+* K, ψ'.comp (algebraMap F R) = io ∧
      (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  classical
  set P := IsDiscreteValuationRing.maximalIdeal V with hP
  have hb : (1 : NNReal) < 2 := one_lt_two
  letI nK : NormedField K := (P.adicAbv (K := K) hb).toNormedField
  have hnorm : ∀ x : K, ‖x‖ = (WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (valV V x) : ℝ) :=
    fun x => rfl
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  have hint : ∀ a : V, ‖algebraMap V K a‖ ≤ 1 := by
    intro a
    rw [hnorm]
    exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff hb).mpr (P.valuation_le_one (K := K) a)
  have hintlt : ∀ a : V, ‖algebraMap V K a‖ < 1 ↔ a ∈ IsLocalRing.maximalIdeal V := by
    intro a
    rw [hnorm]
    have h := WithZeroMulInt.toNNReal_lt_one_iff (m := P.valuation K (algebraMap V K a)) hb
    rw [P.valuation_lt_one_iff_mem] at h
    exact_mod_cast h
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : V, algebraMap V K a = x := by
    intro x hx
    have hv : P.valuation K x ≤ 1 := by
      rw [hnorm] at hx
      exact (WithZeroMulInt.toNNReal_le_one_iff hb).mp (by exact_mod_cast hx)
    have huniq : ∀ w : HeightOneSpectrum V, w = P := by
      intro w
      ext1
      exact IsLocalRing.eq_maximalIdeal w.isMaximal
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x
      (fun w => by rw [huniq w]; exact hv)
    exact ⟨a, ha⟩
  have hev : ∀ (q : Polynomial V) (a : V),
      Polynomial.eval (algebraMap V K a) (q.map (algebraMap V K)) = algebraMap V K (Polynomial.eval a q) := by
    intro q a
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hH : ModelDimension.Alg.HenselN K := by
    intro h α hco hα hlt
    obtain ⟨f, rfl⟩ : ∃ f : Polynomial V, f.map (algebraMap V K) = h := by
      have hl : h ∈ Polynomial.lifts (algebraMap V K) :=
        (Polynomial.lifts_iff_coeff_lifts h).mpr (fun k => hmem _ (hco k))
      exact Polynomial.mem_lifts h |>.mp hl
    obtain ⟨a, rfl⟩ := hmem α hα
    rw [Polynomial.derivative_map, hev, hev] at hlt
    rw [Polynomial.derivative_map, hev, hev]
    set y := Polynomial.eval a f
    set d := Polynomial.eval a (Polynomial.derivative f)
    have hd : algebraMap V K d ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      have := norm_nonneg (algebraMap V K y)
      nlinarith
    have hdpos : 0 < ‖algebraMap V K d‖ ^ 2 := by positivity
    have hq : ‖algebraMap V K y / algebraMap V K d ^ 2‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one hdpos]
      exact hlt
    obtain ⟨e, he⟩ := hmem _ hq.le
    have hem : e ∈ IsLocalRing.maximalIdeal V := (hintlt e).mp (by rw [he]; exact hq)
    have hy : y = d ^ 2 * e := by
      apply IsFractionRing.injective V K
      rw [map_mul, map_pow, he]
      field_simp
    obtain ⟨β, hβ, c, hc⟩ := ModelDimension.Alg.exists_root f a e hem hy
    refine ⟨algebraMap V K β, ?_, ?_⟩
    · rw [hev, hβ, map_zero]
    · rw [← map_sub, hc, map_mul, norm_mul, he, norm_div, norm_pow]
      calc ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * ‖algebraMap V K c‖
          ≤ ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * 1 := by
            gcongr
            exact hint c
        _ = _ := mul_one _
  obtain ⟨N, hN0, hNm, hNf⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : V) ∈ IsLocalRing.maximalIdeal V ∧
      Finite (V ⧸ Ideal.span {(N : V)}) := by
    haveI : CharP (IsLocalRing.ResidueField V) (ringChar (IsLocalRing.ResidueField V)) :=
      ringChar.charP _
    refine ⟨ringChar (IsLocalRing.ResidueField V),
      CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _, ?_, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact ringChar.Nat.cast_ringChar
    · have hne : Ideal.span {((ringChar (IsLocalRing.ResidueField V) : ℕ) : V)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _)
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
      obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
      haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hT
      have hfin := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal V)) k
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hk] at hfin
      exact hfin
  have hNK : ‖(N : K)‖ < 1 := by
    have := (hintlt (N : V)).mpr hNm
    simpa using this
  have hNne : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hdense : Dense {x : K | IsAlgebraic ℤ x} := by
    refine ModelDimension.Alg.dense_algebraic hH (fun z => ?_) N hN0 hNK (fun α hα => ?_)
    · simpa using hint (z : V)
    · haveI := hNf
      obtain ⟨m, hm⟩ := ModelDimension.Alg.exists_monic (V := V) N
      refine ⟨m, fun δ hδ => ?_⟩
      obtain ⟨a, rfl⟩ := hmem α hα
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hNK
      obtain ⟨Q, hQm, hQd, c, hc⟩ := hm a k
      refine ⟨Q, hQm, hQd, ?_⟩
      rw [Polynomial.aeval_algebraMap_apply, hc, map_mul, norm_mul, map_pow, norm_pow, map_natCast]
      calc ‖(N : K)‖ ^ k * ‖algebraMap V K c‖ ≤ ‖(N : K)‖ ^ k * 1 := by
            gcongr
            exact hint c
        _ < δ := by rw [mul_one]; exact hk
  letI : Algebra F K := io.toAlgebra
  have hdF : Dense {x : K | IsAlgebraic F x} :=
    hdense.mono (fun x hx => IsAlgebraic.extendScalars (algebraMap ℤ F).injective_int hx)
  let ψa : R →ₐ[F] K := { ψ with commutes' := fun r => by exact RingHom.congr_fun hψ r }
  have hFZ : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance
  obtain ⟨ε, hε, hεn⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ d : K, ‖d‖ < ε → d = 0 ∨ (n : ℤ) ≤ vV V d := by
    refine ⟨(WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (WithZero.exp (-(n : ℤ))) : ℝ), ?_, ?_⟩
    · exact_mod_cast WithZeroMulInt.toNNReal_pos _ WithZero.exp_ne_zero
    · intro d hd
      by_cases h0 : d = 0
      · exact Or.inl h0
      right
      rw [hnorm] at hd
      have hlt : valV V d < WithZero.exp (-(n : ℤ)) :=
        (WithZeroMulInt.toNNReal_strictMono hb).lt_iff_lt.mp (by exact_mod_cast hd)
      have hne : valV V d ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
      rw [← WithZero.exp_log hne, WithZero.exp_lt_exp] at hlt
      show (n : ℤ) ≤ -(valV V d).log
      omega
  obtain ⟨ψ', h1, h2, h3⟩ := ModelDimension.Alg.approx_smooth hH hNne hNK hdF ψa S ε hε g hg
  refine ⟨ψ'.toRingHom, ?_, fun x => ?_, fun s hs => ?_, h3⟩
  · ext r
    exact ψ'.commutes r
  · exact (h1 x).restrictScalars ℤ
  · rcases hεn _ (h2 s hs) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr h

/- English proof (translation)
Introduce `F _ _ R _ _ _ _ T hT io ψ hψ S n g hg`. Use `letI := T.cr`. Use `letI := T.dom`. Use `letI := T.dvr`. Use `letI := T.cpl`.

Use `letI := T.ch0`. Take `⟨ψ', h1, h2, h3, h4⟩` from `ModelDimension.Alg.approx_dvr F R T.V (FractionRing T.V) hT io ψ hψ S n g hg`. Use `⟨ψ', h1, fun x => ?_, h3, h4⟩` and prove the remaining obligations. Take `⟨p, hp, hpx⟩` from `h2 x`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Simplify using `only [Polynomial.aeval_def, algebraMap_int_eq] at hpx`. Rewrite using `[Polynomial.aeval_def, show algebraMap ℤ T.Fr = Int.castRingHom T.Fr from RingHom.ext_int _ _]`. Conclude with `hpx`.
-/
theorem ModelDimension.algebraic_approximation_valued : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  intro F _ _ R _ _ _ _ T hT io ψ hψ S n g hg
  letI := T.cr; letI := T.dom; letI := T.dvr; letI := T.cpl; letI := T.ch0
  obtain ⟨ψ', h1, h2, h3, h4⟩ :=
    ModelDimension.Alg.approx_dvr F R T.V (FractionRing T.V) hT io ψ hψ S n g hg
  refine ⟨ψ', h1, fun x => ?_, h3, h4⟩
  obtain ⟨p, hp, hpx⟩ := h2 x
  refine ⟨p, hp, ?_⟩
  simp only [Polynomial.aeval_def, algebraMap_int_eq] at hpx
  rw [Polynomial.aeval_def, show algebraMap ℤ T.Fr = Int.castRingHom T.Fr from RingHom.ext_int _ _]
  exact hpx
