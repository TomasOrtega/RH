import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.ZetaPole

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `by rintro rfl; norm_num at hs`. Establish `h` using `(GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm.hasSum`. Rewrite `h` using `[← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff]`. Use `HasSum.tsum_eq (h.sigma fun n => ?_)` and prove the remaining obligations. Establish `: ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘ (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = (n : ℂ) ^ (-s)`.

Introduce and unpack `⟨I, rfl⟩`. Both sides reduce to the same expression. Simplify using `only [this]`. Use `Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}` as an intermediate fact. Establish `e : LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n = ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (n : ℂ) ^ (-s)`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[hs0]`. Rewrite using `[LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `hasSum_fintype _`.
-/
theorem dedekindZeta_eq_tsum_ideal (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm.hasSum
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
  refine HasSum.tsum_eq (h.sigma fun n => ?_)
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (n : ℂ) ^ (-s) := by
    rintro ⟨I, rfl⟩; rfl
  simp only [this]
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have e : LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n =
      ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hs0]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
      simp
  rw [e]
  exact hasSum_fintype _

noncomputable def logFactor (n : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (n : ℝ) ^ (-s))

/- English proof (translation)
The claim follows from `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)`.
-/
theorem rpow_lt_one {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)

/- English proof (translation)
Establish `h1` using `rpow_lt_one hn hs`. Establish `h2 : 0 ≤ (n : ℝ) ^ (-s)` using `by positivity`. Unfold `logFactor`. Use `Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logFactor_nonneg {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : 0 ≤ logFactor n s := by
  have h1 := rpow_lt_one hn hs
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  unfold logFactor
  have := Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)
  linarith

/- English proof (translation)
Establish `h1` using `rpow_lt_one hn one_pos`. Establish `h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)`. Unfold `logFactor`. Use `Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logFactor_le {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 1 ≤ s) : logFactor n s ≤ logFactor n 1 := by
  have h1 := rpow_lt_one hn one_pos
  have h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)
  unfold logFactor
  have := Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s))
    (by linarith) (by linarith)
  linarith

/- English proof (translation)
Establish `h1` using `rpow_lt_one hn hs`. Unfold `logFactor`. Rewrite using `[Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_cpow (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem ofReal_logFactor {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) :
    ((logFactor n s : ℝ) : ℂ) = -Complex.log (1 - (n : ℂ) ^ (-(s : ℂ))) := by
  have h1 := rpow_lt_one hn hs
  unfold logFactor
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

/- English proof (translation)
Establish `hS` using `(GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).of_norm`. Establish `pinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal` using `fun v w h => HeightOneSpectrum.ext h`. Establish `h` using `(Summable.clog_one_sub (hS.comp_injective pinj)).neg`. Rewrite using `[← Complex.summable_ofReal]`. Use `h.congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)]`. Both sides reduce to the same expression.
-/
theorem summable_logFactor (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => logFactor (Ideal.absNorm v.asIdeal) s := by
  have hS := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).of_norm
  have pinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  have h := (Summable.clog_one_sub (hS.comp_injective pinj)).neg
  rw [← Complex.summable_ofReal]
  refine h.congr fun v => ?_
  rw [ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)]
  rfl

/- English proof (translation)
Establish `hs' : 1 < (s : ℂ).re` using `by simpa using hs`. Establish `hs0 : (s : ℂ) ≠ 0` using `by rintro h; rw [h] at hs'; norm_num at hs'`. Establish `h` using `GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1) (by simp) (by simp) (fun I J => by`. Apply the tactic sequence `by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])`. Apply the tactic sequence `(fun I => by split_ifs <;> simp) s hs'`.

Establish `e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))` using `fun I => by`. Distinguish the cases in `hI : I = ⊥`. Simplify using `[hI, hs0]`. Simplify using `[hI]`. Simplify using `only [e1] at h`.

Simplify using `only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _) (lt_trans one_pos hs)] at h`. Rewrite using `[dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp, Complex.ofReal_re]`.
-/
theorem norm_dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by
  classical
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by rintro h; rw [h] at hs'; norm_num at hs'
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs'
  have e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))
      = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hs0]
    · simp [hI]
  simp only [e1] at h
  simp only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _)
    (lt_trans one_pos hs)] at h
  rw [dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp,
    Complex.ofReal_re]

/- English proof (translation)
Introduce `K F _ _ _ _ S hS f hf hN`. Use `set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc`. Establish `key : ∀ s : ℝ, 1 < s → Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖`. Introduce `s hs`. Rewrite using `[norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`.

Establish `hK` using `summable_logFactor K hs`. Establish `hF` using `summable_logFactor F hs`. Establish `h1` using `tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf`. Establish `h2` using `hF.comp_injective hf`. Establish `e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) = fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s`.

Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, hN]`. Rewrite `h1`, `h2` using `[e]`. Rewrite `h1` using `[h2.tsum_prod]`. Simplify using `only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, tsum_mul_left, Nat.cast_ofNat] at h1`.

Establish `h3` using `hK.sum_add_tsum_compl (s := hS.toFinset)`. Rewrite `h3` using `[hS.coe_toFinset]`. Establish `h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c` using `Finset.sum_le_sum fun v _ => logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le`. Establish `h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s = ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `tK` using `(tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm`. Establish `tF` using `(tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm`. Establish `t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0)`. Establish `: Continuous fun s : ℝ => ‖(s : ℂ) - 1‖` using `by fun_prop`. Simplify using `using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`.

Establish `hle` using `le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by filter_upwards [self_mem_nhdsWithin] with s hs`. Use `mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)` as an intermediate fact. Simplify using `only [norm_mul]`. Use the proof step `nlinarith)`. Establish `hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖` using `norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)`.

Establish `: 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_injective_double_primes :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  intro K F _ _ _ _ S hS f hf hN
  set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc
  have key : ∀ s : ℝ, 1 < s →
      Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖ := by
    intro s hs
    rw [norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hK := summable_logFactor K hs
    have hF := summable_logFactor F hs
    have h1 := tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf
    have h2 := hF.comp_injective hf
    have e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) =
        fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s := by
      funext x
      simp only [Function.comp_apply, hN]
    rw [e] at h1 h2
    rw [h2.tsum_prod] at h1
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      tsum_mul_left, Nat.cast_ofNat] at h1
    have h3 := hK.sum_add_tsum_compl (s := hS.toFinset)
    rw [hS.coe_toFinset] at h3
    have h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c :=
      Finset.sum_le_sum fun v _ =>
        logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le
    have h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s =
      ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s := rfl
    linarith
  have tK := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have tF := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hle := le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)
    simp only [norm_mul]
    nlinarith)
  have hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖ :=
    norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  have : 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2 := by positivity
  linarith

end GlobalTheory.Mem.ZetaPole
