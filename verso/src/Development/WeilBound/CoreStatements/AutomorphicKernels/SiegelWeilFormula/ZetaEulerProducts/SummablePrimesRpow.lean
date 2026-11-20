import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

/- English proof (translation)
Use `set X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1 with hX`. Establish `h0 : X ⊥ = 0` using `by simp [hX]`. Establish `h1 : ∀ I, I ≠ ⊥ → X I = 1` using `fun I hI => by simp only [hX, if_neg hI]`. Establish `hmul : ∀ I J, X (I * J) = X I * X J`. Introduce `I J`.

Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Rewrite using `[Ideal.bot_mul, h0, zero_mul]`. Distinguish the cases in `hJ : J = ⊥`. Substitute `hJ` using the available equality.

Rewrite using `[Ideal.mul_bot, h0, mul_zero]`. Rewrite using `[h1 I hI, h1 J hJ, h1 _ (fun h => (Ideal.mul_eq_bot.1 h).elim hI hJ), one_mul]`. Establish `hle : ∀ I, ‖X I‖ ≤ 1`. Introduce `I`. Distinguish the cases in `hI : I = ⊥`.

Substitute `hI` using the available equality. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[h1 I hI]`. Simplify using the standard rewrite rules.

Establish `h` using `GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X h0 (h1 _ top_ne_bot) hmul hle s hs`. Establish `hs0 : -s ≠ 0`. Introduce and unpack `h0`. Rewrite `h0` using `[neg_eq_zero]`. Substitute `h0` using the available equality.

Evaluate the numerical expressions using `at hs`. Establish `e1 : ∀ I : Ideal (𝓞 K), X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)`. Introduce `I`. Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality.

Rewrite using `[h0, zero_mul, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow hs0]`. Rewrite using `[h1 I hI, one_mul]`. Establish `e2 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1` using `fun P => h1 _ P.ne_bot`. Simplify using `only [e1, e2] at h`. Rewrite using `[GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs, h]`.
-/
theorem dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  classical
  set X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1 with hX
  have h0 : X ⊥ = 0 := by simp [hX]
  have h1 : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => by simp only [hX, if_neg hI]
  have hmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · subst hI
      rw [Ideal.bot_mul, h0, zero_mul]
    by_cases hJ : J = ⊥
    · subst hJ
      rw [Ideal.mul_bot, h0, mul_zero]
    rw [h1 I hI, h1 J hJ, h1 _ (fun h => (Ideal.mul_eq_bot.1 h).elim hI hJ), one_mul]
  have hle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]; simp
    · rw [h1 I hI]; simp
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X h0 (h1 _ top_ne_bot) hmul hle s hs
  have hs0 : -s ≠ 0 := by
    rintro h0
    rw [neg_eq_zero] at h0
    subst h0
    norm_num at hs
  have e1 : ∀ I : Ideal (𝓞 K), X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) =
      ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0, zero_mul, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow hs0]
    · rw [h1 I hI, one_mul]
  have e2 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => h1 _ P.ne_bot
  simp only [e1, e2] at h
  rw [GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs, h]

/- English proof (translation)
Establish `h0 : Ideal.absNorm P.asIdeal ≠ 0` using `fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `h1 : Ideal.absNorm P.asIdeal ≠ 1` using `fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_absNorm' (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h =>
    P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/- English proof (translation)
Establish `h` using `GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)`. Establish `hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal` using `fun P Q hPQ => HeightOneSpectrum.ext hPQ`. Use `(h.comp_injective hinj).congr fun P => ?_` and prove the remaining obligations. Establish `hpos : 0 < Ideal.absNorm P.asIdeal` using `by have := two_le_absNorm' K P; omega`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[Complex.norm_natCast_cpow_of_pos hpos]`. Simplify using the standard rewrite rules.
-/
theorem summable_primes_rpow (K : Type) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have h := GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
  have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
    fun P Q hPQ => HeightOneSpectrum.ext hPQ
  refine (h.comp_injective hinj).congr fun P => ?_
  have hpos : 0 < Ideal.absNorm P.asIdeal := by have := two_le_absNorm' K P; omega
  simp only [Function.comp_apply]
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  simp

/- English proof (translation)
Establish `hE` using `((GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K)) (fun P => Ideal.absNorm P.asIdeal) (fun _ => 1) (two_le_absNorm' K) (fun _ => by simp) (summable_primes_rpow K)).1 s hs).2`. Rewrite `hE` using `[← dedekindZeta_eq_exp K hs, ← GroundTheory.Global.continuedDedekindZeta_eq K hs]`. Establish `hne : GroundTheory.Global.continuedDedekindZeta K s ≠ 0`. Rewrite using `[GroundTheory.Global.continuedDedekindZeta_eq K hs, dedekindZeta_eq_exp K hs]`. Conclude with `Complex.exp_ne_zero _`.

Use `⟨?_, hne⟩` and prove the remaining obligations. Use `hE.inv₀ hne` as an intermediate fact. Simplify using `using this`.
-/
theorem zeta_euler (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
        (GroundTheory.Global.continuedDedekindZeta K s)⁻¹ ∧
      GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
  have hE := ((GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun _ => 1) (two_le_absNorm' K) (fun _ => by simp)
    (summable_primes_rpow K)).1 s hs).2
  rw [← dedekindZeta_eq_exp K hs, ← GroundTheory.Global.continuedDedekindZeta_eq K hs] at hE
  have hne : GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
    rw [GroundTheory.Global.continuedDedekindZeta_eq K hs, dedekindZeta_eq_exp K hs]
    exact Complex.exp_ne_zero _
  refine ⟨?_, hne⟩
  have := hE.inv₀ hne
  simpa using this

end PositivityTheory.Lord
