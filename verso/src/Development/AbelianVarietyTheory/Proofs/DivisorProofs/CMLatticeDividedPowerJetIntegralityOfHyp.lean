import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoissonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestLast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPassScaled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeTwoMulPadicValIntDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicValIntDiscrDivLeDeltaVp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzJetConj

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatValRam GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsFieldData IsIntLattice c_vp cE_vp a0 delta_vp)
open ReciprocityTheory.ChartRestriction.L1 (IsTauOf DD jT)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb)
open scoped UpperHalfPlane Classical

namespace GlobalTheory.JetIntElliptic

/- English proof (translation)
Establish `h : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹`. Establish `h1 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l])` using `by simp`. Rewrite using `[h1, norm_algebraMap', Padic.norm_p]`. Use `⟨⟨natCast_mem _ l, ?_⟩, ⟨inv_mem (natCast_mem _ l), ?_⟩⟩` and prove the remaining obligations. Establish `: (⟨(l : ℂ), natCast_mem _ l⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)` using `rfl`.

Rewrite using `[this, map_natCast, h, Real.rpow_neg_one]`. Establish `: (⟨(l : ℂ)⁻¹, inv_mem (natCast_mem _ l)⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)⁻¹` using `rfl`. Rewrite using `[this, map_inv₀, map_natCast, norm_inv, h, inv_inv, Real.rpow_one]`.
-/
theorem sz_l (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    Sz l lam (-1) (l : ℂ) ∧ Sz l lam 1 (l : ℂ)⁻¹ := by
  have h : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h1, norm_algebraMap', Padic.norm_p]
  refine ⟨⟨natCast_mem _ l, ?_⟩, ⟨inv_mem (natCast_mem _ l), ?_⟩⟩
  · have : (⟨(l : ℂ), natCast_mem _ l⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ) := rfl
    rw [this, map_natCast, h, Real.rpow_neg_one]
  · have : (⟨(l : ℂ)⁻¹, inv_mem (natCast_mem _ l)⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)⁻¹ := rfl
    rw [this, map_inv₀, map_natCast, norm_inv, h, inv_inv, Real.rpow_one]

/- English proof (translation)
Take `⟨m, hm⟩ : l ^ padicValNat l D ∣ D` from `pow_padicValNat_dvd`. Establish `h` using `sz_mul (sz_pow (sz_l l lam).1 (padicValNat l D)) (sz_nat (l := l) (lam := lam) m)`. Establish `h2 : (D : ℂ) = (l : ℂ) ^ padicValNat l D * m` using `by exact_mod_cast hm`. Rewrite `h` using `[← h2]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sz_val (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  obtain ⟨m, hm⟩ : l ^ padicValNat l D ∣ D := pow_padicValNat_dvd
  have h := sz_mul (sz_pow (sz_l l lam).1 (padicValNat l D)) (sz_nat (l := l) (lam := lam) m)
  have h2 : (D : ℂ) = (l : ℂ) ^ padicValNat l D * m := by exact_mod_cast hm
  rw [← h2] at h
  convert h using 1
  ring

/- English proof (translation)
Establish `h0 : 0 ≤ delta_vp E l` using `by unfold delta_vp; positivity`. Unfold `c_vp`. Use `split_ifs with h`. Use `⟨?_, by positivity, ⟨a0 𝔣 l, by simp⟩⟩` and prove the remaining obligations. Take `⟨v, hv, hvd⟩` from `h`.

Take `⟨-, -, l', hl', -, hm, hnd, -⟩` from `h𝔣.2.2 v hvd`. Establish `hll : l' = l`. Assume the negation of the conclusion as `hne`. Establish `hc : IsCoprime (l' : ℤ) (l : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl' hl).2 hne)`. Take `⟨a, b, hab⟩` from `hc`.

Establish `h1 : (1 : OF E) = (a : OF E) * (l' : OF E) + (b : OF E) * (l : OF E)` using `by exact_mod_cast hab.symm`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)))`. Substitute `hll` using the available equality. Establish `: delta_vp E l' = 0`. Unfold `delta_vp`.

Rewrite using `[padicValInt.eq_zero_of_not_dvd hnd]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Check the signs of the components of the expression. Conclude with `⟨le_rfl, h0, ⟨(padicValInt l (discr E) : ℚ) / (Module.finrank ℚ E : ℚ), by unfold delta_vp; push_cast; rfl⟩⟩`.
-/
theorem c_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (l : ℕ) (hl : l.Prime) :
    delta_vp E l ≤ c_vp 𝔣 l ∧ 0 ≤ c_vp 𝔣 l ∧ ∃ q : ℚ, (q : ℝ) = c_vp 𝔣 l := by
  have h0 : 0 ≤ delta_vp E l := by unfold delta_vp; positivity
  unfold c_vp
  split_ifs with h
  · refine ⟨?_, by positivity, ⟨a0 𝔣 l, by simp⟩⟩
    obtain ⟨v, hv, hvd⟩ := h
    obtain ⟨-, -, l', hl', -, hm, hnd, -⟩ := h𝔣.2.2 v hvd
    have hll : l' = l := by
      by_contra hne
      have hc : IsCoprime (l' : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl' hl).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have h1 : (1 : OF E) = (a : OF E) * (l' : OF E) + (b : OF E) * (l : OF E) := by exact_mod_cast hab.symm
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (h1 ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)))
    subst hll
    have : delta_vp E l' = 0 := by
      unfold delta_vp
      rw [padicValInt.eq_zero_of_not_dvd hnd]; simp
    rw [this]; positivity
  · exact ⟨le_rfl, h0, ⟨(padicValInt l (discr E) : ℚ) / (Module.finrank ℚ E : ℚ), by unfold delta_vp; push_cast; rfl⟩⟩

/- English proof (translation)
Establish `hc : IsCMField.complexConj E w = -w`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj, map_neg, hψ]`. Simplify using the standard rewrite rules. Use `split_ifs at hθ ⊢ with h`.

Substitute `hθ` using the available equality. Take `⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m` from `⟨(d + 1) / 4, by omega⟩`. Establish `hm' : (d : E) + 1 = 4 * m` using `by exact_mod_cast hm`. Use `⟨⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]`.

Simplify using `only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]`. Take the linear combination `(1 / 4 : E) * hw - (1 / 4 : E) * hm'`. Rewrite using `[map_div₀, map_add, map_neg, map_one, hc, map_ofNat]`. Take the linear combination `hw`. Substitute `hθ` using the available equality.

Use `⟨⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]`. Simplify using `only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]`. Take the linear combination `hw`. Rewrite using `[hc]`.

Use `push_cast`. Take the linear combination `4 * hw`.
-/
theorem theta_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (d : ℕ) (w θ : E) (hw : w ^ 2 = -(d : E))
    (hψ : ψ w = Complex.I * (Real.sqrt d : ℝ)) (hθ : θ = (if d % 4 = 3 then (-1 + w) / 2 else w)) :
    IsIntegral ℤ θ ∧ (θ - IsCMField.complexConj E θ) ^ 2 = -(((if d % 4 = 3 then d else 4 * d : ℕ) : ℕ) : E) := by
  have hc : IsCMField.complexConj E w = -w := by
    apply ψ.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hψ]
    simp
  split_ifs at hθ ⊢ with h
  · subst hθ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
    have hm' : (d : E) + 1 = 4 * m := by exact_mod_cast hm
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination (1 / 4 : E) * hw - (1 / 4 : E) * hm'
    · rw [map_div₀, map_add, map_neg, map_one, hc, map_ofNat]
      linear_combination hw
  · subst hθ
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination hw
    · rw [hc]; push_cast
      linear_combination 4 * hw

/- English proof (translation)
Take `⟨k, rfl⟩` from `hd`. Establish `hk : 0 < k` using `Nat.pos_of_mul_pos_left hN`. Use `⟨fun _ => (k : ZMod (M₀ * k)), funext fun i => ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]`. Rewrite using `[← Nat.cast_mul, ZMod.natCast_self]`.

Establish `h0 : ((k : ℕ) : ZMod (M₀ * k)) = 0` using `congrFun h 0`. Use `Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff _ _).1 h0)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tors_ex (N M₀ : ℕ) (hN : 0 < N) (h1 : 1 < M₀) (hd : M₀ ∣ N) : ∃ y : Fin 2 → ZMod N, M₀ • y = 0 ∧ y ≠ 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hN
  refine ⟨fun _ => (k : ZMod (M₀ * k)), funext fun i => ?_, fun h => ?_⟩
  · simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · have h0 : ((k : ℕ) : ZMod (M₀ * k)) = 0 := congrFun h 0
    have := Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff _ _).1 h0)
    nlinarith

/- English proof (translation)
Use `haveI := Fact.mk hl`. Use `haveI := Fact.mk hd`. Establish `h1 : padicValNat l d = if l = d then 1 else 0` using `by split_ifs with h`. Substitute `h` using the available equality. Conclude with `padicValNat_self`.

Conclude with `padicValNat_primes h`. Establish `h2 : padicValNat l 4 = if l = 2 then 2 else 0` using `by split_ifs with h`. Substitute `h` using the available equality. Conclude with `padicValNat.prime_pow 2`. Use `padicValNat.eq_zero_of_not_dvd fun hh => h ?_` and prove the remaining obligations.

Conclude with `(Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2) hh)`. Distinguish the cases in `h3 : d % 4 = 3`. Apply the tactic sequence `simp only [h3, if_true, h1, not_true, and_false, if_false] split_ifs <;> norm_num`. Simplify using `only [h3, if_false, not_false_iff, and_true]`. Rewrite using `[padicValNat.mul (by norm_num) hd.ne_zero, h1, h2]`.

Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem val_facts (l d : ℕ) (hl : l.Prime) (hd : d.Prime) (h4 : 4 < d) :
    (padicValNat l (if d % 4 = 3 then d else 4 * d) : ℝ) / 2 =
      (if l = d then 1 / 2 else 0) + (if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0) := by
  haveI := Fact.mk hl
  haveI := Fact.mk hd
  have h1 : padicValNat l d = if l = d then 1 else 0 := by
    split_ifs with h
    · subst h; exact padicValNat_self
    · exact padicValNat_primes h
  have h2 : padicValNat l 4 = if l = 2 then 2 else 0 := by
    split_ifs with h
    · subst h; exact padicValNat.prime_pow 2
    · refine padicValNat.eq_zero_of_not_dvd fun hh => h ?_
      exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2) hh)
  by_cases h3 : d % 4 = 3
  · simp only [h3, if_true, h1, not_true, and_false, if_false]
    split_ifs <;> norm_num
  · simp only [h3, if_false, not_false_iff, and_true]
    rw [padicValNat.mul (by norm_num) hd.ne_zero, h1, h2]
    split_ifs <;> norm_num

/- English proof (translation)
Establish `h1 : 2 * pi / r * γ / (Ω / lp) / (Ω / lp) = (pi / im) * (2 * im / r * γ * lp ^ 2) / Ω ^ 2` using `by field_simp`. Establish `h2 : ∀ x : ℂ, x / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) = x / Ω ^ (t * f + 2 * K)` using `fun x => by`. Rewrite using `[div_div, ← mul_pow]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h1, h2, ← pow_mul, div_pow, div_pow Ω, mul_pow (pi / im), mul_pow n, pow_add, pow_mul Ω 2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fin_id (jt Ω p n lp γ pi im r : ℂ) (t f K : ℕ) (hΩ : Ω ≠ 0) (hp : p ≠ 0) (hlp : lp ≠ 0) (hpi : pi ≠ 0) (him : im ≠ 0)
    (hr : r ≠ 0) :
    n ^ (t * f) * jt * ((2 * pi / r * γ / (Ω / lp) / (Ω / lp)) ^ K / ((Ω / lp) ^ t) ^ f) =
      jt * (pi / im) ^ K / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) * (n * lp) ^ (t * f) *
        (2 * im / r * γ * lp ^ 2) ^ K := by
  have h1 : 2 * pi / r * γ / (Ω / lp) / (Ω / lp) = (pi / im) * (2 * im / r * γ * lp ^ 2) / Ω ^ 2 := by field_simp
  have h2 : ∀ x : ℂ, x / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) = x / Ω ^ (t * f + 2 * K) := fun x => by
    rw [div_div, ← mul_pow]; congr 2; field_simp
  rw [h1, h2, ← pow_mul, div_pow, div_pow Ω, mul_pow (pi / im), mul_pow n, pow_add, pow_mul Ω 2]
  field_simp

/- English proof (translation)
Introduce `hEis E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ`. Take `⟨w, θ, τ, hw, hφw, hθ, hφθ, htau, him⟩` from `GlobalTheory.QuadGenerator.exists_generator E I d φ Λ hF hΛ`. Establish `hδ2` using `GlobalTheory.RootDiscrExp.half_le_delta_two_vp E I d φ hF`. Take `⟨hd, h4, hUn, -, -, hI2, hCM, -⟩` from `hF`. Establish `hcard` using `card_eq_finrank hCM`.

Establish `hf2 : 2 ≤ Module.finrank ℚ (FR E)` using `hcard ▸ hI2`. Take `⟨i₀⟩ : Nonempty I` from `Fintype.card_pos_iff.1 (by omega)`. Take `⟨hint, hsq⟩` from `theta_facts (φ i₀) d w θ hw (hφw i₀) hθ`. Establish `hvD` using `val_facts l d hl hd h4`. Use `set D : ℕ := if d % 4 = 3 then d else 4 * d with hDdef`.

Apply the tactic sequence `have hD0 : 0 < D := by rw [hDdef]; split_ifs <;> omega`. Take `⟨M₀, hM₀1, hM₀⟩ : ∃ M₀ : ℕ, 1 < M₀ ∧ ¬ l ∣ M₀` from `⟨l + 1, by have := hl.pos; omega, fun h => hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right dvd_rfl).1 h))⟩`. Take `⟨M, M', L, hM, hM', hMM, hL, hLm, hLs, hNs⟩` from `GlobalTheory.RoadE.passl E l lam 𝔣 Q y θ D M₀ h𝔣 hQl hy hD0 hint hsq hM₀`. Establish `hMpos : 0 < M` using `Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)`. Establish `hM'pos : 0 < M'` using `Nat.pos_of_ne_zero fun h => hM' (h ▸ dvd_zero l)`.

Establish `hNpos : 0 < M' * l ^ (padicValNat l D + a0 𝔣 l)` using `Nat.mul_pos hM'pos (pow_pos hl.pos _)`. Use `haveI : NeZero (M' * l ^ (padicValNat l D + a0 𝔣 l)) := ⟨hNpos.ne'⟩`. Take `⟨t, ht, ht0⟩` from `tors_ex _ M₀ hNpos hM₀1 (hMM.mul_right _)`. Take `⟨hδc, hc0, q, hq⟩` from `c_facts 𝔣 h𝔣 l hl`. Establish `hdF` using `(GlobalTheory.DiscrTower.padicValInt_discr_div_le_delta_vp E l hl).trans hδc`.

Take `⟨γ, hγ0, hγ, hγ'⟩` from `GlobalTheory.QFam.exists_sz_scale l lam (q + if l = d then 1 / 2 else 0)`. Establish `hqh : ((q + if l = d then 1 / 2 else 0 : ℚ) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0`. Apply the tactic sequence `rw [← hq]; split_ifs <;> push_cast <;> ring`. Rewrite `hγ`, `hγ'` using `[hqh]`. Establish `hΩ0 : Ω ≠ 0`.

Introduce and unpack `rfl`. Conclude with `latDisc_ne_zero Λ (by rw [← hΩ]; simp)`. Establish `hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd.pos)`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `him0 : ((τ.im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast τ.im_pos.ne'`. Establish `hlp : (l : ℂ) ^ a0 𝔣 l ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hl.ne_zero)`. Establish `hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero`. Use `⟨fun _ => Ω / (l : ℂ) ^ a0 𝔣 l, fun _ => 2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l), fun i => ?_, fun g κ u hg hu => ?_⟩` and prove the remaining obligations.

Use `⟨div_ne_zero hΩ0 hlp, div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hpi) hsd) hγ0) (div_ne_zero hΩ0 hlp), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Ω / (l : ℂ) ^ a0 𝔣 l / Ω = ((l : ℂ)⁻¹) ^ a0 𝔣 l` using `by rw [inv_pow]; field_simp`. Rewrite using `[h1]`. Simplify using `using sz_pow (sz_l l lam).2 (a0 𝔣 l)`. Establish `h1 : Ω / (l : ℂ) ^ a0 𝔣 l * (2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l)) * (Real.sqrt d : ℝ) / (2 * Real.pi) = γ` using `by field_simp beta_reduce`.

Rewrite using `[h1]`. Conclude with `hγ'`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_equiv_cmType_realEmbeddings E I φ hCM`. Establish `hD` using `GlobalTheory.HilbFam.iterD_defSum_eq_jet hEis E I φ e θ τ _ L (M * D) s _ g κ u hf2 hs hNpos hL he hφθ (Nat.mul_pos hMpos hD0) hLm hg hu`. Take `⟨hω, hj, hst⟩` from `GlobalTheory.SzTau.main l lam d Λ 1 Ω τ hd h4 hΛ htau hΩ`.

Use `haveI : IsGalois ℚ (FR E) := (IsAbelianGalois.tower_bot ℚ (FR E) E).toIsGalois`. Establish `hfpos : (0 : ℝ) < Module.finrank ℚ (FR E)` using `by exact_mod_cast (by omega : 0 < Module.finrank ℚ (FR E))`. Establish `ha0 : (0 : ℝ) ≤ a0 𝔣 l` using `Nat.cast_nonneg _`. Establish `hv0 : (0 : ℝ) ≤ padicValNat l D` using `Nat.cast_nonneg _`. Establish `hJ` using `hjsz hEis (FR E) hf2 s _ L hs hL z hz l lam (fun j => κ (e.symm j)) t M' M₀ (padicValNat l D + a0 𝔣 l) (cE_vp l z) (-(padicValNat l D : ℝ) / 2) (2 * c_vp 𝔣 l + 2 * a0 𝔣 l + (padicValNat l D : ℝ) / 2) (Nat.cast_nonneg _) (fun C => by`.

Establish `h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z` using `Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat) (Finset.mem_univ C)`. Establish `h2` using `(Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))).trans (Int.ofNat_le.2 h1)`. Conclude with `h2)` after adjusting the coercions. Use the proof step `hM' hL.1 hLs hNs (by push_cast; linarith) (by positivity) hM₀ ht ht0 τ _ hj hω`. Use the proof step `(div_ne_zero (by simpa using hΩ0) hp)`.

Use the proof step `(sz_mono (hst _ M₀ t hM₀ ht ht0) (by`. Rewrite using `[hvD]`. Distinguish the cases in `h2 : l = 2`. Establish `hc2 : (1 / 2 : ℝ) ≤ c_vp 𝔣 l` using `by subst h2; exact hδ2.trans hδc`. Establish `hld : ¬ l = d` using `by omega`.

Simplify using `only [h2, if_true, true_and] at hld ⊢`. Rewrite using `[← h2]`. Apply the tactic sequence `split_ifs <;> linarith`. Apply the tactic sequence `simp only [h2, if_false, false_and] split_ifs <;> linarith))`. Establish `hsum : ∑ j, κ (e.symm j) = ∑ i, κ i` using `Equiv.sum_comp e.symm κ`.

Establish `hr : Sz l lam (-(if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0)) (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ)`. Break down `him with ⟨h3, h⟩ | ⟨h3, h⟩` into its components or cases. Establish `: (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = 1` using `by rw [h]; push_cast; field_simp`. Rewrite using `[this]`. Simplify `sz_one (l := l) (lam := lam)` using `[h3]`.

Establish `: (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = ((2 : ℕ) : ℂ)` using `by rw [h]; push_cast; field_simp`. Rewrite using `[this]`. Use `split_ifs with h5`. Take `⟨rfl, -⟩` from `h5`. Conclude with `(sz_l 2 lam).1`.

Simplify using `using sz_nat (l := l) (lam := lam) 2`. Establish `hn : Sz l lam (0 + -(padicValNat l D : ℝ)) ((M * D : ℕ) : ℂ)`. Rewrite using `[Nat.cast_mul]`. Conclude with `sz_mul (sz_nat M) (sz_val l lam D)`. Establish `hlps` using `sz_pow (sz_l l lam).1 (a0 𝔣 l)`.

Establish `hall` using `sz_mul (sz_mul hJ (sz_pow (sz_mul hn hlps) (2 * s * Module.finrank ℚ (FR E)))) (sz_pow (sz_mul (sz_mul hr hγ) (sz_pow hlps 2)) (∑ i, κ i))`. Use `beta_reduce`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, hcard]`. Establish `hD' : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 = _` using `hD`. Rewrite using `[hD', fin_id _ Ω (2 * Real.pi * Complex.I) _ _ γ _ (τ.im : ℝ) _ (2 * s) _ _ hΩ0 hp hlp hpi him0 hsd]`.

Rewrite `hall` using `[wt, hsum, Complex.ofReal_div]`. Use `sz_mono hall ?_` and prove the remaining obligations. Establish `hdF' : (padicValInt l (discr (FR E)) : ℝ) ≤ c_vp 𝔣 l * Module.finrank ℚ (FR E)` using `(div_le_iff₀ hfpos).1 hdF`. Establish `hs0 : (0 : ℝ) ≤ s` using `Nat.cast_nonneg _`. Establish `h6` using `mul_le_mul_of_nonneg_left hdF' hs0`.

Establish `h7 : 0 ≤ (s : ℝ) * (c_vp 𝔣 l * Module.finrank ℚ (FR E))` using `by positivity`. Establish `h8 : (if l = 2 ∧ ¬ d % 4 = 3 then (1 : ℝ) else 0) = (padicValNat l D : ℝ) / 2 - (if l = d then 1 / 2 else 0)`. Rewrite using `[hvD]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h8]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem core (hjsz : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ)) : EisExp → JetInt := by
  intro hEis E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  obtain ⟨w, θ, τ, hw, hφw, hθ, hφθ, htau, him⟩ := GlobalTheory.QuadGenerator.exists_generator E I d φ Λ hF hΛ
  have hδ2 := GlobalTheory.RootDiscrExp.half_le_delta_two_vp E I d φ hF
  obtain ⟨hd, h4, hUn, -, -, hI2, hCM, -⟩ := hF
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (FR E) := hcard ▸ hI2
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨hint, hsq⟩ := theta_facts (φ i₀) d w θ hw (hφw i₀) hθ
  have hvD := val_facts l d hl hd h4
  set D : ℕ := if d % 4 = 3 then d else 4 * d with hDdef
  have hD0 : 0 < D := by rw [hDdef]; split_ifs <;> omega
  obtain ⟨M₀, hM₀1, hM₀⟩ : ∃ M₀ : ℕ, 1 < M₀ ∧ ¬ l ∣ M₀ :=
    ⟨l + 1, by have := hl.pos; omega, fun h => hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right dvd_rfl).1 h))⟩
  obtain ⟨M, M', L, hM, hM', hMM, hL, hLm, hLs, hNs⟩ :=
    GlobalTheory.RoadE.passl E l lam 𝔣 Q y θ D M₀ h𝔣 hQl hy hD0 hint hsq hM₀
  have hMpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hM'pos : 0 < M' := Nat.pos_of_ne_zero fun h => hM' (h ▸ dvd_zero l)
  have hNpos : 0 < M' * l ^ (padicValNat l D + a0 𝔣 l) := Nat.mul_pos hM'pos (pow_pos hl.pos _)
  haveI : NeZero (M' * l ^ (padicValNat l D + a0 𝔣 l)) := ⟨hNpos.ne'⟩
  obtain ⟨t, ht, ht0⟩ := tors_ex _ M₀ hNpos hM₀1 (hMM.mul_right _)
  obtain ⟨hδc, hc0, q, hq⟩ := c_facts 𝔣 h𝔣 l hl
  have hdF := (GlobalTheory.DiscrTower.padicValInt_discr_div_le_delta_vp E l hl).trans hδc
  obtain ⟨γ, hγ0, hγ, hγ'⟩ := GlobalTheory.QFam.exists_sz_scale l lam (q + if l = d then 1 / 2 else 0)
  have hqh : ((q + if l = d then 1 / 2 else 0 : ℚ) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
    rw [← hq]; split_ifs <;> push_cast <;> ring
  rw [hqh] at hγ hγ'
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him0 : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hlp : (l : ℂ) ^ a0 𝔣 l ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  refine ⟨fun _ => Ω / (l : ℂ) ^ a0 𝔣 l, fun _ => 2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l), fun i => ?_,
    fun g κ u hg hu => ?_⟩
  · refine ⟨div_ne_zero hΩ0 hlp, div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hpi) hsd) hγ0)
      (div_ne_zero hΩ0 hlp), ?_, ?_⟩
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l / Ω = ((l : ℂ)⁻¹) ^ a0 𝔣 l := by rw [inv_pow]; field_simp
      rw [h1]
      simpa using sz_pow (sz_l l lam).2 (a0 𝔣 l)
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l * (2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l)) * (Real.sqrt d : ℝ) /
          (2 * Real.pi) = γ := by field_simp
      beta_reduce
      rw [h1]
      exact hγ'
  · obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings E I φ hCM
    have hD := GlobalTheory.HilbFam.iterD_defSum_eq_jet hEis E I φ e θ τ _ L (M * D) s _ g κ u hf2 hs hNpos hL he hφθ
      (Nat.mul_pos hMpos hD0) hLm hg hu
    obtain ⟨hω, hj, hst⟩ := GlobalTheory.SzTau.main l lam d Λ 1 Ω τ hd h4 hΛ htau hΩ
    haveI : IsGalois ℚ (FR E) := (IsAbelianGalois.tower_bot ℚ (FR E) E).toIsGalois
    have hfpos : (0 : ℝ) < Module.finrank ℚ (FR E) := by exact_mod_cast (by omega : 0 < Module.finrank ℚ (FR E))
    have ha0 : (0 : ℝ) ≤ a0 𝔣 l := Nat.cast_nonneg _
    have hv0 : (0 : ℝ) ≤ padicValNat l D := Nat.cast_nonneg _
    have hJ := hjsz hEis (FR E) hf2 s _ L hs hL z hz l lam (fun j => κ (e.symm j)) t M' M₀ (padicValNat l D + a0 𝔣 l)
      (cE_vp l z) (-(padicValNat l D : ℝ) / 2) (2 * c_vp 𝔣 l + 2 * a0 𝔣 l + (padicValNat l D : ℝ) / 2) (Nat.cast_nonneg _)
      (fun C => by
        have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
          Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
            (Finset.mem_univ C)
        have h2 := (Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))).trans
          (Int.ofNat_le.2 h1)
        exact_mod_cast h2)
      hM' hL.1 hLs hNs (by push_cast; linarith) (by positivity) hM₀ ht ht0 τ _ hj hω
      (div_ne_zero (by simpa using hΩ0) hp)
      (sz_mono (hst _ M₀ t hM₀ ht ht0) (by
        rw [hvD]
        by_cases h2 : l = 2
        · have hc2 : (1 / 2 : ℝ) ≤ c_vp 𝔣 l := by subst h2; exact hδ2.trans hδc
          have hld : ¬ l = d := by omega
          simp only [h2, if_true, true_and] at hld ⊢
          rw [← h2]
          split_ifs <;> linarith
        · simp only [h2, if_false, false_and]
          split_ifs <;> linarith))
    have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
    have hr : Sz l lam (-(if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0)) (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) := by
      rcases him with ⟨h3, h⟩ | ⟨h3, h⟩
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = 1 := by rw [h]; push_cast; field_simp
        rw [this]; simpa [h3] using sz_one (l := l) (lam := lam)
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by rw [h]; push_cast; field_simp
        rw [this]
        split_ifs with h5
        · obtain ⟨rfl, -⟩ := h5; exact (sz_l 2 lam).1
        · simpa using sz_nat (l := l) (lam := lam) 2
    have hn : Sz l lam (0 + -(padicValNat l D : ℝ)) ((M * D : ℕ) : ℂ) := by
      rw [Nat.cast_mul]; exact sz_mul (sz_nat M) (sz_val l lam D)
    have hlps := sz_pow (sz_l l lam).1 (a0 𝔣 l)
    have hall := sz_mul (sz_mul hJ (sz_pow (sz_mul hn hlps) (2 * s * Module.finrank ℚ (FR E))))
      (sz_pow (sz_mul (sz_mul hr hγ) (sz_pow hlps 2)) (∑ i, κ i))
    beta_reduce
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, hcard]
    have hD' : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 = _ := hD
    rw [hD', fin_id _ Ω (2 * Real.pi * Complex.I) _ _ γ _ (τ.im : ℝ) _ (2 * s) _ _ hΩ0 hp hlp hpi him0 hsd]
    rw [wt, hsum, Complex.ofReal_div] at hall
    refine sz_mono hall ?_
    have hdF' : (padicValInt l (discr (FR E)) : ℝ) ≤ c_vp 𝔣 l * Module.finrank ℚ (FR E) := (div_le_iff₀ hfpos).1 hdF
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have h6 := mul_le_mul_of_nonneg_left hdF' hs0
    have h7 : 0 ≤ (s : ℝ) * (c_vp 𝔣 l * Module.finrank ℚ (FR E)) := by positivity
    have h8 : (if l = 2 ∧ ¬ d % 4 = 3 then (1 : ℝ) else 0) = (padicValNat l D : ℝ) / 2 - (if l = d then 1 / 2 else 0) := by
      rw [hvD]; ring
    rw [h8]
    push_cast
    nlinarith

/- English proof (translation)
Introduce `_ hPZ _ _` and use `core GlobalTheory.HilbFam.sz_jet_conj (GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ) hPZ)`.
-/
theorem jetInt : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := fun _ hPZ _ _ =>
  core GlobalTheory.HilbFam.sz_jet_conj (GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ) hPZ)

end GlobalTheory.JetIntElliptic
