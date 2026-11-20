import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LimitPowMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LatticeDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.FormsAR

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Break down `Nat.eq_zero_or_pos M with rfl | hM` into its components or cases. Conclude with `⟨0, by simp⟩`. Establish `hx' : x ∈ (b ^ M ⊔ c ^ M).radical`. Rewrite using `[Ideal.radical_sup, Ideal.radical_pow _ hM.ne', Ideal.radical_pow _ hM.ne', ← Ideal.radical_sup]`. Conclude with `hx`.

Conclude with `hx'`.
-/
private theorem UpperTheory.V.AlgebraTools.Conn.core_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K, x ^ K ∈ b ^ M ⊔ c ^ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, by simp⟩
  · have hx' : x ∈ (b ^ M ⊔ c ^ M).radical := by
      rw [Ideal.radical_sup, Ideal.radical_pow _ hM.ne', Ideal.radical_pow _ hM.ne',
        ← Ideal.radical_sup]
      exact hx
    exact hx'

/- English proof (translation)
Use `haveI := hP`. Establish `hmem : ∀ n : ℕ, algebraMap R (Localization.AtPrime P) r ∈ (maximalIdeal (Localization.AtPrime P)) ^ n`. Introduce `n`. Take `⟨K, hK⟩` from `h n`. Establish `h1 : algebraMap R (Localization.AtPrime P) (y ^ K * r) ∈ (maximalIdeal (Localization.AtPrime P)) ^ n`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hK`. Establish `hu : IsUnit (algebraMap R (Localization.AtPrime P) (y ^ K))` using `IsLocalization.map_units (Localization.AtPrime P) (⟨y ^ K, P.primeCompl.pow_mem hy K⟩ : P.primeCompl)`. Rewrite `h1` using `[map_mul]`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).mp h1`.

Establish `h0 : algebraMap R (Localization.AtPrime P) r = 0`. Establish `hb` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime P)) (maximalIdeal.isMaximal _).ne_top`. Rewrite using `[← Ideal.mem_bot, ← hb, Ideal.mem_iInf]`. Conclude with `hmem`. Conclude with `IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P) (h0.trans (map_zero _).symm)`.
-/
private theorem UpperTheory.V.AlgebraTools.Conn.core_krull {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (P : Ideal R) (hP : P.IsPrime) (y r : R) (hy : y ∉ P)
    (h : ∀ n : ℕ, ∃ K : ℕ, y ^ K * r ∈ P ^ n) : r = 0 := by
  haveI := hP
  have hmem : ∀ n : ℕ, algebraMap R (Localization.AtPrime P) r ∈
      (maximalIdeal (Localization.AtPrime P)) ^ n := by
    intro n
    obtain ⟨K, hK⟩ := h n
    have h1 : algebraMap R (Localization.AtPrime P) (y ^ K * r) ∈
        (maximalIdeal (Localization.AtPrime P)) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hK
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) (y ^ K)) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨y ^ K, P.primeCompl.pow_mem hy K⟩ : P.primeCompl)
    rw [map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have h0 : algebraMap R (Localization.AtPrime P) r = 0 := by
    have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime P))
      (maximalIdeal.isMaximal _).ne_top
    rw [← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
    exact hmem
  exact IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    (h0.trans (map_zero _).symm)

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `A R _ _ _ _ _ _ _ _ I _ J u v b c P Q y z hJ hJI hreg hIJ hbc hu hv hP hQ hbP hcQ hIP hIQ hy hz hyP hzQ`. Use `haveI : IsNoetherianRing R := IsNoetherianRing.of_finite A R`. Take `⟨a, ha⟩` from `UpperTheory.V.AlgebraTools.Conn.limit (R := R) I J u v b c hJ hJI hreg hIJ hbc (IsNoetherian.noetherian b) (IsNoetherian.noetherian c) hu hv`. Take `⟨d, r, hd, hr⟩` from `UpperTheory.V.AlgebraTools.Conn.bidual (M := R) a`. Take `⟨k, hk⟩` from `UpperTheory.V.AlgebraTools.Conn.formsAR (M := R) I`.

Establish `key : ∀ w : A, algebraMap A R w ∈ (b ⊔ c).radical → ∀ n : ℕ, ∃ N, n ≤ N ∧ ∃ K : ℕ, ∃ β ∈ b ^ N, ∃ γ ∈ c ^ N, β + γ = (algebraMap A R w) ^ K ∧ algebraMap A R d * β - (algebraMap A R w) ^ K * r ∈ (I.map (algebraMap A R)) ^ n`. Introduce `w hw n`. Take `⟨N, hnN, hN⟩` from `ha (n + k)`. Take `⟨K, hK⟩` from `core_pow_mem b c _ hw N`. Take `⟨β, hβ, γ, hγ, hβγ⟩` from `Submodule.mem_sup.mp hK`.

Use `⟨N, le_trans (Nat.le_add_right n k) hnN, K, β, hβ, γ, hγ, hβγ, ?_⟩` and prove the remaining obligations. Establish `hforms : ∀ l : Module.Dual A R, l (d • β - w ^ K • r) ∈ I ^ (n + k)`. Introduce `l`. Establish `h1` using `hN (w ^ K) β γ hβ hγ (by rw [map_pow, hβγ]) l`. Establish `h2 : l (d • β - w ^ K • r) = d * (l β - w ^ K * a l)`.

Rewrite using `[map_sub, map_smul, map_smul, hr, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ _ h1`. Establish `h4 : d • β - w ^ K • r ∈ Ideal.map (algebraMap A R) (I ^ n)`.

Establish `h3` using `hk n _ hforms`. Rewrite `h3` using `[Ideal.smul_top_eq_map]`. Conclude with `h3`. Rewrite using `[← Ideal.map_pow]`. Simplify `h4` using `[Algebra.smul_def]`.

Establish `hr0 : r = 0`. Use `core_krull P hP (algebraMap A R y) r hyP fun n => ?_` and prove the remaining obligations. Take `⟨N, hnN, K, β, hβ, γ, hγ, -, hdiff⟩` from `key y hy n`. Use `⟨K, ?_⟩` and prove the remaining obligations. Establish `hβP : β ∈ P ^ n` using `Ideal.pow_right_mono hbP n (Ideal.pow_le_pow_right hnN hβ)`.

Establish `hd' : algebraMap A R d * β - (algebraMap A R y) ^ K * r ∈ P ^ n` using `Ideal.pow_right_mono hIP n hdiff`. Establish `he : (algebraMap A R y) ^ K * r = algebraMap A R d * β - (algebraMap A R d * β - (algebraMap A R y) ^ K * r)` using `by ring`. Rewrite using `[he]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hβP) hd'`. Establish `hdr : algebraMap A R d - r = 0`.

Use `core_krull Q hQ (algebraMap A R z) _ hzQ fun n => ?_` and prove the remaining obligations. Take `⟨N, hnN, K, β, hβ, γ, hγ, hβγ, hdiff⟩` from `key z hz n`. Use `⟨K, ?_⟩` and prove the remaining obligations. Establish `hγQ : γ ∈ Q ^ n` using `Ideal.pow_right_mono hcQ n (Ideal.pow_le_pow_right hnN hγ)`. Establish `hd' : algebraMap A R d * β - (algebraMap A R z) ^ K * r ∈ Q ^ n` using `Ideal.pow_right_mono hIQ n hdiff`.

Establish `he : (algebraMap A R z) ^ K * (algebraMap A R d - r) = (algebraMap A R d * β - (algebraMap A R z) ^ K * r) + algebraMap A R d * γ`. Rewrite using `[← hβγ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `Ideal.add_mem _ hd' (Ideal.mul_mem_left _ _ hγQ)`.

Rewrite `hdr` using `[hr0, sub_zero]`. Conclude with `hd (FaithfulSMul.algebraMap_injective A R (hdr.trans (map_zero _).symm))`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.core :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
      [FaithfulSMul A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c P Q : Ideal R) (y z : A),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) → (∀ m, ∃ N, I ^ N ≤ J m) →
      b * c ≤ (I.map (algebraMap A R)).radical →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      P.IsPrime → Q.IsPrime → b ≤ P → c ≤ Q → I.map (algebraMap A R) ≤ P → I.map (algebraMap A R) ≤ Q →
      algebraMap A R y ∈ (b ⊔ c).radical → algebraMap A R z ∈ (b ⊔ c).radical →
      algebraMap A R y ∉ P → algebraMap A R z ∉ Q → False := by
  intro A R _ _ _ _ _ _ _ _ I _ J u v b c P Q y z hJ hJI hreg hIJ hbc hu hv hP hQ hbP hcQ hIP hIQ
    hy hz hyP hzQ
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  obtain ⟨a, ha⟩ := UpperTheory.V.AlgebraTools.Conn.limit (R := R) I J u v b c hJ hJI hreg hIJ hbc
    (IsNoetherian.noetherian b) (IsNoetherian.noetherian c) hu hv
  obtain ⟨d, r, hd, hr⟩ := UpperTheory.V.AlgebraTools.Conn.bidual (M := R) a
  obtain ⟨k, hk⟩ := UpperTheory.V.AlgebraTools.Conn.formsAR (M := R) I
  have key : ∀ w : A, algebraMap A R w ∈ (b ⊔ c).radical → ∀ n : ℕ, ∃ N, n ≤ N ∧ ∃ K : ℕ,
      ∃ β ∈ b ^ N, ∃ γ ∈ c ^ N, β + γ = (algebraMap A R w) ^ K ∧
      algebraMap A R d * β - (algebraMap A R w) ^ K * r ∈ (I.map (algebraMap A R)) ^ n := by
    intro w hw n
    obtain ⟨N, hnN, hN⟩ := ha (n + k)
    obtain ⟨K, hK⟩ := core_pow_mem b c _ hw N
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hK
    refine ⟨N, le_trans (Nat.le_add_right n k) hnN, K, β, hβ, γ, hγ, hβγ, ?_⟩
    have hforms : ∀ l : Module.Dual A R, l (d • β - w ^ K • r) ∈ I ^ (n + k) := by
      intro l
      have h1 := hN (w ^ K) β γ hβ hγ (by rw [map_pow, hβγ]) l
      have h2 : l (d • β - w ^ K • r) = d * (l β - w ^ K * a l) := by
        rw [map_sub, map_smul, map_smul, hr, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ h1
    have h4 : d • β - w ^ K • r ∈ Ideal.map (algebraMap A R) (I ^ n) := by
      have h3 := hk n _ hforms
      rw [Ideal.smul_top_eq_map] at h3
      exact h3
    rw [← Ideal.map_pow]
    simpa [Algebra.smul_def] using h4
  have hr0 : r = 0 := by
    refine core_krull P hP (algebraMap A R y) r hyP fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, -, hdiff⟩ := key y hy n
    refine ⟨K, ?_⟩
    have hβP : β ∈ P ^ n := Ideal.pow_right_mono hbP n (Ideal.pow_le_pow_right hnN hβ)
    have hd' : algebraMap A R d * β - (algebraMap A R y) ^ K * r ∈ P ^ n :=
      Ideal.pow_right_mono hIP n hdiff
    have he : (algebraMap A R y) ^ K * r =
        algebraMap A R d * β - (algebraMap A R d * β - (algebraMap A R y) ^ K * r) := by ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hβP) hd'
  have hdr : algebraMap A R d - r = 0 := by
    refine core_krull Q hQ (algebraMap A R z) _ hzQ fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, hβγ, hdiff⟩ := key z hz n
    refine ⟨K, ?_⟩
    have hγQ : γ ∈ Q ^ n := Ideal.pow_right_mono hcQ n (Ideal.pow_le_pow_right hnN hγ)
    have hd' : algebraMap A R d * β - (algebraMap A R z) ^ K * r ∈ Q ^ n :=
      Ideal.pow_right_mono hIQ n hdiff
    have he : (algebraMap A R z) ^ K * (algebraMap A R d - r) =
        (algebraMap A R d * β - (algebraMap A R z) ^ K * r) + algebraMap A R d * γ := by
      rw [← hβγ]
      ring
    rw [he]
    exact Ideal.add_mem _ hd' (Ideal.mul_mem_left _ _ hγQ)
  rw [hr0, sub_zero] at hdr
  exact hd (FaithfulSMul.algebraMap_injective A R (hdr.trans (map_zero _).symm))
