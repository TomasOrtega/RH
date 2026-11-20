import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `e`. Establish `key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) = (aeval (fun i : Fin N => C s * X i)).comp (rename e)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using the standard rewrite rules.

Use `congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key` as an intermediate fact. Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[this, hp e]`.
-/
theorem isSymmetric_aeval_smul_X {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by
  intro e
  have key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) =
      (aeval (fun i : Fin N => C s * X i)).comp (rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have := congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key
  simp only [AlgHom.comp_apply] at this
  rw [this, hp e]

/- English proof (translation)
Establish `: r + a ≤ r * a + 1` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem k_sub_one_le (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by
  have : r + a ≤ r * a + 1 := by nlinarith
  omega

end

end Top

open Top MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `f r a c hf hr ha`. Take `⟨κ, hκpm, hκ⟩` from `hasDD_schur hB r a c`. Take `⟨c0, hc0, hInt, hMain⟩` from `hA f (r + a)`. Establish `hκ0` using `kappa_ne_zero hκpm`. Establish `hra : r * a ≠ 0` using `Nat.mul_ne_zero (by omega) (by omega)`.

Establish `hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0` using `by exact_mod_cast (hRP r a).ne'`. Use `⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0), fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩` and prove the remaining obligations. Introduce `Q hQ k hk2 hkN τ τ' hττ'`. Establish `hk1` using `k_sub_one_le r a k hr ha hkN`. Use `set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef`.

Establish `hGF` using `smallPowerSum_mul_restPolynomial f r a c k hk2 τ'`. Take `⟨P, hP, -, S', hS', hI⟩` from `hMain _ Q hQ k (by omega) hkN τ _ (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')`. Establish `hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1)`. Apply `IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))` to reduce the goal to its premises. Rewrite using `[hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]`.

Establish `hτ'mem : τ' ∈ Finset.univ.erase τ` using `Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩`. Establish `hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1)`. Rewrite using `[← Finset.add_sum_erase _ _ hτ'mem]`. Establish `h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a)`. Rewrite using `[Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by`.

Simplify using `[hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,`. Use the proof step `Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),`. Use the proof step `Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Use `congr 1`. Rewrite using `[h2]`.

Simplify using `only [hqdef, if_true]`. Take `⟨f', rfl⟩ : ∃ f', f = f' + 2` from `⟨f - 2, by omega⟩`. Simplify using `only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]`. Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.

Establish `hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1` using `(Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))`. Apply the tactic sequence `have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)`. Establish `hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k`. Simplify using `only [mstar, if_true, hsum]`. Take `⟨f', rfl⟩ : ∃ f', f = f' + 2` from `⟨f - 2, by omega⟩`.

Simplify using `only [show f' + 2 - 1 = f' + 1 by omega]`. Establish `h3 : r * a ≤ (f' + 1) * (r * a)` using `Nat.le_mul_of_pos_left _ (by omega)`. Rewrite using `[show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]`. Use linear arithmetic over natural numbers and integers. Establish `hms : mstar f r a q (f * (r * a) + 1) τ = fun σ => if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a`.

Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Rewrite using `[hmτ, if_pos rfl]`. Distinguish the cases in `hσ' : σ = τ'`.

Substitute `hσ'` using the available equality. Simplify using `[mstar, hσ, hqdef]`. Simplify using `[mstar, hσ, hσ', hqdef]`. Establish `hqτ : q τ = 0` using `by simp [hqdef, Ne.symm hττ']`. Rewrite `hres` using `[hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)]`.

Use `set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1) with hχR`. Establish `hprod : ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) = (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)`. Rewrite using `[← Finset.mul_prod_erase _ _ hτ'mem]`. Use `congr 1`. Simplify using `only [hqdef, if_true]`.

Rewrite using `[blockCoeff, if_neg (by omega)]`. Rewrite using `[Finset.prod_congr rfl fun σ hσ => by`. Rewrite using `[show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero, blockCoeff_rect_eq hCI r a hra]]`. Rewrite using `[Finset.prod_const, Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]`. Use `congr 1`.

Establish `hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) = ((f * (r * a) + 1).factorial : ℚ) / (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 2))`. Establish `hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2))`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]`. Use `congr 2`. Simplify using `only [hms, if_neg hττ', if_true]`.

Rewrite using `[Finset.prod_congr rfl (fun σ hσ => show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by`. Simplify using `only [hms, if_neg (Finset.ne_of_mem_erase hσ), if_neg (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,`. Use the proof step `Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),`. Use the proof step `Finset.card_univ, Fintype.card_fin]`. Use `congr 1`.

Establish `hs'` using `(Finset.mem_piAntidiag.mp (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1`. Establish `h` using `Nat.multinomial_spec (Finset.univ : Finset (Fin f)) (mstar f r a q (f * (r * a) + 1) τ)`. Rewrite `h` using `[hp, hs']`. Establish `hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0` using `by positivity`. Rewrite using `[eq_div_iff hden, ← h]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set T := ∑ nu ∈ partitionsOf r k, C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT`. Establish `hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) * aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T`. Rewrite using `[hT]`.

Use `Finset.sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[blockCoeff, if_pos rfl, if_neg (by omega)]`. Establish `hs` using `sum_of_mem_partitionsOf hnu`. Establish `hanti` using `antitone_of_mem_partitionsOf hnu`. Establish `h` using `hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)`.

Establish `hs2 : ∑ i, (a + nu i) = r * a + k`. Rewrite using `[Finset.sum_add_distrib, hs]`. Simplify using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]`. Rewrite `h` using `[hs2]`. Rewrite using `[h]`.

Rewrite `hres` using `[hTeq, hprod]`. Establish `hTsym : T.IsSymmetric`. Introduce `e`. Rewrite using `[hT, map_sum]`. Use `Finset.sum_congr rfl fun nu _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]`. Use `set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) * ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK`. Establish `hPS : powerSumHom (r + a) S' = K • T`. Rewrite using `[hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]`. Simplify using `only [map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0`. Conclude with `(Nat.multinomial_pos _ _).ne'` after adjusting the coercions. Distinguish the cases in `hχ : χR = 0`. Take `⟨S, hS⟩` from `Flag.exists_powerSumHom_eq hTsym`.

Establish `hS'0 : S' = 0`. Apply `Flag.powerSumHom_injective` to reduce the goal to its premises. Rewrite using `[hPS, hK, hχ, map_zero]`. Simplify using the standard rewrite rules. Use `⟨S, hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[restTerm, hI, hS'0, coeff_zero, hχ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK0 : K ≠ 0`. Rewrite using `[hK]`. Conclude with `mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0) (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0`.

Use `⟨K⁻¹ • S', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]`. Rewrite using `[restTerm, hI, coeff_smul, smul_eq_mul]`. Rewrite using `[hK, hmult]`. Establish `hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0` using `by positivity`.

Establish `hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0` using `by positivity`. Take `⟨f', rfl⟩ : ∃ f', f = f' + 2` from `⟨f - 2, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at hden ⊢`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem OtherFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    OtherFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ τ' hττ'
  have hk1 := k_sub_one_le r a k hr ha hkN
  set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ'
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hτ'mem : τ' ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1) := by
    rw [← Finset.add_sum_erase _ _ hτ'mem]
    have h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a) := by
      rw [Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by
        simp [hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,
        Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
    rw [h2]
    simp only [hqdef, if_true]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]
    rw [add_mul, one_mul]
    omega
  have hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k := by
    simp only [mstar, if_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [show f' + 2 - 1 = f' + 1 by omega]
    have h3 : r * a ≤ (f' + 1) * (r * a) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ =>
      if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, if_pos rfl]
    · by_cases hσ' : σ = τ'
      · subst hσ'; simp [mstar, hσ, hqdef]
      · simp [mstar, hσ, hσ', hqdef]
  have hqτ : q τ = 0 := by simp [hqdef, Ne.symm hττ']
  rw [hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)] at hres
  set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    with hχR
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2) := by
    rw [← Finset.mul_prod_erase _ _ hτ'mem]
    congr 1
    · simp only [hqdef, if_true]
      rw [blockCoeff, if_neg (by omega)]
    · rw [Finset.prod_congr rfl fun σ hσ => by
        rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
          blockCoeff_rect_eq hCI r a hra]]
      rw [Finset.prod_const, Finset.card_erase_of_mem hτ'mem,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
      congr 1
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]
      congr 2
      · simp only [hms, if_neg hττ', if_true]
      · rw [Finset.prod_congr rfl (fun σ hσ =>
          show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
            simp only [hms, if_neg (Finset.ne_of_mem_erase hσ),
              if_neg (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,
          Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
          Finset.card_univ, Fintype.card_fin]
        congr 1
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
        ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set T := ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [blockCoeff, if_pos rfl, if_neg (by omega)]
    have hs := sum_of_mem_partitionsOf hnu
    have hanti := antitone_of_mem_partitionsOf hnu
    have h := hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)
    have hs2 : ∑ i, (a + nu i) = r * a + k := by
      rw [Finset.sum_add_distrib, hs]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
    rw [hs2] at h
    rw [h]
  rw [hTeq, hprod] at hres
  have hTsym : T.IsSymmetric := by
    intro e
    rw [hT, map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  by_cases hχ : χR = 0
  · obtain ⟨S, hS⟩ := Flag.exists_powerSumHom_eq hTsym
    have hS'0 : S' = 0 := by
      apply Flag.powerSumHom_injective
      rw [hPS, hK, hχ, map_zero]
      simp
    refine ⟨S, hS, ?_⟩
    rw [restTerm, hI, hS'0, coeff_zero, hχ]
    ring
  · have hK0 : K ≠ 0 := by
      rw [hK]
      exact mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0)
        (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0
    refine ⟨K⁻¹ • S', ?_, ?_⟩
    · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
    · rw [restTerm, hI, coeff_smul, smul_eq_mul]
      rw [hK, hmult]
      have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
      have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hden ⊢
      field_simp
      ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
