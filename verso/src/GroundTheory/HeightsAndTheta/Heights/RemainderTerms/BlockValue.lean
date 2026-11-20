import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def gmf (f r a : ℕ) (c : SmallBlock) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  (∏ σ, blockEmb f (r + a) σ (yEval r a c (extraFactor r (q σ)))) * smallBlockMu f r a c ^ e *
    fibreClass f r a c

def gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
    (Nat.multinomial Finset.univ m : ℚ) •
      ∏ σ, blockEmb f (r + a) σ (blockOut r a c κ (q σ) (m σ))

/- English proof (translation)
Rewrite using `[gmf, expand_blocks, gmfOut]`. Use `hasDD_sum _ fun m _ => hasDD_smul _ (hasDD_prod f (r + a) _ _ fun σ => ?_)` and prove the remaining obligations. Conclude with `hasDD_block hF r a c κ hκ (q σ) (m σ)`.
-/
theorem hasDD_gmf (hF : FrobeniusCharacterFormula.Statement) (f r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q : Fin f → ℕ) (e : ℕ) :
    HasDD f (r + a) (gmf f r a c q e) (gmfOut f r a c κ q e) := by
  rw [gmf, expand_blocks, gmfOut]
  refine hasDD_sum _ fun m _ => hasDD_smul _ (hasDD_prod f (r + a) _ _ fun σ => ?_)
  exact hasDD_block hF r a c κ hκ (q σ) (m σ)

def toN (N : ℕ) : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun p : Fin 1 × Fin N => X p.2)

/- English proof (translation)
Establish `key : (restrictToBlock f N τ).comp (blockEmb f N σ) = aeval (fun p : Fin 1 × Fin N => if σ = τ then X p.2 else 0)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[restrictToBlock, blockEmb]`. Use `congrArg (fun φ : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ P) key` as an intermediate fact.

Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[this]`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[show (fun _ : Fin 1 × Fin N => (0 : MvPolynomial (Fin N) ℚ)) = 0 from rfl, MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq]`.
-/
theorem restrictToBlock_blockEmb (f N : ℕ) (τ σ : Fin f) (P : RootRing 1 N) :
    restrictToBlock f N τ (blockEmb f N σ P) =
      if σ = τ then toN N P else C (constantCoeff P) := by
  have key : (restrictToBlock f N τ).comp (blockEmb f N σ) =
      aeval (fun p : Fin 1 × Fin N => if σ = τ then X p.2 else 0) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [restrictToBlock, blockEmb]
  have := congrArg (fun φ : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ P) key
  simp only [AlgHom.comp_apply] at this
  rw [this]
  split_ifs with h
  · rfl
  · rw [show (fun _ : Fin 1 × Fin N => (0 : MvPolynomial (Fin N) ℚ)) = 0 from rfl,
      MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq]

/- English proof (translation)
Establish `key : (toN (r + a)).comp (xSign r a c) = aeval (fun i : Fin (r + a) => C c.sign * X i)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[toN, xSign]`. Conclude with `congrArg (fun φ : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] MvPolynomial (Fin (r + a)) ℚ => φ p) key`.
-/
theorem toN_xSign (r a : ℕ) (c : SmallBlock) (p : MvPolynomial (Fin (r + a)) ℚ) :
    toN (r + a) (xSign r a c p) = aeval (fun i : Fin (r + a) => C c.sign * X i) p := by
  have key : (toN (r + a)).comp (xSign r a c) =
      aeval (fun i : Fin (r + a) => C c.sign * X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [toN, xSign]
  exact congrArg (fun φ : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] MvPolynomial (Fin (r + a)) ℚ => φ p) key

def mstar (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) : Fin f → ℕ :=
  fun σ => if σ = τ then e - ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') else r * a - q σ

/- English proof (translation)
Rewrite using `[Finset.mem_piAntidiag]`. Use `⟨?_, fun i _ => Finset.mem_univ i⟩` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]`. Establish `: ∑ x ∈ Finset.univ.erase τ, mstar f r a q e τ x = ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ')` using `Finset.sum_congr rfl fun x hx => by simp [mstar, Finset.ne_of_mem_erase hx]`. Rewrite using `[this]`.

Simplify using `only [mstar, if_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mstar_mem (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    mstar f r a q e τ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, fun i _ => Finset.mem_univ i⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]
  have : ∑ x ∈ Finset.univ.erase τ, mstar f r a q e τ x =
      ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') :=
    Finset.sum_congr rfl fun x hx => by simp [mstar, Finset.ne_of_mem_erase hx]
  rw [this]
  simp only [mstar, if_true]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Rewrite `hm` using `[Finset.mem_piAntidiag]`. Establish `hs` using `hm.1`.

Rewrite `hs` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ σ)]`. Establish `: ∑ x ∈ Finset.univ.erase σ, m x = ∑ σ' ∈ Finset.univ.erase σ, (r * a - q σ')` using `Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)`. Simplify using `only [mstar, if_true]`. Use linear arithmetic over natural numbers and integers. Simplify using `[mstar, hσ, h σ hσ]`.
-/
theorem eq_mstar_of (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) (m : Fin f → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e)
    (h : ∀ σ, σ ≠ τ → m σ = r * a - q σ) : m = mstar f r a q e τ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    rw [Finset.mem_piAntidiag] at hm
    have hs := hm.1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)] at hs
    have : ∑ x ∈ Finset.univ.erase σ, m x = ∑ σ' ∈ Finset.univ.erase σ, (r * a - q σ') :=
      Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
    simp only [mstar, if_true]
    omega
  · simp [mstar, hσ, h σ hσ]

/- English proof (translation)
Rewrite using `[gmfOut, map_sum]`. Rewrite using `[Finset.sum_eq_single (mstar f r a q e τ)]`. Rewrite using `[map_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]`. Rewrite using `[restrictToBlock_blockEmb, if_pos rfl]`. Establish `: ∏ x ∈ Finset.univ.erase τ, restrictToBlock f (r + a) τ (blockEmb f (r + a) x (blockOut r a c κ (q x) (mstar f r a q e τ x))) = C (∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ))`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun σ hσ => ?_` and prove the remaining obligations. Establish `hne` using `Finset.ne_of_mem_erase hσ`. Rewrite using `[restrictToBlock_blockEmb, if_neg hne, constantCoeff_blockOut]`. Simplify using `only [mstar, if_neg hne]`.

Rewrite using `[if_pos (by have := hq σ hne; omega)]`. Rewrite using `[this, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Introduce `m hm hne`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hστ, hσ⟩ : ∃ σ, σ ≠ τ ∧ m σ ≠ r * a - q σ := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne (eq_mstar_of f r a q e τ m hm hcon)`. Rewrite using `[map_smul, map_prod, Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]`. Rewrite using `[restrictToBlock_blockEmb, if_neg hστ, constantCoeff_blockOut, if_neg, map_zero]`.

Use `hq σ hστ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (mstar_mem f r a q e τ he) h`.
-/
theorem restrict_gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (hq : ∀ σ, σ ≠ τ → q σ ≤ r * a)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    restrictToBlock f (r + a) τ (gmfOut f r a c κ q e) =
      ((Nat.multinomial Finset.univ (mstar f r a q e τ) : ℚ) *
          ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) •
        toN (r + a) (blockOut r a c κ (q τ) (mstar f r a q e τ τ)) := by
  rw [gmfOut, map_sum]
  rw [Finset.sum_eq_single (mstar f r a q e τ)]
  · rw [map_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [restrictToBlock_blockEmb, if_pos rfl]
    have : ∏ x ∈ Finset.univ.erase τ, restrictToBlock f (r + a) τ
        (blockEmb f (r + a) x (blockOut r a c κ (q x) (mstar f r a q e τ x))) =
        C (∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun σ hσ => ?_
      have hne := Finset.ne_of_mem_erase hσ
      rw [restrictToBlock_blockEmb, if_neg hne, constantCoeff_blockOut]
      simp only [mstar, if_neg hne]
      rw [if_pos (by have := hq σ hne; omega)]
    rw [this, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_natCast]
    ring
  · intro m hm hne
    obtain ⟨σ, hστ, hσ⟩ : ∃ σ, σ ≠ τ ∧ m σ ≠ r * a - q σ := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_mstar_of f r a q e τ m hm hcon)
    rw [map_smul, map_prod, Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [restrictToBlock_blockEmb, if_neg hστ, constantCoeff_blockOut, if_neg, map_zero]
    have := hq σ hστ
    omega
  · intro h
    exact absurd (mstar_mem f r a q e τ he) h

/- English proof (translation)
Simplify using `only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`. Conclude with `Iff.rfl`.
-/
theorem mem_partitionsOf_iff {m n : ℕ} (lam : Fin m → ℕ) :
    lam ∈ partitionsOf m n ↔ ∑ i, lam i = n ∧ Antitone lam := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[blockOut, map_sum, Finset.mul_sum]`. Establish `hterm : ∀ lam ∈ partitionsOf r (q + m), toN (r + a) (blockCoeff q m lam • pushOut r a c κ lam) = if ∀ i, a ≤ lam i then C κ * (C (blockCoeff q m lam) * aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) (fun i => lam i - a))) else 0`. Introduce `lam _`. Rewrite using `[map_smul, pushOut]`. Use `split_ifs`.

Rewrite using `[map_mul, toN_xSign, smul_eq_C_mul]`. Simplify using `only [toN, aeval_C, algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.sum_filter]`.

Use `symm`. Use `Finset.sum_nbij' (fun nu i => a + nu i) (fun lam i => lam i - a) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `nu hnu`. Rewrite `hnu` using `[mem_partitionsOf_iff]`. Rewrite using `[Finset.mem_filter, mem_partitionsOf_iff]`.

Use `⟨⟨?_, fun i j hij => Nat.add_le_add_left (hnu.2 hij) a⟩, fun i => Nat.le_add_right a _⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, hnu.1]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Use linear arithmetic over natural numbers and integers. Introduce `lam hlam`.

Rewrite `hlam` using `[Finset.mem_filter, mem_partitionsOf_iff]`. Rewrite using `[mem_partitionsOf_iff]`. Use `⟨?_, fun i j hij => Nat.sub_le_sub_right (hlam.1.2 hij) a⟩` and prove the remaining obligations. Establish `h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlam.2 i)`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1`. Use linear arithmetic over natural numbers and integers. Introduce `nu _`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Introduce `lam hlam`. Rewrite `hlam` using `[Finset.mem_filter]`. Use function extensionality and compare the values at `i`. Conclude with `Nat.add_sub_cancel' (hlam.2 i)`.

Introduce `nu _`. Simplify using the standard rewrite rules.
-/
theorem toN_blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m k : ℕ) (hk : q + m = k + r * a) :
    toN (r + a) (blockOut r a c κ q m) =
      C κ * ∑ nu ∈ partitionsOf r k, C (blockCoeff q m (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) := by
  rw [blockOut, map_sum, Finset.mul_sum]
  have hterm : ∀ lam ∈ partitionsOf r (q + m),
      toN (r + a) (blockCoeff q m lam • pushOut r a c κ lam) =
        if ∀ i, a ≤ lam i then C κ * (C (blockCoeff q m lam) *
          aeval (fun i : Fin (r + a) => C c.sign * X i)
            (schur (Fin (r + a)) (fun i => lam i - a))) else 0 := by
    intro lam _
    rw [map_smul, pushOut]
    split_ifs
    · rw [map_mul, toN_xSign, smul_eq_C_mul]
      simp only [toN, aeval_C, algebraMap_eq]
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun nu i => a + nu i) (fun lam i => lam i - a) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [mem_partitionsOf_iff] at hnu
    rw [Finset.mem_filter, mem_partitionsOf_iff]
    refine ⟨⟨?_, fun i j hij => Nat.add_le_add_left (hnu.2 hij) a⟩, fun i => Nat.le_add_right a _⟩
    rw [Finset.sum_add_distrib, hnu.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · intro lam hlam
    rw [Finset.mem_filter, mem_partitionsOf_iff] at hlam
    rw [mem_partitionsOf_iff]
    refine ⟨?_, fun i j hij => Nat.sub_le_sub_right (hlam.1.2 hij) a⟩
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlam.2 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  · intro nu _
    funext i
    simp
  · intro lam hlam
    rw [Finset.mem_filter] at hlam
    funext i
    exact Nat.add_sub_cancel' (hlam.2 i)
  · intro nu _
    simp

/- English proof (translation)
Rewrite using `[blockOut, Finset.sum_eq_single (rectangle r a)]`. Establish `h0 : (fun i : Fin r => rectangle r a i - a) = 0` using `funext fun i => by simp [rectangle]`. Rewrite using `[pushOut, if_pos (fun i => by simp [rectangle]), h0, schur_zero, map_one, mul_one, smul_eq_C_mul, ← C_mul, mul_comm]`. Introduce `lam hlam hne`. Rewrite using `[pushOut, if_neg, smul_zero]`.

Introduce `hall`. Apply `hne` to reduce the goal to its premises. Rewrite `hlam` using `[mem_partitionsOf_iff]`. Establish `h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hall i)`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1`. Establish `h2 : ∑ i, (lam i - a) = 0` using `by omega`. Use function extensionality and compare the values at `i`. Use `Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)` as an intermediate fact.

Use `hall i` as an intermediate fact. Simplify using `only [rectangle]`. Use linear arithmetic over natural numbers and integers. Introduce `h'`. Conclude with `absurd ((rectangle_mem_partitionsOf r a _).mpr h) h'`.
-/
theorem blockOut_rect (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) (h : q + m = r * a) :
    blockOut r a c κ q m = C (blockCoeff q m (rectangle r a) * κ) := by
  rw [blockOut, Finset.sum_eq_single (rectangle r a)]
  · have h0 : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [pushOut, if_pos (fun i => by simp [rectangle]), h0, schur_zero, map_one, mul_one, smul_eq_C_mul,
      ← C_mul, mul_comm]
  · intro lam hlam hne
    rw [pushOut, if_neg, smul_zero]
    intro hall
    apply hne
    rw [mem_partitionsOf_iff] at hlam
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hall i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : ∑ i, (lam i - a) = 0 := by omega
    funext i
    have := Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)
    have := hall i
    simp only [rectangle]
    omega
  · intro h'
    exact absurd ((rectangle_mem_partitionsOf r a _).mpr h) h'

/- English proof (translation)
Rewrite using `[gmfOut, Finset.sum_eq_single (fun _ : Fin f => r * a)]`. Simplify using `only [Pi.zero_apply]`. Rewrite using `[Finset.prod_congr rfl fun σ _ => by rw [blockOut_rect r a c κ 0 (r * a) (by simp)]]`. Simplify using `only [blockEmb, rename_C, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[smul_eq_C_mul, ← C_pow, ← C_mul]`.

Introduce `m hm hne`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : ∃ σ, m σ < r * a := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hne` to reduce the goal to its premises.

Rewrite `hm` using `[Finset.mem_piAntidiag]`. Establish `hle : ∀ σ ∈ (Finset.univ : Finset (Fin f)), (fun _ => r * a) σ ≤ m σ` using `fun σ _ => hcon σ`. Establish `hsum : ∑ σ : Fin f, (fun _ => r * a) σ = ∑ σ, m σ`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Rewrite using `[hm.1]`.

Use function extensionality and compare the values at `σ`. Conclude with `((Finset.sum_eq_sum_iff_of_le hle).mp hsum σ (Finset.mem_univ σ)).symm`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]`. Rewrite using `[Pi.zero_apply, blockOut_eq_zero_of_lt r a c κ 0 (m σ) (by omega), map_zero]`. Introduce `h`.

It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Rewrite using `[Finset.mem_piAntidiag]`. Use `⟨by simp, fun i _ => Finset.mem_univ i⟩` and prove the remaining obligations.
-/
theorem gmfOut_zero (f r a : ℕ) (c : SmallBlock) (κ : ℚ) :
    gmfOut f r a c κ 0 (f * (r * a)) =
      C ((Nat.multinomial Finset.univ (fun _ : Fin f => r * a) : ℚ) *
        (blockCoeff 0 (r * a) (rectangle r a) * κ) ^ f) := by
  rw [gmfOut, Finset.sum_eq_single (fun _ : Fin f => r * a)]
  · simp only [Pi.zero_apply]
    rw [Finset.prod_congr rfl fun σ _ => by rw [blockOut_rect r a c κ 0 (r * a) (by simp)]]
    simp only [blockEmb, rename_C, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [smul_eq_C_mul, ← C_pow, ← C_mul]
  · intro m hm hne
    obtain ⟨σ, hσ⟩ : ∃ σ, m σ < r * a := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [Finset.mem_piAntidiag] at hm
      have hle : ∀ σ ∈ (Finset.univ : Finset (Fin f)), (fun _ => r * a) σ ≤ m σ :=
        fun σ _ => hcon σ
      have hsum : ∑ σ : Fin f, (fun _ => r * a) σ = ∑ σ, m σ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [hm.1]
      funext σ
      exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum σ (Finset.mem_univ σ)).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [Pi.zero_apply, blockOut_eq_zero_of_lt r a c κ 0 (m σ) (by omega), map_zero]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨by simp, fun i _ => Finset.mem_univ i⟩

end

end Top

end RestTerms

end GroundTheory.Heights₂.Heights
