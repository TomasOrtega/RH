import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElementStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformCongruenceLevelGamma1CapGamma0Statement

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Rewrite `hx`, the goal using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Conclude with `dvd_trans (Int.natCast_dvd_natCast.mpr h) hx`.
-/
theorem intCast_zmod_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {x y : ℤ} (hx : (x : ZMod K) = y) :
    (x : ZMod K₁) = y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

/- English proof (translation)
Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)` after adjusting the coercions. Conclude with `intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)` after adjusting the coercions.

Conclude with `intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)` after adjusting the coercions. Conclude with `intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)` after adjusting the coercions.
-/
theorem mem_Gamma_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ CongruenceSubgroup.Gamma K₁ := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)

/- English proof (translation)
Establish `h1` using `CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)`. Establish `h2` using `CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)`. Use `show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l`. Conclude with `Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩`.
-/
theorem mem_Gam_of_Gamma {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ Gam N l := by
  have h1 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)
  show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
  exact Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩,
    CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `CongruenceSubgroup.Gamma_mem.1 hδ`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]`.
-/
theorem entries_eq_one_of_mem_Gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]

/- English proof (translation)
Introduce `N l w hN hl hl2 hlN hw Φ hΦ n`. Take `⟨hhom, hadd, hinv, -⟩` from `hΦ`. Take `⟨M₁, hM₁, hadd₁⟩` from `hadd n`. Take `⟨M₂, hM₂, hinv₂⟩` from `GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)`. Take `⟨b, M', hlM', hMeq⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'`.

Establish `hM'pos : 0 < M'`. Break down `Nat.eq_zero_or_pos M' with h | h` into its components or cases. Conclude with `absurd (h ▸ dvd_zero l) hlM'`. Conclude with `h`. Take `⟨c, hcΓ, hcomm, hcneg⟩` from `GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'`.

Establish `hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n)`. Rewrite using `[hMeq]`. Conclude with `dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩`. Establish `hM₁K : M₁ ∣ M' * N * l ^ (max b n)` using `dvd_trans (dvd_mul_right _ _) hMK`. Establish `hM₂K : M₂ ∣ M' * N * l ^ (max b n)` using `dvd_trans (dvd_mul_left _ _) hMK`.

Establish `hnA : l ^ n ∣ l ^ (max b n)` using `pow_dvd_pow l (le_max_right b n)`. Establish `hnK : l ^ n ∣ M' * N * l ^ (max b n)` using `dvd_trans hnA (dvd_mul_left _ _)`. Take `⟨L1, L2, L3, -, -, L6, L7⟩` from `GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))`. Establish `hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal` using `by haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))`. Conclude with `Subgroup.normal_subgroupOf`.

Establish `h2 : IsUnit (2 : ZMod (l ^ n))`. Establish `hc : Nat.Coprime 2 (l ^ n)` using `Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))`. Simplify using `using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc`. Take `⟨z, hzS, hzc, hzΔ⟩` from `GlobalTheory.T.exists_cocycle_extension_of_neg_central_element (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n))) (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap) (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2 (MvPolynomial.homogeneousS …`. Rewrite `hv`, the goal using `[MvPolynomial.mem_homogeneousSubmodule]`.

Conclude with `L3 _ _ _ hv)`. Use `_ hΔ`. Use the proof step `(fun δ hδ v => by`. Establish `hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n)` using `mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)`. Use `show slP _ v = v`.

Rewrite using `[L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])`. Use the proof step `⟨c, hcΓ⟩`. Use the proof step `(fun v hv => by show slP _ v = -v`. Rewrite `hv` using `[MvPolynomial.mem_homogeneousSubmodule]`. Rewrite using `[L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]`.

Introduce `i j`. Establish `h` using `hcneg i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at h ⊢`. Conclude with `intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)` after adjusting the coercions. Conclude with `intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)` after adjusting the coercions.

Conclude with `intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)` after adjusting the coercions. Conclude with `intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))` after adjusting the coercions. Use the proof step `(fun g => by`. Rewrite using `[Subgroup.mem_subgroupOf]`. Simplify using `using hcomm g)`.

Use the proof step `(fun g => Φ n g)`. Use the proof step `(fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))`. Use the proof step `(fun δ hδ δ' hδ' => by`. Use `hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))` as an intermediate fact. Simplify using `using this)`.

Use the proof step `(fun g δ hδ => by`. Use `hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))` as an intermediate fact. Simplify using `using this)`. Use `⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `γ hγ`.

Simplify using `only [dif_pos hγ]`. Conclude with `(MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)`. Introduce `γ hγ δ hδ`. Simplify using `only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]`. Simplify using `using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩`.

Use `⟨M' * N * l ^ (max b n) * l, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `hδG : δ ∈ Gam N l` using `mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ`. Establish `hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))` using `mem_Gamma_of_dvd (dvd_mul_right _ _) hδ`. Simplify using `only [dif_pos hδG]`. Conclude with `hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)`.
-/
theorem exists_coc_near : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ,
    IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)),
      IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  intro N l w hN hl hl2 hlN hw Φ hΦ n
  obtain ⟨hhom, hadd, hinv, -⟩ := hΦ
  obtain ⟨M₁, hM₁, hadd₁⟩ := hadd n
  obtain ⟨M₂, hM₂, hinv₂⟩ :=
    GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)
  obtain ⟨b, M', hlM', hMeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · exact absurd (h ▸ dvd_zero l) hlM'
    · exact h
  obtain ⟨c, hcΓ, hcomm, hcneg⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'
  have hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n) := by
    rw [hMeq]
    exact dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩
  have hM₁K : M₁ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_right _ _) hMK
  have hM₂K : M₂ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_left _ _) hMK
  have hnA : l ^ n ∣ l ^ (max b n) := pow_dvd_pow l (le_max_right b n)
  have hnK : l ^ n ∣ M' * N * l ^ (max b n) := dvd_trans hnA (dvd_mul_left _ _)
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  have hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))
    exact Subgroup.normal_subgroupOf
  have h2 : IsUnit (2 : ZMod (l ^ n)) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    simpa using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  obtain ⟨z, hzS, hzc, hzΔ⟩ := GlobalTheory.T.exists_cocycle_extension_of_neg_central_element (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap)
    (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod (l ^ n)) w)
    (fun g v hv => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv ⊢
      exact L3 _ _ _ hv)
    _ hΔ
    (fun δ hδ v => by
      have hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n) :=
        mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)
      show slP _ v = v
      rw [L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])
    ⟨c, hcΓ⟩
    (fun v hv => by
      show slP _ v = -v
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv
      rw [L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]
      intro i j
      have h := hcneg i j
      fin_cases i <;> fin_cases j <;> simp at h ⊢
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))
    (fun g => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm g)
    (fun g => Φ n g)
    (fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))
    (fun δ hδ δ' hδ' => by
      have := hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _
        (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))
      simpa using this)
    (fun g δ hδ => by
      have := hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))
      simpa using this)
  classical
  refine ⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)
  · intro γ hγ δ hδ
    simp only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]
    simpa using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩
  · refine ⟨M' * N * l ^ (max b n) * l,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩
    have hδG : δ ∈ Gam N l :=
      mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ
    have hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n)) :=
      mem_Gamma_of_dvd (dvd_mul_right _ _) hδ
    simp only [dif_pos hδG]
    exact hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)

end GlobalTheory.KZ.H3
