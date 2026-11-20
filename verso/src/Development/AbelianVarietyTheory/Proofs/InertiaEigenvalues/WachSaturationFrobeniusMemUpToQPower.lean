import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiSat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Use `W.φD_smul T (algebraMap (LetA O n) W.EE a) y` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.φE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) y
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Take `⟨n₁, hn₁, rfl⟩` from `hy`. Take `⟨j, hj⟩` from `W.N_φ T₁ n₁ hn₁`. Use `⟨j, W.Q ^ j • W.φD T₁ n₁, hj, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `congr 1`.

Conclude with `W.map_φ π n₁`.
-/
theorem φD_map_Q {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (y : W.DD T₂)
    (hy : y ∈ (W.N T₁).map (mapA W π)) : ∃ j : ℕ, W.Q ^ j • W.φD T₂ y ∈ (W.N T₁).map (mapA W π) := by
  obtain ⟨n₁, hn₁, rfl⟩ := hy
  obtain ⟨j, hj⟩ := W.N_φ T₁ n₁ hn₁
  refine ⟨j, W.Q ^ j • W.φD T₁ n₁, hj, ?_⟩
  rw [map_smul]
  congr 1
  exact W.map_φ π n₁

/- English proof (translation)
Use `set N'' := (W.N T₁).map (mapA W π) with hN''`. Take `⟨hxN, k, hk1, hk2⟩` from `hx`. Set `J : Ideal (LetA O n)` to `{ carrier := {a | ∃ j : ℕ, W.Q ^ j • a • W.φD T₂ x ∈ N''} add_mem' := by`. Introduce and unpack `a b ⟨i, hi⟩ ⟨j, hj⟩`. Use `⟨i + j, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_smul, smul_add, pow_add]`. Use `N''.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `N''.smul_mem _ hi`. Rewrite using `[mul_smul]`.

Conclude with `N''.smul_mem _ hj`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨j, hj⟩`. Use `⟨j, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, mul_smul, smul_comm]`. Conclude with `N''.smul_mem c hj }`. Establish `hJ : ∀ (a : LetA O n) (j : ℕ), W.Q ^ j • a • W.φD T₂ x ∈ N'' → ∀ (b : LetA O n) (E : ℕ), j ≤ E → W.Q ^ E • (b * a) • W.φD T₂ x ∈ N''`. Introduce `a j hj b E hjE`. Establish `: W.Q ^ E • (b * a) • W.φD T₂ x = (W.Q ^ (E - j) * b) • (W.Q ^ j • a • W.φD T₂ x)`.

Rewrite using `[smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Use `conv_lhs => rw [← Nat.sub_add_cancel hjE, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `N''.smul_mem _ hj`. Establish `hl : ((l : ℕ) : LetA O n) ^ k ∈ J`. Take `⟨j, hj⟩` from `φD_map_Q W π _ hk1`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[φD_smulA, map_pow, map_natCast]`.

Conclude with `hj`. Establish `hπq : (letπ * W.q) ^ k ∈ J`. Take `⟨j, hj⟩` from `φD_map_Q W π _ hk2`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[φD_smulA, map_pow, W.φA_π]`.

Conclude with `hj`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hlp (letπ : LetA O n) 1`. Establish `hq : letπ * W.q = (letπ + 1 : LetA O n) ^ l - 1`. Use function extensionality and compare the values at `i`. Use `W.q₀_def` as an intermediate fact.

Rewrite `this` using `[hp]`. Simplify using `[letπ, LocWach.q, this, add_comm]`. Establish `hπl : (letπ : LetA O n) ^ l = letπ * W.q - (l : LetA O n) * (letπ * r)`. Rewrite using `[hq, hr]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hrad : (letπ : LetA O n) ^ l ∈ J.radical`. Rewrite using `[hπl]`. Use `Ideal.sub_mem _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hπq)) ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hl))`. Take `⟨m, j₁, hj₁⟩` from `hrad`.

Take `⟨j₂, hj₂⟩` from `hl`. Take `⟨a, ha⟩` from `W.N_φ T₂ x hxN`. Express the relevant statement in the definitionally equal form `W.Q ^ a • W.φD T₂ x ∈ W.N T₂ at ha`. Use `⟨a + j₁ + j₂, ?_, k + l * m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_assoc, pow_add, mul_comm, mul_smul]`.

Conclude with `(W.N T₂).smul_mem _ ha`. Use `hJ _ j₂ hj₂ ((l : LetA O n) ^ (l * m)) (a + j₁ + j₂) (by omega)` as an intermediate fact. Rewrite `this` using `[← pow_add, Nat.add_comm (l * m) k]`. Rewrite using `[smul_comm]`. Conclude with `this`.

Use `hJ _ j₁ hj₁ ((letπ : LetA O n) ^ k) (a + j₁ + j₂) (by omega)` as an intermediate fact. Rewrite `this` using `[← pow_mul, ← pow_add]`. Rewrite using `[smul_comm]`. Conclude with `this`.
-/
theorem φD_satM_gen (l : ℕ) (hlp : l.Prime) (hp : PD.p = l) {T₁ T₂ : LocLat G Qp LL O}
    (π : LatHom T₁.L T₂.L) (x : W.DD T₂)
    (hx : x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) :
    ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  set N'' := (W.N T₁).map (mapA W π) with hN''
  obtain ⟨hxN, k, hk1, hk2⟩ := hx
  let J : Ideal (LetA O n) :=
    { carrier := {a | ∃ j : ℕ, W.Q ^ j • a • W.φD T₂ x ∈ N''}
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        rw [add_smul, smul_add, pow_add]
        refine N''.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N''.smul_mem _ hi
        · rw [mul_smul]; exact N''.smul_mem _ hj
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [smul_eq_mul, mul_smul, smul_comm]
        exact N''.smul_mem c hj }
  have hJ : ∀ (a : LetA O n) (j : ℕ), W.Q ^ j • a • W.φD T₂ x ∈ N'' → ∀ (b : LetA O n) (E : ℕ), j ≤ E →
      W.Q ^ E • (b * a) • W.φD T₂ x ∈ N'' := by
    intro a j hj b E hjE
    have : W.Q ^ E • (b * a) • W.φD T₂ x = (W.Q ^ (E - j) * b) • (W.Q ^ j • a • W.φD T₂ x) := by
      rw [smul_smul, smul_smul, smul_smul]
      congr 1
      conv_lhs => rw [← Nat.sub_add_cancel hjE, pow_add]
      ring
    rw [this]
    exact N''.smul_mem _ hj
  have hl : ((l : ℕ) : LetA O n) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk1
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, map_natCast] at hj
    exact hj
  have hπq : (letπ * W.q) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk2
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, W.φA_π] at hj
    exact hj
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hlp (letπ : LetA O n) 1
  have hq : letπ * W.q = (letπ + 1 : LetA O n) ^ l - 1 := by
    funext i
    have := W.q₀_def
    rw [hp] at this
    simp [letπ, LocWach.q, this, add_comm]
  have hπl : (letπ : LetA O n) ^ l = letπ * W.q - (l : LetA O n) * (letπ * r) := by
    rw [hq, hr]; ring
  have hrad : (letπ : LetA O n) ^ l ∈ J.radical := by
    rw [hπl]
    refine Ideal.sub_mem _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hπq)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hl))
  obtain ⟨m, j₁, hj₁⟩ := hrad
  obtain ⟨j₂, hj₂⟩ := hl
  obtain ⟨a, ha⟩ := W.N_φ T₂ x hxN
  change W.Q ^ a • W.φD T₂ x ∈ W.N T₂ at ha
  refine ⟨a + j₁ + j₂, ?_, k + l * m, ?_, ?_⟩
  · rw [add_assoc, pow_add, mul_comm, mul_smul]
    exact (W.N T₂).smul_mem _ ha
  · have := hJ _ j₂ hj₂ ((l : LetA O n) ^ (l * m)) (a + j₁ + j₂) (by omega)
    rw [← pow_add, Nat.add_comm (l * m) k] at this
    rw [smul_comm]
    exact this
  · have := hJ _ j₁ hj₁ ((letπ : LetA O n) ^ k) (a + j₁ + j₂) (by omega)
    rw [← pow_mul, ← pow_add] at this
    rw [smul_comm]
    exact this

/- English proof (translation)
Introduce `D HW F l _ K s LL h W T₁ T₂ π _hc₁ _hc₂ x hx`. Conclude with `φD_satM_gen W l Fact.out ((D.loc l).PD_p K) π x hx`.
-/
theorem φD_satM_Q : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _hc₁ _hc₂ x hx
  exact φD_satM_gen W l Fact.out ((D.loc l).PD_p K) π x hx

end GlobalTheory.NL.PhiSat
