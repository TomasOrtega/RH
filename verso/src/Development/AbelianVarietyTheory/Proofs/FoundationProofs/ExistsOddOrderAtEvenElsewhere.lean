import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Unfold `_root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq`. Simplify using `[_root_.GlobalTheory.QNorm.mem_sqSub]`.
-/
private lemma mem_locSq_iff' (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.QNorm.locSq F S ↔
      (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) (x : F))) ∧
        ∀ σ : F →+* ℝ, IsSquare (σ (x : F)) := by
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  simp [_root_.GlobalTheory.QNorm.mem_sqSub]

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Take `⟨r, hr⟩` from `h`. Establish `hne : σ (x : F) ≠ 0` using `(map_ne_zero σ).mpr x.ne_zero`. Conclude with `lt_of_le_of_ne (by rw [hr]; exact mul_self_nonneg r) (Ne.symm hne)`.
-/
private lemma pos_of_isSquare_real_embedding_unit {F : Type} [Field F] (σ : F →+* ℝ) (x : Fˣ)
    (h : IsSquare (σ (x : F))) : 0 < σ (x : F) := by
  obtain ⟨r, hr⟩ := h
  have hne : σ (x : F) ≠ 0 := (map_ne_zero σ).mpr x.ne_zero
  exact lt_of_le_of_ne (by rw [hr]; exact mul_self_nonneg r) (Ne.symm hne)

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Establish `hv : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Establish `hy0 : Valued.v y ≠ 0`. Introduce `h0`. Rewrite `hv` using `[hy, map_mul, h0, zero_mul]`.

Conclude with `((Valuation.ne_zero_iff _).mpr hx) hv.symm`. Use `⟨WithZero.log (Valued.v y), ?_⟩` and prove the remaining obligations. Rewrite using `[← hv, hy, map_mul, two_mul, WithZero.exp_add, WithZero.exp_log hy0]`.
-/
private lemma exists_valuation_eq_exp_two_mul_of_isSquare_completion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : F) (hx : x ≠ 0)
    (h : IsSquare (algebraMap F (v.adicCompletion F) x)) :
    ∃ n : ℤ, v.valuation F x = WithZero.exp (2 * n) := by
  obtain ⟨y, hy⟩ := h
  have hv : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [hy, map_mul, h0, zero_mul] at hv
    exact ((Valuation.ne_zero_iff _).mpr hx) hv.symm
  refine ⟨WithZero.log (Valued.v y), ?_⟩
  rw [← hv, hy, map_mul, two_mul, WithZero.exp_add, WithZero.exp_log hy0]

open NumberField IsDedekindDomain in
open scoped WithZero in

/- English proof (translation)
Introduce `F _ _ δ σ₀ hδ H v₀`. Take `⟨S₀, hS₀, hδS₀, -⟩` from `_root_.GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub F δ hδ`. Use `set S := insert v₀ S₀ with hSdef`. Establish `hv₀S : v₀ ∈ S` using `Finset.mem_insert_self _ _`. Establish `hS : _root_.GlobalTheory.QNorm.admitted F S` using `hS₀.mono (Finset.subset_insert _ _)`.

Establish `hδS : δ ∈ _root_.GlobalTheory.QNorm.sUnits F S`. Rewrite `hδS₀`, the goal using `[_root_.GlobalTheory.QNorm.mem_sUnits]`. Introduce `v hv`. Conclude with `hδS₀ v fun h => hv (Finset.mem_insert_of_mem h)`. Take `⟨T, hST, hcard, hTsq, hpat⟩` from `_root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδS hδ`.

Establish `htop` using `_root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat`. Use `set U := _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) with hU`. Use `set M := _root_.GlobalTheory.QNorm.locSq F S with hM`. Establish `hgoodU : ∀ u ∈ U, ∀ v, v ∉ S → IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨ ∃ n : ℤ, v.valuation F (u : F) = WithZero.exp (2 * n)`. Introduce `u hu v hv`.

Distinguish the cases in `hvT : v ∈ T`. Conclude with `Or.inl (hTsq v hvT)`. Use `right`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[hU, _root_.GlobalTheory.QNorm.mem_sUnits]`.

Rewrite using `[hu v (by simp [hv, hvT])]`. Simplify using the standard rewrite rules. Establish `hinf : M ⊓ U = _root_.GlobalTheory.QNorm.sqs U ⊓ U`. Use extensionality with `y`. Simplify using `only [Subgroup.mem_inf]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hyM, hyU⟩`. Conclude with `⟨_root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F (S ∪ T) y hyU (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyM), hyU⟩`. Introduce and unpack `⟨hysq, hyU⟩`. Conclude with `⟨_root_.GlobalTheory.QNorm.sqs_le_locSq F U S hysq, hyU⟩`.

Establish `hrel : M.relIndex U = 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F))`. Rewrite using `[← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits]`. Take `⟨hM0, hMle⟩` from `_root_.GlobalTheory.QNorm.index_locSq_le F S`. Establish `hidx` using `_root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup U M`. Establish `hunion : (S ∪ T).card = S.card + T.card` using `Finset.card_union_of_disjoint hST`.

Rewrite `hidx` using `[hrel, hunion]`. Establish `hsup0 : (U ⊔ M).index ≠ 0`. Introduce `h0`. Rewrite `hidx` using `[h0, mul_zero]`. Conclude with `hM0 hidx`.

Establish `hle2 : (U ⊔ M).index ≤ 2`. Establish `h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) = 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2`. Rewrite using `[show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `h : 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * (U ⊔ M).index ≤ 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2`. Rewrite using `[← hidx, ← h4]`. Conclude with `hMle`. Conclude with `Nat.le_of_mul_le_mul_left h (by positivity)`. Apply the tactic sequence `obtain ⟨xs, hxs0, hxsS, hxsσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun _ => 1) (fun σ => if σ = σ₀ then -1 else 1) (fun _ => one_ne_zero) (fun σ => by split_ifs <;> norm_num)`.

Simplify using `only [mul_one] at hxsS`. Establish `hxsσ₀ : σ₀ xs < 0`. Establish `h` using `hxsσ σ₀`. Rewrite `h` using `[if_pos rfl]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hxsσ' : ∀ σ, σ ≠ σ₀ → 0 < σ xs` using `fun σ hσ => by`. Establish `h` using `hxsσ σ`. Rewrite `h` using `[if_neg hσ, mul_one]`. Then use the resulting hypothesis. Use `set X : Fˣ := Units.mk0 xs hxs0 with hX`. Establish `hXnot : X ∉ U ⊔ M`.

Introduce `hXmem`. Take `⟨y, hyU, z, hzM, hyz⟩` from `Subgroup.mem_sup.mp hXmem`. Rewrite `hzM` using `[hM, mem_locSq_iff']`. Establish `hy : (y : F) = xs / z`. Rewrite using `[eq_div_iff z.ne_zero, ← Units.val_mul, hyz, hX, Units.val_mk0]`.

Establish `hzpos : ∀ σ : F →+* ℝ, 0 < σ (z : F)` using `fun σ => pos_of_isSquare_real_embedding_unit σ z (hzM.2 σ)`. Establish `hpos` using `H y y.ne_zero (fun v => by`. Distinguish the cases in `hv : v ∈ S`. Use `right`. Apply `exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ y.ne_zero` to reduce the goal to its premises.

Rewrite using `[hy, map_div₀]`. Conclude with `(hxsS v hv).div (hzM.1 v hv)`. Conclude with `hgoodU y hyU v hv) (fun σ hσ => by`. Rewrite using `[hy, map_div₀]`. Conclude with `div_pos (hxsσ' σ hσ) (hzpos σ))`.

Rewrite `hpos` using `[hy, map_div₀]`. Use `(div_pos_iff_of_pos_right (hzpos σ₀)).mp hpos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hidx2 : (U ⊔ M).index = 2`. Establish `hne1 : (U ⊔ M).index ≠ 1`.

Introduce `h1`. Conclude with `hXnot (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top X)`. Use linear arithmetic over natural numbers and integers. Take `⟨ϖ, hϖ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F v₀`. Establish `hϖ0 : ϖ ≠ 0`.

Introduce `h0`. Rewrite `hϖ` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`. Take `⟨xa, hxa0, hxaS, -⟩` from `_root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun v => if v = v₀ then algebraMap F (v.adicCompletion F) ϖ else 1) (fun _ => 1) (fun v => by split_ifs`. Conclude with `(map_ne_zero _).mpr hϖ0`.

Conclude with `one_ne_zero)`. Use the proof step `(fun _ => one_ne_zero)`. Establish `hav₀ : ∃ n : ℤ, v₀.valuation F xa = WithZero.exp (2 * n + 1)`. Establish `h` using `hxaS v₀ hv₀S`. Rewrite `h` using `[if_pos rfl, ← map_mul]`.

Take `⟨n, hn⟩` from `exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ (xa * ϖ) (mul_ne_zero hxa0 hϖ0) h`. Establish `hva : v₀.valuation F xa ≠ 0` using `(Valuation.ne_zero_iff _).mpr hxa0`. Rewrite `hn` using `[map_mul, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_add]`. Establish `h'` using `WithZero.exp_injective hn`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← WithZero.exp_log hva]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `haS : ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) xa)` using `fun v hv hne => by`. Establish `h` using `hxaS v hv`.

Rewrite `h` using `[if_neg hne, mul_one]`. Then use the resulting hypothesis. Use `set A : Fˣ := Units.mk0 xa hxa0 with hA`. Choose the witnesses or unpack the hypotheses as in `⟨B, hBmem, hBv₀, hBS⟩ : ∃ B : Fˣ, B ∈ U ⊔ M ∧ (∃ n : ℤ, v₀.valuation F (B : F) = WithZero.exp (2 * n + 1)) ∧ ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) (B : F)) := by`. Distinguish the cases in `hAmem : A ∈ U ⊔ M`. Conclude with `⟨A, hAmem, hav₀, haS⟩`.

Use `⟨A * X, (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hAmem hXnot), ?_, ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ xs hxs0 (hxsS v₀ hv₀S)`. Take `⟨n, hn⟩` from `hav₀`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul, hn, hm, ← WithZero.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `v hv hne`. Rewrite using `[Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul]`. Conclude with `(haS v hv hne).mul (hxsS v hv)`.

Take `⟨u, huU, m, hmM, hum⟩` from `Subgroup.mem_sup.mp hBmem`. Rewrite `hmM` using `[hM, mem_locSq_iff']`. Establish `hum' : (u : F) * m = B` using `by rw [← Units.val_mul, hum]`. Establish `hu : (u : F) = B / m` using `by rw [eq_div_iff m.ne_zero, hum']`. Use `⟨u, u.ne_zero, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨n, hn⟩` from `hBv₀`. Take `⟨k, hk⟩` from `exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ m m.ne_zero (hmM.1 v₀ hv₀S)`. Establish `hvu : v₀.valuation F (u : F) ≠ 0` using `(Valuation.ne_zero_iff _).mpr u.ne_zero`. Establish `h` using `congrArg (v₀.valuation F) hum'`. Rewrite `h` using `[map_mul, hn, hk, ← WithZero.exp_log hvu, ← WithZero.exp_add]`.

Establish `h'` using `WithZero.exp_injective h`. Use `⟨n - k, ?_⟩` and prove the remaining obligations. Rewrite using `[← WithZero.exp_log hvu]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Introduce `v hne`. Distinguish the cases in `hv : v ∈ S`. Use `right`. Apply `exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ u.ne_zero` to reduce the goal to its premises. Rewrite using `[hu, map_div₀]`.

Conclude with `(hBS v hv hne).div (hmM.1 v hv)`. Conclude with `hgoodU u huU v hv`.
-/
theorem _root_.GlobalTheory.QNorm.exists_odd_order_at_even_elsewhere : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ)
    (σ₀ : F →+* ℝ), ¬ IsSquare (δ : F) →
    (∀ t : F, t ≠ 0 → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
        ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n)) →
      (∀ σ : F →+* ℝ, σ ≠ σ₀ → 0 < σ t) → 0 < σ₀ t) →
    ∀ v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ t : F, t ≠ 0 ∧
      (∃ n : ℤ, v₀.valuation F t = WithZero.exp (2 * n + 1)) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
          ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n) := by
  intro F _ _ δ σ₀ hδ H v₀
  classical
  obtain ⟨S₀, hS₀, hδS₀, -⟩ := _root_.GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub F δ hδ
  set S := insert v₀ S₀ with hSdef
  have hv₀S : v₀ ∈ S := Finset.mem_insert_self _ _
  have hS : _root_.GlobalTheory.QNorm.admitted F S :=
    hS₀.mono (Finset.subset_insert _ _)
  have hδS : δ ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hδS₀ ⊢
    intro v hv
    exact hδS₀ v fun h => hv (Finset.mem_insert_of_mem h)
  obtain ⟨T, hST, hcard, hTsq, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδS hδ
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  set U := _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) with hU
  set M := _root_.GlobalTheory.QNorm.locSq F S with hM
  have hgoodU : ∀ u ∈ U, ∀ v, v ∉ S → IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
      ∃ n : ℤ, v.valuation F (u : F) = WithZero.exp (2 * n) := by
    intro u hu v hv
    by_cases hvT : v ∈ T
    · exact Or.inl (hTsq v hvT)
    · right
      refine ⟨0, ?_⟩
      rw [hU, _root_.GlobalTheory.QNorm.mem_sUnits] at hu
      rw [hu v (by simp [hv, hvT])]
      simp
  have hinf : M ⊓ U = _root_.GlobalTheory.QNorm.sqs U ⊓ U := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyM, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F (S ∪ T) y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyM), hyU⟩
    · rintro ⟨hysq, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.sqs_le_locSq F U S hysq, hyU⟩
  have hrel : M.relIndex U = 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right,
      _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits]
  obtain ⟨hM0, hMle⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup U M
  have hunion : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  rw [hrel, hunion] at hidx
  have hsup0 : (U ⊔ M).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hidx
    exact hM0 hidx
  have hle2 : (U ⊔ M).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    have h : 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * (U ⊔ M).index ≤
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [← hidx, ← h4]
      exact hMle
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  obtain ⟨xs, hxs0, hxsS, hxsσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun _ => 1)
    (fun σ => if σ = σ₀ then -1 else 1) (fun _ => one_ne_zero)
    (fun σ => by split_ifs <;> norm_num)
  simp only [mul_one] at hxsS
  have hxsσ₀ : σ₀ xs < 0 := by
    have h := hxsσ σ₀
    rw [if_pos rfl] at h
    linarith
  have hxsσ' : ∀ σ, σ ≠ σ₀ → 0 < σ xs := fun σ hσ => by
    have h := hxsσ σ
    rwa [if_neg hσ, mul_one] at h
  set X : Fˣ := Units.mk0 xs hxs0 with hX
  have hXnot : X ∉ U ⊔ M := by
    intro hXmem
    obtain ⟨y, hyU, z, hzM, hyz⟩ := Subgroup.mem_sup.mp hXmem
    rw [hM, mem_locSq_iff'] at hzM
    have hy : (y : F) = xs / z := by
      rw [eq_div_iff z.ne_zero, ← Units.val_mul, hyz, hX, Units.val_mk0]
    have hzpos : ∀ σ : F →+* ℝ, 0 < σ (z : F) := fun σ => pos_of_isSquare_real_embedding_unit σ z (hzM.2 σ)
    have hpos := H y y.ne_zero (fun v => by
      by_cases hv : v ∈ S
      · right
        apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ y.ne_zero
        rw [hy, map_div₀]
        exact (hxsS v hv).div (hzM.1 v hv)
      · exact hgoodU y hyU v hv) (fun σ hσ => by
        rw [hy, map_div₀]
        exact div_pos (hxsσ' σ hσ) (hzpos σ))
    rw [hy, map_div₀] at hpos
    have := (div_pos_iff_of_pos_right (hzpos σ₀)).mp hpos
    linarith
  have hidx2 : (U ⊔ M).index = 2 := by
    have hne1 : (U ⊔ M).index ≠ 1 := by
      intro h1
      exact hXnot (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top X)
    omega
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v₀
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨xa, hxa0, hxaS, -⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S
    (fun v => if v = v₀ then algebraMap F (v.adicCompletion F) ϖ else 1) (fun _ => 1)
    (fun v => by
      split_ifs
      · exact (map_ne_zero _).mpr hϖ0
      · exact one_ne_zero)
    (fun _ => one_ne_zero)
  have hav₀ : ∃ n : ℤ, v₀.valuation F xa = WithZero.exp (2 * n + 1) := by
    have h := hxaS v₀ hv₀S
    rw [if_pos rfl, ← map_mul] at h
    obtain ⟨n, hn⟩ :=
      exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ (xa * ϖ) (mul_ne_zero hxa0 hϖ0) h
    have hva : v₀.valuation F xa ≠ 0 := (Valuation.ne_zero_iff _).mpr hxa0
    rw [map_mul, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_add] at hn
    have h' := WithZero.exp_injective hn
    refine ⟨n, ?_⟩
    rw [← WithZero.exp_log hva]
    congr 1
    omega
  have haS : ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) xa) := fun v hv hne => by
    have h := hxaS v hv
    rwa [if_neg hne, mul_one] at h
  set A : Fˣ := Units.mk0 xa hxa0 with hA
  obtain ⟨B, hBmem, hBv₀, hBS⟩ : ∃ B : Fˣ, B ∈ U ⊔ M ∧
      (∃ n : ℤ, v₀.valuation F (B : F) = WithZero.exp (2 * n + 1)) ∧
      ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) (B : F)) := by
    by_cases hAmem : A ∈ U ⊔ M
    · exact ⟨A, hAmem, hav₀, haS⟩
    · refine ⟨A * X, (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hAmem hXnot),
        ?_, ?_⟩
      · obtain ⟨m, hm⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ xs hxs0 (hxsS v₀ hv₀S)
        obtain ⟨n, hn⟩ := hav₀
        refine ⟨n + m, ?_⟩
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul, hn, hm,
          ← WithZero.exp_add]
        congr 1
        ring
      · intro v hv hne
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul]
        exact (haS v hv hne).mul (hxsS v hv)
  obtain ⟨u, huU, m, hmM, hum⟩ := Subgroup.mem_sup.mp hBmem
  rw [hM, mem_locSq_iff'] at hmM
  have hum' : (u : F) * m = B := by rw [← Units.val_mul, hum]
  have hu : (u : F) = B / m := by rw [eq_div_iff m.ne_zero, hum']
  refine ⟨u, u.ne_zero, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hBv₀
    obtain ⟨k, hk⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ m m.ne_zero (hmM.1 v₀ hv₀S)
    have hvu : v₀.valuation F (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    have h := congrArg (v₀.valuation F) hum'
    rw [map_mul, hn, hk, ← WithZero.exp_log hvu, ← WithZero.exp_add] at h
    have h' := WithZero.exp_injective h
    refine ⟨n - k, ?_⟩
    rw [← WithZero.exp_log hvu]
    congr 1
    omega
  · intro v hne
    by_cases hv : v ∈ S
    · right
      apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ u.ne_zero
      rw [hu, map_div₀]
      exact (hBS v hv hne).div (hmM.1 v hv)
    · exact hgoodU u huU v hv

end GlobalTheory.QNorm
