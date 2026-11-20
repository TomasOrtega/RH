import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Gen

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/- English proof (translation)
Rewrite using `[← FractionalIdeal.spanSingleton_mul_spanSingleton]`. Conclude with `FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)`.
-/
theorem idxChange_cnt_mul (v : HeightOneSpectrum R) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x * y)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x) +
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ y) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

/- English proof (translation)
Rewrite using `[FractionalIdeal.spanSingleton_one]`. Conclude with `FractionalIdeal.count_one K v`.
-/
theorem idxChange_cnt_one (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (1 : K)) = 0 := by
  rw [FractionalIdeal.spanSingleton_one]
  exact FractionalIdeal.count_one K v

/- English proof (translation)
Rewrite using `[FractionalIdeal.count_coe K v hJ]`. Assume the negation of the conclusion as `hne`. Establish `hne' : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0`. Conclude with `hne` after adjusting the coercions. Establish `hd` using `(Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne'`.

Rewrite `hd` using `[Ideal.dvd_iff_le]`. Conclude with `h hd`.
-/
theorem idxChange_cnt_ideal_zero (v : HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ 0)
    (h : ¬ J ≤ v.asIdeal) : FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K v hJ]
  by_contra hne
  have hne' : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by
    exact_mod_cast hne
  have hd := (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne'
  rw [Ideal.dvd_iff_le] at hd
  exact h hd

/- English proof (translation)
Establish `h1` using `FractionalIdeal.count_mono K v ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ) ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h)`. Rewrite `h1` using `[FractionalIdeal.count_self]`. Then use the resulting hypothesis.
-/
theorem idxChange_cnt_ideal_pos (v : HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ 0)
    (h : J ≤ v.asIdeal) : 1 ≤ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) := by
  have h1 := FractionalIdeal.count_mono K v
    ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h)
  rwa [FractionalIdeal.count_self] at h1

/- English proof (translation)
The claim follows from `(FractionalIdeal.coeIdeal_span_singleton (S := R⁰) (P := K) a).symm`.
-/
theorem idxChange_span_alg (a : R) :
    FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) =
      ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ K) :=
  (FractionalIdeal.coeIdeal_span_singleton (S := R⁰) (P := K) a).symm

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ v.asIdeal.zero_mem)`. Rewrite using `[idxChange_span_alg]`. Use `idxChange_cnt_ideal_zero v _ ?_ ?_` and prove the remaining obligations. Simplify `hs0` using `[Ideal.span_singleton_eq_bot]`. Rewrite using `[Ideal.span_singleton_le_iff_mem]` and apply the resulting hypothesis.
-/
theorem idxChange_cnt_unit (v : HeightOneSpectrum R) {s : R} (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  rw [idxChange_span_alg]
  refine idxChange_cnt_ideal_zero v _ ?_ ?_
  · simpa [Ideal.span_singleton_eq_bot] using hs0
  · rwa [Ideal.span_singleton_le_iff_mem]

/- English proof (translation)
Rewrite using `[idxChange_span_alg]`. Use `idxChange_cnt_ideal_pos v _ ?_ ?_` and prove the remaining obligations. Simplify `ha` using `[Ideal.span_singleton_eq_bot]`. Rewrite using `[Ideal.span_singleton_le_iff_mem]` and apply the resulting hypothesis.
-/
theorem idxChange_cnt_mem (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) (hp : a ∈ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  rw [idxChange_span_alg]
  refine idxChange_cnt_ideal_pos v _ ?_ ?_
  · simpa [Ideal.span_singleton_eq_bot] using ha
  · rwa [Ideal.span_singleton_le_iff_mem]

/- English proof (translation)
Rewrite using `[idxChange_span_alg]`. Conclude with `FractionalIdeal.count_coe_nonneg K v _`.
-/
theorem idxChange_cnt_nonneg (v : HeightOneSpectrum R) (a : R) :
    0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  rw [idxChange_span_alg]
  exact FractionalIdeal.count_coe_nonneg K v _

/- English proof (translation)
Establish `hp1 : v.asIdeal ≠ ⊤` using `v.isPrime.ne_top`. Take `⟨ϖ, hϖ1, hϖ2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot hp1 1`. Rewrite `hϖ1` using `[pow_one]`. Establish `hϖ0 : ϖ ≠ 0` using `fun h => hϖ2 (h ▸ Ideal.zero_mem _)`. Establish `hdvd : v.asIdeal ∣ Ideal.span {ϖ}`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hϖ1`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJp : ¬ J ≤ v.asIdeal`. Introduce `hle`.

Apply `hϖ2` to reduce the goal to its premises. Establish `: Ideal.span {ϖ} ≤ v.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self ϖ)`.

Establish `hspan0 : Ideal.span {ϖ} ≠ 0` using `by simpa [Ideal.span_singleton_eq_bot] using hϖ0`. Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Apply `hspan0` to reduce the goal to its premises. Rewrite using `[hJ]`.

Simplify using the standard rewrite rules. Take `⟨t, htJ, htp⟩` from `Set.not_subset.mp hJp`. Use `⟨ϖ, hϖ1, hϖ0, ?_, t, htp, ?_⟩` and prove the remaining obligations. Rewrite using `[idxChange_span_alg, hJ, FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K v ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr v.ne_bot) ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ0), FractionalIdeal.count_self, idxChange_cnt_ideal_zero v J hJ0 hJp]`. Simplify using the standard rewrite rules.

Introduce `x hx`. Establish `hmem : x * t ∈ Ideal.span {ϖ}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul hx htJ`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp hmem`.

Conclude with `⟨u, by rw [mul_comm t x, ← hu, mul_comm]⟩`.
-/
theorem idxChange_unif (v : HeightOneSpectrum R) :
    ∃ ϖ : R, ϖ ∈ v.asIdeal ∧ ϖ ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1 ∧
      ∃ t : R, t ∉ v.asIdeal ∧ ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u := by
  have hp1 : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  obtain ⟨ϖ, hϖ1, hϖ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot hp1 1
  rw [pow_one] at hϖ1
  have hϖ0 : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Ideal.zero_mem _)
  have hdvd : v.asIdeal ∣ Ideal.span {ϖ} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hϖ1
  obtain ⟨J, hJ⟩ := hdvd
  have hJp : ¬ J ≤ v.asIdeal := by
    intro hle
    apply hϖ2
    have : Ideal.span {ϖ} ≤ v.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self ϖ)
  have hspan0 : Ideal.span {ϖ} ≠ 0 := by simpa [Ideal.span_singleton_eq_bot] using hϖ0
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hspan0
    rw [hJ]; simp
  obtain ⟨t, htJ, htp⟩ := Set.not_subset.mp hJp
  refine ⟨ϖ, hϖ1, hϖ0, ?_, t, htp, ?_⟩
  · rw [idxChange_span_alg, hJ, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K v ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr v.ne_bot)
        ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ0),
      FractionalIdeal.count_self, idxChange_cnt_ideal_zero v J hJ0 hJp]
    simp
  · intro x hx
    have hmem : x * t ∈ Ideal.span {ϖ} := by
      rw [hJ]; exact Ideal.mul_mem_mul hx htJ
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨u, by rw [mul_comm t x, ← hu, mul_comm]⟩

end Gen

section Lat

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

def idxChangeAct (e : Fin d → Fin d → K) (γ : Matrix (Fin d) (Fin d) K) : Fin d → Fin d → K :=
  fun i => ∑ k, γ k i • e k

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [idxChangeAct, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem idxChange_act_mul (e : Fin d → Fin d → K) (A B : Matrix (Fin d) (Fin d) K) :
    idxChangeAct (idxChangeAct e A) B = idxChangeAct e (A * B) := by
  funext i
  simp only [idxChangeAct, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[idxChangeAct, Matrix.one_apply]`.
-/
theorem idxChange_act_one (e : Fin d → Fin d → K) : idxChangeAct e 1 = e := by
  funext i
  simp [idxChangeAct, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[idxChangeAct, Matrix.diagonal_apply, ite_smul]`.
-/
theorem idxChange_act_diagonal (e : Fin d → Fin d → K) (g : Fin d → K) :
    idxChangeAct e (Matrix.diagonal g) = fun k => g k • e k := by
  funext i
  simp [idxChangeAct, Matrix.diagonal_apply, ite_smul]

/- English proof (translation)
Simplify using `only [idxChangeAct, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem idxChange_sum_smul_act (e : Fin d → Fin d → K) (γ : Matrix (Fin d) (Fin d) K)
    (g : Fin d → K) : ∑ i, g i • idxChangeAct e γ i = ∑ k, (γ *ᵥ g) k • e k := by
  simp only [idxChangeAct, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/- English proof (translation)
Rewrite `he`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[idxChange_sum_smul_act]`. Establish `h0 : γ *ᵥ g = 0` using `funext (he _ hg)`. Use `Matrix.eq_zero_of_mulVec_eq_zero hγ h0` as an intermediate fact.

Introduce `i`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem idxChange_linIndep_act {e : Fin d → Fin d → K} (he : LinearIndependent K e)
    {γ : Matrix (Fin d) (Fin d) K} (hγ : γ.det ≠ 0) : LinearIndependent K (idxChangeAct e γ) := by
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  rw [idxChange_sum_smul_act] at hg
  have h0 : γ *ᵥ g = 0 := funext (he _ hg)
  have := Matrix.eq_zero_of_mulVec_eq_zero hγ h0
  intro i
  rw [this]; rfl

/- English proof (translation)
Introduce `h0`. Take `⟨g, hg0, hg⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Rewrite `he` using `[Fintype.linearIndependent_iff]`. Apply `hg0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Use `he g ?_ i` and prove the remaining obligations. Rewrite using `[idxChange_sum_smul_act, hg]`. Simplify using the standard rewrite rules.
-/
theorem idxChange_det_ne_zero {e : Fin d → Fin d → K} {γ : Matrix (Fin d) (Fin d) K}
    (he : LinearIndependent K (idxChangeAct e γ)) : γ.det ≠ 0 := by
  intro h0
  obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [Fintype.linearIndependent_iff] at he
  apply hg0
  funext i
  refine he g ?_ i
  rw [idxChange_sum_smul_act, hg]
  simp

/- English proof (translation)
Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `h` using `linearIndependent_iff_card_eq_finrank_span.mp he`. Rewrite `h` using `[Set.finrank]`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem idxChange_span_top {e : Fin d → Fin d → K} (he : LinearIndependent K e) :
    Submodule.span K (Set.range e) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := linearIndependent_iff_card_eq_finrank_span.mp he
  rw [Set.finrank] at h
  rw [← h]
  simp

/- English proof (translation)
Apply `indexBasic_locS_top (K := K)` to reduce the goal to its premises. Rewrite using `[Submodule.span_span_of_tower]`. Conclude with `idxChange_span_top he`.
-/
theorem idxChange_locS_top {e : Fin d → Fin d → K} (he : LinearIndependent K e) :
    locS (nonZeroDivisors R) (Submodule.span R (Set.range e)) = ⊤ := by
  apply indexBasic_locS_top (K := K)
  rw [Submodule.span_span_of_tower]
  exact idxChange_span_top he

/- English proof (translation)
Unfold `locLen`. Rewrite using `[hX, hY]`.
-/
theorem idxChange_locLen_congr (p : Ideal R) [p.IsPrime] {X X' Y Y' : Submodule R (Fin d → K)}
    (hX : localization₂ p X = localization₂ p X') (hY : localization₂ p Y = localization₂ p Y') : locLen p X Y = locLen p X' Y' := by
  unfold locLen
  rw [hX, hY]

/- English proof (translation)
Establish `hinf : localization₂ p (A ⊓ B) = localization₂ p (A' ⊓ B')`. Unfold `localization₂ at hA hB ⊢`. Rewrite using `[locBasic_locS_inf, locBasic_locS_inf, hA, hB]`. Unfold `lidx`. Rewrite using `[idxChange_locLen_congr p hA hinf, idxChange_locLen_congr p hB hinf]`.
-/
theorem idxChange_lidx_congr (p : Ideal R) [p.IsPrime] {A A' B B' : Submodule R (Fin d → K)}
    (hA : localization₂ p A = localization₂ p A') (hB : localization₂ p B = localization₂ p B') : lidx p A B = lidx p A' B' := by
  have hinf : localization₂ p (A ⊓ B) = localization₂ p (A' ⊓ B') := by
    unfold localization₂ at hA hB ⊢
    rw [locBasic_locS_inf, locBasic_locS_inf, hA, hB]
  unfold lidx
  rw [idxChange_locLen_congr p hA hinf, idxChange_locLen_congr p hB hinf]

/- English proof (translation)
Unfold `lidx`. Conclude with `sub_self _`.
-/
theorem idxChange_lidx_self (p : Ideal R) [p.IsPrime] (A : Submodule R (Fin d → K)) :
    lidx p A A = 0 := by
  unfold lidx
  exact sub_self _

/- English proof (translation)
Use `set A := Submodule.span R (Set.range e)`. Use `set B := Submodule.span R (Set.range f)`. Use `set C := Submodule.span R (Set.range g)`. Establish `hfin : ∀ X Y : Submodule R (Fin d → K), X.FG → locS (nonZeroDivisors R) Y = ⊤ → Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤`. Introduce `X Y hX hY`.

Take `⟨c, hc, hcY⟩` from `indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)`. Conclude with `Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hc hcY)`. Establish `hAt : locS (nonZeroDivisors R) A = ⊤` using `idxChange_locS_top he`. Establish `hBt : locS (nonZeroDivisors R) B = ⊤` using `idxChange_locS_top hf`. Establish `hCt : locS (nonZeroDivisors R) C = ⊤` using `idxChange_locS_top hg`.

Establish `hAfg : A.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hBfg : B.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hCfg : C.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤`. Rewrite using `[locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]`.

Simplify using the standard rewrite rules. Establish `hAD` using `hfin A _ hAfg hDt`. Establish `hBD` using `hfin B _ hBfg hDt`. Establish `hCD` using `hfin C _ hCfg hDt`. Rewrite using `[indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hAD hCD, indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) (le_trans inf_le_left inf_le_right) hAD hBD, indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le …`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxChange_lidx_add (p : Ideal R) [p.IsPrime] {e f g : Fin d → Fin d → K}
    (he : LinearIndependent K e) (hf : LinearIndependent K f) (hg : LinearIndependent K g) :
    lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range g)) =
      lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range f)) +
        lidx p (Submodule.span R (Set.range f)) (Submodule.span R (Set.range g)) := by
  set A := Submodule.span R (Set.range e)
  set B := Submodule.span R (Set.range f)
  set C := Submodule.span R (Set.range g)
  have hfin : ∀ X Y : Submodule R (Fin d → K), X.FG → locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨c, hc, hcY⟩ :=
      indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hc hcY)
  have hAt : locS (nonZeroDivisors R) A = ⊤ := idxChange_locS_top he
  have hBt : locS (nonZeroDivisors R) B = ⊤ := idxChange_locS_top hf
  have hCt : locS (nonZeroDivisors R) C = ⊤ := idxChange_locS_top hg
  have hAfg : A.FG := Submodule.fg_span (Set.finite_range _)
  have hBfg : B.FG := Submodule.fg_span (Set.finite_range _)
  have hCfg : C.FG := Submodule.fg_span (Set.finite_range _)
  have hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
    rw [locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]
    simp
  have hAD := hfin A _ hAfg hDt
  have hBD := hfin B _ hBfg hDt
  have hCD := hfin C _ hCfg hDt
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring

/- English proof (translation)
Establish `key : ∀ N : Submodule R (Fin d → K), locS S N = locS S (locS T N)`. Introduce `N`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `locBasic_locS_mono S (locBasic_le_locS T N)`. Introduce `x hx`.

Take `⟨s, hs, hsx⟩` from `locBasic_mem_locS.mp hx`. Take `⟨t, ht, htx⟩` from `locBasic_mem_locS.mp hsx`. Conclude with `locBasic_mem_locS.mpr ⟨t * s, S.mul_mem (hTS ht) hs, by rwa [mul_smul]⟩`. Rewrite using `[key L, key M, h]`.
-/
theorem idxChange_locS_of_le {S T : Submonoid R} (hTS : T ≤ S) {L M : Submodule R (Fin d → K)}
    (h : locS T L = locS T M) : locS S L = locS S M := by
  have key : ∀ N : Submodule R (Fin d → K), locS S N = locS S (locS T N) := by
    intro N
    apply le_antisymm
    · exact locBasic_locS_mono S (locBasic_le_locS T N)
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
      obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp hsx
      exact locBasic_mem_locS.mpr ⟨t * s, S.mul_mem (hTS ht) hs, by rwa [mul_smul]⟩
  rw [key L, key M, h]

end Lat

section Scale

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

def IdxChangeP (v : HeightOneSpectrum R) (γ : Matrix (Fin d) (Fin d) K) : Prop :=
  ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    lidx v.asIdeal (Submodule.span R (Set.range e))
        (Submodule.span R (Set.range (idxChangeAct e γ))) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ γ.det)

/- English proof (translation)
Introduce `e he`. Rewrite using `[idxChange_act_one, idxChange_lidx_self, Matrix.det_one, idxChange_cnt_one]`.
-/
theorem indexChange_one (v : HeightOneSpectrum R) : IdxChangeP (d := d) v (1 : Matrix _ _ K) := by
  intro e he
  rw [idxChange_act_one, idxChange_lidx_self, Matrix.det_one, idxChange_cnt_one]

/- English proof (translation)
Introduce `e he`. Establish `heA` using `idxChange_linIndep_act he hA`. Establish `hadd` using `idxChange_lidx_add v.asIdeal he heA (idxChange_linIndep_act heA hB)`. Rewrite `hadd` using `[PA e he, PB _ heA, idxChange_act_mul]`. Rewrite using `[hadd, Matrix.det_mul, idxChange_cnt_mul v hA hB]`.
-/
theorem indexChange_mul (v : HeightOneSpectrum R) {A B : Matrix (Fin d) (Fin d) K}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (PA : IdxChangeP v A) (PB : IdxChangeP v B) :
    IdxChangeP v (A * B) := by
  intro e he
  have heA := idxChange_linIndep_act he hA
  have hadd := idxChange_lidx_add v.asIdeal he heA (idxChange_linIndep_act heA hB)
  rw [PA e he, PB _ heA, idxChange_act_mul] at hadd
  rw [hadd, Matrix.det_mul, idxChange_cnt_mul v hA hB]

abbrev idxChangeDg (i : Fin d) (x : K) : Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal (Function.update (1 : Fin d → K) i x)

/- English proof (translation)
Rewrite using `[Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]`. Simplify using the standard rewrite rules.
-/
theorem idxChange_det_Dg (i : Fin d) (x : K) : (idxChangeDg i x).det = x := by
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

/- English proof (translation)
Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hk]`.
-/
theorem idxChange_Dg_mul (i : Fin d) (x y : K) :
    idxChangeDg i x * idxChangeDg i y = idxChangeDg i (x * y) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_of_ne hk]

/- English proof (translation)
Rewrite using `[idxChange_act_diagonal]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[algebraMap_smul]`.

Simplify using `[Function.update_of_ne hk]`.
-/
theorem idxChange_act_Dg_alg (e : Fin d → Fin d → K) (i : Fin d) (a : R) :
    idxChangeAct e (idxChangeDg i (algebraMap R K a)) = Function.update e i (a • e i) := by
  rw [idxChange_act_diagonal]
  funext k
  by_cases hk : k = i
  · subst hk; simp [algebraMap_smul]
  · simp [Function.update_of_ne hk]

/- English proof (translation)
Introduce `e he`. Establish `hdy : (idxChangeDg i y).det ≠ 0` using `by rw [idxChange_det_Dg]; exact hy`. Establish `hdx : (idxChangeDg i x).det ≠ 0` using `by rw [idxChange_det_Dg]; exact hx`. Establish `hey` using `idxChange_linIndep_act he hdy`. Establish `hadd` using `idxChange_lidx_add v.asIdeal he hey (idxChange_linIndep_act hey hdx)`.

Rewrite `hadd` using `[Px _ hey, idxChange_act_mul, idxChange_Dg_mul, mul_comm y x, Pxy e he]`. Rewrite `hadd`, the goal using `[idxChange_det_Dg]`. Rewrite `hadd` using `[idxChange_det_Dg, idxChange_cnt_mul v hx hy]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem indexChange_cancel (v : HeightOneSpectrum R) (i : Fin d) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) (Px : IdxChangeP v (idxChangeDg i x)) (Pxy : IdxChangeP v (idxChangeDg i (x * y))) :
    IdxChangeP v (idxChangeDg i y) := by
  intro e he
  have hdy : (idxChangeDg i y).det ≠ 0 := by rw [idxChange_det_Dg]; exact hy
  have hdx : (idxChangeDg i x).det ≠ 0 := by rw [idxChange_det_Dg]; exact hx
  have hey := idxChange_linIndep_act he hdy
  have hadd := idxChange_lidx_add v.asIdeal he hey (idxChange_linIndep_act hey hdx)
  rw [Px _ hey, idxChange_act_mul, idxChange_Dg_mul, mul_comm y x, Pxy e he] at hadd
  rw [idxChange_det_Dg] at hadd ⊢
  rw [idxChange_det_Dg, idxChange_cnt_mul v hx hy] at hadd
  linarith

/- English proof (translation)
Introduce `e he`. Rewrite using `[idxChange_act_Dg_alg, idxChange_det_Dg, idxChange_cnt_unit v hs]`. Establish `hloc : localization₂ v.asIdeal (Submodule.span R (Set.range e)) = localization₂ v.asIdeal (Submodule.span R (Set.range (Function.update e i (s • e i))))`. Unfold `localization₂`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `hsub : Submodule.span R (Set.range e) ≤ locS v.asIdeal.primeCompl (Submodule.span R (Set.range (Function.update e i (s • e i))))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Conclude with `⟨s, hs, Submodule.subset_span ⟨k, by simp⟩⟩`. Conclude with `locBasic_le_locS _ _ (Submodule.subset_span ⟨k, by simp [Function.update_of_ne hk]⟩)`. Combine the equalities or inequalities in the displayed calculation. Apply `locBasic_locS_mono` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Rewrite using `[Function.update_of_ne hk]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Rewrite using `[idxChange_lidx_congr v.asIdeal hloc rfl, idxChange_lidx_self]`.
-/
theorem indexChange_unit (v : HeightOneSpectrum R) (i : Fin d) {s : R} (hs : s ∉ v.asIdeal) :
    IdxChangeP v (idxChangeDg i (algebraMap R K s)) := by
  intro e he
  rw [idxChange_act_Dg_alg, idxChange_det_Dg, idxChange_cnt_unit v hs]
  have hloc : localization₂ v.asIdeal (Submodule.span R (Set.range e)) =
      localization₂ v.asIdeal (Submodule.span R (Set.range (Function.update e i (s • e i)))) := by
    unfold localization₂
    apply le_antisymm
    · have hsub : Submodule.span R (Set.range e) ≤
          locS v.asIdeal.primeCompl (Submodule.span R (Set.range (Function.update e i (s • e i)))) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        by_cases hk : k = i
        · subst hk
          exact ⟨s, hs, Submodule.subset_span ⟨k, by simp⟩⟩
        · exact locBasic_le_locS _ _ (Submodule.subset_span ⟨k, by simp [Function.update_of_ne hk]⟩)
      calc locS v.asIdeal.primeCompl (Submodule.span R (Set.range e))
          ≤ locS v.asIdeal.primeCompl (locS v.asIdeal.primeCompl
              (Submodule.span R (Set.range (Function.update e i (s • e i))))) :=
            locBasic_locS_mono _ hsub
        _ = _ := locBasic_locS_idem _ _
    · apply locBasic_locS_mono
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = i
      · subst hk
        simp only [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rw [Function.update_of_ne hk]
        exact Submodule.subset_span ⟨k, rfl⟩
  rw [idxChange_lidx_congr v.asIdeal hloc rfl, idxChange_lidx_self]

end Scale

section Pi

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

/- English proof (translation)
Introduce `e he`. Rewrite using `[idxChange_act_Dg_alg, idxChange_det_Dg, hcnt]`. Establish `: Nonempty (Fin d)` using `⟨i⟩`. Use `set p := v.asIdeal with hpdef`. Use `set upd := Function.update e i (ϖ • e i) with hupd`.

Use `set A := Submodule.span R (Set.range e) with hAdef`. Use `set B := Submodule.span R (Set.range upd) with hBdef`. Establish `hupdi : upd i = ϖ • e i` using `by simp [upd]`. Establish `hupdk : ∀ k, k ≠ i → upd k = e k` using `fun k hk => by simp [upd, Function.update_of_ne hk]`. Establish `hBA : B ≤ A`.

Rewrite using `[hBdef, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[hupdi]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[hupdk k hk]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Set `be` to `basisOfLinearIndependentOfCardEqFinrank he (by simp)`. Establish `hbe : ∀ k, be k = e k` using `fun k => by`.

Simplify using `[be, coe_basisOfLinearIndependentOfCardEqFinrank]`. Set `f : (Fin d → K) →ₗ[R] K` to `(be.coord i).restrictScalars R`. Establish `hf : ∀ k, f (e k) = if k = i then 1 else 0`. Introduce `k`. Simplify using `only [f, LinearMap.restrictScalars_apply, Basis.coord_apply, ← hbe, Basis.repr_self]`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Establish `hcoord : ∀ x ∈ B, ∃ u : R, f x = algebraMap R K (ϖ * u)`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[hupdi, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one, mul_one]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[hupdk k hk, hf, if_neg hk]`.

Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, hu⟩` from `hx`. Take `⟨u', hu'⟩` from `hy`.

Conclude with `⟨u + u', by rw [map_add, hu, hu', mul_add, map_add]⟩`. Consider the case `smul a x _ hx`. Take `⟨u, hu⟩` from `hx`. Conclude with `⟨a * u, by rw [map_smul, hu, Algebra.smul_def, ← map_mul]; ring_nf⟩`. Establish `hK1 : ∀ r ∈ p, r • e i ∈ localization₂ p B`.

Introduce `r hr`. Take `⟨u, hu⟩` from `ht r hr`. Use `⟨t, htp, ?_⟩` and prove the remaining obligations. Establish `: t • r • e i = u • upd i`. Rewrite using `[hupdi, smul_smul, smul_smul, hu, mul_comm]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hK2 : ∀ r : R, r • e i ∈ localization₂ p B → r ∈ p`. Introduce `r hr`. Take `⟨s, hs, hsr⟩` from `hr`.

Take `⟨u, hu⟩` from `hcoord _ hsr`. Rewrite `hu` using `[smul_smul, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one]`. Establish `h2 : s * r = ϖ * u` using `IsFractionRing.injective R K hu`. Establish `hmem : s * r ∈ p`. Rewrite using `[h2]`.

Conclude with `Ideal.mul_mem_right _ _ (by`. Assume the negation of the conclusion as `hϖ`. Use `idxChange_cnt_unit (K := K) v hϖ` as an intermediate fact. Rewrite `this` using `[hcnt]`. Conclude with `one_ne_zero this)`.

Break down `v.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `absurd h hs`. Conclude with `h`. Establish `hei : e i ∈ localization₂ p A` using `locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `Q` to `↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype`.

Set `φ : R →ₗ[R] Q` to `LinearMap.toSpanSingleton R Q (Submodule.Quotient.mk ⟨e i, hei⟩)`. Establish `hker : LinearMap.ker φ = p`. Use extensionality with `r`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, SetLike.val_smul]`. Conclude with `⟨hK2 r, hK1 r⟩`.

Establish `hsurj : Function.Surjective φ`. Introduce `q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H y`. Take `⟨s, hs, hsy⟩` from `y.2`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hsy`. Take `⟨t', i', hi', hti⟩` from `v.isMaximal.exists_inv hs`. Use `⟨t' * c i, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, SetLike.val_smul]`. Apply `indexBasic_smul_locP p B hs` to reduce the goal to its premises.

Establish `hsc : s * (t' * c i) = c i - i' * c i` using `by linear_combination (c i) * hti`. Establish `key : s • ((t' * c i) • e i - (y : Fin d → K)) = -((i' * c i) • e i + ∑ k ∈ Finset.univ.erase i, c k • e k)`. Rewrite using `[smul_sub, ← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_smul, hsc, sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`.

Use `(localization₂ p B).neg_mem ((localization₂ p B).add_mem (hK1 _ (Ideal.mul_mem_right _ _ hi')) ?_)` and prove the remaining obligations. Use `(localization₂ p B).sum_mem fun k hk => ?_` and prove the remaining obligations. Establish `hki : k ≠ i` using `Finset.ne_of_mem_erase hk`. Use `locBasic_le_locS _ _ ?_` and prove the remaining obligations. Rewrite using `[← hupdk k hki]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Establish `: IsSimpleModule R (R ⧸ p)` using `isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp v.isMaximal)`. Establish `hlen : Module.length R Q = 1`. Rewrite using `[← (LinearMap.quotKerEquivOfSurjective φ hsurj).length_eq, (Submodule.quotEquivOfEq _ _ hker).length_eq]`. Conclude with `Module.length_eq_one R _`.

Unfold `lidx`. Rewrite using `[inf_eq_right.mpr hBA, indexBasic_locLen_self]`. Unfold `locLen`. Rewrite using `[hlen]`. Simplify using the standard rewrite rules.
-/
theorem indexChange_uniformizer (v : HeightOneSpectrum R) (i : Fin d) {ϖ t : R}
    (hcnt : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1)
    (htp : t ∉ v.asIdeal) (ht : ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u) :
    IdxChangeP v (idxChangeDg i (algebraMap R K ϖ)) := by
  intro e he
  rw [idxChange_act_Dg_alg, idxChange_det_Dg, hcnt]
  have : Nonempty (Fin d) := ⟨i⟩
  set p := v.asIdeal with hpdef
  set upd := Function.update e i (ϖ • e i) with hupd
  set A := Submodule.span R (Set.range e) with hAdef
  set B := Submodule.span R (Set.range upd) with hBdef
  have hupdi : upd i = ϖ • e i := by simp [upd]
  have hupdk : ∀ k, k ≠ i → upd k = e k := fun k hk => by simp [upd, Function.update_of_ne hk]
  have hBA : B ≤ A := by
    rw [hBdef, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk; rw [hupdi]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [hupdk k hk]; exact Submodule.subset_span ⟨k, rfl⟩

  let be := basisOfLinearIndependentOfCardEqFinrank he (by simp)
  have hbe : ∀ k, be k = e k := fun k => by
    simp [be, coe_basisOfLinearIndependentOfCardEqFinrank]
  let f : (Fin d → K) →ₗ[R] K := (be.coord i).restrictScalars R
  have hf : ∀ k, f (e k) = if k = i then 1 else 0 := by
    intro k
    simp only [f, LinearMap.restrictScalars_apply, Basis.coord_apply, ← hbe, Basis.repr_self]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  have hcoord : ∀ x ∈ B, ∃ u : R, f x = algebraMap R K (ϖ * u) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hk : k = i
      · subst hk
        refine ⟨1, ?_⟩
        rw [hupdi, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one, mul_one]
      · refine ⟨0, ?_⟩
        rw [hupdk k hk, hf, if_neg hk]; simp
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨u', hu'⟩ := hy
      exact ⟨u + u', by rw [map_add, hu, hu', mul_add, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨a * u, by rw [map_smul, hu, Algebra.smul_def, ← map_mul]; ring_nf⟩
  have hK1 : ∀ r ∈ p, r • e i ∈ localization₂ p B := by
    intro r hr
    obtain ⟨u, hu⟩ := ht r hr
    refine ⟨t, htp, ?_⟩
    have : t • r • e i = u • upd i := by
      rw [hupdi, smul_smul, smul_smul, hu, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hK2 : ∀ r : R, r • e i ∈ localization₂ p B → r ∈ p := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := hr
    obtain ⟨u, hu⟩ := hcoord _ hsr
    rw [smul_smul, map_smul, hf, if_pos rfl, Algebra.smul_def, mul_one] at hu
    have h2 : s * r = ϖ * u := IsFractionRing.injective R K hu
    have hmem : s * r ∈ p := by
      rw [h2]
      exact Ideal.mul_mem_right _ _ (by
        by_contra hϖ
        have := idxChange_cnt_unit (K := K) v hϖ
        rw [hcnt] at this
        exact one_ne_zero this)
    rcases v.isPrime.mem_or_mem hmem with h | h
    · exact absurd h hs
    · exact h
  have hei : e i ∈ localization₂ p A := locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let Q := ↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype
  let φ : R →ₗ[R] Q := LinearMap.toSpanSingleton R Q (Submodule.Quotient.mk ⟨e i, hei⟩)
  have hker : LinearMap.ker φ = p := by
    ext r
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      SetLike.val_smul]
    exact ⟨hK2 r, hK1 r⟩
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨s, hs, hsy⟩ := y.2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hsy
      obtain ⟨t', i', hi', hti⟩ := v.isMaximal.exists_inv hs
      refine ⟨t' * c i, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, SetLike.val_smul]
      apply indexBasic_smul_locP p B hs
      have hsc : s * (t' * c i) = c i - i' * c i := by linear_combination (c i) * hti
      have key : s • ((t' * c i) • e i - (y : Fin d → K)) =
          -((i' * c i) • e i + ∑ k ∈ Finset.univ.erase i, c k • e k) := by
        rw [smul_sub, ← hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_smul, hsc,
          sub_smul]
        abel
      rw [key]
      refine (localization₂ p B).neg_mem ((localization₂ p B).add_mem (hK1 _ (Ideal.mul_mem_right _ _ hi')) ?_)
      refine (localization₂ p B).sum_mem fun k hk => ?_
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      refine locBasic_le_locS _ _ ?_
      rw [← hupdk k hki]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have : IsSimpleModule R (R ⧸ p) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp v.isMaximal)
  have hlen : Module.length R Q = 1 := by
    rw [← (LinearMap.quotKerEquivOfSurjective φ hsurj).length_eq,
      (Submodule.quotEquivOfEq _ _ hker).length_eq]
    exact Module.length_eq_one R _
  unfold lidx
  rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
  unfold locLen
  rw [hlen]
  simp

end Pi

section Main

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

/- English proof (translation)
Take `⟨ϖ, _, hϖ0, hcntϖ, t, htp, ht⟩` from `idxChange_unif (K := K) v`. Establish `hinj` using `IsFractionRing.injective R K`. Establish `hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0` using `fun b hb => (map_ne_zero_iff _ hinj).mpr hb`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `a ha hc`. Establish `hap : a ∉ v.asIdeal`. Introduce `h`. Use `idxChange_cnt_mem (K := K) v ha h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `indexChange_unit v i hap`. Consider the case `succ n ih`. Introduce `a ha hc`. Establish `hap : a ∈ v.asIdeal`.

Assume the negation of the conclusion as `h`. Rewrite `hc` using `[idxChange_cnt_unit v h]`. Use linear arithmetic over natural numbers and integers. Take `⟨a', ha'⟩` from `ht a hap`. Establish `ht0 : t ≠ 0` using `fun h => htp (h ▸ v.asIdeal.zero_mem)`.

Establish `ha'0 : a' ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha'` using `[mul_zero]`. Break down `mul_eq_zero.mp ha' with h | h` into its components or cases. Conclude with `ht0 h`.

Conclude with `ha h`. Establish `hc' : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a')) = n`. Establish `e1` using `idxChange_cnt_mul v (hne t ht0) (hne a ha)`. Establish `e2` using `idxChange_cnt_mul v (hne ϖ hϖ0) (hne a' ha'0)`. Rewrite `e1` using `[← map_mul, ha', map_mul]`.

Rewrite `e2` using `[e1, idxChange_cnt_unit v htp, hc, hcntϖ]`. Move the coercions through the operations in `at e2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `Pa'` using `ih a' ha'0 hc'`. Establish `Pϖa' : IdxChangeP v (idxChangeDg i (algebraMap R K ϖ * algebraMap R K a'))`.

Rewrite using `[← idxChange_Dg_mul]`. Conclude with `indexChange_mul v (by rw [idxChange_det_Dg]; exact hne ϖ hϖ0) (by rw [idxChange_det_Dg]; exact hne a' ha'0) (indexChange_uniformizer v i hcntϖ htp ht) Pa'`. Establish `Pta : IdxChangeP v (idxChangeDg i (algebraMap R K t * algebraMap R K a))`. Rewrite using `[← map_mul, ha', map_mul]`. Conclude with `Pϖa'`.

Conclude with `indexChange_cancel v i (hne t ht0) (hne a ha) (indexChange_unit v i htp) Pta`.
-/
theorem indexChange_integral (v : HeightOneSpectrum R) (i : Fin d) :
    ∀ n : ℕ, ∀ a : R, a ≠ 0 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) = n →
      IdxChangeP v (idxChangeDg i (algebraMap R K a)) := by
  obtain ⟨ϖ, _, hϖ0, hcntϖ, t, htp, ht⟩ := idxChange_unif (K := K) v
  have hinj := IsFractionRing.injective R K
  have hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).mpr hb
  intro n
  induction n with
  | zero =>
    intro a ha hc
    have hap : a ∉ v.asIdeal := by
      intro h
      have := idxChange_cnt_mem (K := K) v ha h
      omega
    exact indexChange_unit v i hap
  | succ n ih =>
    intro a ha hc
    have hap : a ∈ v.asIdeal := by
      by_contra h
      rw [idxChange_cnt_unit v h] at hc
      omega
    obtain ⟨a', ha'⟩ := ht a hap
    have ht0 : t ≠ 0 := fun h => htp (h ▸ v.asIdeal.zero_mem)
    have ha'0 : a' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ha'
      rcases mul_eq_zero.mp ha' with h | h
      · exact ht0 h
      · exact ha h
    have hc' : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a')) =
        n := by
      have e1 := idxChange_cnt_mul v (hne t ht0) (hne a ha)
      have e2 := idxChange_cnt_mul v (hne ϖ hϖ0) (hne a' ha'0)
      rw [← map_mul, ha', map_mul] at e1
      rw [e1, idxChange_cnt_unit v htp, hc, hcntϖ] at e2
      push_cast at e2
      linarith
    have Pa' := ih a' ha'0 hc'
    have Pϖa' : IdxChangeP v (idxChangeDg i (algebraMap R K ϖ * algebraMap R K a')) := by
      rw [← idxChange_Dg_mul]
      exact indexChange_mul v (by rw [idxChange_det_Dg]; exact hne ϖ hϖ0)
        (by rw [idxChange_det_Dg]; exact hne a' ha'0) (indexChange_uniformizer v i hcntϖ htp ht) Pa'
    have Pta : IdxChangeP v (idxChangeDg i (algebraMap R K t * algebraMap R K a)) := by
      rw [← map_mul, ha', map_mul]; exact Pϖa'
    exact indexChange_cancel v i (hne t ht0) (hne a ha) (indexChange_unit v i htp) Pta

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective R K`. Establish `hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0` using `fun b hb => (map_ne_zero_iff _ hinj).mpr hb`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Apply `hx` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `hP : ∀ c : R, c ≠ 0 → IdxChangeP v (idxChangeDg i (algebraMap R K c))` using `fun c hc => indexChange_integral v i _ c hc (Int.toNat_of_nonneg (idxChange_cnt_nonneg v c)).symm`. Establish `Pbx : IdxChangeP v (idxChangeDg i (algebraMap R K b * (algebraMap R K a / algebraMap R K b)))`.

Rewrite using `[mul_div_cancel₀ _ (hne b hb0)]`. Conclude with `hP a ha0`. Conclude with `indexChange_cancel v i (hne b hb0) hx (hP b hb0) Pbx`.
-/
theorem indexChange_scalar (v : HeightOneSpectrum R) (i : Fin d) {x : K} (hx : x ≠ 0) :
    IdxChangeP v (idxChangeDg i x) := by
  have hinj := IsFractionRing.injective R K
  have hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).mpr hb
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp
  have hP : ∀ c : R, c ≠ 0 → IdxChangeP v (idxChangeDg i (algebraMap R K c)) := fun c hc =>
    indexChange_integral v i _ c hc (Int.toNat_of_nonneg (idxChange_cnt_nonneg v c)).symm
  have Pbx : IdxChangeP v
      (idxChangeDg i (algebraMap R K b * (algebraMap R K a / algebraMap R K b))) := by
    rw [mul_div_cancel₀ _ (hne b hb0)]; exact hP a ha0
  exact indexChange_cancel v i (hne b hb0) hx (hP b hb0) Pbx

/- English proof (translation)
It suffices to establish `h : ∀ s : Finset (Fin d), IdxChangeP v (Matrix.diagonal fun k => if k ∈ s then g k else 1) by simpa using h Finset.univ`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using indexChange_one (K := K) (d := d) v`. Consider the case `insert i s hi ih`.

Establish `heq : Matrix.diagonal (fun k => if k ∈ insert i s then g k else 1) = Matrix.diagonal (fun k => if k ∈ s then g k else 1) * idxChangeDg i (g i)`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[hi]`. Simplify using `[hk]`. Rewrite using `[heq]`. Use `indexChange_mul v ?_ (by rw [idxChange_det_Dg]; exact hg i) ih (indexChange_scalar v i (hg i))` and prove the remaining obligations.

Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => by split_ifs`. Conclude with `hg k`. Conclude with `one_ne_zero`.
-/
theorem indexChange_diagonal (v : HeightOneSpectrum R) (g : Fin d → K) (hg : ∀ k, g k ≠ 0) :
    IdxChangeP v (Matrix.diagonal g) := by
  suffices h : ∀ s : Finset (Fin d), IdxChangeP v (Matrix.diagonal fun k => if k ∈ s then g k else 1)
    by simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using indexChange_one (K := K) (d := d) v
  | insert i s hi ih =>
    have heq : Matrix.diagonal (fun k => if k ∈ insert i s then g k else 1) =
        Matrix.diagonal (fun k => if k ∈ s then g k else 1) * idxChangeDg i (g i) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [hi]
      · simp [hk]
    rw [heq]
    refine indexChange_mul v ?_ (by rw [idxChange_det_Dg]; exact hg i) ih (indexChange_scalar v i (hg i))
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by
      split_ifs
      · exact hg k
      · exact one_ne_zero

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul, Finset.sum_add_distrib, ite_smul, add_comm]`. Simplify using `[idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, ite_smul, hk, Ne.symm hk]`.
-/
theorem indexChangeAction_transvection (e : Fin d → Fin d → K) {i j : Fin d} (hij : i ≠ j) :
    idxChangeAct e (Matrix.transvection i j (1 : K)) = Function.update e j (e j + e i) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, add_smul, Finset.sum_add_distrib, ite_smul, add_comm]
  · simp [idxChangeAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      ite_smul, hk, Ne.symm hk]

/- English proof (translation)
Introduce `e he`. Rewrite using `[Matrix.det_transvection_of_ne i j hij, idxChange_cnt_one, indexChangeAction_transvection e hij]`. Establish `hspan : Submodule.span R (Set.range (Function.update e j (e j + e i))) = Submodule.span R (Set.range e)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `Submodule.add_mem _ (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Function.update_of_ne hk]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Establish `h1 : Function.update e k (e k + e i) k ∈ Submodule.span R (Set.range (Function.update e k (e k + e i)))` using `Submodule.subset_span ⟨k, rfl⟩`. Establish `h2 : Function.update e k (e k + e i) i ∈ Submodule.span R (Set.range (Function.update e k (e k + e i)))` using `Submodule.subset_span ⟨i, rfl⟩`. Rewrite `h1` using `[Function.update_self]`. Rewrite `h2` using `[Function.update_of_ne hij]`.

Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Establish `h1 : Function.update e j (e j + e i) k ∈ Submodule.span R (Set.range (Function.update e j (e j + e i)))` using `Submodule.subset_span ⟨k, rfl⟩`. Rewrite `h1` using `[Function.update_of_ne hk]`. Then use the resulting hypothesis. Rewrite using `[hspan, idxChange_lidx_self]`.
-/
theorem indexChangeLocal_transvection (v : HeightOneSpectrum R) {i j : Fin d} (hij : i ≠ j) :
    IdxChangeP v (Matrix.transvection i j (1 : K)) := by
  intro e he
  rw [Matrix.det_transvection_of_ne i j hij, idxChange_cnt_one, indexChangeAction_transvection e hij]
  have hspan : Submodule.span R (Set.range (Function.update e j (e j + e i))) =
      Submodule.span R (Set.range e) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · subst hk
        simp only [Function.update_self]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨k, rfl⟩)
          (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Function.update_of_ne hk]; exact Submodule.subset_span ⟨k, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · subst hk
        have h1 : Function.update e k (e k + e i) k ∈
            Submodule.span R (Set.range (Function.update e k (e k + e i))) :=
          Submodule.subset_span ⟨k, rfl⟩
        have h2 : Function.update e k (e k + e i) i ∈
            Submodule.span R (Set.range (Function.update e k (e k + e i))) :=
          Submodule.subset_span ⟨i, rfl⟩
        rw [Function.update_self] at h1
        rw [Function.update_of_ne hij] at h2
        have := Submodule.sub_mem _ h1 h2
        simpa using this
      · have h1 : Function.update e j (e j + e i) k ∈
            Submodule.span R (Set.range (Function.update e j (e j + e i))) :=
          Submodule.subset_span ⟨k, rfl⟩
        rwa [Function.update_of_ne hk] at h1
  rw [hspan, idxChange_lidx_self]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `h`. Simplify using `[Matrix.transvection, hij, Function.update_of_ne (Ne.symm hij)]`.

Establish `hs : ∀ x : K, Matrix.single i j x a b = 0`. Introduce `x`. Rewrite using `[Matrix.single_apply]`. Use `split_ifs with h'`. Conclude with `absurd ⟨h'.1.symm, h'.2.symm⟩ h`.

Both sides reduce to the same expression. Simplify using `only [Matrix.transvection, Matrix.add_apply, hs, add_zero]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Distinguish the cases in `ha : a = i`.

Substitute `ha` using the available equality. Simplify using `[hc]`. Simplify using `[Function.update_of_ne ha]`. Simplify using `[hab]`.
-/
theorem idxChange_transvection_conj {i j : Fin d} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    Matrix.transvection i j c =
      idxChangeDg i c * Matrix.transvection i j (1 : K) * idxChangeDg i c⁻¹ := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.transvection, hij, Function.update_of_ne (Ne.symm hij)]
  · have hs : ∀ x : K, Matrix.single i j x a b = 0 := by
      intro x
      rw [Matrix.single_apply]
      split_ifs with h'
      · exact absurd ⟨h'.1.symm, h'.2.symm⟩ h
      · rfl
    simp only [Matrix.transvection, Matrix.add_apply, hs, add_zero]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = i
      · subst ha; simp [hc]
      · simp [Function.update_of_ne ha]
    · simp [hab]

/- English proof (translation)
Break down `t with ⟨i, j, hij, c⟩` into its components or cases. Rewrite using `[Matrix.TransvectionStruct.toMatrix_mk]`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Rewrite using `[Matrix.transvection_zero]`.

Conclude with `indexChange_one v`. Rewrite using `[idxChange_transvection_conj hij hc]`. Establish `hd1 : (idxChangeDg i c).det ≠ 0` using `by rw [idxChange_det_Dg]; exact hc`. Establish `hd2 : (Matrix.transvection i j (1 : K)).det ≠ 0`. Rewrite using `[Matrix.det_transvection_of_ne i j hij]`.

Conclude with `one_ne_zero`. Establish `hd3 : (idxChangeDg i c⁻¹).det ≠ 0` using `by rw [idxChange_det_Dg]; exact inv_ne_zero hc`. Use `indexChange_mul v (by rw [Matrix.det_mul]; exact mul_ne_zero hd1 hd2) hd3 (indexChange_mul v hd1 hd2 (indexChange_scalar v i hc) (indexChangeLocal_transvection v hij)) (indexChange_scalar v i (inv_ne_zero hc))` and prove the remaining obligations.
-/
theorem indexChange_transvection (v : HeightOneSpectrum R) (t : Matrix.TransvectionStruct (Fin d) K) :
    IdxChangeP v t.toMatrix := by
  rcases t with ⟨i, j, hij, c⟩
  rw [Matrix.TransvectionStruct.toMatrix_mk]
  by_cases hc : c = 0
  · subst hc
    rw [Matrix.transvection_zero]
    exact indexChange_one v
  rw [idxChange_transvection_conj hij hc]
  have hd1 : (idxChangeDg i c).det ≠ 0 := by rw [idxChange_det_Dg]; exact hc
  have hd2 : (Matrix.transvection i j (1 : K)).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero
  have hd3 : (idxChangeDg i c⁻¹).det ≠ 0 := by rw [idxChange_det_Dg]; exact inv_ne_zero hc
  refine indexChange_mul v (by rw [Matrix.det_mul]; exact mul_ne_zero hd1 hd2) hd3
    (indexChange_mul v hd1 hd2 (indexChange_scalar v i hc) (indexChangeLocal_transvection v hij))
    (indexChange_scalar v i (inv_ne_zero hc))

/- English proof (translation)
Use `Matrix.diagonal_transvection_induction_of_det_ne_zero (IdxChangeP v) γ hγ ?_ (indexChange_transvection v) (fun A B hA hB PA PB => indexChange_mul v hA hB PA PB)` and prove the remaining obligations. Introduce `D hD`. Use `indexChange_diagonal v D fun k => ?_` and prove the remaining obligations. Rewrite `hD` using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)`.
-/
theorem indexChange_of_det_ne_zero (v : HeightOneSpectrum R) (γ : Matrix (Fin d) (Fin d) K) (hγ : γ.det ≠ 0) :
    IdxChangeP v γ := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (IdxChangeP v) γ hγ ?_
    (indexChange_transvection v) (fun A B hA hB PA PB => indexChange_mul v hA hB PA PB)
  intro D hD
  refine indexChange_diagonal v D fun k => ?_
  rw [Matrix.det_diagonal] at hD
  exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)

end Main

section Final

open NumberField

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold `hcompl`. Rewrite using `[Submonoid.closure_le]`. Introduce and unpack `s ⟨_, hs2⟩`. Use `show s ∉ (conjPl w).asIdeal`. Introduce `hmem`.

Express the relevant statement in the definitionally equal form `s ∈ w.asIdeal.map (cO K) at hmem`. Rewrite `hmem` using `[Ideal.mem_map_of_equiv]`. Take `⟨x, hx, rfl⟩` from `hmem`. Use `hs2 x ?_ hx` and prove the remaining obligations. Use `show (x : K) = star ((cO K x : 𝓞 K) : K)`.

Simplify using `[cO]`.
-/
theorem idxChange_hcompl_le_conj (w : HeightOneSpectrum (𝓞 K)) :
    hcompl (K := K) w.asIdeal ≤ (conjPl w).asIdeal.primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  rintro s ⟨_, hs2⟩
  show s ∉ (conjPl w).asIdeal
  intro hmem
  change s ∈ w.asIdeal.map (cO K) at hmem
  rw [Ideal.mem_map_of_equiv] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  refine hs2 x ?_ hx
  show (x : K) = star ((cO K x : 𝓞 K) : K)
  simp [cO]

/- English proof (translation)
Unfold `idx vw`. Rewrite using `[← idxChange_lidx_congr v.asIdeal rfl hloc]`. Conclude with `indexChange_of_det_ne_zero v γ hγ e he`.
-/
theorem idxChange_at {d : ℕ} (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin d → K))
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (γ : Matrix (Fin d) (Fin d) K)
    (hγ : γ.det ≠ 0)
    (hloc : localization₂ v.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ v.asIdeal L) :
    idx v (Submodule.span (𝓞 K) (Set.range e)) L = vw v γ.det := by
  unfold idx vw
  rw [← idxChange_lidx_congr v.asIdeal rfl hloc]
  exact indexChange_of_det_ne_zero v γ hγ e he

/- English proof (translation)
Introduce `K _ _ _ d L _ e he w γ hloc`. Take `⟨he', hl⟩` from `hloc`. Establish `hdet : γ.det ≠ 0` using `idxChange_det_ne_zero (e := e) (γ := γ) he'`. Unfold `loc at hl`. Establish `h1 : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) = localization₂ w.asIdeal L`.

Unfold `localization₂`. Conclude with `idxChange_locS_of_le (locBasic_hcompl_le (K := K) w.asIdeal) hl`. Establish `h2 : localization₂ (conjPl w).asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) = localization₂ (conjPl w).asIdeal L`. Unfold `localization₂`. Conclude with `idxChange_locS_of_le (idxChange_hcompl_le_conj w) hl`.

Conclude with `⟨idxChange_at w L e he γ hdet h1, idxChange_at (conjPl w) L e he γ hdet h2⟩`.
-/
theorem index_change_formula : IdxChange := by
  intro K _ _ _ d L _ e he w γ hloc
  obtain ⟨he', hl⟩ := hloc
  have hdet : γ.det ≠ 0 := idxChange_det_ne_zero (e := e) (γ := γ) he'
  unfold loc at hl
  have h1 : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ w.asIdeal L := by
    unfold localization₂
    exact idxChange_locS_of_le (locBasic_hcompl_le (K := K) w.asIdeal) hl
  have h2 : localization₂ (conjPl w).asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ (conjPl w).asIdeal L := by
    unfold localization₂
    exact idxChange_locS_of_le (idxChange_hcompl_le_conj w) hl
  exact ⟨idxChange_at w L e he γ hdet h1, idxChange_at (conjPl w) L e he γ hdet h2⟩

end Final

end Formalism.DivisionValues
