import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAdicCompleteOfFgOfNatCastMemStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement

open IsLocalRing TensorProduct

namespace GlobalTheory.NoTangent

open MvPowerSeries

/- English proof (translation)
Establish `h1 : ∀ P : MvPolynomial σ O, E (P : MvPowerSeries σ O) = 0`. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c => rw [MvPolynomial.coe_C]`. Conclude with `hC c`.

Consider the case `add p q hp hq => rw [MvPolynomial.coe_add, map_add, hp, hq, add_zero]`. Consider the case `mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hmul, hp, hX]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ h ∈ Ideal.span (Set.range fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)), φ₀ h = 0 ∧ E h = 0`. Introduce `h hh`.

Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Conclude with `⟨ha j, by simp only [map_sub, hX, hC, sub_zero]⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]`. Consider the case `smul s x _ hx => simp [hmul, hx.1, hx.2]`. Take `⟨P, hP⟩` from `hP g`. Use `(h2 _ hP).2` as an intermediate fact. Rewrite `this` using `[map_sub, h1, sub_zero]`. Then use the resulting hypothesis.
-/
theorem leibniz_eq_zero {O C σ : Type} [CommRing O] [CommRing C]
    (φ₀ : MvPowerSeries σ O →+* C) (E : MvPowerSeries σ O →+ C) (a : σ → O)
    (hmul : ∀ g h, E (g * h) = φ₀ g * E h + φ₀ h * E g)
    (hC : ∀ c, E (MvPowerSeries.C c) = 0) (hX : ∀ j, E (X j) = 0)
    (ha : ∀ j, φ₀ (X j - MvPowerSeries.C (a j)) = 0)
    (hP : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O,
      g - (P : MvPowerSeries σ O) ∈
        Ideal.span (Set.range fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)))
    (g : MvPowerSeries σ O) : E g = 0 := by
  have h1 : ∀ P : MvPolynomial σ O, E (P : MvPowerSeries σ O) = 0 := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.coe_C]; exact hC c
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add, hp, hq, add_zero]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hmul, hp, hX]; simp
  have h2 : ∀ h ∈ Ideal.span (Set.range fun j =>
      (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)), φ₀ h = 0 ∧ E h = 0 := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨ha j, by simp only [map_sub, hX, hC, sub_zero]⟩
    | zero => simp
    | add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]
    | smul s x _ hx => simp [hmul, hx.1, hx.2]
  obtain ⟨P, hP⟩ := hP g
  have := (h2 _ hP).2
  rwa [map_sub, h1, sub_zero] at this

/- English proof (translation)
Set `L : MvPolynomial.restrictTotalDegree σ O M →ₗ[O] (MvPowerSeries σ O ⧸ I)` to `(Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := O) O).toLinearMap ∘ₗ (MvPolynomial.restrictTotalDegree σ O M).subtype`. Use `Module.Finite.of_surjective L ?_` and prove the remaining obligations. Introduce `q`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨P, hP, hg⟩` from `h g`.

Use `⟨⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩, ?_⟩` and prove the remaining obligations. Establish `: L ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ = Ideal.Quotient.mk I (P : MvPowerSeries σ O)`. Simplify using `[L]`. Rewrite using `[this]`. Conclude with `(Ideal.Quotient.eq.2 hg).symm`.
-/
theorem finite_quotient {O σ : Type} [CommRing O] [Finite σ] (I : Ideal (MvPowerSeries σ O))
    (M : ℕ) (h : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O, P.totalDegree ≤ M ∧
      g - (P : MvPowerSeries σ O) ∈ I) : Module.Finite O (MvPowerSeries σ O ⧸ I) := by
  let L : MvPolynomial.restrictTotalDegree σ O M →ₗ[O] (MvPowerSeries σ O ⧸ I) :=
    (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := O) O).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ O M).subtype
  refine Module.Finite.of_surjective L ?_
  intro q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨P, hP, hg⟩ := h g
  refine ⟨⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩, ?_⟩
  have : L ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ =
      Ideal.Quotient.mk I (P : MvPowerSeries σ O) := by
    simp [L]
  rw [this]
  exact (Ideal.Quotient.eq.2 hg).symm

/- English proof (translation)
Introduce `C _ _ _ v O _ _ hv p hp hc J hJ hJt hpJ σ _ n e f M N U hN hM hdet φ φ' hfst`. Establish `hJc` using `GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J hJ hJt hpJ`. Establish `hfin` using `finite_quotient _ M (GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J hJ hJc σ (Fin n) f M hM)`. Set `I` to `Ideal.span (Set.range f)`. Set `ψ : MvPowerSeries σ O →ₐ[O] DualNumber C` to `φ.comp (Ideal.Quotient.mkₐ O I)`.

Set `ψ' : MvPowerSeries σ O →ₐ[O] DualNumber C` to `φ'.comp (Ideal.Quotient.mkₐ O I)`. Set `φ₀ : MvPowerSeries σ O →ₐ[O] C` to `(TrivSqZeroExt.fstHom O C C).comp ψ`. Establish `h0 : ∀ g, (ψ g).fst = φ₀ g` using `fun g => rfl`. Establish `h0' : ∀ g, (ψ' g).fst = φ₀ g` using `fun g => (hfst _).symm`. Establish `hψI : ∀ g ∈ I, ψ g = 0` using `fun g hg => by`.

Simplify using `[ψ, Ideal.Quotient.eq_zero_iff_mem.2 hg]`. Establish `hψI' : ∀ g ∈ I, ψ' g = 0` using `fun g hg => by`. Simplify using `[ψ', Ideal.Quotient.eq_zero_iff_mem.2 hg]`. Establish `hCa : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c` using `fun c => rfl`. Establish `hle : ∀ g, v (φ₀ g) ≤ 1`.

Introduce `g`. Establish `h1 : IsIntegral O (Ideal.Quotient.mkₐ O I g)` using `Algebra.IsIntegral.isIntegral _`. Establish `h2` using `h1.map ((TrivSqZeroExt.fstHom O C C).comp φ)`. Conclude with `hv.mem_of_integral h2`. Use `choose a ha using fun j => hv.exists_of_le_one (hle (X j))`.

Set `K : Ideal (MvPowerSeries σ O)` to `{ carrier := {g | v (φ₀ g) < 1} add_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at hx hy ⊢`. Conclude with `v.map_add_lt hx hy`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun s x hx => by`.

Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (hle s) zero_le hx }`. Establish `hK : ∀ g, g ∈ K ↔ v (φ₀ g) < 1` using `fun g => Iff.rfl`. Establish `hJK : J ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O)`. Introduce `c hc`.

Rewrite using `[Ideal.mem_comap, hK, hCa, AlgHom.commutes]`. Use `lt_of_le_of_ne (hv.map_le_one c) fun h => hJt ?_` and prove the remaining obligations. Conclude with `J.eq_top_of_isUnit_mem hc (hv.isUnit_of_one' h)`. Establish `hIK : I ≤ K`. Introduce `g hg`.

Rewrite using `[hK, ← h0, hψI g hg]`. Simplify using the standard rewrite rules. Establish `hXK : ∀ j, X j ∈ K`. Introduce `j`. Establish `h1 : (X j : MvPowerSeries σ O) ^ M ∈ K` using `(hM.trans (sup_le hIK (Ideal.map_le_iff_le_comap.2 hJK))) (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M)`.

Rewrite `h1` using `[hK, map_pow, map_pow]`. Use `lt_of_le_of_ne (hle _) fun h => ?_` and prove the remaining obligations. Simplify using `[h] at h1`. Set `J' : Ideal O` to `J ⊔ Ideal.span (Set.range a)`. Establish `hJ' : J'.FG` using `Submodule.FG.sup hJ (Submodule.fg_span (Set.finite_range a))`.

Establish `hJ'K : J' ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O)`. Use `sup_le hJK (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, hK, hCa, AlgHom.commutes, ha]`. Conclude with `hXK j`.

Establish `hJ't : J' ≠ ⊤`. Introduce `h`. Establish `: (1 : O) ∈ J'` using `h ▸ Submodule.mem_top`. Establish `h2` using `hJ'K this`. Rewrite `h2` using `[Ideal.mem_comap, hK]`.

Simplify using `at h2`. Establish `hJ'c` using `GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J' hJ' hJ't (Ideal.mem_sup_left hpJ)`. Establish `hP` using `GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J' hJ' hJ'c σ σ (fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)) 1 (by`. Rewrite using `[pow_one, Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `: (X j : MvPowerSeries σ O) = (X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j)` using `by ring`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩) (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))))`. Set `d : Fin n → C` to `fun j => (ψ' (X (e j))).snd - (ψ (X (e j))).snd`. Set `E : MvPowerSeries σ O →+ C` to `{ toFun := fun g => (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j map_zero' := by simp map_add' := fun x y => by`.

Simplify using `only [map_add, TrivSqZeroExt.snd_add, add_mul, Finset.sum_add_distrib]`. Use `ring }`. Establish `hE : ∀ g, E g = (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j` using `fun g => rfl`. Establish `hE0 : ∀ g, E g = 0`. Use `leibniz_eq_zero (φ₀ : MvPowerSeries σ O →+* C) E a ?_ ?_ ?_ ?_ (fun g => (hP g).imp fun P h => h.2)` and prove the remaining obligations.

Introduce `g h`. Simplify using `only [hE, map_mul, DualNumber.snd_mul, h0, h0', Derivation.leibniz, smul_eq_mul, map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c`. Rewrite using `[hE]`.

Simplify using `only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, sub_zero]`. Rewrite using `[hCa, AlgHom.commutes, AlgHom.commutes, sub_self]`. Introduce `s`. Take `⟨k, rfl⟩` from `e.surjective s`. Rewrite using `[hE, Finset.sum_eq_single k]`.

Simplify using `[d, pderiv_X]`. Introduce `j _ hj`. Simplify using `[pderiv_X, hj, hj.symm]`. Simplify using the standard rewrite rules. Introduce `j`.

Rewrite using `[RingHom.coe_coe, map_sub, hCa, AlgHom.commutes, ha, sub_self]`. Establish `hd : d = 0`. Set `A : Matrix (Fin n) (Fin n) (MvPowerSeries σ O)` to `Matrix.of fun i j : Fin n => MvPowerSeries.pderiv O (e j) (f i)`. Use `Matrix.eq_zero_of_mulVec_eq_zero (M := (φ₀ : MvPowerSeries σ O →+* C).mapMatrix A) ?_ ?_` and prove the remaining obligations. Rewrite using `[← RingHom.map_det, hdet, map_mul, map_natCast]`.

Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 hN) (U.isUnit.map _).ne_zero`. Use function extensionality and compare the values at `i`. Establish `h1` using `hE0 (f i)`. Establish `hi : f i ∈ I` using `Ideal.subset_span ⟨i, rfl⟩`. Rewrite `h1` using `[hE, hψI _ hi, hψI' _ hi, sub_self, zero_sub, neg_eq_zero]`.

Simplify `h1` using `[Matrix.mulVec, dotProduct, A]`. Use `AlgHom.ext fun q => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Use `TrivSqZeroExt.ext (hfst _) ?_` and prove the remaining obligations. Establish `h1` using `hE0 g`.

Rewrite `h1` using `[hE, hd]`. Simplify using `only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at h1`. Conclude with `(sub_eq_zero.1 h1).symm`.
-/
theorem algHom_dualNumber_ext : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ O) (M N : ℕ) (U : (MvPowerSeries σ O)ˣ), N ≠ 0 → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) J → Matrix.det (Matrix.of fun i j : Fin n => MvPowerSeries.pderiv O (e j) (f i)) = (N : MvPowerSeries σ O) * U → ∀ φ φ' : (MvPowerSeries σ O ⧸ Ideal.span (Set.range f)) →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ' := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJt hpJ σ _ n e f M N U hN hM hdet φ φ' hfst
  classical
  have hJc := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J hJ hJt hpJ
  have hfin := finite_quotient _ M (GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J hJ hJc σ (Fin n) f M hM)
  let I := Ideal.span (Set.range f)
  let ψ : MvPowerSeries σ O →ₐ[O] DualNumber C := φ.comp (Ideal.Quotient.mkₐ O I)
  let ψ' : MvPowerSeries σ O →ₐ[O] DualNumber C := φ'.comp (Ideal.Quotient.mkₐ O I)
  let φ₀ : MvPowerSeries σ O →ₐ[O] C := (TrivSqZeroExt.fstHom O C C).comp ψ
  have h0 : ∀ g, (ψ g).fst = φ₀ g := fun g => rfl
  have h0' : ∀ g, (ψ' g).fst = φ₀ g := fun g => (hfst _).symm
  have hψI : ∀ g ∈ I, ψ g = 0 := fun g hg => by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hψI' : ∀ g ∈ I, ψ' g = 0 := fun g hg => by
    simp [ψ', Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hCa : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c := fun c => rfl
  have hle : ∀ g, v (φ₀ g) ≤ 1 := by
    intro g
    have h1 : IsIntegral O (Ideal.Quotient.mkₐ O I g) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map ((TrivSqZeroExt.fstHom O C C).comp φ)
    exact hv.mem_of_integral h2
  choose a ha using fun j => hv.exists_of_le_one (hle (X j))
  let K : Ideal (MvPowerSeries σ O) :=
    { carrier := {g | v (φ₀ g) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
        exact v.map_add_lt hx hy
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle s) zero_le hx }
  have hK : ∀ g, g ∈ K ↔ v (φ₀ g) < 1 := fun g => Iff.rfl
  have hJK : J ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    intro c hc
    rw [Ideal.mem_comap, hK, hCa, AlgHom.commutes]
    refine lt_of_le_of_ne (hv.map_le_one c) fun h => hJt ?_
    exact J.eq_top_of_isUnit_mem hc (hv.isUnit_of_one' h)
  have hIK : I ≤ K := by
    intro g hg
    rw [hK, ← h0, hψI g hg]; simp
  have hXK : ∀ j, X j ∈ K := by
    intro j
    have h1 : (X j : MvPowerSeries σ O) ^ M ∈ K :=
      (hM.trans (sup_le hIK (Ideal.map_le_iff_le_comap.2 hJK)))
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M)
    rw [hK, map_pow, map_pow] at h1
    refine lt_of_le_of_ne (hle _) fun h => ?_
    simp [h] at h1
  let J' : Ideal O := J ⊔ Ideal.span (Set.range a)
  have hJ' : J'.FG := Submodule.FG.sup hJ (Submodule.fg_span (Set.finite_range a))
  have hJ'K : J' ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    refine sup_le hJK (Ideal.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hK, hCa, AlgHom.commutes, ha]
    exact hXK j
  have hJ't : J' ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J' := h ▸ Submodule.mem_top
    have h2 := hJ'K this
    rw [Ideal.mem_comap, hK] at h2
    simp at h2
  have hJ'c := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J' hJ' hJ't (Ideal.mem_sup_left hpJ)
  have hP := GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J' hJ' hJ'c σ σ
    (fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (X j : MvPowerSeries σ O) =
          (X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))))
  let d : Fin n → C := fun j => (ψ' (X (e j))).snd - (ψ (X (e j))).snd
  let E : MvPowerSeries σ O →+ C :=
    { toFun := fun g => (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, TrivSqZeroExt.snd_add, add_mul, Finset.sum_add_distrib]; ring }
  have hE : ∀ g, E g = (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j :=
    fun g => rfl
  have hE0 : ∀ g, E g = 0 := by
    refine leibniz_eq_zero (φ₀ : MvPowerSeries σ O →+* C) E a ?_ ?_ ?_ ?_
      (fun g => (hP g).imp fun P h => h.2)
    · intro g h
      simp only [hE, map_mul, DualNumber.snd_mul, h0, h0', Derivation.leibniz, smul_eq_mul,
        map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        RingHom.coe_coe]
      ring
    · intro c
      rw [hE]
      simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, sub_zero]
      rw [hCa, AlgHom.commutes, AlgHom.commutes, sub_self]
    · intro s
      obtain ⟨k, rfl⟩ := e.surjective s
      rw [hE, Finset.sum_eq_single k]
      · simp [d, pderiv_X]
      · intro j _ hj
        simp [pderiv_X, hj, hj.symm]
      · simp
    · intro j
      rw [RingHom.coe_coe, map_sub, hCa, AlgHom.commutes, ha, sub_self]
  have hd : d = 0 := by
    let A : Matrix (Fin n) (Fin n) (MvPowerSeries σ O) :=
      Matrix.of fun i j : Fin n => MvPowerSeries.pderiv O (e j) (f i)
    refine Matrix.eq_zero_of_mulVec_eq_zero
      (M := (φ₀ : MvPowerSeries σ O →+* C).mapMatrix A) ?_ ?_
    · rw [← RingHom.map_det, hdet, map_mul, map_natCast]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (U.isUnit.map _).ne_zero
    · funext i
      have h1 := hE0 (f i)
      have hi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [hE, hψI _ hi, hψI' _ hi, sub_self, zero_sub, neg_eq_zero] at h1
      simpa [Matrix.mulVec, dotProduct, A] using h1
  refine AlgHom.ext fun q => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine TrivSqZeroExt.ext (hfst _) ?_
  have h1 := hE0 g
  rw [hE, hd] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  exact (sub_eq_zero.1 h1).symm

end GlobalTheory.NoTangent
