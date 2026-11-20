import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.GlobalTheory
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section

variable {K : Type} [Field K]

/- English proof (translation)
Use `conv_lhs => rw [Y.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, smul_monomial, smul_eq_mul, mul_one]`.
-/
theorem linMap_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Y : MvPolynomial σ K) :
    T Y = ∑ ζ ∈ Y.support, Y.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Y.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

end

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

/- English proof (translation)
Introduce `ζ hζ` and use `hZ ζ (support_dg_subset f Z hζ)`.
-/
theorem Good.dg {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (f : D.EM → K) :
    D.Good p (Formalism.MainNotions.PlaneGram.dg f Z) := fun ζ hζ => hZ ζ (support_dg_subset f Z hζ)

/- English proof (translation)
Rewrite using `[mem_Yset]`. Apply the tactic sequence `rintro (⟨m', h⟩ | ⟨b, -, h⟩ | ⟨m', -, h⟩) <;> simp [mb, mw, mlab, mtp] at h`.
-/
theorem mlab_notMem_Yset (j : Fin D.J) (m : Fin D.r) (t : D.Tau) : D.mlab t ∉ D.Yset j m := by
  rw [mem_Yset]
  rintro (⟨m', h⟩ | ⟨b, -, h⟩ | ⟨m', -, h⟩) <;> simp [mb, mw, mlab, mtp] at h

end TwistData

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

/- English proof (translation)
Introduce `ζ'`. Distinguish the cases in `h : ζ' ∈ (Pj (monomial ζ 1)).support`. Establish `hb : D.SameBlockAlt ζ ζ'` using `hP1 ζ ζ' h`. Establish `h1` using `D.blk_fact hD hr hζ hb`. Conclude with `vge_mono v (by linarith) (hP2 ζ hζ ζ')`.

Rewrite using `[notMem_support_iff.mp h]`. Conclude with `vge_zero v _`.
-/
theorem cge_Pj_monomial (hD : DVRHyp v p) (D : TwistData K) (hr : 1 ≤ D.r)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (ζ : D.EM) (hζ : D.GoodE p ζ) :
    cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (monomial ζ 1)) := by
  intro ζ'
  by_cases h : ζ' ∈ (Pj (monomial ζ 1)).support
  · have hb : D.SameBlockAlt ζ ζ' := hP1 ζ ζ' h
    have h1 := D.blk_fact hD hr hζ hb
    exact vge_mono v (by linarith) (hP2 ζ hζ ζ')
  · rw [notMem_support_iff.mp h]; exact vge_zero v _

/- English proof (translation)
Rewrite using `[linMap_eq_sum Pj Y]`. Use `TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _` and prove the remaining obligations. Introduce `ζ' hζ'`. Conclude with `TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')`.
-/
theorem good_Pj (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by
  rw [linMap_eq_sum Pj Y]
  refine TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _
  intro ζ' hζ'
  exact TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')

/- English proof (translation)
Take `⟨hP1, hP2, hP3, -, hP5⟩` from `hPj`. Establish `hp : 2 ≤ p` using `two_le_p hD`. Establish `hr : 1 ≤ D.r` using `hV.1`. Establish `hJ : 1 ≤ D.J` using `hV.2.1`. Establish `hkap` using `D.kapD_ge_one hp hr hJ`.

Establish `hDm` using `D.Dm_nonneg hp hr h1`. Establish `hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2` using `by linarith`. Use `⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z hZi hZg`. Rewrite using `[← cge_zero_iff_Integral]`.

Establish `hY : cge v 0 (dg gp Z)`. Use `cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ)) ((cge_zero_iff_Integral v Z).mpr hZi)` as an intermediate fact. Simplify using `using this`. Establish `hYg : D.Good p (dg gp Z)` using `TwistData.Good.dg D hZg gp`. Establish `hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z))`.

Rewrite using `[linMap_eq_sum Pj (dg gp Z)]`. Use `cge_sum v _ _ fun ζ hζ => ?_` and prove the remaining obligations. Use `cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))` as an intermediate fact. Simplify using `using this`. Establish `hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z)))`.

Use `cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY` as an intermediate fact. Simplify using `using this`. Use `cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG` as an intermediate fact. Use `cge_mono v ?_ this` and prove the remaining obligations. Use `Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `Z hZg`. Conclude with `TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm`. Introduce `Z _ j i`. Conclude with `(hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2`.

Introduce `Z _ j m θ _ hZ`. Establish `a1` using `(hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1`. Establish `a2` using `hP5 j m _ _ a1`. Establish `a3` using `(hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2`. Conclude with `vala_mono (by linarith) a3`.
-/
theorem omega_clauses (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hPj : (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z)))
    (gp gm : D.EM → K) (hgp : ∀ ζ, 0 ≤ v (gp ζ)) (hgm : ∀ ζ, 0 ≤ v (gm ζ))
    (hcost : ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)) :
    ((⌈D.Dm p C0 + D.kapD p / 2⌉₊ : ℕ) : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
    (∀ Z, Integral v Z → D.Good p Z →
      Integral v (((p : K) ^ ⌈D.Dm p C0 + D.kapD p / 2⌉₊) • dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → D.Good p (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
      vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (dg gm (Pj (dg gp Z)))) := by
  obtain ⟨hP1, hP2, hP3, -, hP5⟩ := hPj
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2 := by linarith
  refine ⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩
  · intro Z hZi hZg
    rw [← cge_zero_iff_Integral]
    have hY : cge v 0 (dg gp Z) := by
      have := cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ))
        ((cge_zero_iff_Integral v Z).mpr hZi)
      simpa using this
    have hYg : D.Good p (dg gp Z) := TwistData.Good.dg D hZg gp
    have hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z)) := by
      rw [linMap_eq_sum Pj (dg gp Z)]
      refine cge_sum v _ _ fun ζ hζ => ?_
      have := cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))
      simpa using this
    have hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z))) := by
      have := cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY
      simpa using this
    have := cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG
    refine cge_mono v ?_ this
    have := Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)
    linarith
  · intro Z hZg
    exact TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm
  · intro Z _ j i
    exact (hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2
  · intro Z _ j m θ _ hZ
    have a1 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1
    have a2 := hP5 j m _ _ a1
    have a3 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2
    exact vala_mono (by linarith) a3

end Main

end Formalism.MainNotions.PlaneGram
