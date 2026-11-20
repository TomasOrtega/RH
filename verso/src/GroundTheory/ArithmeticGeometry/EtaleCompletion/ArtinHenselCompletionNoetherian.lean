import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinApproximationData
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open IsLocalRing

/- English proof (translation)
Take `⟨s, hs⟩` from `(isNoetherianRing_iff_ideal_fg R).1 inferInstance I`. Use `set k := s.card`. Set `a : Fin k → R` to `fun i ↦ (s.equivFin.symm i : R)`. Establish `ha : Set.range a = (s : Set R)`. Use extensionality with `r`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(s.equivFin.symm i).2`. Introduce `hr`. Conclude with `⟨s.equivFin ⟨r, hr⟩, by simp [a]⟩`.

Set `P` to `MvPolynomial (Fin k) R`. Set `σ : P →+* R` to `MvPolynomial.eval a`. Set `J` to `MvPolynomial.idealOfVars (Fin k) R`. Establish `hσX : ∀ i, σ (MvPolynomial.X i) = a i` using `fun i ↦ MvPolynomial.eval_X i`. Establish `hJ : J.map σ = I` using `by show Ideal.map σ (Ideal.span (Set.range MvPolynomial.X)) = I`.

Rewrite using `[Ideal.map_span, ← hs, ← ha, ← Set.range_comp]`. Use `congr 1`. Use extensionality with `i`. Simplify using `[hσX]`. Establish `hJn : ∀ n, (J ^ n).map σ = I ^ n` using `fun n ↦ by rw [Ideal.map_pow, hJ]`.

Establish `hσs : Function.Surjective σ` using `fun r ↦ ⟨MvPolynomial.C r, MvPolynomial.eval_C _⟩`. Establish `hle : ∀ n, J ^ n ≤ (I ^ n).comap σ` using `fun n ↦ by`. Rewrite using `[← Ideal.map_le_iff_le_comap, hJn]`. Set `g : (n : ℕ) → AdicCompletion J P →+* R ⧸ I ^ n` to `fun n ↦ (Ideal.quotientMap (I ^ n) σ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom`. Establish `hg : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow I hmn).comp (g n) = g m`.

Introduce `m n hmn`. Use extensionality with `x`. Take `⟨q, hq⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)`. Establish `hq' : AdicCompletion.evalₐ J m x = Ideal.Quotient.mk _ q`. Take `⟨f, rfl⟩` from `AdicCompletion.mk_surjective J P x`.

Rewrite `hq`, the goal using `[AdicCompletion.evalₐ_mk]`. Establish `h1` using `f.property hmn`. Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Establish `h2 : f.val n - q ∈ J ^ m` using `Ideal.pow_le_pow_right hmn (Ideal.Quotient.eq.1 hq.symm)`. Rewrite using `[Ideal.Quotient.eq]`.

Use `Ideal.add_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Simplify using `only [g, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hq, hq', Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]`. Set `ψ` to `AdicCompletion.liftRingHom I g hg`. Establish `hψ : Function.Surjective ψ`.

Introduce `x`. Take `⟨f, rfl⟩` from `AdicCompletion.mk_surjective I R x`. Establish `hd : ∀ j, f.val (j + 1) - f.val j ∈ (J ^ j).map σ`. Introduce `j`. Establish `h1` using `f.property (Nat.le_succ j)`.

Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Rewrite using `[hJn, ← neg_mem_iff, neg_sub]`. Conclude with `h1`. Use `choose Pj hPj hσP using fun j ↦ (Ideal.mem_map_iff_of_surjective σ hσs).1 (hd j)`. Set `Q : ℕ → P` to `fun n ↦ MvPolynomial.C (f.val 0) + ∑ j ∈ Finset.range n, Pj j`.

Establish `hQ : AdicCompletion.IsAdicCauchy J P Q`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]`. Establish `: Q n - Q m = ∑ j ∈ Finset.Ico m n, Pj j`. Simplify using `only [Q, add_sub_add_left_eq_sub]`.

Rewrite using `[Finset.sum_Ico_eq_sub _ hmn]`. Rewrite using `[this]`. Conclude with `Ideal.sum_mem _ fun j hj ↦ Ideal.pow_le_pow_right (Finset.mem_Ico.1 hj).1 (hPj j)`. Set `Qc : AdicCompletion.AdicCauchySequence J P` to `⟨Q, hQ⟩`. Use `⟨AdicCompletion.mk J P Qc, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk]`. Express the relevant statement in the definitionally equal form `Ideal.quotientMap (I ^ n) σ (hle n) (AdicCompletion.evalₐ J n (AdicCompletion.mk J P Qc)) = _`. Rewrite using `[AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]`. Use `congrArg _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (Q n) = f.val n`.

Simplify using `only [Q, map_add, map_sum, hσP]`. Rewrite using `[show σ (MvPolynomial.C (f.val 0)) = f.val 0 from MvPolynomial.eval_C _]`. Rewrite using `[Finset.sum_range_sub (fun j ↦ f.val j) n]`. Expand and normalize the polynomial expressions, which then agree. Establish `: IsNoetherianRing (AdicCompletion J P)` using `isNoetherianRing_of_ringEquiv _ (MvPowerSeries.toAdicCompletionAlgEquiv (Fin k) R).toRingEquiv`.

Conclude with `isNoetherianRing_of_surjective _ _ ψ hψ`.
-/
theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).1 inferInstance I
  set k := s.card
  let a : Fin k → R := fun i ↦ (s.equivFin.symm i : R)
  have ha : Set.range a = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hr
      exact ⟨s.equivFin ⟨r, hr⟩, by simp [a]⟩
  let P := MvPolynomial (Fin k) R
  let σ : P →+* R := MvPolynomial.eval a
  let J := MvPolynomial.idealOfVars (Fin k) R
  have hσX : ∀ i, σ (MvPolynomial.X i) = a i := fun i ↦ MvPolynomial.eval_X i
  have hJ : J.map σ = I := by
    show Ideal.map σ (Ideal.span (Set.range MvPolynomial.X)) = I
    rw [Ideal.map_span, ← hs, ← ha, ← Set.range_comp]
    congr 1
    ext i
    simp [hσX]
  have hJn : ∀ n, (J ^ n).map σ = I ^ n := fun n ↦ by rw [Ideal.map_pow, hJ]
  have hσs : Function.Surjective σ := fun r ↦ ⟨MvPolynomial.C r, MvPolynomial.eval_C _⟩
  have hle : ∀ n, J ^ n ≤ (I ^ n).comap σ := fun n ↦ by
    rw [← Ideal.map_le_iff_le_comap, hJn]
  let g : (n : ℕ) → AdicCompletion J P →+* R ⧸ I ^ n := fun n ↦
    (Ideal.quotientMap (I ^ n) σ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    have hq' : AdicCompletion.evalₐ J m x = Ideal.Quotient.mk _ q := by
      obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective J P x
      rw [AdicCompletion.evalₐ_mk] at hq ⊢
      have h1 := f.property hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      have h2 : f.val n - q ∈ J ^ m := Ideal.pow_le_pow_right hmn (Ideal.Quotient.eq.1 hq.symm)
      rw [Ideal.Quotient.eq]
      have := Ideal.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    simp only [g, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, ← hq, hq', Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  let ψ := AdicCompletion.liftRingHom I g hg
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
    have hd : ∀ j, f.val (j + 1) - f.val j ∈ (J ^ j).map σ := by
      intro j
      have h1 := f.property (Nat.le_succ j)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      rw [hJn, ← neg_mem_iff, neg_sub]
      exact h1
    choose Pj hPj hσP using fun j ↦ (Ideal.mem_map_iff_of_surjective σ hσs).1 (hd j)
    let Q : ℕ → P := fun n ↦ MvPolynomial.C (f.val 0) + ∑ j ∈ Finset.range n, Pj j
    have hQ : AdicCompletion.IsAdicCauchy J P Q := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have : Q n - Q m = ∑ j ∈ Finset.Ico m n, Pj j := by
        simp only [Q, add_sub_add_left_eq_sub]
        rw [Finset.sum_Ico_eq_sub _ hmn]
      rw [this]
      exact Ideal.sum_mem _ fun j hj ↦
        Ideal.pow_le_pow_right (Finset.mem_Ico.1 hj).1 (hPj j)
    let Qc : AdicCompletion.AdicCauchySequence J P := ⟨Q, hQ⟩
    refine ⟨AdicCompletion.mk J P Qc, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk]
    change Ideal.quotientMap (I ^ n) σ (hle n)
      (AdicCompletion.evalₐ J n (AdicCompletion.mk J P Qc)) = _
    rw [AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    refine congrArg _ ?_
    change σ (Q n) = f.val n
    simp only [Q, map_add, map_sum, hσP]
    rw [show σ (MvPolynomial.C (f.val 0)) = f.val 0 from MvPolynomial.eval_C _]
    rw [Finset.sum_range_sub (fun j ↦ f.val j) n]
    ring
  have : IsNoetherianRing (AdicCompletion J P) :=
    isNoetherianRing_of_ringEquiv _ (MvPowerSeries.toAdicCompletionAlgEquiv (Fin k) R).toRingEquiv
  exact isNoetherianRing_of_surjective _ _ ψ hψ

instance instIsNoetherianRingAdicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) :=
  isNoetherianRing_adicCompletion R I

end GroundTheory.Arith.Etale
