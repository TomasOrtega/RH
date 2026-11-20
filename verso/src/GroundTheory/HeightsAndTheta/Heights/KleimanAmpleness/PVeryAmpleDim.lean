import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDimSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDimTie
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AmpleAffineGen

noncomputable section

universe u w

namespace VeryAmpleDim

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
The claim follows from `(Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)`.
-/
theorem mem_sub_of_mem_secs {H : SubSystem k x Ω} {s : Ω} (hs : s ∈ H.secs) (I : Chart x) :
    s ∈ H.sub I :=
  (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)

/- English proof (translation)
Establish `hle : ampleBase (S` using `k) h j ≤ (funField (k := k) h).toSubalgebra := Algebra.adjoin_le (by`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `IntermediateField.subset_adjoin k _ ⟨j, l, hj, rfl⟩)`. Conclude with `hle ha`.
-/
theorem ampleBase_le_funField {r : ℕ} (h : Fin (r + 1) → Ω) {j : Fin (r + 1)} (hj : h j ≠ 0) {a : Ω}
    (ha : a ∈ ampleBase (S := k) h j) : a ∈ funField (k := k) h := by
  have hle : ampleBase (S := k) h j ≤ (funField (k := k) h).toSubalgebra :=
    Algebra.adjoin_le (by
      rintro _ ⟨l, rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨j, l, hj, rfl⟩)
  exact hle ha

/- English proof (translation)
The claim follows from `ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)`.
-/
theorem mem_funField_of_mem_chartRing {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x :=
  ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)

/- English proof (translation)
Use `show IntermediateField.adjoin k _ ≤ _`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, l, hj, rfl⟩`. Take `⟨Q', hQ'⟩` from `Nb.invertible (singleChart hi)`. Establish `hone : (1 : Ω) ∈ Nb.sub (singleChart hi) * Q'`.

Rewrite using `[hQ']`. Conclude with `Submodule.one_le.mp le_rfl`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hq0⟩ : ∃ q ∈ Q', q ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Establish `hbot : Q' = ⊥` using `(Submodule.eq_bot_iff _).mpr hc`. Rewrite `hone` using `[hbot, Submodule.mul_bot]`. Conclude with `one_ne_zero ((Submodule.mem_bot _).mp hone)`. Establish `hmem : ∀ l, h l * q ∈ chartRing k x (singleChart hi)`. Introduce `l`.

Establish `hl` using `Submodule.mul_mem_mul (mem_sub_of_mem_secs (hv.mem_secs l) (singleChart hi)) hq`. Rewrite `hl` using `[hQ']`. Take `⟨a, ha⟩` from `Submodule.mem_one.mp hl`. Rewrite using `[← ha]`. Conclude with `a.2`.

Establish `e : h l / h j = (h l * q) / (h j * q)` using `(mul_div_mul_right _ _ hq0).symm`. Rewrite using `[e]`. Conclude with `div_mem (mem_funField_of_mem_chartRing hi (hmem l)) (mem_funField_of_mem_chartRing hi (hmem j))`.
-/
theorem funField_le (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    funField (k := k) h ≤ funField (k := k) x := by
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, l, hj, rfl⟩
  obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hi)
  have hone : (1 : Ω) ∈ Nb.sub (singleChart hi) * Q' := by
    rw [hQ']; exact Submodule.one_le.mp le_rfl
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hc
    push Not at hc
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hc
    rw [hbot, Submodule.mul_bot] at hone
    exact one_ne_zero ((Submodule.mem_bot _).mp hone)
  have hmem : ∀ l, h l * q ∈ chartRing k x (singleChart hi) := by
    intro l
    have hl := Submodule.mul_mem_mul (mem_sub_of_mem_secs (hv.mem_secs l) (singleChart hi)) hq
    rw [hQ'] at hl
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hl
    rw [← ha]
    exact a.2
  have e : h l / h j = (h l * q) / (h j * q) := (mul_div_mul_right _ _ hq0).symm
  rw [e]
  exact div_mem (mem_funField_of_mem_chartRing hi (hmem l)) (mem_funField_of_mem_chartRing hi (hmem j))

/- English proof (translation)
Take `⟨n, a, b, J, -, hb, hsum, hloc⟩` from `hv.affine j₀ hj₀`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, b t ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Simplify using `[hc] at hsum`.

Establish `hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I` using `fun I => Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1, one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩`. Establish `hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k` using `k) h := fun z hz => ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)`. Take `⟨c, hc⟩` from `(J t).2.1`. Establish `hxc : x c ≠ 0` using `(mem_support x).mp ((J t).2.2 hc)`. Establish `key : ∀ l, x l / x c ∈ funField (k` using `k) h := by`.

Introduce `l`. Establish `hA : x l / x c ∈ chartRing k x (J t)` using `⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩`. Establish `hE : ∀ I : Chart x, ∃ E : ℕ, b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I`. Introduce `I`. Take `⟨e, he⟩` from `hloc t I`.

Take `⟨D, hD⟩` from `exists_pow_mul_mem I (J t) (chartRing_mono (subset_unionChart_right I (J t)) hA)`. Use `⟨e * D, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]`. Conclude with `(ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D) (mem_ampleSubalg_of_mem_chartRing (hh I) hD)`. Use `choose E hE using hE`.

Establish `hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀)`. Use `Set.mem_iInter.mpr fun I => ?_` and prove the remaining obligations. Establish `hle : E I ≤ ∑ I, E I` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)`. Establish `e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c))`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`.

Rewrite using `[e]`. Conclude with `(ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _) (hE I)`. Rewrite using `[← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]`. Conclude with `div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)`. Use `show IntermediateField.adjoin k _ ≤ _`.

Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, l, hi, rfl⟩`. Establish `e : x l / x i = (x l / x c) / (x i / x c)` using `by field_simp`. Rewrite using `[e]`. Conclude with `div_mem (key l) (key i)`.
-/
theorem le_funField (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by
  classical
  obtain ⟨n, a, b, J, -, hb, hsum, hloc⟩ := hv.affine j₀ hj₀
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I := fun I =>
    Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1,
      one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩
  have hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k := k) h := fun z hz =>
    ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)
  obtain ⟨c, hc⟩ := (J t).2.1
  have hxc : x c ≠ 0 := (mem_support x).mp ((J t).2.2 hc)
  have key : ∀ l, x l / x c ∈ funField (k := k) h := by
    intro l
    have hA : x l / x c ∈ chartRing k x (J t) :=
      ⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩
    have hE : ∀ I : Chart x, ∃ E : ℕ,
        b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I := by
      intro I
      obtain ⟨e, he⟩ := hloc t I
      obtain ⟨D, hD⟩ := exists_pow_mul_mem I (J t)
        (chartRing_mono (subset_unionChart_right I (J t)) hA)
      refine ⟨e * D, ?_⟩
      rw [← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D)
        (mem_ampleSubalg_of_mem_chartRing (hh I) hD)
    choose E hE using hE
    have hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀) := by
      refine Set.mem_iInter.mpr fun I => ?_
      have hle : E I ≤ ∑ I, E I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
      have e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _)
        (hE I)
    rw [← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]
    exact div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, l, hi, rfl⟩
  have e : x l / x i = (x l / x c) / (x i / x c) := by field_simp
  rw [e]
  exact div_mem (key l) (key i)

end VeryAmpleDim

/- English proof (translation)
Introduce `k _ Ω _ _ N x e Nb r h hx hv`. Take `⟨i, hi⟩` from `hx.relevant`. Establish `hxi : x i ≠ 0`. Introduce `h0`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, h j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨Q', hQ'⟩` from `Nb.invertible (singleChart hxi)`.

Establish `hbot : Nb.sub (singleChart hxi) = ⊥`. Rewrite using `[← hv.generates (singleChart hxi), Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `hc l`. Rewrite `hQ'` using `[hbot, Submodule.bot_mul]`.

Establish `h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω)`. Rewrite using `[hQ']`. Conclude with `Submodule.one_le.mp le_rfl`. Conclude with `one_ne_zero ((Submodule.mem_bot _).mp h1)`. Establish `hfield : funField (k` using `k) x = funField (k := k) h := le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)`.

Establish `hdx : dimCl k x = e` using `(DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx`. Use `(DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_` and prove the remaining obligations. Rewrite using `[← hdx]`. Unfold `dimCl`. Rewrite using `[hfield]`.
-/
theorem VeryAmpleDim.proof : VeryAmpleDim.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hx hv
  obtain ⟨i, hi⟩ := hx.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    apply hi
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hxi)
    have hbot : Nb.sub (singleChart hxi) = ⊥ := by
      rw [← hv.generates (singleChart hxi), Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact hc l
    rw [hbot, Submodule.bot_mul] at hQ'
    have h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω) := by
      rw [hQ']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hfield : funField (k := k) x = funField (k := k) h :=
    le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)
  have hdx : dimCl k x = e := (DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx
  refine (DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_
  rw [← hdx]
  unfold dimCl
  rw [hfield]

end

end GroundTheory.Heights₂.Heights.Kleiman
