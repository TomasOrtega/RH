import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightProductFormula

/- English proof (translation)
Rewrite using `[reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]`.
-/
theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = sg v x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

/- English proof (translation)
Simplify using `[rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem rowF_apply {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) (i : Fin 2) :
    rowF s x i = algebraMap F (Af F) (s 0) * x.val 0 i + algebraMap F (Af F) (s 1) * x.val 1 i := by
  simp [rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Simplify using `only [map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_id {F : Type} [Field F] [NumberField F] (s s' : Fin 2 → F) (x : GF F) :
    algebraMap F (Af F) (s 0 * s' 1 - s 1 * s' 0) * (Matrix.GeneralLinearGroup.det x : Af F) =
      rowF s x 0 * rowF s' x 1 - rowF s x 1 * rowF s' x 0 := by
  rw [rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [map_sub, map_mul]
  ring

end UpperTheory.Esk.HeightProductFormula

namespace UpperTheory.Esk

open HeightProductFormula in
/- English proof (translation)
Introduce `hM hMo hR F _ _ _ c _ χ s s' hΔ x`. Take `⟨hpos, hmul, -, hprod⟩` from `UpperTheory.V.Sd.Hm.absf F`. Establish `hs : s ≠ 0` using `fun h => hΔ (by simp [h])`. Establish `hs' : s' ≠ 0` using `fun h => hΔ (by simp [h])`. Take `⟨t, k, hk, ht⟩` from `(hR F s x).1 hs`.

Take `⟨t', k', hk', ht'⟩` from `(hR F s' x).1 hs'`. Establish `hn : nF s x = absF t` using `(hR F s x).2 t k hk ht`. Establish `hn' : nF s' x = absF t'` using `(hR F s' x).2 t' k' hk' ht'`. Take `⟨hK, hO, -⟩` from `hM F`. Establish `hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1` using `fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w`.

Use `set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd`. Use `set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x`. Establish `key : absF U1 ≤ absF (t * t')`. Use `hMo F _ _ fun w => ?_` and prove the remaining obligations. Establish `e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)`.

Express the relevant statement in the definitionally equal form `algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _`. Rewrite using `[det_id, ht, ht, ht', ht', Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul, map_mul]`. Establish `h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1`.

Rewrite using `[map_sub, map_mul, map_mul]`. Use `(Valuation.map_sub _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)`. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)`. Combine the equalities or inequalities in the displayed calculation. Establish `hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x)` using `hmul _ _`. Establish `hP` using `hprod (Units.mk0 Δ hΔ)`. Express the relevant statement in the definitionally equal form `(∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP`.

Simplify using `only [reAt_eq] at hP`. Express the relevant statement in the definitionally equal form `absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤ ∏ v, sg v Δ ^ 2`. Rewrite using `[hn, hn']`. Establish `hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2`. Rewrite using `[← Finset.prod_pow]`.

Conclude with `Finset.prod_congr rfl fun v _ => (sq_abs _).symm`. Rewrite using `[hsq]`. Use `set P := ∏ v, |sg v Δ|`. Use `set R := absF (ratU F (Units.mk0 Δ hΔ))`. Use `set A := absF (Matrix.GeneralLinearGroup.det x)`.

Establish `hA` using `hpos (Matrix.GeneralLinearGroup.det x)`. Establish `hT` using `hpos t`. Establish `hT'` using `hpos t'`. Establish `hRp` using `hpos (ratU F (Units.mk0 Δ hΔ))`. Establish `hPp : 0 ≤ P` using `Finset.prod_nonneg fun v _ => abs_nonneg _`.

Rewrite `key` using `[hU1, hmul t t']`. Establish `hA2 : A ≤ absF t * absF t' * P`. Establish `: A = P * (R * A)` using `by rw [← mul_assoc, hP, one_mul]`. Rewrite using `[this, mul_comm (absF t * absF t') P]`. Conclude with `mul_le_mul_of_nonneg_left key hPp`.

Rewrite using `[div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]`. Conclude with `pow_le_pow_left₀ hA.le (by linarith) 2`.
-/
theorem dProd : AMem → AMono → ARow → DProd := by
  intro hM hMo hR F _ _ _ c _ χ s s' hΔ x
  obtain ⟨hpos, hmul, -, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hs : s ≠ 0 := fun h => hΔ (by simp [h])
  have hs' : s' ≠ 0 := fun h => hΔ (by simp [h])
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s' x).1 hs'
  have hn : nF s x = absF t := (hR F s x).2 t k hk ht
  have hn' : nF s' x = absF t' := (hR F s' x).2 t' k' hk' ht'
  obtain ⟨hK, hO, -⟩ := hM F
  have hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1 :=
    fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w
  set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd
  set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x
  have key : absF U1 ≤ absF (t * t') := by
    refine hMo F _ _ fun w => ?_
    have e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0) := by
      change algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _
      rw [det_id, ht, ht, ht', ht', Units.val_mul]
      ring
    rw [e, map_mul, map_mul]
    have h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1 := by
      rw [map_sub, map_mul, map_mul]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)
    calc _ ≤ Valued.v (pLoc F w ((t * t' : (Af F)ˣ) : Af F)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  have hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x) := hmul _ _
  have hP := hprod (Units.mk0 Δ hΔ)
  change (∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP
  simp only [reAt_eq] at hP
  change absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤
    ∏ v, sg v Δ ^ 2
  rw [hn, hn']
  have hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2 := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => (sq_abs _).symm
  rw [hsq]
  set P := ∏ v, |sg v Δ|
  set R := absF (ratU F (Units.mk0 Δ hΔ))
  set A := absF (Matrix.GeneralLinearGroup.det x)
  have hA := hpos (Matrix.GeneralLinearGroup.det x)
  have hT := hpos t
  have hT' := hpos t'
  have hRp := hpos (ratU F (Units.mk0 Δ hΔ))
  have hPp : 0 ≤ P := Finset.prod_nonneg fun v _ => abs_nonneg _
  rw [hU1, hmul t t'] at key
  have hA2 : A ≤ absF t * absF t' * P := by
    have : A = P * (R * A) := by rw [← mul_assoc, hP, one_mul]
    rw [this, mul_comm (absF t * absF t') P]
    exact mul_le_mul_of_nonneg_left key hPp
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ hA.le (by linarith) 2

end UpperTheory.Esk
