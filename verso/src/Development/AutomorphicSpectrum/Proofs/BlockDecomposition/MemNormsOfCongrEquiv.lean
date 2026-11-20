import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]`.

Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]`. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc, Algebra.commutes a H, Matrix.mul_assoc]`.
-/
theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} {X Y H : Matrix (Fin n) (Fin n) K}
    (h : X * H = H * Y) (p : K[X]) : aeval X p * H = H * aeval Y p := by
  have hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc,
      Algebra.commutes a H, Matrix.mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hsep : γ₀.val.charpoly.Separable` using `hell.2.2.1`. Take `⟨r₀, hr₀⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep (by rw [Units.mul_inv, Units.inv_mul])`. Establish `hPr : γ₀.val.charpoly ∣ X * r₀ - 1`. Use `GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]`.

Use `set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA`. Use `set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH`. Establish `hAsep : A.charpoly.Separable` using `by rw [hA, Matrix.charpoly_map]; exact hsep.map`. Establish `hAP : A.charpoly = atPl w γ₀.val.charpoly` using `Matrix.charpoly_map _ _`. Take `⟨f, hf⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm`.

Establish `hAi : A * aeval A (atPl w r₀) = 1`. Rewrite using `[hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hcA : cT (cj w) A * H * A = H`. Use `congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv` as an intermediate fact. Simplify using `only [Matrix.map_mul, cT_map hU w hw] at this`.

Conclude with `this`. Establish `hHu : IsUnit H.det`. Rewrite using `[hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(hdet.isUnit).map _`. Establish `hcT : cT (cj w) A * H = H * aeval A (atPl w r₀)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m`. Rewrite using `[← hAP]`. Use `GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_` and prove the remaining obligations. Establish `h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀))`.

Rewrite using `[GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]`. Establish `h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f)`. Rewrite using `[hc2, hf, h1, Matrix.mul_assoc]`. Establish `h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f`. Establish `hHi : H⁻¹ * H = 1` using `Matrix.nonsing_inv_mul _ hHu`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, h2, ← Matrix.mul_assoc]`. Use `_ = _ := by rw [hHi, Matrix.one_mul]`. Rewrite using `[map_sub, map_mul, ← h3, sub_self]`. Set `ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q` to `(involBase Q k).toRingHom`.

Set `Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q` to `eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)`. Set `g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q` to `(Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom`. Establish `hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p`. Introduce `p`. Establish `e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q))` using `RingHom.ext fun e => hι1 e`.

Express the relevant statement in the definitionally equal form `eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _`. Rewrite using `[eval₂_map, e]`. Use `(Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _`. Rewrite using `[← aeval_def]`.

Use `congr 1`. Conclude with `AdjoinRoot.aeval_eq p`. Establish `hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹`. Rewrite using `[hΦ]`. Use `congr 1`.

Establish `h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0` using `AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)`. Rewrite `h1` using `[map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀))`. Establish `e1 : ib.comp ι = ι.comp (cj w)` using `RingHom.ext fun y => hιc y`.

Establish `e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹`. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ invol Q (alpha Q) = _`. Rewrite using `[invol_alpha]`. Express the relevant statement in the definitionally equal form `ib (eval₂ ι _ f) = eval₂ ι _ _`. Rewrite using `[Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]`.

Conclude with `congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm`. Take `⟨t, ht⟩` from `hdiv`. Establish `hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t`. Rewrite using `[← ht]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : Φ (atPl w γ₀.val.charpoly) = 0`. Rewrite using `[hΦ]`. Conclude with `(congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)`. Establish `hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q)`. Rewrite using `[hinvΦ, ← map_mul, hft, map_add, map_mul, h0, zero_mul, add_zero, hx]`.

Both sides reduce to the same expression. Establish `hu : IsUnit (Φ f)` using `isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)`. Conclude with `⟨hu.unit, Units.ext hz⟩`.
-/
theorem mem_norms_of_congr (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q)
    (hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e)
    (hιc : ∀ y, involBase Q k (ι y) = ι (cj w y))
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = eval₂ ι ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := Matrix.charpoly_map _ _
  obtain ⟨f, hf⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    exact this
  have hHu : IsUnit H.det := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet.isUnit).map _
  have hcT : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀)) := by
      rw [GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]
    have h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
      rw [hc2, hf, h1, Matrix.mul_assoc]
    have h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f := by
      have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hHu
      calc aeval A m = H⁻¹ * H * aeval A m := by rw [hHi, Matrix.one_mul]
        _ = H⁻¹ * H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
          rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
        _ = _ := by rw [hHi, Matrix.one_mul]
    rw [map_sub, map_mul, ← h3, sub_self]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t := by
    rw [← ht]; ring
  have h0 : Φ (atPl w γ₀.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) := by
    rw [hinvΦ, ← map_mul, hft, map_add, map_mul, h0, zero_mul, add_zero, hx]
    rfl
  have hu : IsUnit (Φ f) :=
    isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)
  exact ⟨hu.unit, Units.ext hz⟩

/- English proof (translation)
Use `mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `inclBase Q k (j (algebraMap E _ e)) = _`. Rewrite using `[hj1]`. Simplify using `[inclBase]`. Express the relevant statement in the definitionally equal form `involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))`.

Rewrite using `[hj2]`. Generalize the expression as in `j y = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [inclBase, involBase, invol_algebraMap]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem mem_norms_of_congr_equiv (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (j : w.adicCompletion E ≃+* k ⊗[maximalRealSubfield E] E)
    (hj1 : ∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e)
    (hj2 : ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) =
      eval₂ (((inclBase Q k).toRingHom).comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  refine mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx
  · change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  · change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]

end GlobalTheory.CompanionTheory.NormCongr
