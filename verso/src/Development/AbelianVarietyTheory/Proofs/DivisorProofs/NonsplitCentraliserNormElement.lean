import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormInert

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, Polynomial.map_add, map_add, ← hp, ← hq]`. Use extensionality with `i j`. Simplify using `[cT]`.

Consider the case `monomial k a`. Rewrite using `[aeval_monomial, Polynomial.map_monomial, aeval_monomial]`. Establish `e : (A.map s)ᵀ ^ k = ((A ^ k).map s)ᵀ` using `by rw [← Matrix.transpose_pow, Matrix.map_pow]`. Use extensionality with `i j`. Simplify using `[cT, e, Algebra.algebraMap_eq_smul_one]`.
-/
theorem cT_aeval {K : Type} [Field K] (s : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    cT s (aeval A f) = aeval (cT s A) (f.map s) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map s)ᵀ ^ k = ((A ^ k).map s)ᵀ := by rw [← Matrix.transpose_pow, Matrix.map_pow]
    ext i j
    simp [cT, e, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Take `⟨P, hP, hPv⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Use `⟨⟨P, hP.isPrime, fun h0 => v.ne_bot ?_⟩, HeightOneSpectrum.ext hPv.over.symm⟩` and prove the remaining obligations. Rewrite using `[hPv.over, h0]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`.
-/
theorem exists_over (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  refine ⟨⟨P, hP.isPrime, fun h0 => v.ne_bot ?_⟩, HeightOneSpectrum.ext hPv.over.symm⟩
  rw [hPv.over, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

/- English proof (translation)
Establish `hns : ¬ IsSplitAt w` using `fun ⟨u, hne, hu⟩ => hne (huniq u (hu.trans hw))`. Establish `hmain` using `GlobalTheory.ConjAtPlace.main E hU w`. Establish `hσ` using `(hmain.2.2.2.1 hns).1`. Establish `hinj : Function.Injective (GlobalTheory.LFun.toCompl hw)`. Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations.

Establish `h1` using `GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v) (GlobalTheory.AdelicU.evalV_singleFin_self v) y`. Establish `h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0` using `FiniteAdeleRing.ext _ fun u => by`. Distinguish the cases in `e : u.under (𝓞 (maximalRealSubfield E)) = v`. Rewrite using `[GlobalTheory.LFun.finAdEquiv_apply e, h1]`. Take `rfl` from `huniq u e`.

Conclude with `hy`. Rewrite using `[GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]`. Both sides reduce to the same expression. Rewrite using `[← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]`. Establish `hsurj` using `GlobalTheory.LFun.InertChart.toCompl_surjective hw`.

Set `e` to `RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hw) ⟨hinj, hsurj⟩`. Establish `hF : ∀ a, cj w (GlobalTheory.LFun.complMap hw a) = GlobalTheory.LFun.complMap hw a`. Use `(HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hw)) (GlobalTheory.LFun.InertChart.continuous_complMap hw) (funext fun x => by` as an intermediate fact. Simplify using `only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]`. Conclude with `congrArg _ ((IsCMField.complexConj E).commutes x))`.

Conclude with `fun a => congrFun this a`. Establish `hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hw y) = GlobalTheory.LFun.toCompl hw (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))) ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) …`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `⟨e.symm, fun x => e.symm_apply_eq.2 ?_, fun x => e.symm_apply_eq.2 ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.LFun.toCompl_tmul hw 1 x`. Rewrite `h` using `[map_one, one_mul]`.

Conclude with `h.symm`. Take `⟨y, rfl⟩` from `e.surjective x`. Rewrite using `[e.symm_apply_apply]`. Conclude with `hcomp y`.
-/
theorem localEquiv (hU : Unr E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (w : Pl E)
    (hw : w.under (𝓞 (maximalRealSubfield E)) = v)
    (huniq : ∀ u : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v → u = w) :
    ∃ j : w.adicCompletion E ≃+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
      (∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e) ∧
      ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x) := by
  classical
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u (hu.trans hw))
  have hmain := GlobalTheory.ConjAtPlace.main E hU w
  have hσ := (hmain.2.2.2.1 hns).1
  have hinj : Function.Injective (GlobalTheory.LFun.toCompl hw) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
      (GlobalTheory.AdelicU.evalV_singleFin_self v) y
    have h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
      FiniteAdeleRing.ext _ fun u => by
        by_cases e : u.under (𝓞 (maximalRealSubfield E)) = v
        · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
          obtain rfl := huniq u e
          exact hy
        · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
            (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
          rfl
    rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]
  have hsurj := GlobalTheory.LFun.InertChart.toCompl_surjective hw
  let e := RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hw) ⟨hinj, hsurj⟩
  have hF : ∀ a, cj w (GlobalTheory.LFun.complMap hw a) = GlobalTheory.LFun.complMap hw a := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hw)) (GlobalTheory.LFun.InertChart.continuous_complMap hw)
      (funext fun x => by
        simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))
    exact fun a => congrFun this a
  have hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hw y) = GlobalTheory.LFun.toCompl hw
      (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨e.symm, fun x => e.symm_apply_eq.2 ?_, fun x => e.symm_apply_eq.2 ?_⟩
  · have h := GlobalTheory.LFun.toCompl_tmul hw 1 x
    rw [map_one, one_mul] at h
    exact h.symm
  · obtain ⟨y, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply]
    exact hcomp y

/- English proof (translation)
Introduce `E _ _ _ hU n γ hγ hell m hloc r Q hQ _ v huniq`. Take `⟨w, hw⟩` from `exists_over (E := E) v`. Establish `hns : ¬ IsSplitAt w` using `fun ⟨u, hne, hu⟩ => hne (huniq u w (hu.trans hw) hw)`. Take `⟨c, hc1, hc2⟩` from `hloc w hns`. Take `⟨j, hj1, hj2⟩` from `localEquiv hU v w hw (fun u hu => huniq u w hu hw)`.

Establish `hsep : γ.val.charpoly.Separable` using `hell.2.2.1`. Take `⟨r₀, hr₀⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val (γ⁻¹).val hsep (by rw [Units.mul_inv, Units.inv_mul])`. Establish `hPr : γ.val.charpoly ∣ X * r₀ - 1`. Use `GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ.val hsep _ ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]`.

Use `set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ.val.map (algebraMap E (w.adicCompletion E)) with hA`. Establish `hAsep : A.charpoly.Separable` using `by rw [hA, Matrix.charpoly_map]; exact hsep.map`. Establish `hAP : A.charpoly = atPl w γ.val.charpoly` using `Matrix.charpoly_map _ _`. Establish `hc1' : A * c = c * A` using `hc1.symm`. Take `⟨f, rfl⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c hAsep hc1'`.

Establish `hAi : A * aeval A (atPl w r₀) = 1`. Rewrite using `[hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hcA : cT (cj w) A * A = 1`. Establish `h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1` using `hγ`. Use `congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h0` as an intermediate fact.

Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hns, Matrix.mul_one] at this`. Conclude with `this`. Establish `hcT : cT (cj w) A = aeval A (atPl w r₀)`. Combine the equalities or inequalities in the displayed calculation. Establish `hdiv : atPl w γ.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - atPl w m`.

Rewrite using `[← hAP]`. Use `GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_` and prove the remaining obligations. Establish `h2 : cT (cj w) (aeval A f) * aeval A f = aeval A (atPl w m)`. Rewrite using `[hc2, hA, aeval_map_mat]`. Rewrite `h2` using `[cT_aeval, hcT, ← aeval_comp]`.

Rewrite using `[map_sub, map_mul, h2, sub_self]`. Use `set k := v.adicCompletion (maximalRealSubfield E)`. Set `ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q` to `((inclBase Q k).toRingHom).comp j.toRingHom`. Establish `hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e`. Introduce `e`.

Express the relevant statement in the definitionally equal form `inclBase Q k (j (algebraMap E _ e)) = _`. Rewrite using `[hj1]`. Simplify using `[inclBase]`. Establish `hιc : ∀ y, involBase Q k (ι y) = ι (cj w y)`. Introduce `y`.

Express the relevant statement in the definitionally equal form `involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))`. Rewrite using `[hj2]`. Generalize the expression as in `j y = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e => simp [inclBase, involBase, invol_algebraMap]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Set `ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q` to `(involBase Q k).toRingHom`. Set `Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q` to `eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)`. Set `g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q` to `(Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom`.

Establish `hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p`. Introduce `p`. Establish `e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q))` using `RingHom.ext fun e => hι1 e`. Express the relevant statement in the definitionally equal form `eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _`. Rewrite using `[eval₂_map, e]`.

Use `(Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _`. Rewrite using `[← aeval_def]`. Use `congr 1`. Conclude with `AdjoinRoot.aeval_eq p`.

Establish `hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹`. Rewrite using `[hΦ]`. Use `congr 1`. Establish `h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0` using `AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)`. Rewrite `h1` using `[map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero]`.

Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `hinv : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀))`. Establish `e1 : ib.comp ι = ι.comp (cj w)` using `RingHom.ext fun y => hιc y`. Establish `e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹`. Express the relevant statement in the definitionally equal form `(1 : k) ⊗ₜ invol Q (alpha Q) = _`.

Rewrite using `[invol_alpha]`. Express the relevant statement in the definitionally equal form `ib (eval₂ ι _ f) = eval₂ ι _ _`. Rewrite using `[Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]`. Conclude with `congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm`. Take `⟨t, ht⟩` from `hdiv`.

Establish `hft : f * (f.map (cj w)).comp (atPl w r₀) = atPl w m + atPl w γ.val.charpoly * t`. Rewrite using `[← ht]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Φ f, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Φ f * ib (Φ f) = _`.

Establish `h0 : Φ (atPl w γ.val.charpoly) = 0`. Rewrite using `[hΦ]`. Conclude with `(congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)`. Rewrite using `[hinv, ← map_mul, hft, map_add, map_mul, h0, zero_mul, add_zero, hΦ]`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ hU n γ hγ hell m hloc r Q hQ _ v huniq
  classical
  obtain ⟨w, hw⟩ := exists_over (E := E) v
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u w (hu.trans hw) hw)
  obtain ⟨c, hc1, hc2⟩ := hloc w hns
  obtain ⟨j, hj1, hj2⟩ := localEquiv hU v w hw (fun u hu => huniq u w hu hw)

  have hsep : γ.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val (γ⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]

  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ.val.map (algebraMap E (w.adicCompletion E)) with hA
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ.val.charpoly := Matrix.charpoly_map _ _
  have hc1' : A * c = c * A := hc1.symm
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c hAsep hc1'
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * A = 1 := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h0
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hns, Matrix.mul_one] at this
    exact this
  have hcT : cT (cj w) A = aeval A (atPl w r₀) := by
    calc cT (cj w) A = cT (cj w) A * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA, Matrix.one_mul]
  have hdiv : atPl w γ.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - atPl w m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h2 : cT (cj w) (aeval A f) * aeval A f = aeval A (atPl w m) := by
      rw [hc2, hA, aeval_map_mat]
    rw [cT_aeval, hcT, ← aeval_comp] at h2
    rw [map_sub, map_mul, h2, sub_self]

  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    ((inclBase Q k).toRingHom).comp j.toRingHom
  have hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e := by
    intro e
    change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]
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
  have hinv : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = atPl w m + atPl w γ.val.charpoly * t := by
    rw [← ht]; ring
  refine ⟨Φ f, ?_⟩
  change Φ f * ib (Φ f) = _
  have h0 : Φ (atPl w γ.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  rw [hinv, ← map_mul, hft, map_add, map_mul, h0, zero_mul, add_zero, hΦ]

end GlobalTheory.NormInert
