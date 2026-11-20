import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

namespace GlobalTheory.LocGL.DetQuot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `⟨parIndEquiv e (Representation.Equiv.mk (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).toLinearEquiv.symm fun g => ?_)⟩` and prove the remaining obligations. Use `LinearMap.ext_ring ?_` and prove the remaining obligations. Apply `(PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).injective` to reduce the goal to its premises. Simplify using `[ofChar_apply, hΘ, PiTensorProduct.one_def, piTensor_tprod, detRep, detChar_apply, Units.coe_prod]`.
-/
theorem nonempty_equiv_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {θ : Fin t → kˣ →* ℂˣ} {Θ : Levi k (fun _ : Fin t => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    Nonempty ((parInd e (ofChar Θ)).Equiv (multiProd e fun a => detRep (Fin 1) (θ a))) := by
  refine ⟨parIndEquiv e (Representation.Equiv.mk
    (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).toLinearEquiv.symm fun g => ?_)⟩
  refine LinearMap.ext_ring ?_
  apply (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).injective
  simp [ofChar_apply, hΘ, PiTensorProduct.one_def, piTensor_tprod, detRep, detChar_apply, Units.coe_prod]

/- English proof (translation)
Establish `hsm : IsSmooth (detRep n η)` using `(isSmooth_ofChar_iff _).2 hη.detChar`. Set `ψ : (jac e (detRep n η)).IntertwiningMap (ofChar (detLevi e η))` to `{ toLinearMap := (twKer (detRep n η) (unipRad k e) 1).liftQ LinearMap.id (by rw [twKer_detRep]; exact bot_le) isIntertwining' := fun g => LinearMap.ext fun x => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.SmGL.Model.jac_detRep, map_smul, ofChar_apply, smul_eq_mul] }`. Take `⟨f, hf⟩` from `(GlobalTheory.SmGL.Model.evalOne_bijective e hsm (ofChar (detLevi e η))).2 ψ`. Use `⟨f, (injective_iff_map_eq_zero f).2 fun c hc => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc0`. Establish `h1 : f 1 = 0`. Establish `h1' : (1 : ℂ) = c⁻¹ • c` using `by simp [hc0]`. Rewrite using `[h1', map_smul, hc, smul_zero]`. Establish `h2 : ψ (Submodule.Quotient.mk (p` using `twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = 1 := rfl`.

Establish `h3 : ψ (Submodule.Quotient.mk (p` using `twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = (f 1).1.1 1 := by`. Rewrite using `[← hf]`. Both sides reduce to the same expression. Rewrite `h3` using `[h1]`. Conclude with `one_ne_zero (h2.symm.trans h3)`.
-/
theorem exists_embedding {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ f : (detRep n η).IntertwiningMap (parInd e (ofChar (detLevi e η))), Function.Injective f := by
  have hsm : IsSmooth (detRep n η) := (isSmooth_ofChar_iff _).2 hη.detChar
  let ψ : (jac e (detRep n η)).IntertwiningMap (ofChar (detLevi e η)) :=
    { toLinearMap := (twKer (detRep n η) (unipRad k e) 1).liftQ LinearMap.id
        (by rw [twKer_detRep]; exact bot_le)
      isIntertwining' := fun g => LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.SmGL.Model.jac_detRep, map_smul, ofChar_apply,
          smul_eq_mul] }
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e hsm (ofChar (detLevi e η))).2 ψ
  refine ⟨f, (injective_iff_map_eq_zero f).2 fun c hc => ?_⟩
  by_contra hc0
  have h1 : f 1 = 0 := by
    have h1' : (1 : ℂ) = c⁻¹ • c := by simp [hc0]
    rw [h1', map_smul, hc, smul_zero]
  have h2 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = 1 := rfl
  have h3 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = (f 1).1.1 1 := by
    rw [← hf]; rfl
  rw [h1] at h3
  exact one_ne_zero (h2.symm.trans h3)

/- English proof (translation)
Use `set lam : Module.Dual ℂ V := ((f 1 : smoothPart π.dual) : Module.Dual ℂ V) with hlam`. Establish `key : ∀ g v, lam (π g v) = (χ g : ℂ) * lam v`. Introduce `g v`. Establish `h1 : f (ofChar (χ⁻¹) (g⁻¹) (1 : ℂ)) = contra π (g⁻¹) (f 1)` using `LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) (1 : ℂ)`. Establish `h2 : ofChar (χ⁻¹) (g⁻¹) (1 : ℂ) = (χ g : ℂ) • (1 : ℂ)` using `by simp [ofChar_apply]`.

Rewrite `h1` using `[h2, map_smul]`. Establish `h3` using `congrArg (fun x : smoothPart π.dual => (x : Module.Dual ℂ V) v) h1`. Simplify using `only [contra_apply, inv_inv] at h3`. Rewrite using `[← h3]`. Simplify using `[lam]`.

Establish `hne : lam ≠ 0`. Introduce `h0`. Establish `h1 : f 1 = 0` using `Subtype.ext (by simpa [lam] using h0)`. Conclude with `one_ne_zero (hf (h1.trans (map_zero f).symm))`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, lam v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (LinearMap.ext h)`. Use `⟨⟨lam, fun g => LinearMap.ext fun w => ?_⟩, fun c => ⟨(c / lam v) • v, ?_⟩⟩` and prove the remaining obligations. Simplify using `[key, ofChar_apply]`.

Simplify using `[hv]`.
-/
theorem exists_surjective_of_contra {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {χ : G →* ℂˣ} (f : (ofChar χ⁻¹).IntertwiningMap (contra π))
    (hf : Function.Injective f) : ∃ l : π.IntertwiningMap (ofChar χ), Function.Surjective l := by
  set lam : Module.Dual ℂ V := ((f 1 : smoothPart π.dual) : Module.Dual ℂ V) with hlam
  have key : ∀ g v, lam (π g v) = (χ g : ℂ) * lam v := by
    intro g v
    have h1 : f (ofChar (χ⁻¹) (g⁻¹) (1 : ℂ)) = contra π (g⁻¹) (f 1) :=
      LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) (1 : ℂ)
    have h2 : ofChar (χ⁻¹) (g⁻¹) (1 : ℂ) = (χ g : ℂ) • (1 : ℂ) := by simp [ofChar_apply]
    rw [h2, map_smul] at h1
    have h3 := congrArg (fun x : smoothPart π.dual => (x : Module.Dual ℂ V) v) h1
    simp only [contra_apply, inv_inv] at h3
    rw [← h3]
    simp [lam]
  have hne : lam ≠ 0 := by
    intro h0
    have h1 : f 1 = 0 := Subtype.ext (by simpa [lam] using h0)
    exact one_ne_zero (hf (h1.trans (map_zero f).symm))
  obtain ⟨v, hv⟩ : ∃ v, lam v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  refine ⟨⟨lam, fun g => LinearMap.ext fun w => ?_⟩, fun c => ⟨(c / lam v) • v, ?_⟩⟩
  · simp [key, ofChar_apply]
  · simp [hv]

/- English proof (translation)
Establish `hc : IsSmoothChar (detLevi e η⁻¹)`. Unfold `detLevi`. Conclude with `(hη.inv.detChar.comp (leviEmb k e) (continuous_leviEmb (R := k) e)).mul (isSmoothChar_deltaHalf k).inv`. Establish `hc' : IsSmoothChar (detLevi e η⁻¹)⁻¹` using `hc.inv`. Establish `hτ : IsSmooth (ofChar (detLevi e η⁻¹)⁻¹)` using `(isSmooth_ofChar_iff _).2 hc'`.

Take `⟨Φ1⟩` from `GlobalTheory.LocGL.ProjLine.nonempty_equiv_contra_ofChar hc'`. Rewrite `Φ1` using `[inv_inv]`. Take `⟨Φ2⟩` from `(GlobalTheory.SmGL.IndDual.inductionContragredient k).nonempty_equiv e hτ`. Take `⟨f, hf⟩` from `exists_embedding e hη.inv`. Set `F` to `(Φ2.toIntertwiningMap.comp (parIndEquiv e Φ1).toIntertwiningMap).comp f`.

Establish `hF : Function.Injective F` using `fun a b h => hf ((EquivLike.injective (parIndEquiv e Φ1)) ((EquivLike.injective Φ2) h))`. Establish `hdet : detChar n η⁻¹ = (detChar n η)⁻¹`. Use extensionality with `g`. Simplify using `[detChar_apply]`. Establish `key : ∀ (χ' : GL n k →* ℂˣ), χ' = (detChar n η)⁻¹ → ∀ f' : (ofChar χ').IntertwiningMap (contra (parInd e (ofChar (detLevi e η⁻¹)⁻¹))), Function.Injective f' → ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (ofChar (detChar n η)), Function.Surjective l`.

Introduce and unpack `χ' rfl f' hf'`. Conclude with `exists_surjective_of_contra f' hf'`. Conclude with `key (detChar n η⁻¹) hdet F hF`.
-/
theorem exists_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (detRep n η), Function.Surjective l := by
  have hc : IsSmoothChar (detLevi e η⁻¹) := by
    unfold detLevi
    exact (hη.inv.detChar.comp (leviEmb k e) (continuous_leviEmb (R := k) e)).mul
      (isSmoothChar_deltaHalf k).inv
  have hc' : IsSmoothChar (detLevi e η⁻¹)⁻¹ := hc.inv
  have hτ : IsSmooth (ofChar (detLevi e η⁻¹)⁻¹) := (isSmooth_ofChar_iff _).2 hc'
  obtain ⟨Φ1⟩ := GlobalTheory.LocGL.ProjLine.nonempty_equiv_contra_ofChar hc'
  rw [inv_inv] at Φ1
  obtain ⟨Φ2⟩ := (GlobalTheory.SmGL.IndDual.inductionContragredient k).nonempty_equiv e hτ
  obtain ⟨f, hf⟩ := exists_embedding e hη.inv
  let F := (Φ2.toIntertwiningMap.comp (parIndEquiv e Φ1).toIntertwiningMap).comp f
  have hF : Function.Injective F := fun a b h =>
    hf ((EquivLike.injective (parIndEquiv e Φ1)) ((EquivLike.injective Φ2) h))
  have hdet : detChar n η⁻¹ = (detChar n η)⁻¹ := by
    ext g
    simp [detChar_apply]
  have key : ∀ (χ' : GL n k →* ℂˣ), χ' = (detChar n η)⁻¹ →
      ∀ f' : (ofChar χ').IntertwiningMap (contra (parInd e (ofChar (detLevi e η⁻¹)⁻¹))), Function.Injective f' →
      ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (ofChar (detChar n η)), Function.Surjective l := by
    rintro χ' rfl f' hf'
    exact exists_surjective_of_contra f' hf'
  exact key (detChar n η⁻¹) hdet F hF

/- English proof (translation)
Use `⟨l.comp Φ.symm.toIntertwiningMap, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hl y`. Use `⟨Φ x, ?_⟩` and prove the remaining obligations. Use `show l (Φ.symm (Φ x)) = l x`. Rewrite using `[Representation.Equiv.symm_apply_apply]`.
-/
theorem surj_of_equiv {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (Φ : π.Equiv σ) (l : π.IntertwiningMap τ) (hl : Function.Surjective l) :
    ∃ l' : σ.IntertwiningMap τ, Function.Surjective l' := by
  refine ⟨l.comp Φ.symm.toIntertwiningMap, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hl y
  refine ⟨Φ x, ?_⟩
  show l (Φ.symm (Φ x)) = l x
  rw [Representation.Equiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[MonoidHom.inv_apply, detLevi_apply, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hs : (((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) = -(-((modExp (fun _ : Fin t => Fin 1) a : ℤ) : ℂ) / 2)`. Rewrite using `[modExp_fin (fun _ : Fin t => Fin 1) (fun _ => Fintype.card_fin 1) a]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, absPow_neg]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]`.
-/
theorem detLevi_inv_apply {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    (χ : kˣ →* ℂˣ) (g : Levi k fun _ : Fin t => Fin 1) :
    (detLevi e χ⁻¹)⁻¹ g =
      ∏ a : Fin t, (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (GeneralLinearGroup.det (g a)) := by
  rw [MonoidHom.inv_apply, detLevi_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : (((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) =
      -(-((modExp (fun _ : Fin t => Fin 1) a : ℤ) : ℂ) / 2) := by
    rw [modExp_fin (fun _ : Fin t => Fin 1) (fun _ => Fintype.card_fin 1) a]
    push_cast
    ring
  rw [hs, absPow_neg]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]

/- English proof (translation)
Take `⟨Φ⟩` from `nonempty_equiv_multiProd e (Θ := (detLevi e χ⁻¹)⁻¹) (θ := fun a : Fin t => χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (detLevi_inv_apply e χ)`. Take `⟨l, hl⟩` from `exists_surjective e hχ`. Conclude with `surj_of_equiv Φ l hl`.
-/
theorem exists_surjective_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ l : (multiProd e fun a : Fin t => detRep (Fin 1)
      (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ))).IntertwiningMap (detRep n χ), Function.Surjective l := by
  obtain ⟨Φ⟩ := nonempty_equiv_multiProd e (Θ := (detLevi e χ⁻¹)⁻¹)
    (θ := fun a : Fin t => χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (detLevi_inv_apply e χ)
  obtain ⟨l, hl⟩ := exists_surjective e hχ
  exact surj_of_equiv Φ l hl

/- English proof (translation)
Take `rfl : x = fun a => IrrGL.ofChar (θ a) (hθ a)` from `funext hx`. Establish `hd : ∑ a : Fin t, (IrrGL.ofChar (θ a) (hθ a)).1 = t` using `by simp [IrrGL.ofChar]`. Conclude with `⟨stdBlocks _ hd, hd, ⟨multiProdEquiv _ fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a))⟩⟩`.
-/
theorem exists_equiv_prodIrr {t : ℕ} {θ : Fin t → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin t → IrrGL k}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) :
    ∃ (e : (Σ _ : Fin t, Fin 1) ≃ Fin t) (hd' : ∑ a, (x a).1 = t), Nonempty ((multiProd e fun a => detRep (Fin 1) (θ a)).Equiv (prodIrr x hd')) := by
  obtain rfl : x = fun a => IrrGL.ofChar (θ a) (hθ a) := funext hx
  have hd : ∑ a : Fin t, (IrrGL.ofChar (θ a) (hθ a)).1 = t := by simp [IrrGL.ofChar]
  exact ⟨stdBlocks _ hd, hd, ⟨multiProdEquiv _ fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a))⟩⟩

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Establish `hθ : ∀ a : Fin t, IsSmoothChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ))` using `fun a => hχ.mul (isSmoothChar_absPow _)`. Establish `hx' : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (hθ a)` using `fun a => (hx a).trans (IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _))`. Take `⟨e, hd, hΦ⟩` from `exists_equiv_prodIrr hθ hx'`. Take `⟨Φ⟩` from `hΦ`. Take `⟨l, hl⟩` from `exists_surjective_multiProd (t := t) (n := Fin t) e (χ := χ) hχ`.

Use `⟨hd, ?_⟩` and prove the remaining obligations. Conclude with `surj_of_equiv Φ l hl`.
-/
private theorem exists_surjective_prodIrr_to_detRep (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL k}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l := by
  have hθ : ∀ a : Fin t, IsSmoothChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) :=
    fun a => hχ.mul (isSmoothChar_absPow _)
  have hx' : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (hθ a) :=
    fun a => (hx a).trans (IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _))
  obtain ⟨e, hd, hΦ⟩ := exists_equiv_prodIrr hθ hx'
  obtain ⟨Φ⟩ := hΦ
  obtain ⟨l, hl⟩ := exists_surjective_multiProd (t := t) (n := Fin t) e (χ := χ) hχ
  refine ⟨hd, ?_⟩
  exact surj_of_equiv Φ l hl

/- English proof (translation)
The claim follows from `exists_surjective_prodIrr_to_detRep t hχ hx`.
-/
theorem exists_surjective_prodIrr (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL k}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l :=
  exists_surjective_prodIrr_to_detRep t hχ hx

end GlobalTheory.LocGL.DetQuot

namespace GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `H k _ _ _ _ _ t χ hχ`. Set `x : Fin t → IrrGL k` to `fun j => (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)`. Take `⟨hd, l, hl⟩` from `DetQuot.exists_surjective_prodIrr t hχ (x := x) (fun j => rfl)`. Establish `hcusp : ∀ j, (x j).IsCusp` using `fun j => (IrrGL.isCusp_ofChar χ hχ).nu _`. Set `Δ : Fin t → Segment k` to `fun j => Segment.single (x j) (hcusp j)`.

Establish `hfirst : ∀ j, (Δ j).first = x j` using `fun j => Segment.first_ofFirst _ _ _ _`. Establish `hord : IsOrderedForm Δ (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map]`. Use `congr 1`.

Apply `List.ext_get (by simp)` to reduce the goal to its premises. Introduce `i h1 h2`. Simplify using `[Δ, x]`. Introduce and unpack `i j hij ⟨-, m, hm, heq⟩`. Rewrite `heq` using `[hfirst, hfirst]`.

Establish `key : (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + (m : ℝ) : ℝ) : ℂ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[IrrGL.nu_nu]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[IrrGL.nu_ofChar_inj]`. Establish `hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)` using `by exact_mod_cast hij`. Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL : LFactors (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) x` using `⟨Δ, hord, fun j => (single_spec (hcusp j)).2.1⟩`. Take `⟨π0, hπ0⟩` from `H k _ t t x hd hL`. Take `⟨Ψ⟩` from `hπ0.equiv_of_surjective (IrrRep.det (Fin t) χ hχ).irr l hl`. Conclude with `⟨t, x, hd, hL, hπ0.of_equiv Ψ.symm (Representation.Equiv.refl _)⟩`.
-/
theorem isL_det : StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k))
      (IrrRep.det (Fin t) χ hχ).ρ := by
  intro H k _ _ _ _ _ t χ hχ
  let x : Fin t → IrrGL k := fun j => (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)
  obtain ⟨hd, l, hl⟩ := DetQuot.exists_surjective_prodIrr t hχ (x := x) (fun j => rfl)
  have hcusp : ∀ j, (x j).IsCusp := fun j => (IrrGL.isCusp_ofChar χ hχ).nu _
  let Δ : Fin t → Segment k := fun j => Segment.single (x j) (hcusp j)
  have hfirst : ∀ j, (Δ j).first = x j := fun j => Segment.first_ofFirst _ _ _ _
  have hord : IsOrderedForm Δ (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) := by
    refine ⟨?_, ?_⟩
    · rw [Fin.univ_val_map]
      congr 1
      apply List.ext_get (by simp)
      intro i h1 h2
      simp [Δ, x]
    · rintro i j hij ⟨-, m, hm, heq⟩
      rw [hfirst, hfirst] at heq
      have key : (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) =
          (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + (m : ℝ) : ℝ) : ℂ) := by
        calc (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) = x j := rfl
          _ = (x i).nu (m : ℂ) := heq
          _ = ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ) : ℂ)).nu (m : ℂ) := rfl
          _ = _ := by
            rw [IrrGL.nu_nu]
            congr 1
            push_cast
            ring
      rw [IrrGL.nu_ofChar_inj] at key
      have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      linarith
  have hL : LFactors (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) x :=
    ⟨Δ, hord, fun j => (single_spec (hcusp j)).2.1⟩
  obtain ⟨π0, hπ0⟩ := H k _ t t x hd hL
  obtain ⟨Ψ⟩ := hπ0.equiv_of_surjective (IrrRep.det (Fin t) χ hχ).irr l hl
  exact ⟨t, x, hd, hL, hπ0.of_equiv Ψ.symm (Representation.Equiv.refl _)⟩

end GlobalTheory.LocGL

end
