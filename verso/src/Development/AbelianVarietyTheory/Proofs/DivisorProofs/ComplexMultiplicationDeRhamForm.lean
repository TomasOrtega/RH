import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr)

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_apply {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (x : M₂) : e.conjRingEquiv f x = e (f (e.symm x)) := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[conj_apply]`.
-/
theorem conj_symm_conj {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) : e.symm.conjRingEquiv (e.conjRingEquiv f) = f := by
  ext x; simp [conj_apply]

/- English proof (translation)
Introduce `x y hxy`. Establish `h` using `congrArg (TensorProduct.piScalarRight R K K (Fin n)) hxy`. Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun h i`. Simplify using `[inK] at hi`.

Apply `IsFractionRing.injective R K` to reduce the goal to its premises. Simplify `hi` using `[Algebra.smul_def]`.
-/
theorem inK_injective [IsFractionRing R K] (n : ℕ) : Function.Injective (inK (O := R) K (Fin n → R)) := by
  intro x y hxy
  have h := congrArg (TensorProduct.piScalarRight R K K (Fin n)) hxy
  funext i
  have hi := congrFun h i
  simp [inK] at hi
  apply IsFractionRing.injective R K
  simpa [Algebra.smul_def] using hi

variable {H : Type} [AddCommGroup H] [Module R H]

/- English proof (translation)
Simplify using `[inK, LinearMap.baseChange_tmul]`.
-/
theorem baseChange_inK (T : Module.End R H) (h : H) : T.baseChange K (inK K H h) = inK K H (T h) := by
  simp [inK, LinearMap.baseChange_tmul]

/- English proof (translation)
Use `LinearMap.ext fun h ↦ hinj ?_` and prove the remaining obligations. Establish `e` using `LinearMap.congr_fun hT.eq (inK K H h)`. Simplify using `only [Module.End.mul_apply] at e ⊢`. Rewrite using `[hM, ← baseChange_inK, e, ← LinearMap.map_smul, ← hM, baseChange_inK]`.
-/
theorem commute_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R} {N : Module.End K (K ⊗[R] H)}
    {M : Module.End R H} (hM : IsScaledRestr D N M) {T : Module.End R H} (hT : Commute N (T.baseChange K)) :
    Commute M T := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun hT.eq (inK K H h)
  simp only [Module.End.mul_apply] at e ⊢
  rw [hM, ← baseChange_inK, e, ← LinearMap.map_smul, ← hM, baseChange_inK]

/- English proof (translation)
Use `LinearMap.ext fun h ↦ hinj ?_` and prove the remaining obligations. Establish `e` using `LinearMap.congr_fun h0 (inK K H h)`. Simplify using `only [Module.End.mul_apply, LinearMap.zero_apply] at e ⊢`. Rewrite using `[hM, hM', LinearMap.map_smul, e, smul_zero, smul_zero, map_zero]`.
-/
theorem mul_eq_zero_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R}
    {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H} (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M')
    (h0 : N * N' = 0) : M * M' = 0 := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun h0 (inK K H h)
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at e ⊢
  rw [hM, hM', LinearMap.map_smul, e, smul_zero, smul_zero, map_zero]

/- English proof (translation)
Simplify using `[inK, Algebra.algebraMap_eq_smul_one]`.
-/
theorem bilin_inK (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (inK K H u) (inK K H v) = algebraMap R K (B u v) := by
  simp [inK, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Apply `IsFractionRing.injective R K` to reduce the goal to its premises. Rewrite using `[map_add, map_zero, ← bilin_inK, ← bilin_inK, hM, hM, LinearMap.map_smul₂, LinearMap.map_smul, ← smul_add, hs, smul_zero]`.
-/
theorem skew_of_scaledRestr [IsFractionRing R K] {D : R} {N : Module.End K (K ⊗[R] H)} {M : Module.End R H}
    (hM : IsScaledRestr D N M) (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (u v : H) : B (M u) v + B u (M v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_add, map_zero, ← bilin_inK, ← bilin_inK, hM, hM, LinearMap.map_smul₂, LinearMap.map_smul, ← smul_add, hs, smul_zero]

/- English proof (translation)
Apply `IsFractionRing.injective R K` to reduce the goal to its premises. Rewrite using `[map_zero, ← bilin_inK, hM, hM', LinearMap.map_smul₂, LinearMap.map_smul, hs, smul_zero, smul_zero]`.
-/
theorem orth_of_scaledRestr [IsFractionRing R K] {D : R} {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) (N' y) = 0) (u v : H) : B (M u) (M' v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_zero, ← bilin_inK, hM, hM', LinearMap.map_smul₂, LinearMap.map_smul, hs, smul_zero, smul_zero]

end GlobalTheory.AdmTransport

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr ofF)

/- English proof (translation)
Introduce `E _ _ _ c 𝔠 R _ _ _ K _ _ _ X₀ cm hcm n eH ψ₀ hpol I _ D N M hM hN hNN hskew horth`. Establish `hinj` using `inK_injective (R := R) (K := K) n`. Establish `hact : ∀ a : OF E, act (dp0 R) (𝟙 _) cm (ofF c a) = act (dp0 R) (𝟙 _) X₀.rm a`. Introduce `a`. Use `haveI := cm.hom (ofF c a)`.

Use `haveI := X₀.rm.hom a`. Rewrite using `[act_apply, act_apply]`. Conclude with `push_congr _ _ (hcm a)`. Establish `hcomm : ∀ i (a : OF E), Commute (eH.symm.conjRingEquiv (M i)) (act (dp0 R) (𝟙 _) X₀.rm a)`. Introduce `i a`.

Establish `h1` using `commute_of_scaledRestr hinj (hM i) (hN i a)`. Establish `h2` using `h1.map eH.symm.conjRingEquiv`. Rewrite using `[← hact]`. Simplify `h2` using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, conj_symm_conj]`. Use `set B : LinearMap.BilinForm R (Fin n → R) := ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap with hB`.

Establish `hBψ : ∀ x y, ψ₀ x y = B (eH x) (eH y)` using `by intro x y; simp [hB]`. Establish `hs₀ : ∀ i x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) y + ψ₀ x (eH.symm.conjRingEquiv (M i) y) = 0`. Introduce `i x y`. Rewrite using `[hBψ, hBψ x]`. Simplify `skew_of_scaledRestr (hM i) B (hskew i) (eH x) (eH y)` using `[conj_apply]`.

Establish `ho₀ : ∀ i j x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) (eH.symm.conjRingEquiv (M j) y) = 0`. Introduce `i j x y`. Rewrite using `[hBψ]`. Simplify `orth_of_scaledRestr (hM i) (hM j) B (horth i j) (eH x) (eH y)` using `[conj_apply]`. Use `⟨hcomm, fun i j ↦ ?_, fun c' ψ hψ ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, mul_eq_zero_of_scaledRestr hinj (hM i) (hM j) (hNN i j), map_zero]`. Take `⟨m, t, hm, ht⟩` from `hpol c' ψ hψ`. Establish `hm' : (m : R) ≠ 0` using `Nat.cast_ne_zero.2 hm`. Establish `hT : ∀ i y, act (dp0 R) (𝟙 _) X₀.rm t (eH.symm.conjRingEquiv (M i) y) = eH.symm.conjRingEquiv (M i) (act (dp0 R) (𝟙 _) X₀.rm t y)`. Introduce `i y`.

Use `LinearMap.congr_fun (hcomm i t).eq y` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Conclude with `this.symm`. Use `⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hm'` to reduce the goal to its premises.

Rewrite using `[mul_add, ht, ht, hT, mul_zero]`. Conclude with `hs₀ i x _`. Apply `mul_left_cancel₀ hm'` to reduce the goal to its premises. Rewrite using `[ht, hT, mul_zero]`. Conclude with `ho₀ i j x _`.
-/
theorem admissible_transport_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (cm : OAct (orderC c) X₀.A),
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
    (∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X₀.A)), IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c) ψ →
      ∃ (n : ℕ) (t : 𝓞 (FR E)), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X₀.rm t y)) →
    ∀ (I : Type) [Fintype I] (D : R) (N : I → Module.End K (K ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    (∀ i (a : OF E), Commute (N i) (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a)).baseChange K)) →
    (∀ i j, N i * N j = 0) →
    (∀ i x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) y + LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x (N i y) = 0) →
    (∀ i j x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) (N j y) = 0) → admitted X₀ (fun i ↦ eH.symm.conjRingEquiv (M i)) := by
  intro E _ _ _ c 𝔠 R _ _ _ K _ _ _ X₀ cm hcm n eH ψ₀ hpol I _ D N M hM hN hNN hskew horth
  have hinj := inK_injective (R := R) (K := K) n

  have hact : ∀ a : OF E, act (dp0 R) (𝟙 _) cm (ofF c a) = act (dp0 R) (𝟙 _) X₀.rm a := by
    intro a
    haveI := cm.hom (ofF c a)
    haveI := X₀.rm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm a)

  have hcomm : ∀ i (a : OF E), Commute (eH.symm.conjRingEquiv (M i)) (act (dp0 R) (𝟙 _) X₀.rm a) := by
    intro i a
    have h1 := commute_of_scaledRestr hinj (hM i) (hN i a)
    have h2 := h1.map eH.symm.conjRingEquiv
    rw [← hact]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, conj_symm_conj] using h2
  set B : LinearMap.BilinForm R (Fin n → R) := ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap with hB
  have hBψ : ∀ x y, ψ₀ x y = B (eH x) (eH y) := by intro x y; simp [hB]
  have hs₀ : ∀ i x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) y + ψ₀ x (eH.symm.conjRingEquiv (M i) y) = 0 := by
    intro i x y
    rw [hBψ, hBψ x]
    simpa [conj_apply] using skew_of_scaledRestr (hM i) B (hskew i) (eH x) (eH y)
  have ho₀ : ∀ i j x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) (eH.symm.conjRingEquiv (M j) y) = 0 := by
    intro i j x y
    rw [hBψ]
    simpa [conj_apply] using orth_of_scaledRestr (hM i) (hM j) B (horth i j) (eH x) (eH y)
  refine ⟨hcomm, fun i j ↦ ?_, fun c' ψ hψ ↦ ?_⟩
  · rw [← map_mul, mul_eq_zero_of_scaledRestr hinj (hM i) (hM j) (hNN i j), map_zero]
  · obtain ⟨m, t, hm, ht⟩ := hpol c' ψ hψ
    have hm' : (m : R) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hT : ∀ i y, act (dp0 R) (𝟙 _) X₀.rm t (eH.symm.conjRingEquiv (M i) y) =
        eH.symm.conjRingEquiv (M i) (act (dp0 R) (𝟙 _) X₀.rm t y) := by
      intro i y
      have := LinearMap.congr_fun (hcomm i t).eq y
      simp only [Module.End.mul_apply] at this
      exact this.symm
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · apply mul_left_cancel₀ hm'
      rw [mul_add, ht, ht, hT, mul_zero]
      exact hs₀ i x _
    · apply mul_left_cancel₀ hm'
      rw [ht, hT, mul_zero]
      exact ho₀ i j x _

end GlobalTheory.AdmTransport
