import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS

section

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `hJij : ∀ i j, σ (J i j) = J j i` using `fun i j => by`. Use `congrFun (congrFun hJ j) i` as an intermediate fact. Simplify `this` using `[cT]`. Simplify using `only [form, hform, map_sum, map_mul, hσ, hJij]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_conj_symm (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A}
    (hJ : IsHerm σ J) (a b : n → A) : σ (form σ J b a) = form σ J a b := by
  have hJij : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  simp only [form, hform, map_sum, map_mul, hσ, hJij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hJa : J *ᵥ a = 0`. Use function extensionality and compare the values at `i`. Use `h0 (Pi.single i 1)` as an intermediate fact. Establish `hs : (fun k => σ ((Pi.single i (1 : A) : n → A) k)) = Pi.single i 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite `this` using `[form, hform_eq, hs]`.

Simplify `this` using `[dotProduct, Pi.single_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_form_eq_zero (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : n → A) (h0 : ∀ w, form σ J a w = 0) : a = 0 := by
  have hJa : J *ᵥ a = 0 := by
    funext i
    have := h0 (Pi.single i 1)
    have hs : (fun k => σ ((Pi.single i (1 : A) : n → A) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [form, hform_eq, hs] at this
    simpa [dotProduct, Pi.single_apply] using this
  calc a = (J⁻¹ * J) *ᵥ a := by rw [Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hJa, Matrix.mulVec_zero]

end

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ h hA`. Use `haveI := quad_finite h.quad`. Use `haveI := genAlg_isReduced h hA`. Take `⟨b⟩` from `hA.2.2.1`. Use `haveI : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b`.

Use `haveI : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b`. Take `⟨v, hv⟩` from `hA.2.2.2.1`. Take `⟨τ, hτ, hττ, hτE, hplus⟩` from `exists_adjEquiv h hA`. Establish `hP'` using `hP F E (genAlg (γ : Matrix n n E))`. Set `φ : genAlg (γ : Matrix n n E) →ₗ[E] E` to `{ toFun := fun y => form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v map_add' := fun a b => by`.

Simplify using `only [form, hform_eq, Subalgebra.coe_add, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]`. Use the proof step `map_smul' := fun c a => by`. Simplify using `only [form, hform_eq, Subalgebra.coe_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }`. Take `⟨x, hx⟩` from `hP'.2 φ`. Establish `hxy : ∀ y, Algebra.trace E _ (x * y) = form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v` using `fun y => by`.

Use `LinearMap.congr_fun hx y` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply]`. Then use the resulting hypothesis. Establish `hK : ∀ y y' : genAlg (γ : Matrix n n E), form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) = Algebra.trace E _ (x * (τ y' * y))` using `fun y y' => by`. Rewrite using `[hxy, form_adj _ h.nondeg, ← hτ, Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.

Set `σE : E ≃+* E` to `RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective h.quad.invol)`. Establish `hTr : ∀ z, Algebra.trace E _ (τ z) = σ (Algebra.trace E (genAlg (γ : Matrix n n E)) z)`. Introduce `z`. Establish `he : (algebraMap E (genAlg (γ : Matrix n n E))).comp (σE : E →+* E) = (τ.toRingEquiv : genAlg (γ : Matrix n n E) →+* genAlg (γ : Matrix n n E)).comp (algebraMap E (genAlg (γ : Matrix n n E)))` using `RingHom.ext fun e => (hτE e).symm`. Use `Algebra.trace_eq_of_equiv_equiv σE τ.toRingEquiv he z` as an intermediate fact.

Rewrite using `[this]`. Conclude with `(σE.apply_symm_apply _).symm`. Establish `hxτ : τ x = x`. Use `hP'.1 (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Simplify using `only [Algebra.traceForm_apply]`.

Establish `e1 : τ x * y = τ (x * (τ y * 1))` using `by rw [mul_one, map_mul, hττ]`. Rewrite using `[e1, hTr, ← hK]`. Establish `hs` using `form_conj_symm (σ : E →+* E) h.quad.invol h.herm ((y : Matrix n n E) *ᵥ v) (((1 : genAlg (γ : Matrix n n E)) : Matrix n n E) *ᵥ v)`. Simplify using `only [RingHom.coe_coe] at hs`. Rewrite using `[hs, hK, map_one, one_mul]`.

Establish `hxplus : x ∈ plusAlg σ J (γ : Matrix n n E)` using `(hplus x).2 hxτ`. Establish `hinj : ∀ y : genAlg (γ : Matrix n n E), x * y = 0 → y = 0`. Introduce `y hy`. Establish `h0 : (y : Matrix n n E) *ᵥ v = 0`. Use `eq_zero_of_form_eq_zero (σ : E →+* E) h.nondeg _ fun w => ?_` and prove the remaining obligations.

Take `⟨y', rfl⟩` from `hv.2 w`. Simplify using `only`. Rewrite using `[hK, mul_left_comm, hy, mul_zero, map_zero]`. Use `hv.1 ?_` and prove the remaining obligations. Simplify using `only [h0, ZeroMemClass.coe_zero, Matrix.zero_mulVec]`.

Set `xp : plusAlg σ J (γ : Matrix n n E)` to `⟨x, hxplus⟩`. Use `haveI : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _`. Establish `hsurj : Function.Surjective (LinearMap.mulLeft F xp)`. Use `LinearMap.injective_iff_surjective.1 fun a c hac => ?_` and prove the remaining obligations. Establish `: x * ((a : genAlg (γ : Matrix n n E)) - c) = 0`.

Use `congrArg Subtype.val hac` as an intermediate fact. Simplify using `only [LinearMap.mulLeft_apply] at this`. Rewrite using `[mul_sub]`. Conclude with `sub_eq_zero.2 this`. Conclude with `Subtype.ext (sub_eq_zero.1 (hinj _ this))`.

Take `⟨w, hw⟩` from `hsurj 1`. Establish `hu : IsUnit xp` using `⟨⟨xp, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩`. Use `⟨hu.unit, v, hv, fun y y' => ⟨τ y', hτ y', ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hK]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `x * (τ y' * y) = x * y * τ y'`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem traceClause_of_tracePerfect (hP : TracePerfect) : TraceClause := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  haveI := quad_finite h.quad
  haveI := genAlg_isReduced h hA
  obtain ⟨b⟩ := hA.2.2.1
  haveI : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  haveI : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  obtain ⟨v, hv⟩ := hA.2.2.2.1
  obtain ⟨τ, hτ, hττ, hτE, hplus⟩ := exists_adjEquiv h hA
  have hP' := hP F E (genAlg (γ : Matrix n n E))
  let φ : genAlg (γ : Matrix n n E) →ₗ[E] E :=
    { toFun := fun y => form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v
      map_add' := fun a b => by
        simp only [form, hform_eq, Subalgebra.coe_add, Matrix.add_mulVec, Matrix.mulVec_add,
          dotProduct_add]
      map_smul' := fun c a => by
        simp only [form, hform_eq, Subalgebra.coe_smul, Matrix.smul_mulVec,
          Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }
  obtain ⟨x, hx⟩ := hP'.2 φ
  have hxy : ∀ y, Algebra.trace E _ (x * y) = form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v :=
    fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this

  have hK : ∀ y y' : genAlg (γ : Matrix n n E),
      form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) =
        Algebra.trace E _ (x * (τ y' * y)) := fun y y' => by
    rw [hxy, form_adj _ h.nondeg, ← hτ, Matrix.mulVec_mulVec]
    rfl

  let σE : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective h.quad.invol)
  have hTr : ∀ z, Algebra.trace E _ (τ z) = σ (Algebra.trace E (genAlg (γ : Matrix n n E)) z) := by
    intro z
    have he : (algebraMap E (genAlg (γ : Matrix n n E))).comp (σE : E →+* E) =
        (τ.toRingEquiv : genAlg (γ : Matrix n n E) →+* genAlg (γ : Matrix n n E)).comp
          (algebraMap E (genAlg (γ : Matrix n n E))) := RingHom.ext fun e => (hτE e).symm
    have := Algebra.trace_eq_of_equiv_equiv σE τ.toRingEquiv he z
    rw [this]
    exact (σE.apply_symm_apply _).symm

  have hxτ : τ x = x := by
    refine hP'.1 (LinearMap.ext fun y => ?_)
    simp only [Algebra.traceForm_apply]
    have e1 : τ x * y = τ (x * (τ y * 1)) := by rw [mul_one, map_mul, hττ]
    rw [e1, hTr, ← hK]
    have hs := form_conj_symm (σ : E →+* E) h.quad.invol h.herm
      ((y : Matrix n n E) *ᵥ v) (((1 : genAlg (γ : Matrix n n E)) : Matrix n n E) *ᵥ v)
    simp only [RingHom.coe_coe] at hs
    rw [hs, hK, map_one, one_mul]
  have hxplus : x ∈ plusAlg σ J (γ : Matrix n n E) := (hplus x).2 hxτ

  have hinj : ∀ y : genAlg (γ : Matrix n n E), x * y = 0 → y = 0 := by
    intro y hy
    have h0 : (y : Matrix n n E) *ᵥ v = 0 := by
      refine eq_zero_of_form_eq_zero (σ : E →+* E) h.nondeg _ fun w => ?_
      obtain ⟨y', rfl⟩ := hv.2 w
      simp only
      rw [hK, mul_left_comm, hy, mul_zero, map_zero]
    refine hv.1 ?_
    simp only [h0, ZeroMemClass.coe_zero, Matrix.zero_mulVec]

  let xp : plusAlg σ J (γ : Matrix n n E) := ⟨x, hxplus⟩
  haveI : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have hsurj : Function.Surjective (LinearMap.mulLeft F xp) := by
    refine LinearMap.injective_iff_surjective.1 fun a c hac => ?_
    have : x * ((a : genAlg (γ : Matrix n n E)) - c) = 0 := by
      have := congrArg Subtype.val hac
      simp only [LinearMap.mulLeft_apply] at this
      rw [mul_sub]; exact sub_eq_zero.2 this
    exact Subtype.ext (sub_eq_zero.1 (hinj _ this))
  obtain ⟨w, hw⟩ := hsurj 1
  have hu : IsUnit xp := ⟨⟨xp, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  refine ⟨hu.unit, v, hv, fun y y' => ⟨τ y', hτ y', ?_⟩⟩
  rw [hK]
  congr 1
  change x * (τ y' * y) = x * y * τ y'
  ring

end GlobalTheory.RegSS
