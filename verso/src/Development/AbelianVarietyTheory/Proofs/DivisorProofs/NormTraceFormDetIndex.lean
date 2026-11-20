import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisSpansUnitaryLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSkewHermitianRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceIntegralOfPreservedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceFormSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGramDetEqIndexStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def skewSub (G : Matrix (Fin r) (Fin r) E) : Submodule (maximalRealSubfield E) (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0}
  zero_mem' := ⟨by simp, by simp [herm, cc]⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    have h2 := hY.2 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX := by
    have hc : IsCMField.complexConj E (c : E) = c := IsCMField.complexConj_apply_eq_self E c
    have e : c • X = (c : E) • X := rfl
    refine ⟨by rw [e, trace_smul, hX.1, smul_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    rw [e]
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hc] at h1 ⊢
    have e1 : ∀ a b, ((c : E) * (X *ᵥ u) a) * G a b * (IsCMField.complexConj E) (w b) =
        (c : E) * ((X *ᵥ u) a * G a b * (IsCMField.complexConj E) (w b)) := fun a b => by ring
    have e2 : ∀ a b, u a * G a b * ((c : E) * (IsCMField.complexConj E) ((X *ᵥ w) b)) =
        (c : E) * (u a * G a b * (IsCMField.complexConj E) ((X *ᵥ w) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h1, mul_zero]

def trForm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) :
    LinearMap.BilinForm (maximalRealSubfield E) (skewSub G) :=
  LinearMap.mk₂ (maximalRealSubfield E)
    (fun X Y => ⟨(X.1 * Y.1).trace, GlobalTheory.T.trace_product_skew_hermitian_real E r G X.1 Y.1 hG hd X.2.2 Y.2.2⟩)
    (fun X₁ X₂ Y => Subtype.ext (by simp [add_mul, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))
    (fun X Y₁ Y₂ => Subtype.ext (by simp [mul_add, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trForm_apply (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (X Y : skewSub G) : ((trForm G hG hd X Y : maximalRealSubfield E) : E) = (X.1 * Y.1).trace := rfl

/- English proof (translation)
Rewrite using `[← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]`.
-/
theorem norm_algebraMap_real (d : maximalRealSubfield E) :
    Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E d) = (Algebra.norm ℚ d) ^ 2 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]

/- English proof (translation)
The claim follows from `isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E) (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective`.
-/
theorem isIntegral_coe_iff (x : maximalRealSubfield E) : IsIntegral ℤ (x : E) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective

/- English proof (translation)
Introduce `E _ _ _ r G Λ e hr hΛ he hli`. Take `⟨hG, hd, hfg, hsp, -⟩` from `hΛ`. Establish `heV : ∀ i, e i ∈ skewSub G` using `fun i => ⟨(he i).1, (he i).2.1⟩`. Use `set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def`. Establish `hve : (skewSub G).subtype ∘ v = e` using `rfl`.

Establish `hvli : LinearIndependent (maximalRealSubfield E) v` using `LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)`. Establish `hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) = Submodule.span _ (Set.range e)`. Rewrite using `[Submodule.map_span, ← Set.range_comp, hve]`. Establish `hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v)`. Introduce and unpack `⟨X, hX⟩ -`.

Establish `h` using `GlobalTheory.T.lie_basis_spans_unitary_lie E r G e hG hd heV hli X hX.1 hX.2`. Rewrite `h` using `[← hmapv]`. Take `⟨y, hy, hyX⟩` from `h`. Establish `: y = ⟨X, hX⟩` using `Subtype.ext hyX`. Rewrite using `[← this]` and apply the resulting hypothesis.

Use `set b := Module.Basis.mk hvli hspan with hb`. Establish `hbv : ∀ i, b i = v i` using `fun i => Module.Basis.mk_apply hvli hspan i`. Use `set B := trForm G hG hd with hB`. Use `set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def`. Establish `hf : Function.Injective f` using `Subtype.val_injective`.

Use `set L' := (lieLat G Λ).comap f with hL'`. Establish `hLrange : lieLat G Λ ≤ f.range` using `fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩`. Establish `hLmap : L'.map f = lieLat G Λ` using `AddSubgroup.map_comap_eq_self hLrange`. Establish `hsymm : B.IsSymm` using `⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩`. Establish `hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0`.

Introduce `X hX`. Apply `Subtype.ext` to reduce the goal to its premises. Use `GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_` and prove the remaining obligations. Use `congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)` as an intermediate fact. Simplify `this` using `[hB, trForm_apply]`.

Establish `hnd : B.Nondegenerate` using `⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩`. Establish `hbL : ∀ i, b i ∈ L'` using `fun i => by rw [hbv]; exact he i`. Establish `hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L'`. Introduce `a x hx`. Use `⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E))` using `(isIntegral_coe_iff _).2 a.isIntegral_coe`. Establish `e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1` using `rfl`. Rewrite using `[e1, smul_mulVec]`. Establish `e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y)`. Rewrite using `[← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]`.

Both sides reduce to the same expression. Rewrite using `[e2]`. Conclude with `Λ.smul_mem _ (hx.2.2 y hy)`. Establish `hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y)`. Introduce `x hx y hy`.

Rewrite using `[← isIntegral_coe_iff, hB, trForm_apply]`. Use `GlobalTheory.T.trace_integral_of_preserved_lattice E r Λ _ hfg hsp fun z hz => ?_` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec]`. Conclude with `hx.2.2 _ (hy.2.2 z hz)`. Establish `key` using `GlobalTheory.T.norm_gram_det_eq_index (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint`.

Establish `hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det = algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]`.

Both sides reduce to the same expression. Establish `I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)})`. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]`. Use `congr 2`. Use extensionality with `Y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← isIntegral_coe_iff, hB, trForm_apply]`. Conclude with `h3 _ hx`.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨y.2.1, y.2.2, fun X hX => ?_⟩` and prove the remaining obligations. Use `hy ⟨X, hX.1, hX.2.1⟩ hX` as an intermediate fact. Rewrite `this` using `[← isIntegral_coe_iff, hB, trForm_apply]`. Conclude with `this`.

Establish `I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) = (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L'`. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]`. Use `congr 1`. Set `g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E` to `{ toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g = Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[g, hbv, v]`. Rewrite using `[← hg, Submodule.map_toAddSubgroup]`.

Both sides reduce to the same expression. Rewrite using `[hdet, norm_algebraMap_real, I1, I2, ← key]`. Use `push_cast`. Rewrite using `[abs_pow, sq_abs]`.
-/
theorem abs_norm_gram_eq_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  intro E _ _ _ r G Λ e hr hΛ he hli
  obtain ⟨hG, hd, hfg, hsp, -⟩ := hΛ
  have heV : ∀ i, e i ∈ skewSub G := fun i => ⟨(he i).1, (he i).2.1⟩
  set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def
  have hve : (skewSub G).subtype ∘ v = e := rfl
  have hvli : LinearIndependent (maximalRealSubfield E) v :=
    LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)
  have hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) =
      Submodule.span _ (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp, hve]
  have hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v) := by
    rintro ⟨X, hX⟩ -
    have h := GlobalTheory.T.lie_basis_spans_unitary_lie E r G e hG hd heV hli X hX.1 hX.2
    rw [← hmapv] at h
    obtain ⟨y, hy, hyX⟩ := h
    have : y = ⟨X, hX⟩ := Subtype.ext hyX
    rwa [← this]
  set b := Module.Basis.mk hvli hspan with hb
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hvli hspan i
  set B := trForm G hG hd with hB
  set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def
  have hf : Function.Injective f := Subtype.val_injective
  set L' := (lieLat G Λ).comap f with hL'
  have hLrange : lieLat G Λ ≤ f.range := fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩
  have hLmap : L'.map f = lieLat G Λ := AddSubgroup.map_comap_eq_self hLrange
  have hsymm : B.IsSymm := ⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩
  have hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0 := by
    intro X hX
    apply Subtype.ext
    refine GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_
    have := congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)
    simpa [hB, trForm_apply] using this
  have hnd : B.Nondegenerate := ⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩
  have hbL : ∀ i, b i ∈ L' := fun i => by rw [hbv]; exact he i
  have hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L' := by
    intro a x hx
    refine ⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩
    have hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E)) := (isIntegral_coe_iff _).2 a.isIntegral_coe
    have e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1 := rfl
    rw [e1, smul_mulVec]
    have e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y) := by
      rw [← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]; rfl
    rw [e2]
    exact Λ.smul_mem _ (hx.2.2 y hy)
  have hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y) := by
    intro x hx y hy
    rw [← isIntegral_coe_iff, hB, trForm_apply]
    refine GlobalTheory.T.trace_integral_of_preserved_lattice E r Λ _ hfg hsp fun z hz => ?_
    rw [← mulVec_mulVec]
    exact hx.2.2 _ (hy.2.2 z hz)
  have key := GlobalTheory.T.norm_gram_det_eq_index (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint
  have hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]
    rfl
  have I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) =
      L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)}) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]
    congr 2
    ext Y
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩
      rw [← isIntegral_coe_iff, hB, trForm_apply]
      exact h3 _ hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, y.2.2, fun X hX => ?_⟩
      have := hy ⟨X, hX.1, hX.2.1⟩ hX
      rw [← isIntegral_coe_iff, hB, trForm_apply] at this
      exact this
  have I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) =
      (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L' := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]
    congr 1
    let g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g =
        Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      simp [g, hbv, v]
    rw [← hg, Submodule.map_toAddSubgroup]
    rfl
  rw [hdet, norm_algebraMap_real, I1, I2, ← key]
  push_cast
  rw [abs_pow, sq_abs]

end GlobalTheory.LieIndex
