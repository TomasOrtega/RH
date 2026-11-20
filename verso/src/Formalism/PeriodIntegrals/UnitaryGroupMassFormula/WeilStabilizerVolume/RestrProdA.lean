import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PosNear

noncomputable section

namespace PI.VolStabW.RestrProdA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

/- English proof (translation)
Establish `h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1) (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1))` using `hasProd_prod_of_ne_finset_one fun b hb => if_neg hb`. Establish `e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹` using `Finset.prod_congr rfl fun b hb => if_pos hb`. Rewrite `h2` using `[e]`. Use `h.mul h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b ∈ S`. Simplify using `[Set.mulIndicator, hb, hS b hb]`. Simplify using `[Set.mulIndicator, hb]`.
-/
theorem hasProd_compl_of_ne_zero {β : Type} {f : β → ℂ} {p : ℂ} (h : HasProd f p) (S : Finset β)
    (hS : ∀ b ∈ S, f b ≠ 0) :
    HasProd ({b | b ∉ S}.mulIndicator f) (p * ∏ b ∈ S, (f b)⁻¹) := by
  classical
  have h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1)
      (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) := hasProd_prod_of_ne_finset_one fun b hb => if_neg hb
  have e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹ :=
    Finset.prod_congr rfl fun b hb => if_pos hb
  rw [e] at h2
  convert h.mul h2 using 1
  funext b
  by_cases hb : b ∈ S
  · simp [Set.mulIndicator, hb, hS b hb]
  · simp [Set.mulIndicator, hb]

/- English proof (translation)
Unfold `HasProd at h ⊢`. Establish `h1` using `((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h`. Use `h1.congr fun s => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]`. Conclude with `ENNReal.ofReal_prod_of_nonneg fun b _ => hf b`.
-/
theorem hasProd_ofReal_of_complex {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by
  unfold HasProd at h ⊢
  have h1 := ((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact ENNReal.ofReal_prod_of_nonneg fun b _ => hf b

/- English proof (translation)
Distinguish the cases in `h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0`. Conclude with `Or.inl h0`. Use `Or.inr fun S => ?_` and prove the remaining obligations. Use `push_neg at h0`. Use `choose g hgSB hg0 using h0`.

Set `Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ` to `fun v => if v ∈ S then g v else (latV b v).indicator 1`. Establish `hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv`. Use `⟨fun v => ?_, ?_, fun Y => rfl⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [Φv, hv, if_true]`.

Conclude with `hgSB v`. Simplify using `only [Φv, hv, if_false]`. Conclude with `PositiveNearLattice.isSB_latV b v a M`. Use `Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hv (if_neg h)`. Establish `hP` using `(hmult _ Φv hpure).hasProd`. Establish `hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0` using `fun v hv => by`. Simplify using `only [Φv, hv, if_true]`. Conclude with `hg0 v`.

Establish `h1` using `hasProd_compl_of_ne_zero hP S hne`. Establish `hL : ∀ v, MeasurableSet (latV (M` using `M) (n := a) b v) := fun v => (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet`. Establish `hfin : ∀ v, m v (latV b v) ≠ ⊤` using `fun v => by`. Establish `h` using `hSB v _ (PositiveNearLattice.isSB_latV b v a M)`. Rewrite `h` using `[integrable_indicator_iff (hL v)]`.

Conclude with `(((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne`. Establish `e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) = fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v ∈ S`. Simplify using `[Set.mulIndicator, hv]`.

Simplify using `only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]`. Rewrite using `[integral_indicator (hL v)]`. Simplify using `[Measure.real]`. Rewrite `h1` using `[e]`. Establish `h2` using `hasProd_ofReal_of_complex (fun v => by`.

Apply the tactic sequence `by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1`. Establish `e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v))`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v ∈ S`. Simplify using `[Set.mulIndicator, hv]`.

Simplify using `[Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]`. Rewrite `h2` using `[e2]`. Conclude with `⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩`.
-/
theorem rpTail_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by
  classical
  by_cases h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0
  · exact Or.inl h0
  refine Or.inr fun S => ?_
  push_neg at h0
  choose g hgSB hg0 using h0
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => if v ∈ S then g v else (latV b v).indicator 1
  have hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv := by
    refine ⟨fun v => ?_, ?_, fun Y => rfl⟩
    · by_cases hv : v ∈ S
      · simp only [Φv, hv, if_true]; exact hgSB v
      · simp only [Φv, hv, if_false]; exact PositiveNearLattice.isSB_latV b v a M
    · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      exact hv (if_neg h)
  have hP := (hmult _ Φv hpure).hasProd
  have hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0 := fun v hv => by
    simp only [Φv, hv, if_true]; exact hg0 v
  have h1 := hasProd_compl_of_ne_zero hP S hne
  have hL : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
    (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
  have hfin : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
    have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
    rw [integrable_indicator_iff (hL v)] at h
    exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
  have e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) =
      fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]
      rw [integral_indicator (hL v)]
      simp [Measure.real]
  rw [e] at h1
  have h2 := hasProd_ofReal_of_complex (fun v => by
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1
  have e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator
      (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v)) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp [Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]
  rw [e2] at h2
  exact ⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩

/- English proof (translation)
Establish `hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k'` using `fun e => by conv_lhs => rw [← b.sum_repr e]`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`.

Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE, map_sum, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, mul_assoc]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, Finsupp.add_apply, add_mul]`.
-/
theorem repr_change {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by
  have hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k' := fun e => by
    conv_lhs => rw [← b.sum_repr e]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE,
      map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, Finsupp.add_apply, add_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ a M d d' b b'`. Establish `key : ∀ x : F, ∀ᶠ v in Filter.cofinite, algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v))` using `fun x => (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2`. Establish `h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈ (v.adicCompletionIntegers F : Set (Fv F v))` using `Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _`. Establish `h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈ (v.adicCompletionIntegers F : Set (Fv F v))` using `Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _`. Use `filter_upwards [h1, h2] with v hv1 hv2`.

Use extensionality with `Y`. Simplify using `only [latV, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hY x i k'`. Rewrite using `[repr_change (Fv F v) b b']`.

Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')`. Introduce `hY x i k`. Rewrite using `[repr_change (Fv F v) b' b]`. Conclude with `Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)`.
-/
theorem latCofin_holds : LatCofin := by
  intro F E _ _ _ _ a M d d' b b'
  have key : ∀ x : F, ∀ᶠ v in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := fun x =>
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _
  filter_upwards [h1, h2] with v hv1 hv2
  ext Y
  simp only [latV, Set.mem_setOf_eq]
  constructor
  · intro hY x i k'
    rw [repr_change (Fv F v) b b']
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')
  · intro hY x i k
    rw [repr_change (Fv F v) b' b]
    exact Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV d b hSB hmult`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Conclude with `rpTail_gen b (fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) hSB hmult`.
-/
theorem rpTail_holds : RPTail := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV d b hSB hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact rpTail_gen b (fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) hSB hmult

end PI.VolStabW.RestrProdA
