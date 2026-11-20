import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Rewrite using `[QuotientGroup.subsingleton_iff, eq_top_iff]`. Introduce `g _`. Rewrite using `[Subgroup.mem_center_iff]`. Introduce `h`. Use extensionality with `i j`.

Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify using `[Matrix.mul_apply, mul_comm]`.
-/
theorem subsingleton_quot_one : Subsingleton (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := by
  rw [QuotientGroup.subsingleton_iff, eq_top_iff]
  intro g _
  rw [Subgroup.mem_center_iff]
  intro h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

/- English proof (translation)
Use `⟨fun h => h.2.1, fun h => ⟨one_pos, h, ?_⟩⟩` and prove the remaining obligations. Use `letI : MeasurableSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := borel _`. Use `haveI : BorelSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := ⟨rfl⟩`. Use `haveI := subsingleton_quot_one (k := k)`. Use `⟨Measure.haar, inferInstance, fun v ℓ _ => ?_⟩` and prove the remaining obligations.

Use `show ∫⁻ q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k), ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2 ∂Measure.haar < ⊤`. Establish `e : (fun q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k) => ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2) = fun _ => ‖ℓ (c.rep.ρ (1 : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)).out v)‖ₑ ^ 2`. Use function extensionality and compare the values at `fun q => by rw [Subsingleton.elim q 1]`. Rewrite using `[e, lintegral_const]`. Conclude with `ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) isCompact_univ.measure_lt_top`.
-/
theorem isSquareIntegrable_one_iff (c : IrrCl (GL (Fin 1) k)) :
    IsSquareIntegrable (⟨1, c⟩ : IrrGL k) ↔ IsUnitarisable (IrrGL.rep ⟨1, c⟩) := by
  refine ⟨fun h => h.2.1, fun h => ⟨one_pos, h, ?_⟩⟩
  letI : MeasurableSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := borel _
  haveI : BorelSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := ⟨rfl⟩
  haveI := subsingleton_quot_one (k := k)
  refine ⟨Measure.haar, inferInstance, fun v ℓ _ => ?_⟩
  show ∫⁻ q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k), ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2 ∂Measure.haar < ⊤
  have e : (fun q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k) => ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2) =
      fun _ => ‖ℓ (c.rep.ρ (1 : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)).out v)‖ₑ ^ 2 :=
    funext fun q => by rw [Subsingleton.elim q 1]
  rw [e, lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) isCompact_univ.measure_lt_top

/- English proof (translation)
Assemble the required witnesses or components as `⟨δ, 1, h, le_rfl, isSpeh_one δ⟩`.
-/
theorem IsSquareIntegrable.isUnitarySpeh {δ : IrrGL k} (h : IsSquareIntegrable δ) : IsUnitarySpeh δ :=
  ⟨δ, 1, h, le_rfl, isSpeh_one δ⟩

/- English proof (translation)
Establish `h : IsUnitarySpeh (IrrGL.of π hs hi)` using `((isSquareIntegrable_one_iff _).2 (GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf π hs hi) hu)).isUnitarySpeh`. Establish `hd : ∑ _ : Fin 1, (IrrGL.of π hs hi).1 = (IrrGL.of π hs hi).1` using `by simp`. Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_one (IrrGL.of π hs hi) hd`. Conclude with `⟨[IrrGL.of π hs hi], [], by simpa using h, by simp, 1, fun _ => IrrGL.of π hs hi, hd, rfl, ⟨(IrrGL.equivOf π hs hi).trans ψ⟩⟩`.
-/
theorem conclusion_one {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hu : IsUnitarisable π) :
    ∃ (u : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = 1), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd)) := by
  have h : IsUnitarySpeh (IrrGL.of π hs hi) :=
    ((isSquareIntegrable_one_iff _).2
      (GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf π hs hi) hu)).isUnitarySpeh
  have hd : ∑ _ : Fin 1, (IrrGL.of π hs hi).1 = (IrrGL.of π hs hi).1 := by simp
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (IrrGL.of π hs hi) hd
  exact ⟨[IrrGL.of π hs hi], [], by simpa using h, by simp, 1, fun _ => IrrGL.of π hs hi, hd, rfl,
    ⟨(IrrGL.equivOf π hs hi).trans ψ⟩⟩

/- English proof (translation)
Take `⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩` from `GenericUnitary.isComplementaryProduct_zero hi`. Choose the witnesses or unpack the hypotheses as in `rfl : h = 0 := by`. Assume the negation of the conclusion as `h0`. Set `a : Fin h` to `⟨0, Nat.pos_of_ne_zero h0⟩`. Take `⟨y, s, hy, -, e⟩` from `GenericUnitary.exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)`.

Establish `h1` using `(Finset.sum_eq_zero_iff.1 hd) a (Finset.mem_univ _)`. Rewrite `h1` using `[e]`. Conclude with `hy.deg_pos.ne' h1`. Conclude with `⟨[], [], by simp, by simp, 0, x, hd, by simp [GenericUnitary.factors], φ⟩`.
-/
theorem conclusion_zero {π : Representation ℂ (GL (Fin 0) k) V} (hi : π.IsIrreducible) :
    ∃ (u : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = 0), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := GenericUnitary.isComplementaryProduct_zero hi
  obtain rfl : h = 0 := by
    by_contra h0
    let a : Fin h := ⟨0, Nat.pos_of_ne_zero h0⟩
    obtain ⟨y, s, hy, -, e⟩ := GenericUnitary.exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)
    have h1 := (Finset.sum_eq_zero_iff.1 hd) a (Finset.mem_univ _)
    rw [e] at h1
    exact hy.deg_pos.ne' h1
  exact ⟨[], [], by simp, by simp, 0, x, hd, by simp [GenericUnitary.factors], φ⟩

/- English proof (translation)
Set `_` to `IsTopologicalAddGroup.rightUniformSpace k`. Use `isUniformAddGroup_of_addCommGroup (G := k)` as an intermediate fact. Set `_ : (Valued.v (R` to `k)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Conclude with `NormedSpace.noncompactSpace k k`.
-/
theorem noncompactSpace_field : NoncompactSpace k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedSpace.noncompactSpace k k

/- English proof (translation)
Use `haveI := noncompactSpace_field (k := k)`. Set `f : GL (Fin 2) k → k` to `fun g => g.val 0 1 * (g⁻¹).val 1 1`. Establish `hf : Continuous f`. Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `(Units.continuous_val (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 0 1`.

Conclude with `(Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 1 1`. Establish `hc : ∀ a b : GL (Fin 2) k, (QuotientGroup.leftRel (Subgroup.center (GL (Fin 2) k))) a b → f a = f b`. Introduce `a b hab`. Rewrite `hab` using `[QuotientGroup.leftRel_apply, Matrix.GeneralLinearGroup.center_eq_range_scalar]`. Take `⟨z, hz⟩` from `hab`.

Take `rfl : b = a * Matrix.GeneralLinearGroup.scalar (Fin 2) z` from `by rw [hz]; simp`. Simplify using `only [f]`. Rewrite using `[mul_inv_rev, ← map_inv, Units.val_mul, Units.val_mul]`. Simplify using `only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply, RingHom.toMonoidHom_eq_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Rewrite using `[mul_assoc, Units.mul_inv_cancel_left]`.

Establish `hs : Function.Surjective f` using `fun x => by`. Use `⟨⟨!![1, x; 0, 1], !![1, -x; 0, 1], ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`. Use `show x * 1 = x`.

Conclude with `mul_one x`. Use `⟨fun h => ?_⟩` and prove the remaining obligations. Use `h.image (hf.quotient_lift hc)` as an intermediate fact. Use `noncompact_univ k ?_` and prove the remaining obligations. Use `this` and compare the differences between its conclusion and the goal.

Use `(Set.eq_univ_of_forall fun x => ?_).symm` and prove the remaining obligations. Take `⟨g, rfl⟩` from `hs x`. Conclude with `⟨QuotientGroup.mk g, trivial, rfl⟩`.
-/
theorem noncompactSpace_quot_two : NoncompactSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := by
  haveI := noncompactSpace_field (k := k)
  let f : GL (Fin 2) k → k := fun g => g.val 0 1 * (g⁻¹).val 1 1
  have hf : Continuous f := by
    refine Continuous.mul ?_ ?_
    · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 0 1
    · exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 1 1
  have hc : ∀ a b : GL (Fin 2) k, (QuotientGroup.leftRel (Subgroup.center (GL (Fin 2) k))) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hab
    obtain ⟨z, hz⟩ := hab
    obtain rfl : b = a * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by rw [hz]; simp
    simp only [f]
    rw [mul_inv_rev, ← map_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply,
      RingHom.toMonoidHom_eq_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [mul_assoc, Units.mul_inv_cancel_left]
  have hs : Function.Surjective f := fun x => by
    refine ⟨⟨!![1, x; 0, 1], !![1, -x; 0, 1], ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · show x * 1 = x
      exact mul_one x
  refine ⟨fun h => ?_⟩
  have := h.image (hf.quotient_lift hc)
  refine noncompact_univ k ?_
  convert this
  refine (Set.eq_univ_of_forall fun x => ?_).symm
  obtain ⟨g, rfl⟩ := hs x
  exact ⟨QuotientGroup.mk g, trivial, rfl⟩

/- English proof (translation)
Use `letI : MeasurableSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := borel _`. Use `haveI : BorelSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := ⟨rfl⟩`. Use `haveI := noncompactSpace_quot_two (k := k)`. Establish `key : ∀ μ : Measure (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)), μ.IsHaarMeasure → μ Set.univ = ⊤` using `fun μ _ => measure_univ_of_isMulLeftInvariant μ`. Introduce and unpack `⟨-, -, μ, hμ, H⟩`.

Establish `hs : L.toLinearMap ∈ smoothPart c.rep.ρ.dual`. Express the relevant statement in the definitionally equal form `IsOpen {g | c.rep.ρ.dual g L.toLinearMap = L.toLinearMap}`. Use `isOpen_univ` and compare the differences between its conclusion and the goal. Conclude with `Set.eq_univ_of_forall fun g => LinearMap.ext fun w => e g⁻¹ w`. Establish `h : ∫⁻ q : GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k), ‖L (c.rep.ρ q.out (L.symm 1))‖ₑ ^ 2 ∂μ < ⊤` using `H (L.symm 1) _ hs`.

Simplify using `only [e, L.apply_symm_apply, lintegral_const] at h`. Rewrite `h` using `[key μ hμ]`. Simplify using `at h`.
-/
theorem not_isSquareIntegrable_of_trivial (c : IrrCl (GL (Fin 2) k)) (L : c.rep.V ≃ₗ[ℂ] ℂ)
    (e : ∀ g w, L (c.rep.ρ g w) = L w) : ¬ IsSquareIntegrable (⟨2, c⟩ : IrrGL k) := by
  letI : MeasurableSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := borel _
  haveI : BorelSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := ⟨rfl⟩
  haveI := noncompactSpace_quot_two (k := k)
  have key : ∀ μ : Measure (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)), μ.IsHaarMeasure → μ Set.univ = ⊤ :=
    fun μ _ => measure_univ_of_isMulLeftInvariant μ
  rintro ⟨-, -, μ, hμ, H⟩
  have hs : L.toLinearMap ∈ smoothPart c.rep.ρ.dual := by
    change IsOpen {g | c.rep.ρ.dual g L.toLinearMap = L.toLinearMap}
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g => LinearMap.ext fun w => e g⁻¹ w
  have h : ∫⁻ q : GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k), ‖L (c.rep.ρ q.out (L.symm 1))‖ₑ ^ 2 ∂μ < ⊤ :=
    H (L.symm 1) _ hs
  simp only [e, L.apply_symm_apply, lintegral_const] at h
  rw [key μ hμ] at h
  simp at h

/- English proof (translation)
Set `φ` to `IrrGL.equivOf (detRep (Fin 2) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar) (isIrreducible_ofChar _)`. Use `not_isSquareIntegrable_of_trivial _ φ.symm.toLinearEquiv fun g w => (φ.symm.toIntertwiningMap.isIntertwining _ _ g w).trans ?_` and prove the remaining obligations. Conclude with `(ofChar_apply (detChar (Fin 2) (1 : kˣ →* ℂˣ)) g _).trans (one_mul _)`.
-/
theorem not_isSquareIntegrable_one_two :
    ¬ IsSquareIntegrable (IrrGL.of (detRep (Fin 2) (1 : kˣ →* ℂˣ))
      ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar) (isIrreducible_ofChar _)) := by
  let φ := IrrGL.equivOf (detRep (Fin 2) (1 : kˣ →* ℂˣ))
      ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar) (isIrreducible_ofChar _)
  refine not_isSquareIntegrable_of_trivial _ φ.symm.toLinearEquiv fun g w =>
    (φ.symm.toIntertwiningMap.isIntertwining _ _ g w).trans ?_
  exact (ofChar_apply (detChar (Fin 2) (1 : kˣ →* ℂˣ)) g _).trans (one_mul _)

/- English proof (translation)
Use `⟨IrrGL.ofChar χ hχ, 2, (isSquareIntegrable_one_iff _).2 (GenericUnitary.isUnitarisable_of_equiv (equivRep (IrrRep.det (Fin 1) χ hχ)) ((isUnitarisable_ofChar_iff _).2 fun _ => hu _)), one_le_two, ?_⟩` and prove the remaining obligations. Take `⟨hd, ⟨ψ⟩⟩` from `ProjLine.exists_equiv_prodIrr (θ := ![χ * absPow k (1 / 2), χ * absPow k (-(1 / 2))]) (Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow _), hχ.mul (isSmoothChar_absPow _)⟩) (x := spehFactor (IrrGL.ofChar χ hχ) 2) (Fin.forall_fin_two.2 ⟨by`. Rewrite using `[spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]; norm_num, by`. Rewrite using `[spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`. Use the proof step `norm_num⟩)`.

Use the proof step `(Θ := (detLevi ProjLine.pts χ⁻¹)⁻¹) fun g => by`. Rewrite using `[MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two]`. Simplify using `[absPow_neg, mul_comm, mul_left_comm, mul_assoc]`. Conclude with `⟨hd, (isCosocle_detRep_two hχ).of_equiv (IrrGL.equivOf _ _ _) ψ⟩`.
-/
theorem isUnitarySpeh_detRep_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsUnitarySpeh (IrrGL.of (detRep (Fin 2) χ) ((isSmooth_ofChar_iff _).2 hχ.detChar) (isIrreducible_ofChar _)) := by
  refine ⟨IrrGL.ofChar χ hχ, 2, (isSquareIntegrable_one_iff _).2 (GenericUnitary.isUnitarisable_of_equiv
    (equivRep (IrrRep.det (Fin 1) χ hχ)) ((isUnitarisable_ofChar_iff _).2 fun _ => hu _)), one_le_two, ?_⟩
  obtain ⟨hd, ⟨ψ⟩⟩ := ProjLine.exists_equiv_prodIrr (θ := ![χ * absPow k (1 / 2), χ * absPow k (-(1 / 2))])
    (Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow _), hχ.mul (isSmoothChar_absPow _)⟩)
    (x := spehFactor (IrrGL.ofChar χ hχ) 2)
    (Fin.forall_fin_two.2 ⟨by
      rw [spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]; norm_num, by
      rw [spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]; norm_num⟩)
    (Θ := (detLevi ProjLine.pts χ⁻¹)⁻¹) fun g => by
      rw [MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two]
      simp [absPow_neg, mul_comm, mul_left_comm, mul_assoc]
  exact ⟨hd, (isCosocle_detRep_two hχ).of_equiv (IrrGL.equivOf _ _ _) ψ⟩

end GlobalTheory.UnitaryDual

end
