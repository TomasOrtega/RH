import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Establish `h1 : ‖(l : PadicAlgCl l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Establish `h2` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C`. Rewrite `h2` using `[zero_mul]`.

Take `⟨N, hN⟩` from `(h2.eventually_le_const zero_lt_one).exists`. Conclude with `⟨N, by rwa [norm_pow]⟩`.
-/
private theorem im_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

/- English proof (translation)
Establish `hl0 : (l : PadicAlgCl l) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`. Use `letI : Algebra c.O E := (c.O.val.toRingHom.codRestrict E fun x => ((hc _).1 x.2).1).toAlgebra`. Establish `ha : ∀ x : c.O, ((algebraMap c.O E x : E) : PadicAlgCl l) = x` using `fun _ => rfl`. Use `haveI : FaithfulSMul c.O E := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => Subtype.ext (congrArg (fun z : E => (z : PadicAlgCl l)) h)`. Use `haveI : IsFractionRing c.O E := by`.

Use `IsFractionRing.of_field _ _ fun z => ?_` and prove the remaining obligations. Take `⟨N, hN⟩` from `im_small (l := l) ‖(z : PadicAlgCl l)‖`. Use `⟨⟨(l : PadicAlgCl l) ^ N * z, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) z.2, by rwa [norm_mul]⟩⟩, (l : c.O) ^ N, Subtype.ext ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[ha]`.

Clear the denominators using the available nonvanishing facts. Set `m : G →* Matrix (Fin n) (Fin n) E` to `{ toFun := fun g => Matrix.of fun i j => ⟨_, hE g i j⟩ map_one' := by`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Use the proof step `map_mul' := fun g h => by`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply] }`. Choose the witnesses or unpack the hypotheses as in `⟨C, hC⟩ : ∃ C : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by`. Establish `h1 : Continuous fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖` using `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hr i j).norm`. Take `⟨C, hC⟩` from `(isCompact_range h1).bddAbove`.

Use `⟨C, fun g i j => le_trans ?_ (hC ⟨g, rfl⟩)⟩` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖) (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)`. Take `⟨N, hN⟩` from `im_small (l := l) C`. Take `⟨Q, r₀, hQ⟩` from `UpperTheory.V.Pa.Det.latInt (A := c.O) (F := E) m.toHomUnits ((l : c.O) ^ N) (pow_ne_zero _ fun h => hl0 (by simpa using congrArg Subtype.val h)) fun g i j => by`.

Use `⟨⟨(l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) (hE g i j), ?_⟩⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul_of_nonneg_left (hC g i j) (norm_nonneg _)).trans hN`. Rewrite using `[ha]`. Use `push_cast`.

Both sides reduce to the same expression. Use `⟨Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l)) Q, r₀, fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l))) (hQ g)`. Rewrite `h` using `[map_mul, map_mul]`. Apply the tactic sequence `convert h using 2 <;> (ext i j; rfl)`.
-/
private theorem im_model {l : ℕ} [hl : Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {n : ℕ}
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (r : G →* GL (Fin n) (PadicAlgCl l)) (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j)
    (hE : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ E) :
    ∃ (Q : GL (Fin n) (PadicAlgCl l)) (r₀ : G →* GL (Fin n) c.O),
      ∀ g, r g * Q = Q * W.pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  letI : Algebra c.O E := (c.O.val.toRingHom.codRestrict E fun x => ((hc _).1 x.2).1).toAlgebra
  have ha : ∀ x : c.O, ((algebraMap c.O E x : E) : PadicAlgCl l) = x := fun _ => rfl
  haveI : FaithfulSMul c.O E := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    Subtype.ext (congrArg (fun z : E => (z : PadicAlgCl l)) h)
  haveI : IsFractionRing c.O E := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨N, hN⟩ := im_small (l := l) ‖(z : PadicAlgCl l)‖
    refine ⟨⟨(l : PadicAlgCl l) ^ N * z, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) z.2, by rwa [norm_mul]⟩⟩,
      (l : c.O) ^ N, Subtype.ext ?_⟩
    push_cast
    rw [ha]
    field_simp
  let m : G →* Matrix (Fin n) (Fin n) E :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hE g i j⟩
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by
    have h1 : Continuous fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ :=
      continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hr i j).norm
    obtain ⟨C, hC⟩ := (isCompact_range h1).bddAbove
    refine ⟨C, fun g i j => le_trans ?_ (hC ⟨g, rfl⟩)⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨N, hN⟩ := im_small (l := l) C
  obtain ⟨Q, r₀, hQ⟩ := UpperTheory.V.Pa.Det.latInt (A := c.O) (F := E) m.toHomUnits ((l : c.O) ^ N)
    (pow_ne_zero _ fun h => hl0 (by simpa using congrArg Subtype.val h)) fun g i j => by
      refine ⟨⟨(l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, (hc _).2
        ⟨mul_mem (pow_mem (natCast_mem _ _) _) (hE g i j), ?_⟩⟩, Subtype.ext ?_⟩
      · rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC g i j) (norm_nonneg _)).trans hN
      · rw [ha]
        push_cast
        rfl
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l)) Q, r₀, fun g => ?_⟩
  have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l))) (hQ g)
  rw [map_mul, map_mul] at h
  convert h using 2 <;> (ext i j; rfl)

/- English proof (translation)
Take `⟨-, -, hlm, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Establish `hl0 : (l : PadicAlgCl l) ^ N ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)`. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations. Establish `h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖` using `((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)`. Use `filter_upwards [h1] with y hy`.

Rewrite using `[Ideal.Quotient.eq]`. Establish `h2 : ((f y : PadicAlgCl l) - f x) / (l : PadicAlgCl l) ^ N ∈ c.O` using `(hc _).2 ⟨div_mem (sub_mem ((hc _).1 (f y).2).1 ((hc _).1 (f x).2).1) (pow_mem (natCast_mem _ _) _), by`. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ hy.le (norm_nonneg _)⟩`. Establish `h3 : f y - f x = (l : c.O) ^ N * ⟨_, h2⟩` using `Subtype.ext (by push_cast; field_simp)`.

Rewrite using `[h3]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)`.
-/
private theorem im_cont {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) :
    IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal c.O ^ N) (f g) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  rw [Ideal.Quotient.eq]
  have h2 : ((f y : PadicAlgCl l) - f x) / (l : PadicAlgCl l) ^ N ∈ c.O := (hc _).2
    ⟨div_mem (sub_mem ((hc _).1 (f y).2).1 ((hc _).1 (f x).2).1) (pow_mem (natCast_mem _ _) _), by
      rw [norm_div]
      exact div_le_one_of_le₀ hy.le (norm_nonneg _)⟩
  have h3 : f y - f x = (l : c.O) ^ N * ⟨_, h2⟩ := Subtype.ext (by push_cast; field_simp)
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)

/- English proof (translation)
Take `⟨s, hs⟩ : (Subalgebra.toSubmodule c.O).FG` from `Module.Finite.iff_fg.1 c.fin`. Use `⟨IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l)), IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hx' : x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l))` using `by rw [hs]; exact hx clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin _ _ hy`.

Consider the case `zero => exact zero_mem _`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `smul a y _ hy`. Rewrite using `[← algebraMap_smul ℚ_[l] a y]`. Conclude with `IntermediateField.smul_mem _ hy`.

Establish `hi : IsIntegral ℤ_[l] x` using `(Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]`. Introduce `n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]`.

Conclude with `PadicInt.norm_le_one _`.
-/
private theorem im_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  refine ⟨IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul ℚ_[l] a y]
      exact IntermediateField.smul_mem _ hy
  · have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
    have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
    rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

/- English proof (translation)
Introduce `l _ c H _ _ _ _ _ n ρ hρ`. Establish `hr : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j` using `fun i j => (Units.continuous_val.comp hρ).matrix_elem i j`. Take `⟨E₁, f₁, m₁⟩` from `GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l H n ρ hr`. Take `⟨E₂, f₂, m₂⟩` from `im_field c`. Take `⟨c', hc⟩` from `UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)`.

Take `⟨Q, r₀, hQ⟩` from `im_model (E₁ ⊔ E₂) c' hc ρ hr fun g i j => (le_sup_left : E₁ ≤ _) (m₁ g i j)`. Establish `hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q` using `fun g => by`. Rewrite using `[mul_assoc, hQ, inv_mul_cancel_left]`. Use `⟨c', Q, r₀, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ _) (m₂ x hx).1, (m₂ x hx).2⟩, hQ, fun i j N => ?_⟩` and prove the remaining obligations. Use `im_cont (E₁ ⊔ E₂) c' hc _ ?_ N` and prove the remaining obligations.

Establish `e : (fun g => ((W.mat r₀ g i j : c'.O) : PadicAlgCl l)) = fun g => ((Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j`. Use function extensionality and compare the values at `g`. Rewrite using `[← hQ']`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i j`.
-/
theorem UpperTheory.V.Ws.Eb.intModel :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H] {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ →
        ∃ (c' : Coef l) (Q : GL (Fin n) (PadicAlgCl l)) (ρ₀ : H →* GL (Fin n) c'.O), c.O ≤ c'.O ∧ (∀ g, ρ g * Q = Q * W.pushRep (algebraMap c'.O (PadicAlgCl l)) ρ₀ g) ∧ ∀ i j, Alg.AdicCont (maximalIdeal c'.O) fun g => W.mat ρ₀ g i j := by
  intro l _ c H _ _ _ _ _ n ρ hρ
  have hr : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := fun i j =>
    (Units.continuous_val.comp hρ).matrix_elem i j
  obtain ⟨E₁, f₁, m₁⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l H n ρ hr
  obtain ⟨E₂, f₂, m₂⟩ := im_field c
  obtain ⟨c', hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  obtain ⟨Q, r₀, hQ⟩ := im_model (E₁ ⊔ E₂) c' hc ρ hr fun g i j => (le_sup_left : E₁ ≤ _) (m₁ g i j)
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  refine ⟨c', Q, r₀, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ _) (m₂ x hx).1, (m₂ x hx).2⟩, hQ, fun i j N => ?_⟩
  refine im_cont (E₁ ⊔ E₂) c' hc _ ?_ N
  have e : (fun g => ((W.mat r₀ g i j : c'.O) : PadicAlgCl l)) =
      fun g => ((Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := by
    funext g
    rw [← hQ']
    rfl
  rw [e]
  exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i j
