import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

/- English proof (translation)
Use `letI : TopologicalSpace V := moduleTopology ℚ_[l] V`. Use `haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩`. Conclude with `(IsModuleTopology.continuous_of_linearMap φ).comp hf`.
-/
private theorem continuous_linear_functional_comp {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V]
    (φ : V →ₗ[ℚ_[l]] ℚ_[l]) (f : X → V) (hf : QCont l f) : Continuous fun x => φ (f x) := by
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap φ).comp hf

/- English proof (translation)
Set `e` to `Module.finBasis ℚ_[l] V`. Establish `h1 : Continuous fun g => fun i => e.coord i (f g)` using `continuous_pi fun i => continuous_linear_functional_comp _ f hf`. Take `⟨C, hC⟩` from `(isCompact_range h1).isBounded.exists_norm_le`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hc⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by`. Take `⟨c, hc⟩` from `NormedField.exists_lt_norm ℚ_[l] (max C 0)`.

Conclude with `⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩`. Use `⟨Submodule.span ℤ_[l] (Set.range fun i => c • e i), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← e.sum_repr (f g)]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `h2 : ‖e.repr (f g) i / c‖ ≤ 1`.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hc0)]`. Conclude with `((norm_le_pi_norm (fun i => e.coord i (f g)) i).trans (hC _ ⟨g, rfl⟩)).trans hc`. Set `z : ℤ_[l]` to `⟨_, h2⟩`. Establish `h3 : e.repr (f g) i • e i = z • c • e i`. Rewrite using `[← algebraMap_smul ℚ_[l] z, smul_smul]`.

Use `congr 1`. Conclude with `(div_mul_cancel₀ _ hc0).symm`. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
private theorem continuous_bounded_lattice {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [CompactSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module.Finite ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (f : X → V) (hf : QCont l f) : ∃ M : Submodule ℤ_[l] V, M.FG ∧ ∀ g, f g ∈ M := by
  let e := Module.finBasis ℚ_[l] V
  have h1 : Continuous fun g => fun i => e.coord i (f g) := continuous_pi fun i => continuous_linear_functional_comp _ f hf
  obtain ⟨C, hC⟩ := (isCompact_range h1).isBounded.exists_norm_le
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  refine ⟨Submodule.span ℤ_[l] (Set.range fun i => c • e i), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩
  rw [← e.sum_repr (f g)]
  refine sum_mem fun i _ => ?_
  have h2 : ‖e.repr (f g) i / c‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 hc0)]
    exact ((norm_le_pi_norm (fun i => e.coord i (f g)) i).trans (hC _ ⟨g, rfl⟩)).trans hc
  let z : ℤ_[l] := ⟨_, h2⟩
  have h3 : e.repr (f g) i • e i = z • c • e i := by
    rw [← algebraMap_smul ℚ_[l] z, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hc0).symm
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Use `haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] V`. Use `haveI : Module.IsTorsionFree ℤ_[l] M := Function.Injective.moduleIsTorsionFree j hj (map_smul j)`. Set `b` to `Module.finBasis ℤ_[l] M`. Establish `h1 : LinearIndependent ℚ_[l] (j ∘ b)` using `(LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 (b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj))`. Take `⟨ψ, hψ⟩` from `(Finsupp.linearCombination ℚ_[l] (j ∘ b)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h1)`.

Establish `h2 : ∀ m i, ψ (j m) i = (b.repr m i : ℚ_[l])`. Introduce `m i`. Establish `h3 : j m = Finsupp.linearCombination ℚ_[l] (j ∘ b) ((Finsupp.linearEquivFunOnFinite ℚ_[l] ℚ_[l] _).symm fun i => algebraMap ℤ_[l] ℚ_[l] (b.repr m i))`. Rewrite using `[Finsupp.linearCombination_eq_fintype_linearCombination_apply, Fintype.linearCombination_apply]`. Use `conv_lhs => rw [← b.sum_repr m, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, algebraMap_smul]`. Both sides reduce to the same expression. Rewrite using `[h3, ← LinearMap.comp_apply, hψ]`. Both sides reduce to the same expression.

Establish `h4 : ∀ i, ∀ᶠ g in nhds g₀, ‖b.repr (f g - f g₀) i‖ ≤ (l : ℝ) ^ (-N : ℤ)`. Introduce `i`. Establish `h5 : Continuous fun g => ψ (j (f g)) i` using `continuous_linear_functional_comp ((Finsupp.lapply i).comp ψ) _ hf`. Establish `hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ)` using `zpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos) _`. Use `filter_upwards [Metric.tendsto_nhds.1 (h5.tendsto g₀) _ hp] with g hg`.

Rewrite `hg` using `[dist_eq_norm, h2, h2]`. Rewrite using `[map_sub, Finsupp.sub_apply]`. Conclude with `hg.le`. Use `filter_upwards [Filter.eventually_all.2 h4] with g hg`. Use `choose c hc using fun i => Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 (hg i))`.

Use `⟨∑ i, c i • b i, ?_⟩` and prove the remaining obligations. Rewrite using `[← b.sum_repr (f g - f g₀), Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul]`.
-/
private theorem eventually_congruent_mod_l_pow {l : ℕ} [Fact l.Prime] {X V M : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [AddCommGroup M] [Module ℤ_[l] M]
    [Module.Finite ℤ_[l] M] (j : M →ₗ[ℤ_[l]] V) (hj : Function.Injective j)
    (f : X → M) (hf : QCont l fun g => j (f g)) (N : ℕ) (g₀ : X) :
    ∀ᶠ g in nhds g₀, ∃ m : M, f g - f g₀ = (l : ℤ_[l]) ^ N • m := by
  haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] V
  haveI : Module.IsTorsionFree ℤ_[l] M := Function.Injective.moduleIsTorsionFree j hj (map_smul j)
  let b := Module.finBasis ℤ_[l] M
  have h1 : LinearIndependent ℚ_[l] (j ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 (b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj))
  obtain ⟨ψ, hψ⟩ := (Finsupp.linearCombination ℚ_[l] (j ∘ b)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 h1)
  have h2 : ∀ m i, ψ (j m) i = (b.repr m i : ℚ_[l]) := by
    intro m i
    have h3 : j m = Finsupp.linearCombination ℚ_[l] (j ∘ b)
        ((Finsupp.linearEquivFunOnFinite ℚ_[l] ℚ_[l] _).symm fun i => algebraMap ℤ_[l] ℚ_[l] (b.repr m i)) := by
      rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply, Fintype.linearCombination_apply]
      conv_lhs => rw [← b.sum_repr m, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, algebraMap_smul]
      rfl
    rw [h3, ← LinearMap.comp_apply, hψ]
    rfl
  have h4 : ∀ i, ∀ᶠ g in nhds g₀, ‖b.repr (f g - f g₀) i‖ ≤ (l : ℝ) ^ (-N : ℤ) := by
    intro i
    have h5 : Continuous fun g => ψ (j (f g)) i := continuous_linear_functional_comp ((Finsupp.lapply i).comp ψ) _ hf
    have hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos) _
    filter_upwards [Metric.tendsto_nhds.1 (h5.tendsto g₀) _ hp] with g hg
    rw [dist_eq_norm, h2, h2] at hg
    rw [map_sub, Finsupp.sub_apply]
    exact hg.le
  filter_upwards [Filter.eventually_all.2 h4] with g hg
  choose c hc using fun i => Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 (hg i))
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← b.sum_repr (f g - f g₀), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul]

/- English proof (translation)
Take `⟨p, hp, hpe⟩` from `ha`. Rewrite `hpe` using `[← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]`. Take `⟨n, hn⟩` from `hπ _ hpe`. Conclude with `⟨p ^ n, hp.pow n, by rw [← Polynomial.aeval_def, map_pow, hn]⟩`.
-/
private theorem isIntegral_of_nilpotent_kernel {O B E : Type} [CommRing O] [CommRing B] [CommRing E] [Algebra O B] [Algebra O E]
    (π : B →ₐ[O] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : B) (ha : IsIntegral O (π a)) : IsIntegral O a := by
  obtain ⟨p, hp, hpe⟩ := ha
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at hpe
  obtain ⟨n, hn⟩ := hπ _ hpe
  exact ⟨p ^ n, hp.pow n, by rw [← Polynomial.aeval_def, map_pow, hn]⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `ha`. Take `⟨p, hp, hpe⟩` from `Algebra.IsIntegral.isIntegral (R := O) ((u⁻¹ : Aˣ) : A)`. Use `letI : Invertible ((u⁻¹ : Aˣ) : A) := Units.invertible _`. Establish `h1` using `(Polynomial.eval₂_reverse_eq_zero_iff (algebraMap O A) ((u⁻¹ : Aˣ) : A) p).2 hpe`. Rewrite `h1` using `[invOf_units, inv_inv, hu, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]`.

Establish `h4 : p.reverse = Polynomial.X * p.reverse.divX + Polynomial.C 1` using `by conv_lhs => rw [← Polynomial.X_mul_divX_add p.reverse]`. Rewrite using `[Polynomial.coeff_zero_reverse, hp.leadingCoeff]`. Establish `h5` using `(hπ _ h1).isUnit_sub_one`. Rewrite `h5` using `[h4, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one, add_sub_cancel_right]`. Conclude with `isUnit_of_mul_isUnit_left h5`.
-/
private theorem isUnit_of_nilpotent_kernel {O C A : Type} [CommRing O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A]
    [Algebra.IsIntegral O A] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : C) (ha : IsUnit (π a)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨p, hp, hpe⟩ := Algebra.IsIntegral.isIntegral (R := O) ((u⁻¹ : Aˣ) : A)
  letI : Invertible ((u⁻¹ : Aˣ) : A) := Units.invertible _
  have h1 := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap O A) ((u⁻¹ : Aˣ) : A) p).2 hpe
  rw [invOf_units, inv_inv, hu, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at h1
  have h4 : p.reverse = Polynomial.X * p.reverse.divX + Polynomial.C 1 := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add p.reverse]
    rw [Polynomial.coeff_zero_reverse, hp.leadingCoeff]
  have h5 := (hπ _ h1).isUnit_sub_one
  rw [h4, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one, add_sub_cancel_right] at h5
  exact isUnit_of_mul_isUnit_left h5

/- English proof (translation)
Use `haveI : Nontrivial C := π.toRingHom.domain_nontrivial`. Use `haveI : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self (π a) with h | h` into its components or cases. Conclude with `Or.inl (isUnit_of_nilpotent_kernel π hπ a h)`. Conclude with `Or.inr (isUnit_of_nilpotent_kernel π hπ _ (by rwa [map_sub, map_one]))`.

Use `co_finite O O C fun x => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) (π x)`. Use `⟨a, fun h => ha ?_⟩` and prove the remaining obligations. Use `h.map π` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes]`. Then use the resulting hypothesis.
-/
private theorem complete_of_nilpotent_kernel_finite {O C A : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A] [IsCO O A]
    [Algebra.IsIntegral O A] [Module.Finite O C] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) : IsCO O C := by
  haveI : Nontrivial C := π.toRingHom.domain_nontrivial
  haveI : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (π a) with h | h
    · exact Or.inl (isUnit_of_nilpotent_kernel π hπ a h)
    · exact Or.inr (isUnit_of_nilpotent_kernel π hπ _ (by rwa [map_sub, map_one]))
  refine co_finite O O C fun x => ?_
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (π x)
  refine ⟨a, fun h => ha ?_⟩
  have := h.map π
  rwa [map_sub, AlgHom.commutes] at this

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar R _ _ _ ρ E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hr hc`. Establish `hint : ∀ a, IsIntegral O (x a)` using `fun a => (((ptCont (l := l) R E x).2 (Field.toIsField E)).1 a).tower_top`. Set `πO : B →ₐ[O] E` to `π.restrictScalars O`. Set `S : Set B` to `Set.range fun s : Γ × ι × ι => r s.1 s.2.1 s.2.2`. Set `C : Subalgebra O B` to `Algebra.adjoin O S`.

Establish `hSC : ∀ g a b, r g a b ∈ C` using `fun g a b => Algebra.subset_adjoin ⟨(g, a, b), rfl⟩`. Establish `hCx : ∀ c ∈ C, πO c ∈ x.range` using `fun c hc => (Algebra.adjoin_le (S := x.range.comap πO) (by`. Introduce and unpack `_ ⟨⟨g, a, b⟩, rfl⟩`. Conclude with `⟨ρ.hom g a b, (hr g a b).symm⟩)) hc`. Use `haveI hfin : Module.Finite O C := by choose M hM hMr using fun p : ι × ι => continuous_bounded_lattice _ (hc p.1 p.2)`.

Establish `h1 : (Submodule.span ℤ_[l] S).FG`. Use `Submodule.FG.of_le (Submodule.fg_iSup M hM) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g, a, b⟩, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (a, b) (hMr (a, b) g)`. Take `⟨T, hT⟩` from `h1`.

Establish `h2 : Submodule.span O (T : Set B) = Submodule.span O S`. Rewrite using `[← Submodule.span_span_of_tower ℤ_[l] O (T : Set B), hT, Submodule.span_span_of_tower]`. Establish `h3 : C = Algebra.adjoin O (T : Set B)`. Rewrite using `[← Algebra.adjoin_span (R := O) (s := (T : Set B)), h2, Algebra.adjoin_span]`. Establish `h4 : ∀ t ∈ (T : Set B), IsIntegral O t` using `fun t ht => by`.

Take `⟨y, hy⟩` from `hCx t (h3 ▸ Algebra.subset_adjoin ht)`. Conclude with `isIntegral_of_nilpotent_kernel πO hπ t (hy ▸ hint y)`. Rewrite using `[h3]`. Conclude with `Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet h4`. Use `haveI : IsCO O x.range := co_quot O R _ x.rangeRestrict x.rangeRestrict_surjective`.

Use `haveI : Algebra.IsIntegral O x.range := ⟨fun z => by`. Take `⟨a, rfl⟩` from `x.rangeRestrict_surjective z`. Conclude with `(isIntegral_algHom_iff x.range.val Subtype.val_injective).1 (hint a)⟩`. Set `p : C →ₐ[O] x.range` to `(πO.comp C.val).codRestrict _ fun c => hCx c c.2`. Use `haveI hCO : IsCO O C := complete_of_nilpotent_kernel_finite p fun a ha => by`.

Take `⟨n, hn⟩` from `hπ a (congrArg Subtype.val ha)`. Conclude with `⟨n, Subtype.ext (by simpa using hn)⟩`. Set `r' : Γ →* Matrix ι ι C` to `{ toFun := fun g => Matrix.of fun a b => ⟨r g a b, hSC g a b⟩ map_one' := by`. Use extensionality with `a b`. Simplify using `[Matrix.one_apply, apply_ite Subtype.val]`.

Use the proof step `map_mul' := fun g h => by`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply] }`. Use `⟨C, hCO, ⟨r', fun a b N => ?_, fun g a b => ?_⟩, fun g a b => rfl⟩` and prove the remaining obligations. Use `letI : Algebra ℤ_[l] C := ((algebraMap O C).comp (algebraMap ℤ_[l] O)).toAlgebra haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C`.

Establish `hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C` using `by haveI := (dvrFacts l O).2.2.1`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] O C]`. Use `map_nonunit _ _ (map_nonunit _ _ ?_)` and prove the remaining obligations. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.subset_span rfl`.

Use `(IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_` and prove the remaining obligations. Use `filter_upwards [eventually_congruent_mod_l_pow (l := l) (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective (fun g => r' g a b) (hc a b) N g₀] with g hg`. Take `⟨m, hm⟩` from `hg`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations. Rewrite using `[hm, Algebra.smul_def, map_pow]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl N)`. Rewrite using `[← res_map p, ← ρ.red, ← res_map x.rangeRestrict]`. Use `congr 1`. Conclude with `Subtype.ext (hr g a b)`.
-/
theorem UpperTheory.V.Loc.exists_lift_factor_compact_subalgebra :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : R →ₐ[O] E) (r : Γ →* Matrix ι ι B), (∀ g a b, π (r g a b) = x (ρ.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → ∃ (C : Subalgebra O B) (_ : IsCO O ↥C) (ρ' : Lift O rbar ↥C), ∀ g a b, (ρ'.hom g a b : B) = r g a b := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar R _ _ _ ρ E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hr hc
  classical
  have hint : ∀ a, IsIntegral O (x a) := fun a =>
    (((ptCont (l := l) R E x).2 (Field.toIsField E)).1 a).tower_top
  let πO : B →ₐ[O] E := π.restrictScalars O
  let S : Set B := Set.range fun s : Γ × ι × ι => r s.1 s.2.1 s.2.2
  let C : Subalgebra O B := Algebra.adjoin O S
  have hSC : ∀ g a b, r g a b ∈ C := fun g a b => Algebra.subset_adjoin ⟨(g, a, b), rfl⟩
  have hCx : ∀ c ∈ C, πO c ∈ x.range := fun c hc =>
    (Algebra.adjoin_le (S := x.range.comap πO) (by
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact ⟨ρ.hom g a b, (hr g a b).symm⟩)) hc
  haveI hfin : Module.Finite O C := by
    choose M hM hMr using fun p : ι × ι => continuous_bounded_lattice _ (hc p.1 p.2)
    have h1 : (Submodule.span ℤ_[l] S).FG := by
      refine Submodule.FG.of_le (Submodule.fg_iSup M hM) (Submodule.span_le.2 ?_)
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem (a, b) (hMr (a, b) g)
    obtain ⟨T, hT⟩ := h1
    have h2 : Submodule.span O (T : Set B) = Submodule.span O S := by
      rw [← Submodule.span_span_of_tower ℤ_[l] O (T : Set B), hT, Submodule.span_span_of_tower]
    have h3 : C = Algebra.adjoin O (T : Set B) := by
      rw [← Algebra.adjoin_span (R := O) (s := (T : Set B)), h2, Algebra.adjoin_span]
    have h4 : ∀ t ∈ (T : Set B), IsIntegral O t := fun t ht => by
      obtain ⟨y, hy⟩ := hCx t (h3 ▸ Algebra.subset_adjoin ht)
      exact isIntegral_of_nilpotent_kernel πO hπ t (hy ▸ hint y)
    rw [h3]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet h4
  haveI : IsCO O x.range := co_quot O R _ x.rangeRestrict x.rangeRestrict_surjective
  haveI : Algebra.IsIntegral O x.range := ⟨fun z => by
    obtain ⟨a, rfl⟩ := x.rangeRestrict_surjective z
    exact (isIntegral_algHom_iff x.range.val Subtype.val_injective).1 (hint a)⟩
  let p : C →ₐ[O] x.range := (πO.comp C.val).codRestrict _ fun c => hCx c c.2
  haveI hCO : IsCO O C := complete_of_nilpotent_kernel_finite p fun a ha => by
    obtain ⟨n, hn⟩ := hπ a (congrArg Subtype.val ha)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  let r' : Γ →* Matrix ι ι C :=
    { toFun := fun g => Matrix.of fun a b => ⟨r g a b, hSC g a b⟩
      map_one' := by
        ext a b
        simp [Matrix.one_apply, apply_ite Subtype.val]
      map_mul' := fun g h => by
        ext a b
        simp [Matrix.mul_apply] }
  refine ⟨C, hCO, ⟨r', fun a b N => ?_, fun g a b => ?_⟩, fun g a b => rfl⟩
  · letI : Algebra ℤ_[l] C := ((algebraMap O C).comp (algebraMap ℤ_[l] O)).toAlgebra
    haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C
    have hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C := by
      haveI := (dvrFacts l O).2.2.1
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O C]
      refine map_nonunit _ _ (map_nonunit _ _ ?_)
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_
    filter_upwards [eventually_congruent_mod_l_pow (l := l) (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective
      (fun g => r' g a b) (hc a b) N g₀] with g hg
    obtain ⟨m, hm⟩ := hg
    refine Ideal.Quotient.eq.2 ?_
    rw [hm, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl N)
  · rw [← res_map p, ← ρ.red, ← res_map x.rangeRestrict]
    congr 1
    exact Subtype.ext (hr g a b)
