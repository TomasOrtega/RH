import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Conclude with `J.mul_mem_right _ ha`. Conclude with `J.add_mem (ha i) (hb i)`.

Introduce `hx`. Rewrite using `[pi_eq_sum_univ x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top`.
-/
private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]` using `fun i => IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by`. Establish `h` using `hf hmn`. Rewrite `h` using `[SModEq.sub_mem, mem_smul_top_pi]`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.

Conclude with `h i`. Use `choose L hL using key`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, mem_smul_top_pi]`. Introduce `i`.

Establish `h` using `hL i n`. Rewrite `h` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis.
-/
private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

/- English proof (translation)
Use `haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans ℚ_[l]`. Use `haveI : Module.IsTorsionFree ℤ_[l] M := hi.moduleIsTorsionFree _ (map_smul i)`. Use `haveI : Module.Flat ℤ_[l] M := inferInstance`. Establish `hs : ∀ y : TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M, ∃ m : M, TensorProduct.mk ℤ_[l] (ResidueField ℤ_[l]) M 1 m = y` using `TensorProduct.mk_surjective ℤ_[l] M (ResidueField ℤ_[l]) residue_surjective`. Use `choose σ hσ using hs`.

Establish `hr : Module.rank (ResidueField ℤ_[l]) (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) ≤ finrank ℚ_[l] V`. Use `rank_le fun s hs => ?_` and prove the remaining obligations. Establish `h1 : LinearIndependent ℤ_[l] (fun j : s => σ j)` using `IsLocalRing.linearIndependent_of_flat _ (by`. Establish `: (TensorProduct.mk ℤ_[l] (ResidueField ℤ_[l]) M 1 ∘ fun j : s => σ j) = Subtype.val`. Use function extensionality and compare the values at `fun j => hσ j`.

Rewrite using `[this]`. Conclude with `hs)`. Establish `h2` using `h1.map' i (LinearMap.ker_eq_bot.2 hi)`. Establish `h3` using `(LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 h2`. Simplify using `using h3.fintype_card_le_finrank`.

Use `haveI : Module.Finite (ResidueField ℤ_[l]) (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) := Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0))`. Use `haveI : Module.Finite ℤ_[l] (ResidueField ℤ_[l]) := inferInstance`. Use `haveI : Module.Finite ℤ_[l] (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) := Module.Finite.trans (ResidueField ℤ_[l]) _`. Use `haveI : Module.Finite ℤ_[l] (M ⧸ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M)) := @Module.Finite.equiv _ _ _ _ _ _ _ _ this (TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal ℤ_[l]))`. Take `⟨n, p, hp⟩` from `Module.Finite.exists_fin' ℤ_[l] (M ⧸ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M))`.

Take `⟨q, hq⟩` from `Module.projective_lifting_property (Submodule.mkQ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M)) p (Submodule.mkQ_surjective _)`. Use `haveI := isPrecomplete_pi (maximalIdeal ℤ_[l]) n`. Establish `: Function.Surjective q` using `surjective_of_mkQ_comp_surjective (I := maximalIdeal ℤ_[l]) (by rw [hq]; exact hp)`. Conclude with `Module.Finite.of_surjective q this`.
-/
private theorem finOfHaus {l : ℕ} [Fact l.Prime] {V M : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] [Module.Finite ℚ_[l] V] [AddCommGroup M] [Module ℤ_[l] M]
    (i : M →ₗ[ℤ_[l]] V) (hi : Function.Injective i) [IsHausdorff (maximalIdeal ℤ_[l]) M] :
    Module.Finite ℤ_[l] M := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans ℚ_[l]
  haveI : Module.IsTorsionFree ℤ_[l] M := hi.moduleIsTorsionFree _ (map_smul i)
  haveI : Module.Flat ℤ_[l] M := inferInstance
  have hs : ∀ y : TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M, ∃ m : M,
      TensorProduct.mk ℤ_[l] (ResidueField ℤ_[l]) M 1 m = y :=
    TensorProduct.mk_surjective ℤ_[l] M (ResidueField ℤ_[l]) residue_surjective
  choose σ hσ using hs
  have hr : Module.rank (ResidueField ℤ_[l]) (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) ≤ finrank ℚ_[l] V := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndependent ℤ_[l] (fun j : s => σ j) :=
      IsLocalRing.linearIndependent_of_flat _ (by
        have : (TensorProduct.mk ℤ_[l] (ResidueField ℤ_[l]) M 1 ∘ fun j : s => σ j) = Subtype.val :=
          funext fun j => hσ j
        rw [this]; exact hs)
    have h2 := h1.map' i (LinearMap.ker_eq_bot.2 hi)
    have h3 := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 h2
    simpa using h3.fintype_card_le_finrank
  haveI : Module.Finite (ResidueField ℤ_[l]) (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) :=
    Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : Module.Finite ℤ_[l] (ResidueField ℤ_[l]) := inferInstance
  haveI : Module.Finite ℤ_[l] (TensorProduct ℤ_[l] (ResidueField ℤ_[l]) M) :=
    Module.Finite.trans (ResidueField ℤ_[l]) _
  haveI : Module.Finite ℤ_[l] (M ⧸ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M)) :=
    @Module.Finite.equiv _ _ _ _ _ _ _ _ this (TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal ℤ_[l]))
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' ℤ_[l] (M ⧸ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M))
  obtain ⟨q, hq⟩ := Module.projective_lifting_property (Submodule.mkQ (maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] M)) p
    (Submodule.mkQ_surjective _)
  haveI := isPrecomplete_pi (maximalIdeal ℤ_[l]) n
  have : Function.Surjective q := surjective_of_mkQ_comp_surjective (I := maximalIdeal ℤ_[l]) (by rw [hq]; exact hp)
  exact Module.Finite.of_surjective q this

/- English proof (translation)
Use `letI := moduleTopology ℚ_[l] V`. Use `haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩`. Conclude with `(IsModuleTopology.continuous_of_linearMap ψ).comp hφ`.
-/
private theorem qcont_lin {l : ℕ} [Fact l.Prime] {V W X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℚ_[l] W]
    [TopologicalSpace X] {φ : X → V} (hφ : QCont l φ) (ψ : V →ₗ[ℚ_[l]] W) : Continuous fun g => ψ (φ g) := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap ψ).comp hφ

/- English proof (translation)
Set `b` to `Module.finBasis ℚ_[l] V`. Establish `hc : Continuous fun g => b.equivFun.toLinearMap (φ g)` using `qcont_lin hφ _`. Take `⟨C, hC⟩` from `(isCompact_range hc).isBounded.exists_norm_le`. Take `⟨t, ht⟩` from `NormedField.exists_lt_norm ℚ_[l] (max C 0)`. Establish `ht0 : 0 < ‖t‖` using `(le_max_right _ _).trans_lt ht`.

Establish `ht1 : t ≠ 0` using `norm_pos_iff.1 ht0`. Use `⟨Submodule.span ℤ_[l] (Set.range fun j => t • b j), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← b.sum_equivFun (φ g)]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : ‖b.equivFun (φ g) j / t‖ ≤ 1`.

Rewrite using `[norm_div, div_le_one ht0]`. Conclude with `(norm_le_pi_norm _ j).trans ((hC _ ⟨g, rfl⟩).trans ((le_max_left _ _).trans ht.le))`. Take `⟨z, hz⟩ : ∃ z : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] z = b.equivFun (φ g) j / t` from `⟨⟨_, h1⟩, rfl⟩`. Establish `h2 : b.equivFun (φ g) j • b j = z • (t • b j)`. Rewrite using `[← algebraMap_smul ℚ_[l] z, smul_smul, hz, div_mul_cancel₀ _ ht1]`.

Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
private theorem bddLattice {l : ℕ} [Fact l.Prime] {V X : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] [Module.Finite ℚ_[l] V] [TopologicalSpace X] [CompactSpace X]
    {φ : X → V} (hφ : QCont l φ) : ∃ L : Submodule ℤ_[l] V, L.FG ∧ ∀ g, φ g ∈ L := by
  classical
  let b := Module.finBasis ℚ_[l] V
  have hc : Continuous fun g => b.equivFun.toLinearMap (φ g) := qcont_lin hφ _
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
  have ht0 : 0 < ‖t‖ := (le_max_right _ _).trans_lt ht
  have ht1 : t ≠ 0 := norm_pos_iff.1 ht0
  refine ⟨Submodule.span ℤ_[l] (Set.range fun j => t • b j), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩
  rw [← b.sum_equivFun (φ g)]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 : ‖b.equivFun (φ g) j / t‖ ≤ 1 := by
    rw [norm_div, div_le_one ht0]
    exact (norm_le_pi_norm _ j).trans ((hC _ ⟨g, rfl⟩).trans ((le_max_left _ _).trans ht.le))
  obtain ⟨z, hz⟩ : ∃ z : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] z = b.equivFun (φ g) j / t := ⟨⟨_, h1⟩, rfl⟩
  have h2 : b.equivFun (φ g) j • b j = z • (t • b j) := by
    rw [← algebraMap_smul ℚ_[l] z, smul_smul, hz, div_mul_cancel₀ _ ht1]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Use `haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans ℚ_[l]`. Use `haveI : Module.IsTorsionFree ℤ_[l] M := hi.moduleIsTorsionFree _ (map_smul i)`. Use `haveI : Module.Free ℤ_[l] M := inferInstance`. Set `e` to `Module.finBasis ℤ_[l] M`. Establish `h3` using `(LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 (e.linearIndependent.map' i (LinearMap.ker_eq_bot.2 hi))`.

Take `⟨ψ, hψ⟩` from `(Fintype.linearCombination ℚ_[l] (i ∘ e)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (h3.fintypeLinearCombination_injective))`. Establish `key : ∀ m : M, ψ (i m) = fun j => (e.equivFun m j : ℚ_[l])`. Introduce `m`. Establish `: i m = Fintype.linearCombination ℚ_[l] (i ∘ e) fun j => (e.equivFun m j : ℚ_[l])` using `by conv_lhs => rw [← e.sum_equivFun m]`. Rewrite using `[Fintype.linearCombination_apply, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← algebraMap_smul ℚ_[l]]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `LinearMap.congr_fun hψ _`.

Establish `hc` using `qcont_lin hφ ψ`. Simplify using `only [key] at hc`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ)` using `zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _`. Use `filter_upwards [hc.continuousAt (Metric.closedBall_mem_nhds _ hpos)] with g hg`. Establish `h4 : ∀ j, ∃ c : ℤ_[l], c * (l : ℤ_[l]) ^ N = e.equivFun (φ g - φ g₀) j`.

Introduce `j`. Rewrite using `[← Ideal.mem_span_singleton', ← PadicInt.norm_le_pow_iff_mem_span_pow]`. Establish `h5` using `(dist_le_pi_dist _ _ j).trans (Metric.mem_closedBall.1 hg)`. Rewrite `h5` using `[dist_eq_norm]`. Rewrite using `[map_sub]`.

Conclude with `h5`. Use `choose c hcc using h4`. Use `⟨e.equivFun.symm c, e.equivFun.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `j`.

Rewrite using `[← hcc j, mul_comm]`. Both sides reduce to the same expression.
-/
private theorem evCongr {l : ℕ} [Fact l.Prime] {V M X : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (i : M →ₗ[ℤ_[l]] V) (hi : Function.Injective i) [TopologicalSpace X] {φ : X → M}
    (hφ : QCont l fun g => i (φ g)) (N : ℕ) (g₀ : X) :
    ∀ᶠ g in nhds g₀, ∃ m : M, φ g - φ g₀ = ((l : ℤ_[l]) ^ N) • m := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans ℚ_[l]
  haveI : Module.IsTorsionFree ℤ_[l] M := hi.moduleIsTorsionFree _ (map_smul i)
  haveI : Module.Free ℤ_[l] M := inferInstance
  let e := Module.finBasis ℤ_[l] M
  have h3 := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1
    (e.linearIndependent.map' i (LinearMap.ker_eq_bot.2 hi))
  obtain ⟨ψ, hψ⟩ := (Fintype.linearCombination ℚ_[l] (i ∘ e)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (h3.fintypeLinearCombination_injective))
  have key : ∀ m : M, ψ (i m) = fun j => (e.equivFun m j : ℚ_[l]) := by
    intro m
    have : i m = Fintype.linearCombination ℚ_[l] (i ∘ e) fun j => (e.equivFun m j : ℚ_[l]) := by
      conv_lhs => rw [← e.sum_equivFun m]
      rw [Fintype.linearCombination_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← algebraMap_smul ℚ_[l]]
      rfl
    rw [this]
    exact LinearMap.congr_fun hψ _
  have hc := qcont_lin hφ ψ
  simp only [key] at hc
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hc.continuousAt (Metric.closedBall_mem_nhds _ hpos)] with g hg
  have h4 : ∀ j, ∃ c : ℤ_[l], c * (l : ℤ_[l]) ^ N = e.equivFun (φ g - φ g₀) j := by
    intro j
    rw [← Ideal.mem_span_singleton', ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have h5 := (dist_le_pi_dist _ _ j).trans (Metric.mem_closedBall.1 hg)
    rw [dist_eq_norm] at h5
    rw [map_sub]
    exact h5
  choose c hcc using h4
  refine ⟨e.equivFun.symm c, e.equivFun.injective ?_⟩
  rw [map_smul, LinearEquiv.apply_symm_apply]
  funext j
  rw [← hcc j, mul_comm]
  rfl

section Ring

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
  {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
  [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]

/- English proof (translation)
Establish `h : (maximalIdeal O).comap (algebraMap ℤ_[l] O) = maximalIdeal ℤ_[l]` using `eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))`. Rewrite `hc` using `[← h]`. Conclude with `hc`.
-/
private theorem maxZ_le (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] {c : ℤ_[l]} (hc : c ∈ maximalIdeal ℤ_[l]) : algebraMap ℤ_[l] O c ∈ maximalIdeal O := by
  have h : (maximalIdeal O).comap (algebraMap ℤ_[l] O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))
  rw [← h] at hc
  exact hc

include l in
omit [IsNoetherianRing O] in
/- English proof (translation)
Establish `hs : Function.Surjective f.rangeRestrict` using `f.rangeRestrict_surjective`. Use `haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (f.rangeRestrict : R →+* f.range) hs`. Use `haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (f.rangeRestrict : R →+* f.range) hs`. Use `haveI : IsLocalHom (f.rangeRestrict : R →+* f.range) := IsLocalHom.of_surjective _ hs`. Establish `hle : maximalIdeal ℤ_[l] ≤ (maximalIdeal f.range).comap (algebraMap ℤ_[l] f.range)`.

Introduce `c hc`. Establish `h1` using `map_nonunit (f.rangeRestrict : R →+* f.range) _ (map_nonunit (algebraMap O R) _ (maxZ_le l O hc))`. Rewrite using `[Ideal.mem_comap, IsScalarTower.algebraMap_apply ℤ_[l] O f.range, ← f.rangeRestrict.commutes]`. Conclude with `h1`. Use `haveI : IsHausdorff (maximalIdeal ℤ_[l]) f.range := ⟨fun x hx => by`.

Use `IsHausdorff.haus' (I := maximalIdeal f.range) x fun n => ?_` and prove the remaining obligations. Establish `h` using `hx n`. Rewrite `h`, the goal using `[SModEq.zero]`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Use `Submodule.smul_induction_on h (fun c hc y _ => ?_) fun a b ha hb => add_mem ha hb` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n hc))⟩`. Use `haveI : Module.Finite ℤ_[l] f.range := finOfHaus (f.range.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective`. Conclude with `Module.Finite.of_restrictScalars_finite ℤ_[l] O _`.
-/
private theorem finRange [Nontrivial B] (f : R →ₐ[O] B) : Module.Finite O f.range := by
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (f.rangeRestrict : R →+* f.range) hs
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (f.rangeRestrict : R →+* f.range) hs
  haveI : IsLocalHom (f.rangeRestrict : R →+* f.range) := IsLocalHom.of_surjective _ hs
  have hle : maximalIdeal ℤ_[l] ≤ (maximalIdeal f.range).comap (algebraMap ℤ_[l] f.range) := by
    intro c hc
    have h1 := map_nonunit (f.rangeRestrict : R →+* f.range) _
      (map_nonunit (algebraMap O R) _ (maxZ_le l O hc))
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply ℤ_[l] O f.range, ← f.rangeRestrict.commutes]
    exact h1
  haveI : IsHausdorff (maximalIdeal ℤ_[l]) f.range := ⟨fun x hx => by
    refine IsHausdorff.haus' (I := maximalIdeal f.range) x fun n => ?_
    have h := hx n
    rw [SModEq.zero] at h ⊢
    rw [smul_eq_mul, Ideal.mul_top]
    refine Submodule.smul_induction_on h (fun c hc y _ => ?_) fun a b ha hb => add_mem ha hb
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n hc))⟩
  haveI : Module.Finite ℤ_[l] f.range :=
    finOfHaus (f.range.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O _

omit [IsNoetherianRing O] in
/- English proof (translation)
Rewrite using `[Ideal.radical_eq_sInf]`. Use `Submodule.mem_sInf.2 fun P hP => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hP`. Use `haveI : Algebra.IsIntegral O f.range := Algebra.IsIntegral.of_injective f.range.val Subtype.val_injective`. Take `⟨Q, hQ⟩ : ∃ Q : Ideal f.range, ∀ y, y ∈ Q ↔ (y : C) ∈ P` from `⟨Ideal.comap f.range.val P, fun _ => Iff.rfl⟩`.

Establish `hQ' : Q = Ideal.comap f.range.val P` using `Ideal.ext hQ`. Use `haveI : Q.IsPrime := hQ' ▸ Ideal.comap_isPrime _ _`. Establish `h3 : Q.comap (algebraMap O f.range) = maximalIdeal O` using `((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top this)) fun o ho => (hQ _).2 (h1 (Ideal.mem_map_of_mem _ ho))).symm`. Use `haveI h4 : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) _ (h3 ▸ maximalIdeal.isMaximal O)`. Establish `h5` using `Ideal.comap_isMaximal_of_surjective f.rangeRestrict f.rangeRestrict_surjective (K := Q)`.

Rewrite `ha` using `[← eq_maximalIdeal h5]`. Conclude with `(hQ _).1 ha`.
-/
private theorem mem_rad {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C] (f : R →ₐ[O] C) {a : R}
    (ha : a ∈ maximalIdeal R) : f a ∈ ((maximalIdeal O).map (algebraMap O C)).radical := by
  rw [Ideal.radical_eq_sInf]
  refine Submodule.mem_sInf.2 fun P hP => ?_
  obtain ⟨h1, h2⟩ := hP
  haveI : Algebra.IsIntegral O f.range := Algebra.IsIntegral.of_injective f.range.val Subtype.val_injective
  obtain ⟨Q, hQ⟩ : ∃ Q : Ideal f.range, ∀ y, y ∈ Q ↔ (y : C) ∈ P := ⟨Ideal.comap f.range.val P, fun _ => Iff.rfl⟩
  have hQ' : Q = Ideal.comap f.range.val P := Ideal.ext hQ
  haveI : Q.IsPrime := hQ' ▸ Ideal.comap_isPrime _ _
  have h3 : Q.comap (algebraMap O f.range) = maximalIdeal O :=
    ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top this))
      fun o ho => (hQ _).2 (h1 (Ideal.mem_map_of_mem _ ho))).symm
  haveI h4 : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) _ (h3 ▸ maximalIdeal.isMaximal O)
  have h5 := Ideal.comap_isMaximal_of_surjective f.rangeRestrict f.rangeRestrict_surjective (K := Q)
  rw [← eq_maximalIdeal h5] at ha
  exact (hQ _).1 ha

/- English proof (translation)
Use `set J := ((maximalIdeal O).map (algebraMap O C)).radical with hJ`. Establish `h1 : ∀ P : Ideal C, P.IsMaximal → P = J`. Introduce `P hP`. Establish `h2 : P.comap (algebraMap O C) = maximalIdeal O` using `eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)`. Establish `h3 : J ≤ P` using `hP.isPrime.radical_le_iff.2 (Ideal.map_le_iff_le_comap.2 h2.ge)`.

Use `le_antisymm (fun c hc => ?_) h3` and prove the remaining obligations. Take `⟨o, ho⟩` from `h c`. Establish `h4 : o ∈ maximalIdeal O`. Rewrite using `[← h2, Ideal.mem_comap]`. Simplify using `using P.sub_mem hc (h3 ho)`.

Simplify using `using J.add_mem ho (Ideal.le_radical (Ideal.mem_map_of_mem _ h4))`. Take `⟨P, hP⟩` from `Ideal.exists_maximal C`. Use `haveI : IsLocalRing C := IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => (h1 Q hQ).trans (h1 P hP).symm⟩`. Use `co_finite O O C fun c => ?_` and prove the remaining obligations. Rewrite using `[h1 _ (maximalIdeal.isMaximal C)]`.

Conclude with `h c`.
-/
private theorem coOfRad [IsAdicComplete (maximalIdeal O) O] {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    [Nontrivial C] (h : ∀ c : C, ∃ o : O, c - algebraMap O C o ∈ ((maximalIdeal O).map (algebraMap O C)).radical) :
    IsCO O C := by
  set J := ((maximalIdeal O).map (algebraMap O C)).radical with hJ
  have h1 : ∀ P : Ideal C, P.IsMaximal → P = J := by
    intro P hP
    have h2 : P.comap (algebraMap O C) = maximalIdeal O :=
      eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
    have h3 : J ≤ P := hP.isPrime.radical_le_iff.2 (Ideal.map_le_iff_le_comap.2 h2.ge)
    refine le_antisymm (fun c hc => ?_) h3
    obtain ⟨o, ho⟩ := h c
    have h4 : o ∈ maximalIdeal O := by
      rw [← h2, Ideal.mem_comap]
      simpa using P.sub_mem hc (h3 ho)
    simpa using J.add_mem ho (Ideal.le_radical (Ideal.mem_map_of_mem _ h4))
  obtain ⟨P, hP⟩ := Ideal.exists_maximal C
  haveI : IsLocalRing C := IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => (h1 Q hQ).trans (h1 P hP).symm⟩
  refine co_finite O O C fun c => ?_
  rw [h1 _ (maximalIdeal.isMaximal C)]
  exact h c

include l in
/- English proof (translation)
Use `haveI := finRange (l := l) f`. Use `haveI := finRange (l := l) f'`. Use `haveI : Module.Finite O (Algebra.adjoin O T) := Algebra.finite_adjoin_of_finite_of_isIntegral hT fun t ht => by`. Take `⟨n, h⟩` from `hn t ht`. Conclude with `⟨X ^ n, monic_X_pow n, by simp [h]⟩`.

Use `haveI := Subalgebra.finite_sup f.range f'.range`. Set `C : Subalgebra O B` to `f.range ⊔ f'.range ⊔ Algebra.adjoin O T`. Use `haveI : Module.Finite O C := Subalgebra.finite_sup _ _`. Establish `hf : ∀ a, f a ∈ C` using `fun a => (le_sup_left.trans le_sup_left : f.range ≤ C) ⟨a, rfl⟩`. Establish `hf' : ∀ a, f' a ∈ C` using `fun a => (le_sup_right.trans le_sup_left : f'.range ≤ C) ⟨a, rfl⟩`.

Establish `hTC : T ⊆ C` using `fun t ht => (le_sup_right : Algebra.adjoin O T ≤ C) (Algebra.subset_adjoin ht)`. Use `⟨C, coOfRad ?_, this, hf, hf', hTC⟩` and prove the remaining obligations. Use `set J := ((maximalIdeal O).map (algebraMap O C)).radical with hJ`. Set `S : Subalgebra O C` to `(⊥ : Subalgebra O (C ⧸ J)).comap (Ideal.Quotient.mkₐ O J)`. Establish `hS : ∀ c : C, c ∈ S ↔ ∃ o : O, c - algebraMap O C o ∈ J` using `fun c => by`.

Simplify using `only [S, Subalgebra.mem_comap, Algebra.mem_bot, Set.mem_range, ← Ideal.Quotient.eq]`. Conclude with `exists_congr fun o => eq_comm`. Establish `hr : ∀ (φ : R →ₐ[O] B) (hφ : ∀ a, φ a ∈ C), φ.range ≤ S.map C.val`. Introduce and unpack `φ hφ _ ⟨a, rfl⟩`. Take `⟨o, ho⟩` from `IsCO.res_surj (O := O) a`.

Use `⟨φ.codRestrict C hφ a, (hS _).2 ⟨o, ?_⟩, rfl⟩` and prove the remaining obligations. Use `mem_rad (φ.codRestrict C hφ) ho` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes]`. Then use the resulting hypothesis. Establish `hC : C ≤ S.map C.val`. Use `sup_le (sup_le (hr f hf) (hr f' hf')) (Algebra.adjoin_le fun t ht => ⟨⟨t, hTC ht⟩, (hS _).2 ⟨0, ?_⟩, rfl⟩)` and prove the remaining obligations.

Take `⟨n, h⟩` from `hn t ht`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: ((⟨t, hTC ht⟩ : C) - algebraMap O C 0) ^ n = 0` using `Subtype.ext (by simpa using h)`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Introduce `c`. Take `⟨c', h1, h2⟩` from `hC c.2`. Establish `: c' = c` using `Subtype.ext h2`. Conclude with `(hS c).1 (this ▸ h1)`.
-/
private theorem coSub [IsAdicComplete (maximalIdeal O) O] [Nontrivial B] (f f' : R →ₐ[O] B) (T : Set B) (hT : T.Finite)
    (hn : ∀ t ∈ T, IsNilpotent t) :
    ∃ C : Subalgebra O B, IsCO O C ∧ Module.Finite O C ∧ (∀ a, f a ∈ C) ∧ (∀ a, f' a ∈ C) ∧ T ⊆ C := by
  haveI := finRange (l := l) f
  haveI := finRange (l := l) f'
  haveI : Module.Finite O (Algebra.adjoin O T) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hT fun t ht => by
      obtain ⟨n, h⟩ := hn t ht
      exact ⟨X ^ n, monic_X_pow n, by simp [h]⟩
  haveI := Subalgebra.finite_sup f.range f'.range
  let C : Subalgebra O B := f.range ⊔ f'.range ⊔ Algebra.adjoin O T
  haveI : Module.Finite O C := Subalgebra.finite_sup _ _
  have hf : ∀ a, f a ∈ C := fun a => (le_sup_left.trans le_sup_left : f.range ≤ C) ⟨a, rfl⟩
  have hf' : ∀ a, f' a ∈ C := fun a => (le_sup_right.trans le_sup_left : f'.range ≤ C) ⟨a, rfl⟩
  have hTC : T ⊆ C := fun t ht => (le_sup_right : Algebra.adjoin O T ≤ C) (Algebra.subset_adjoin ht)
  refine ⟨C, coOfRad ?_, this, hf, hf', hTC⟩
  set J := ((maximalIdeal O).map (algebraMap O C)).radical with hJ
  let S : Subalgebra O C := (⊥ : Subalgebra O (C ⧸ J)).comap (Ideal.Quotient.mkₐ O J)
  have hS : ∀ c : C, c ∈ S ↔ ∃ o : O, c - algebraMap O C o ∈ J := fun c => by
    simp only [S, Subalgebra.mem_comap, Algebra.mem_bot, Set.mem_range, ← Ideal.Quotient.eq]
    exact exists_congr fun o => eq_comm
  have hr : ∀ (φ : R →ₐ[O] B) (hφ : ∀ a, φ a ∈ C), φ.range ≤ S.map C.val := by
    rintro φ hφ _ ⟨a, rfl⟩
    obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) a
    refine ⟨φ.codRestrict C hφ a, (hS _).2 ⟨o, ?_⟩, rfl⟩
    have := mem_rad (φ.codRestrict C hφ) ho
    rwa [map_sub, AlgHom.commutes] at this
  have hC : C ≤ S.map C.val := by
    refine sup_le (sup_le (hr f hf) (hr f' hf')) (Algebra.adjoin_le fun t ht => ⟨⟨t, hTC ht⟩, (hS _).2 ⟨0, ?_⟩, rfl⟩)
    obtain ⟨n, h⟩ := hn t ht
    refine ⟨n, ?_⟩
    have : ((⟨t, hTC ht⟩ : C) - algebraMap O C 0) ^ n = 0 := Subtype.ext (by simpa using h)
    rw [this]
    exact zero_mem _
  intro c
  obtain ⟨c', h1, h2⟩ := hC c.2
  have : c' = c := Subtype.ext h2
  exact (hS c).1 (this ▸ h1)

end Ring

/- English proof (translation)
Introduce `x y h` and use `by refine SemidirectProduct.ext (Units.ext ?_) (congrArg SemidirectProduct.right h :) ext a b exact hι (congrFun (congrFun (congrArg GG.mat h) a) b)`.
-/
private theorem ggmap_inj {C B : Type} [CommRing C] [CommRing B] (ι : C →+* B) (hι : Function.Injective ι) :
    Function.Injective (GG.map (m := 3) ι) := fun x y h => by
  refine SemidirectProduct.ext (Units.ext ?_) (congrArg SemidirectProduct.right h :)
  ext a b
  exact hι (congrFun (congrFun (congrArg GG.mat h) a) b)

/- English proof (translation)
Set `u : G → GG 3 C` to `fun g => ⟨((Matrix.isUnit_iff_isUnit_det _).2 (hu g)).unit, (r g).right⟩`. Establish `h : ∀ g, GG.map ι (u g) = r g` using `fun g => SemidirectProduct.ext (Units.ext (hA g)) rfl`. Conclude with `⟨MonoidHom.mk' u fun g g' => ggmap_inj ι hι (by rw [map_mul, h, h, h, map_mul]), MonoidHom.ext h, fun g => rfl⟩`.
-/
private theorem descend {C B G : Type} [CommRing C] [CommRing B] [Group G] (ι : C →+* B) (hι : Function.Injective ι)
    (r : G →* GG 3 B) (A : G → Matrix (Fin 3) (Fin 3) C) (hA : ∀ g, (A g).map ι = (r g).mat)
    (hu : ∀ g, IsUnit (A g).det) : ∃ r' : G →* GG 3 C, (GG.map ι).comp r' = r ∧ ∀ g, (r' g).mat = A g := by
  let u : G → GG 3 C := fun g => ⟨((Matrix.isUnit_iff_isUnit_det _).2 (hu g)).unit, (r g).right⟩
  have h : ∀ g, GG.map ι (u g) = r g := fun g => SemidirectProduct.ext (Units.ext (hA g)) rfl
  exact ⟨MonoidHom.mk' u fun g g' => ggmap_inj ι hι (by rw [map_mul, h, h, h, map_mul]), MonoidHom.ext h, fun g => rfl⟩

section Main

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem push_val {R B : Type} [CommRing R] [Algebra O R] [CommRing B] [Algebra O B] (C : Subalgebra O B)
    (f : R →ₐ[O] C) (r : Γ →* GG 3 R) : push (C.val.comp f) r = (GG.map (C.val : C →+* B)).comp (push f r) := rfl

end Main

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hm hred hc`. Use `haveI : Nontrivial B := (π : B →+* E).domain_nontrivial`. Use `existsUnique_of_exists_of_unique ?_ fun f f' hf hf' => ?_` and prove the remaining obligations. Set `y : U.R →ₐ[O] B` to `(IsScalarTower.toAlgHom O E B).comp x`. Set `ν : B →ₗ[ℚ_[l]] B` to `LinearMap.id - ((Algebra.ofId E B).comp π).toLinearMap.restrictScalars ℚ_[l]`.

Establish `hν : ∀ z, ν z = z - algebraMap E B (π z)` using `fun _ => rfl`. Establish `hν0 : ∀ z, π (ν z) = 0` using `fun z => by rw [hν, map_sub, π.commutes]; exact sub_self _`. Establish `hνc : ∀ a b, QCont l fun g => ν ((r g).mat a b)` using `fun a b => by`. Use `letI := moduleTopology ℚ_[l] B`. Use `haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩`.

Use `haveI : ContinuousAdd B := IsModuleTopology.toContinuousAdd ℚ_[l] B`. Conclude with `qcont_lin (hc a b) ν`. Use `choose L hL hLm using fun a b => bddLattice (hνc a b)`. Set `N : Submodule ℤ_[l] B` to `(LinearMap.ker (π.toLinearMap.restrictScalars ℚ_[l])).restrictScalars ℤ_[l]`. Establish `hfg : ((⨆ p : Fin 3 × Fin 3, L p.1 p.2) ⊓ N).FG` using `(Submodule.fg_iSup _ fun p : Fin 3 × Fin 3 => hL p.1 p.2).of_le inf_le_left`.

Take `⟨T, hT⟩` from `hfg`. Establish `hTn : ∀ t ∈ (T : Set B), IsNilpotent t` using `fun t ht => hπ t (hT.le (Submodule.subset_span ht)).2`. Take `⟨C, hC, hCf, hy, -, hTC⟩` from `coSub (l := l) y y T T.finite_toSet hTn`. Establish `hνC : ∀ g a b, ν ((r g).mat a b) ∈ C` using `fun g a b => by`. Establish `h1 : ν ((r g).mat a b) ∈ Submodule.span ℤ_[l] (T : Set B)`.

Rewrite using `[hT]`. Conclude with `⟨le_iSup (fun p : Fin 3 × Fin 3 => L p.1 p.2) (a, b) (hLm a b g), hν0 _⟩`. Conclude with `(Submodule.span_le (p := C.toSubmodule.restrictScalars ℤ_[l])).2 hTC h1`. Establish `hent : ∀ g a b, (r g).mat a b = ν ((r g).mat a b) + y ((U.r.hom g).mat a b)` using `fun g a b => by`. Establish `h1 : π ((r g).mat a b) = x ((U.r.hom g).mat a b)` using `congrFun (congrFun (congrArg GG.mat (DFunLike.congr_fun hred g)) a) b`.

Rewrite using `[hν, h1]`. Conclude with `(sub_add_cancel _ _).symm`. Set `A : GQ l → Matrix (Fin 3) (Fin 3) C` to `fun g a b => ⟨(r g).mat a b, by rw [hent]; exact add_mem (hνC g a b) (hy _)⟩`. Establish `hres : ∀ g, (A g).map (res O C) = (rbar O D.η D.Ψ g).mat` using `fun g => by`. Use extensionality with `a b`.

Establish `h1 : A g a b = ⟨_, hνC g a b⟩ + y.codRestrict C hy ((U.r.hom g).mat a b)` using `Subtype.ext (hent g a b)`. Establish `h2 : res O C ⟨_, hνC g a b⟩ = 0`. Take `⟨n, h⟩` from `hπ _ (hν0 ((r g).mat a b))`. Use `IsNilpotent.eq_zero (IsNilpotent.map ⟨n, Subtype.ext ?_⟩ (res O C))` and prove the remaining obligations. Simplify using `using h`.

Rewrite using `[Matrix.map_apply, h1, map_add, h2, zero_add, res_map, ← U.r.red g]`. Both sides reduce to the same expression. Establish `hu : ∀ g, IsUnit (A g).det` using `fun g => by`. Assume the negation of the conclusion as `hn`. Establish `h1 : res O C (A g).det = 0` using `(res_eq_zero_iff O C _).2 hn`.

Rewrite `h1` using `[AlgHom.map_det, AlgHom.mapMatrix_apply, hres]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (rbar O D.η D.Ψ g).left.isUnit).ne_zero h1`. Take `⟨r', hr', hA⟩` from `descend (C.val : C →+* B) Subtype.val_injective r A (fun g => rfl) hu`. Use `haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C`. Establish `hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C`.

Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] O C]`. Conclude with `map_nonunit (algebraMap O C) _ (maxZ_le l O (by`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _))`. Set `ρ : GLift O D.η D.Ψ C` to `{ hom := r' cont := fun a b n => by`.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g₀`. Use `filter_upwards [evCongr (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective (φ := fun g => A g a b) (hc a b) n g₀] with g hg`. Take `⟨m, hg⟩` from `hg`. Rewrite using `[Ideal.Quotient.eq, hA, hA, hg, Algebra.smul_def, map_pow]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl n)`. Use `red := fun g => by`. Use `SemidirectProduct.ext (Units.ext ?_) ?_` and prove the remaining obligations. Conclude with `(congrArg (fun M => Matrix.map M (res O C)) (hA g)).trans (hres g)`. Conclude with `(congrArg SemidirectProduct.right (DFunLike.congr_fun hr' g) :).trans (hm g) }`.

Take `⟨f, hf, -⟩` from `(U.rep C).2 ρ trivial`. Use `⟨C.val.comp f, ?_⟩` and prove the remaining obligations. Rewrite using `[push_val, ← hr']`. Conclude with `congrArg _ (congrArg GLift.hom hf)`. Take `⟨C, hC, -, h1, h2, -⟩` from `coSub (l := l) f f' ∅ Set.finite_empty (by simp)`.

Establish `h3 : U.r.map (f.codRestrict C h1) = U.r.map (f'.codRestrict C h2)`. Use `GLift.ext (MonoidHom.ext fun g => ggmap_inj (C.val : C →+* B) Subtype.val_injective ?_)` and prove the remaining obligations. Conclude with `DFunLike.congr_fun (hf.trans hf'.symm) g`. Establish `h4` using `((U.rep C).2 _ trivial).unique rfl h3.symm`. Use extensionality with `a`.

Conclude with `congrArg Subtype.val (DFunLike.congr_fun h4 a)`.
-/
theorem UpperTheory.V.Loc.unramified_lift_deformation :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : U.R →ₐ[O] E) (r : GQ l →* GG 3 B), HasMult D.η r → (GG.map (π : B →+* E)).comp r = push x U.r.hom → (∀ a b, QCont l fun g => (r g).mat a b) → ∃! f : U.R →ₐ[O] B, push f U.r.hom = r := by
  intro l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hm hred hc
  classical
  haveI : Nontrivial B := (π : B →+* E).domain_nontrivial
  refine existsUnique_of_exists_of_unique ?_ fun f f' hf hf' => ?_
  · let y : U.R →ₐ[O] B := (IsScalarTower.toAlgHom O E B).comp x
    let ν : B →ₗ[ℚ_[l]] B := LinearMap.id - ((Algebra.ofId E B).comp π).toLinearMap.restrictScalars ℚ_[l]
    have hν : ∀ z, ν z = z - algebraMap E B (π z) := fun _ => rfl
    have hν0 : ∀ z, π (ν z) = 0 := fun z => by rw [hν, map_sub, π.commutes]; exact sub_self _
    have hνc : ∀ a b, QCont l fun g => ν ((r g).mat a b) := fun a b => by
      letI := moduleTopology ℚ_[l] B
      haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
      haveI : ContinuousAdd B := IsModuleTopology.toContinuousAdd ℚ_[l] B
      exact qcont_lin (hc a b) ν
    choose L hL hLm using fun a b => bddLattice (hνc a b)
    let N : Submodule ℤ_[l] B := (LinearMap.ker (π.toLinearMap.restrictScalars ℚ_[l])).restrictScalars ℤ_[l]
    have hfg : ((⨆ p : Fin 3 × Fin 3, L p.1 p.2) ⊓ N).FG :=
      (Submodule.fg_iSup _ fun p : Fin 3 × Fin 3 => hL p.1 p.2).of_le inf_le_left
    obtain ⟨T, hT⟩ := hfg
    have hTn : ∀ t ∈ (T : Set B), IsNilpotent t := fun t ht =>
      hπ t (hT.le (Submodule.subset_span ht)).2
    obtain ⟨C, hC, hCf, hy, -, hTC⟩ := coSub (l := l) y y T T.finite_toSet hTn
    have hνC : ∀ g a b, ν ((r g).mat a b) ∈ C := fun g a b => by
      have h1 : ν ((r g).mat a b) ∈ Submodule.span ℤ_[l] (T : Set B) := by
        rw [hT]
        exact ⟨le_iSup (fun p : Fin 3 × Fin 3 => L p.1 p.2) (a, b) (hLm a b g), hν0 _⟩
      exact (Submodule.span_le (p := C.toSubmodule.restrictScalars ℤ_[l])).2 hTC h1
    have hent : ∀ g a b, (r g).mat a b = ν ((r g).mat a b) + y ((U.r.hom g).mat a b) := fun g a b => by
      have h1 : π ((r g).mat a b) = x ((U.r.hom g).mat a b) :=
        congrFun (congrFun (congrArg GG.mat (DFunLike.congr_fun hred g)) a) b
      rw [hν, h1]
      exact (sub_add_cancel _ _).symm
    let A : GQ l → Matrix (Fin 3) (Fin 3) C := fun g a b =>
      ⟨(r g).mat a b, by rw [hent]; exact add_mem (hνC g a b) (hy _)⟩
    have hres : ∀ g, (A g).map (res O C) = (rbar O D.η D.Ψ g).mat := fun g => by
      ext a b
      have h1 : A g a b = ⟨_, hνC g a b⟩ + y.codRestrict C hy ((U.r.hom g).mat a b) := Subtype.ext (hent g a b)
      have h2 : res O C ⟨_, hνC g a b⟩ = 0 := by
        obtain ⟨n, h⟩ := hπ _ (hν0 ((r g).mat a b))
        refine IsNilpotent.eq_zero (IsNilpotent.map ⟨n, Subtype.ext ?_⟩ (res O C))
        simpa using h
      rw [Matrix.map_apply, h1, map_add, h2, zero_add, res_map, ← U.r.red g]
      rfl
    have hu : ∀ g, IsUnit (A g).det := fun g => by
      by_contra hn
      have h1 : res O C (A g).det = 0 := (res_eq_zero_iff O C _).2 hn
      rw [AlgHom.map_det, AlgHom.mapMatrix_apply, hres] at h1
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (rbar O D.η D.Ψ g).left.isUnit).ne_zero h1
    obtain ⟨r', hr', hA⟩ := descend (C.val : C →+* B) Subtype.val_injective r A (fun g => rfl) hu
    haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C
    have hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O C]
      exact map_nonunit (algebraMap O C) _ (maxZ_le l O (by
        rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _))
    let ρ : GLift O D.η D.Ψ C :=
      { hom := r'
        cont := fun a b n => by
          rw [IsLocallyConstant.iff_eventually_eq]
          intro g₀
          filter_upwards [evCongr (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective
            (φ := fun g => A g a b) (hc a b) n g₀] with g hg
          obtain ⟨m, hg⟩ := hg
          rw [Ideal.Quotient.eq, hA, hA, hg, Algebra.smul_def, map_pow]
          exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl n)
        red := fun g => by
          refine SemidirectProduct.ext (Units.ext ?_) ?_
          · exact (congrArg (fun M => Matrix.map M (res O C)) (hA g)).trans (hres g)
          · exact (congrArg SemidirectProduct.right (DFunLike.congr_fun hr' g) :).trans (hm g) }
    obtain ⟨f, hf, -⟩ := (U.rep C).2 ρ trivial
    refine ⟨C.val.comp f, ?_⟩
    rw [push_val, ← hr']
    exact congrArg _ (congrArg GLift.hom hf)
  · obtain ⟨C, hC, -, h1, h2, -⟩ := coSub (l := l) f f' ∅ Set.finite_empty (by simp)
    have h3 : U.r.map (f.codRestrict C h1) = U.r.map (f'.codRestrict C h2) := by
      refine GLift.ext (MonoidHom.ext fun g => ggmap_inj (C.val : C →+* B) Subtype.val_injective ?_)
      exact DFunLike.congr_fun (hf.trans hf'.symm) g
    have h4 := ((U.rep C).2 _ trivial).unique rfl h3.symm
    ext a
    exact congrArg Subtype.val (DFunLike.congr_fun h4 a)
