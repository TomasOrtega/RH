import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Mathlib.Algebra.Module.Lattice
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨m, hm⟩` from `pow_unbounded_of_one_lt C h1`. Use `⟨m, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hp : (0 : ℝ) < (l : ℝ) ^ m` using `by positivity`. Rewrite using `[norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hp, mul_one]`.

Conclude with `ha.trans hm.le`.
-/
private theorem exists_pow_mul_norm_le {l : ℕ} [Fact l.Prime] (C : ℝ) :
    ∃ m : ℕ, ∀ a : ℚ_[l], ‖a‖ ≤ C → ‖(l : ℚ_[l]) ^ m * a‖ ≤ 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C h1
  refine ⟨m, fun a ha => ?_⟩
  have hp : (0 : ℝ) < (l : ℝ) ^ m := by positivity
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hp, mul_one]
  exact ha.trans hm.le

/- English proof (translation)
Set `b` to `Module.finBasis ℚ_[l] V`. Set `S : Set V` to `Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)`. Establish `hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i))`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `(IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp (h.comp (continuous_id.prodMk continuous_const))`.

Take `⟨C, hC⟩` from `(isCompact_range hc).isBounded.exists_norm_le`. Take `⟨m, hm⟩` from `exists_pow_mul_norm_le (l := l) C`. Establish `hl : ((l : ℚ_[l]) ^ m) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`. Use `⟨Submodule.span ℤ_[l] S, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Set `N : Submodule ℤ_[l] V` to `Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)`.

Establish `hN : N.FG` using `Submodule.fg_span (Set.finite_range _)`. Use `hN.of_le ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨g, i⟩, rfl⟩`. Establish `e` using `b.sum_repr (ρ g (b i))`.

Simplify using `only [SetLike.mem_coe]`. Rewrite using `[← e]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hk : ‖b.repr (ρ g (b i)) k‖ ≤ C` using `((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)`. Set `z : ℤ_[l]` to `⟨_, hm _ hk⟩`.

Establish `: b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k)`. Rewrite using `[← algebraMap_smul ℚ_[l] z, smul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[eq_top_iff, ← b.span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Submodule.subset_span ⟨(1, i), by simp⟩`. Introduce `g x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨g', i⟩, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨(g * g', i), by simp⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ a hx`.
-/
private theorem exists_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    ∃ L : Submodule ℤ_[l] V, Submodule.IsLattice ℚ_[l] L ∧ ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
  classical
  let b := Module.finBasis ℚ_[l] V
  let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
  have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
    refine continuous_pi fun i => ?_
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
      (h.comp (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
  have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  refine ⟨Submodule.span ℤ_[l] S, ⟨?_, ?_⟩, ?_⟩
  · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, i⟩, rfl⟩
    have e := b.sum_repr (ρ g (b i))
    simp only [SetLike.mem_coe]
    rw [← e]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
      ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
        (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, hm _ hk⟩
    have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
      rw [← algebraMap_smul ℚ_[l] z, smul_smul]
      congr 1
      change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
      field_simp
    rw [this]
    exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
  · rw [eq_top_iff, ← b.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by simp⟩
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Introduce `l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h`. Take `⟨L, hL, hst⟩` from `exists_lattice ρ h`. Establish `hr : finrank ℤ_[l] L = finrank ℚ_[l] V`. Unfold `Module.finrank`. Rewrite using `[Submodule.IsLattice.rank' ℚ_[l] L]`.

Set `bL : Basis (Fin (finrank ℚ_[l] V)) ℤ_[l] L` to `Module.finBasisOfFinrankEq ℤ_[l] L hr`. Set `b : Basis (Fin (finrank ℚ_[l] V)) ℚ_[l] V` to `bL.extendOfIsLattice ℚ_[l]`. Set `j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V` to `L.subtype ∘ₗ bL.equivFun.symm.toLinearMap`. Establish `hj : ∀ x, j x = b.equivFun.symm (fun i => (x i : ℚ_[l]))` using `fun x => by`. Simplify using `only [j, b, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, map_sum, map_smul, Submodule.subtype_apply, Basis.extendOfIsLattice_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(algebraMap_smul ℚ_[l] (x i) _).symm`. Set `e : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₜ V` to `{ toEquiv := b.equivFun.symm.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap }`. Establish `hjo : IsOpenEmbedding j`. Establish `: (j : _ → V) = e ∘ Pi.map (fun _ => ((↑) : ℤ_[l] → ℚ_[l]))` using `funext hj`.

Rewrite using `[this]`. Conclude with `e.isOpenEmbedding.comp (IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe)`. Set `r : G → L →ₗ[ℤ_[l]] L` to `fun g => ((ρ g).restrictScalars ℤ_[l]).restrict (hst g)`. Set `ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l])` to `{ toFun := fun g => bL.equivFun.toLinearMap ∘ₗ r g ∘ₗ bL.equivFun.symm.toLinearMap map_one' := by`. Use `LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `ρ 1 _ = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Use the proof step `map_mul' := fun g g' => by`.

Use `LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `ρ (g * g') _ = _`. Rewrite using `[map_mul]`. Use `rfl }`.

Establish `hρ : ∀ g x, j (ρT g x) = ρ g (j x)` using `fun g x => by`. Express the relevant statement in the definitionally equal form `L.subtype (bL.equivFun.symm (bL.equivFun (r g (bL.equivFun.symm x)))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Use `⟨ρT, j, ?_, hjo, hρ, fun y => ?_⟩` and prove the remaining obligations.

Unfold `ReciprocityTheory.Gal.ContAction`. Rewrite using `[hjo.isEmbedding.continuous_iff]`. Establish `: (j ∘ fun p : G × (Fin (finrank ℚ_[l] V) → ℤ_[l]) => ρT p.1 p.2) = fun p => ρ p.1 (j p.2)`. Use function extensionality and compare the values at `fun p => hρ _ _`. Rewrite using `[this]`.

Conclude with `h.comp (continuous_fst.prodMk (hjo.continuous.comp continuous_snd))`. Take `⟨m, hm⟩` from `exists_pow_mul_norm_le (l := l) ‖b.equivFun y‖`. Use `⟨m, fun i => ⟨_, hm _ (norm_le_pi_norm (b.equivFun y) i)⟩, ?_⟩` and prove the remaining obligations. Use `(hj _).trans ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.symm_apply_eq, ← algebraMap_smul ℚ_[l] ((l : ℤ_[l]) ^ m) y, map_smul]`.

Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(l : ℚ_[l]) ^ m * b.equivFun y i = _`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.exists_invariant_lattice_openEmbedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∃ (ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l])) (j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT ∧ IsOpenEmbedding j ∧ (∀ g x, j (ρT g x) = ρ g (j x)) ∧ ∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  obtain ⟨L, hL, hst⟩ := exists_lattice ρ h
  have hr : finrank ℤ_[l] L = finrank ℚ_[l] V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ_[l] L]
  let bL : Basis (Fin (finrank ℚ_[l] V)) ℤ_[l] L := Module.finBasisOfFinrankEq ℤ_[l] L hr
  let b : Basis (Fin (finrank ℚ_[l] V)) ℚ_[l] V := bL.extendOfIsLattice ℚ_[l]
  let j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V := L.subtype ∘ₗ bL.equivFun.symm.toLinearMap
  have hj : ∀ x, j x = b.equivFun.symm (fun i => (x i : ℚ_[l])) := fun x => by
    simp only [j, b, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, map_sum, map_smul,
      Submodule.subtype_apply, Basis.extendOfIsLattice_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ℚ_[l] (x i) _).symm
  let e : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₜ V :=
    { toEquiv := b.equivFun.symm.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap }
  have hjo : IsOpenEmbedding j := by
    have : (j : _ → V) = e ∘ Pi.map (fun _ => ((↑) : ℤ_[l] → ℚ_[l])) := funext hj
    rw [this]
    exact e.isOpenEmbedding.comp (IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe)
  let r : G → L →ₗ[ℤ_[l]] L := fun g => ((ρ g).restrictScalars ℤ_[l]).restrict (hst g)
  let ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l]) :=
    { toFun := fun g => bL.equivFun.toLinearMap ∘ₗ r g ∘ₗ bL.equivFun.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        change ρ 1 _ = _
        rw [map_one]; rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          Module.End.mul_apply]
        change ρ (g * g') _ = _
        rw [map_mul]; rfl }
  have hρ : ∀ g x, j (ρT g x) = ρ g (j x) := fun g x => by
    change L.subtype (bL.equivFun.symm (bL.equivFun (r g (bL.equivFun.symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  refine ⟨ρT, j, ?_, hjo, hρ, fun y => ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [hjo.isEmbedding.continuous_iff]
    have : (j ∘ fun p : G × (Fin (finrank ℚ_[l] V) → ℤ_[l]) => ρT p.1 p.2) = fun p => ρ p.1 (j p.2) :=
      funext fun p => hρ _ _
    rw [this]
    exact h.comp (continuous_fst.prodMk (hjo.continuous.comp continuous_snd))
  · obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) ‖b.equivFun y‖
    refine ⟨m, fun i => ⟨_, hm _ (norm_le_pi_norm (b.equivFun y) i)⟩, ?_⟩
    refine (hj _).trans ?_
    rw [LinearEquiv.symm_apply_eq, ← algebraMap_smul ℚ_[l] ((l : ℤ_[l]) ^ m) y, map_smul]
    funext i
    change (l : ℚ_[l]) ^ m * b.equivFun y i = _
    simp
