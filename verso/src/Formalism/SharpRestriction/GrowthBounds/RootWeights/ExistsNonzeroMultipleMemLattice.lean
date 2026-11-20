import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem
import Lemmata.GeneralBFactLeftVersion.Imports

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Assemble the required witnesses or components as `⟨hfg, hM⟩`.
-/
theorem finite_full_submodule_isLattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hfg : M.FG) (hM : MQ (K := KK O) M = ⊤) : Submodule.IsLattice (KK O) M :=
  ⟨hfg, hM⟩

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_ …`.
-/
theorem exists_nonzero_multiple_mem_lattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hM : MQ (K := KK O) M = ⊤) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Introduce `O _ _ _ V _ _ _ _ _ M hfg hM t z hz`. Establish `: Submodule.IsLattice (KK O) M` using `finite_full_submodule_isLattice M hfg hM`. Set `b` to `Module.finBasis O M`. Set `B` to `b.extendOfIsLattice (KK O)`. Establish `hB : ∀ i, B i = ((b i : M) : V)` using `fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i`.

Establish `hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o`. Introduce `i x hx`. Use `⟨b.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations. Establish `h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j`. Establish `h2` using `congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`. Use `h2.symm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hB, algebraMap_smul]`. Use `conv_lhs => rw [h1]`.

Simplify using `[Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]`. Use `choose o ho using fun i => hz (B.coord i) (hcoord i)`. Use `⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← B.sum_repr z, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `ho i` as an intermediate fact. Rewrite `this` using `[Module.Basis.coord_apply]`. Rewrite using `[this, hB, mul_smul, algebraMap_smul]`.
-/
theorem dual_lattice_values_mem_scaled : DualLatticeDivisibility := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM t z hz
  have : Submodule.IsLattice (KK O) M := finite_full_submodule_isLattice M hfg hM
  let b := Module.finBasis O M
  let B := b.extendOfIsLattice (KK O)
  have hB : ∀ i, B i = ((b i : M) : V) := fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i
  have hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o := by
    intro i x hx
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j := by
      have h2 := congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      refine h2.symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, algebraMap_smul]
    conv_lhs => rw [h1]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]
  choose o ho using fun i => hz (B.coord i) (hcoord i)
  refine ⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
  rw [← B.sum_repr z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ho i
  rw [Module.Basis.coord_apply] at this
  rw [this, hB, mul_smul, algebraMap_smul]

/- English proof (translation)
Introduce `O _ _ _ V _ _ _ _ _ M hfg hM H`. Set `N : Submodule O H` to `M.comap (H.subtype.restrictScalars O)`. Establish `hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M` using `fun x => Iff.rfl`. Establish `hNoeM : IsNoetherian O M` using `isNoetherian_of_fg_of_noetherian M hfg`. Set `φ : N →ₗ[O] M` to `{ toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩ map_add' := fun x y => rfl map_smul' := fun a x => rfl }`.

Establish `hφ : Function.Injective φ`. Introduce `x y hxy`. Establish `: ((x : H) : V) = ((y : H) : V)` using `congrArg (fun w : M => (w : V)) hxy`. Conclude with `Subtype.ext (Subtype.ext this)`. Establish `hNoeN : IsNoetherian O N` using `isNoetherian_of_injective φ hφ`.

Establish `hNfg : N.FG` using `(Module.Finite.iff_fg).1 inferInstance`. Establish `hNspan : Submodule.span (KK O) (N : Set H) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, ha, hax⟩` from `exists_nonzero_multiple_mem_lattice M hM (x : V)`.

Establish `ha1 : algebraMap O (KK O) a ≠ 0` using `(map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha`. Establish `hmem : a • x ∈ N` using `(hmemN _).2 (by simpa using hax)`. Establish `hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x)`. Rewrite using `[← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]`. Rewrite using `[hx]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Establish `: Submodule.IsLattice (KK O) N` using `⟨hNfg, hNspan⟩`. Set `b` to `Module.finBasis O N`. Set `B` to `b.extendOfIsLattice (KK O)`. Establish `hB : ∀ i, B i = ((b i : N) : H)` using `fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i`.

Use `⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)`. Establish `h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B)`. Use function extensionality and compare the values at `j`. Simplify using `[hB]`.

Rewrite using `[h2]`. Conclude with `h1`. Introduce `x hx`. Establish `h1` using `congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`.

Rewrite using `[← h1]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)` and prove the remaining obligations. Simplify using `[hB]`. Introduce `x hxM hxH`. Use `⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`. Conclude with `h1.symm`.
-/
theorem lattice_inter_subspace_basis : LatticeSubspaceBasis := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM H
  let N : Submodule O H := M.comap (H.subtype.restrictScalars O)
  have hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M := fun x => Iff.rfl
  have hNoeM : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
  let φ : N →ₗ[O] M :=
    { toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : ((x : H) : V) = ((y : H) : V) := congrArg (fun w : M => (w : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hNoeN : IsNoetherian O N := isNoetherian_of_injective φ hφ
  have hNfg : N.FG := (Module.Finite.iff_fg).1 inferInstance
  have hNspan : Submodule.span (KK O) (N : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_nonzero_multiple_mem_lattice M hM (x : V)
    have ha1 : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha
    have hmem : a • x ∈ N := (hmemN _).2 (by simpa using hax)
    have hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsLattice (KK O) N := ⟨hNfg, hNspan⟩
  let b := Module.finBasis O N
  let B := b.extendOfIsLattice (KK O)
  have hB : ∀ i, B i = ((b i : N) : H) := fun i => Module.Basis.extendOfIsLattice_apply (KK O) b i
  refine ⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩
  · have h1 := B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
    have h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B) := by
      funext j
      simp [hB]
    rw [h2]
    exact h1
  · intro x hx
    have h1 := congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [hB]
  · intro x hxM hxH
    refine ⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩
    have h1 := congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm

end Formalism.MainNotions.G.GLWeightTheory
