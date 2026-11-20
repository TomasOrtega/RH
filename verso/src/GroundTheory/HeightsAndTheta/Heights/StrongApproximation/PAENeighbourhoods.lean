import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

namespace AENeighbourhoods

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

def intBasis (E : Type) [Field E] [NumberField E] (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : E :=
  algebraMap (𝓞 E) E (RingOfIntegers.basis E l)

/- English proof (translation)
Establish `hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))` using `fun v => Valued.isOpen_valuationSubring _`. Set `W' : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)` to `W`. Establish `h2 : W' ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) (𝓝 0)`. Rewrite using `[← RestrictedProduct.nhds_eq_map_structureMap hopen 0]`. Conclude with `hW`.

Establish `h1` using `Filter.mem_map.1 h2`. Rewrite `h1` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `h1`. Use `⟨hI.toFinset, fun x hx0 hxI => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ v, x v ∈ v.adicCompletionIntegers F` using `fun v => by`.

Distinguish the cases in `hv : v ∈ hI.toFinset`. Rewrite using `[hx0 v hv]`. Conclude with `zero_mem _`. Conclude with `hxI v hv`. Set `x' : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))` to `fun v => ⟨x v, hmem v⟩`.

Establish `hx' : x' ∈ I.pi t` using `fun v hv => by`. Establish `: x' v = 0` using `Subtype.ext (hx0 v (hI.mem_toFinset.2 hv))`. Rewrite using `[this]`. Conclude with `mem_of_mem_nhds (ht v)`. Use `hsub hx'` as an intermediate fact.

Conclude with `this`.
-/
theorem nhds_zero_finiteAdele {W : Set (FiniteAdeleRing (𝓞 F) F)} (hW : W ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ x : FiniteAdeleRing (𝓞 F) F,
      (∀ v ∈ S, x v = 0) → (∀ v ∉ S, x v ∈ v.adicCompletionIntegers F) → x ∈ W := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  let W' : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := W
  have h2 : W' ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) =>
      v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite) (𝓝 0) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hopen 0]
    exact hW
  have h1 := Filter.mem_map.1 h2
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  refine ⟨hI.toFinset, fun x hx0 hxI => ?_⟩
  have hmem : ∀ v, x v ∈ v.adicCompletionIntegers F := fun v => by
    by_cases hv : v ∈ hI.toFinset
    · rw [hx0 v hv]; exact zero_mem _
    · exact hxI v hv
  let x' : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨x v, hmem v⟩
  have hx' : x' ∈ I.pi t := fun v hv => by
    have : x' v = 0 := Subtype.ext (hx0 v (hI.mem_toFinset.2 hv))
    rw [this]; exact mem_of_mem_nhds (ht v)
  have := hsub hx'
  exact this

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, b, rfl⟩` from `hx`. Use `⟨fun l => (RingOfIntegers.basis E).repr b l • a, fun l => zsmul_mem ha _, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr b]`.

Rewrite using `[map_sum, tmul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← smul_tmul]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, fun l => zero_mem _, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨y₁, h₁, rfl⟩` from `hx`. Take `⟨y₂, h₂, rfl⟩` from `hy`. Conclude with `⟨y₁ + y₂, fun l => add_mem (h₁ l) (h₂ l), by simp [add_tmul, Finset.sum_add_distrib]⟩`. Consider the case `neg x _ hx`.

Take `⟨y₁, h₁, rfl⟩` from `hx`. Conclude with `⟨-y₁, fun l => neg_mem (h₁ l), by simp [neg_tmul, Finset.sum_neg_distrib]⟩`.
-/
theorem intAt_repr (v : HeightOneSpectrum (𝓞 F)) {z : Kv E v} (hz : z ∈ intAt E v) :
    ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ z = ∑ l, y l ⊗ₜ[F] intBasis E l := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, rfl⟩ := hx
    refine ⟨fun l => (RingOfIntegers.basis E).repr b l • a, fun l => zsmul_mem ha _, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr b]
    rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, ← smul_tmul]
    rfl
  | zero => exact ⟨0, fun l => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    obtain ⟨y₂, h₂, rfl⟩ := hy
    exact ⟨y₁ + y₂, fun l => add_mem (h₁ l) (h₂ l), by simp [add_tmul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    exact ⟨-y₁, fun l => neg_mem (h₁ l), by simp [neg_tmul, Finset.sum_neg_distrib]⟩

/- English proof (translation)
Rewrite using `[map_sum]`. Both sides reduce to the same expression.
-/
theorem compAt_sum (v : HeightOneSpectrum (𝓞 F))
    (X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) :
    compAt E v (∑ l, X l ⊗ₜ[F] intBasis E l) = ∑ l, X l v ⊗ₜ[F] intBasis E l := by
  rw [map_sum]; rfl

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul x y`. Use `⟨fun l => algebraMap ℚ F ((integralBasis E).repr y l) • x, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← (integralBasis E).sum_repr y]`.

Rewrite using `[tmul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[integralBasis_apply, ← IsScalarTower.algebraMap_smul F, tmul_smul, smul_tmul']`. Both sides reduce to the same expression. Consider the case `add x y hx hy`.

Take `⟨X₁, rfl⟩` from `hx`. Take `⟨X₂, rfl⟩` from `hy`. Conclude with `⟨X₁ + X₂, by simp [add_tmul, Finset.sum_add_distrib]⟩`.
-/
theorem exists_repr (a : AE F E) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      a = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    refine ⟨fun l => algebraMap ℚ F ((integralBasis E).repr y l) • x, ?_⟩
    conv_lhs => rw [← (integralBasis E).sum_repr y]
    rw [tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integralBasis_apply, ← IsScalarTower.algebraMap_smul F, tmul_smul, smul_tmul']
    rfl
  | add x y hx hy =>
    obtain ⟨X₁, rfl⟩ := hx
    obtain ⟨X₂, rfl⟩ := hy
    exact ⟨X₁ + X₂, by simp [add_tmul, Finset.sum_add_distrib]⟩

/- English proof (translation)
Establish `hr : ∀ v, v ∉ S → ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F, (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ compAt E v m = ∑ l, y l ⊗ₜ[F] intBasis E l` using `fun v hv => intAt_repr v (hI v hv)`. Use `choose y hyI hyeq using hr`. Set `Y : ∀ v : HeightOneSpectrum (𝓞 F), Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F` to `fun v => if hv : v ∈ S then 0 else y v hv`. Establish `hYI : ∀ v l, Y v l ∈ v.adicCompletionIntegers F` using `fun v l => by`. Distinguish the cases in `hv : v ∈ S`.

Simplify using `only [Y, dif_pos hv, Pi.zero_apply]`. Conclude with `zero_mem _`. Simplify using `only [Y, dif_neg hv]`. Conclude with `hyI v hv l`. Set `X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F` to `fun l => ⟨fun v => Y v l, Filter.Eventually.of_forall fun v => hYI v l⟩`.

Use `⟨X, fun l v hv => ?_, fun l v _ => hYI v l, hsep _ _ fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y v l = 0`. Simplify using `only [Y, dif_pos hv, Pi.zero_apply]`. Rewrite using `[compAt_sum]`. Express the relevant statement in the definitionally equal form `compAt E v m = ∑ l, Y v l ⊗ₜ[F] intBasis E l`.

Distinguish the cases in `hv : v ∈ S`. Simplify using `only [Y, dif_pos hv, Pi.zero_apply, zero_tmul, Finset.sum_const_zero]`. Conclude with `h0 v hv`. Simplify using `only [Y, dif_neg hv]`. Conclude with `hyeq v hv`.
-/
theorem exists_repr_of_int
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {m : AE F E} (h0 : ∀ v ∈ S, compAt E v m = 0)
    (hI : ∀ v ∉ S, compAt E v m ∈ intAt E v) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      (∀ l, ∀ v ∈ S, X l v = 0) ∧ (∀ l, ∀ v ∉ S, X l v ∈ v.adicCompletionIntegers F) ∧
      m = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  classical
  have hr : ∀ v, v ∉ S → ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ compAt E v m = ∑ l, y l ⊗ₜ[F] intBasis E l :=
    fun v hv => intAt_repr v (hI v hv)
  choose y hyI hyeq using hr
  let Y : ∀ v : HeightOneSpectrum (𝓞 F), Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F :=
    fun v => if hv : v ∈ S then 0 else y v hv
  have hYI : ∀ v l, Y v l ∈ v.adicCompletionIntegers F := fun v l => by
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply]; exact zero_mem _
    · simp only [Y, dif_neg hv]; exact hyI v hv l
  let X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F :=
    fun l => ⟨fun v => Y v l, Filter.Eventually.of_forall fun v => hYI v l⟩
  refine ⟨X, fun l v hv => ?_, fun l v _ => hYI v l, hsep _ _ fun v => ?_⟩
  · change Y v l = 0
    simp only [Y, dif_pos hv, Pi.zero_apply]
  · rw [compAt_sum]
    change compAt E v m = ∑ l, Y v l ⊗ₜ[F] intBasis E l
    by_cases hv : v ∈ S
    · simp only [Y, dif_pos hv, Pi.zero_apply, zero_tmul, Finset.sum_const_zero]; exact h0 v hv
    · simp only [Y, dif_neg hv]; exact hyeq v hv

/- English proof (translation)
Take `⟨X, rfl⟩` from `exists_repr a`. Establish `hev : ∀ᶠ v in Filter.cofinite, ∀ l, X l v ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun l => (X l).2`. Use `⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : ∀ l, X l v ∈ v.adicCompletionIntegers F`. Assume the negation of the conclusion as `h`.

Conclude with `hv ((Filter.eventually_cofinite.1 hev).mem_toFinset.2 h)`. Rewrite using `[compAt_sum]`. Conclude with `AddSubgroup.sum_mem _ fun l _ => AddSubgroup.subset_closure ⟨X l v, hv' l, _, rfl⟩`.
-/
theorem int_cofinite (a : AE F E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v := by
  obtain ⟨X, rfl⟩ := exists_repr a
  have hev : ∀ᶠ v in Filter.cofinite, ∀ l, X l v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun l => (X l).2
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv => ?_⟩
  have hv' : ∀ l, X l v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv ((Filter.eventually_cofinite.1 hev).mem_toFinset.2 h)
  rw [compAt_sum]
  exact AddSubgroup.sum_mem _ fun l _ => AddSubgroup.subset_closure ⟨X l v, hv' l, _, rfl⟩

/- English proof (translation)
Use `IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)` as an intermediate fact. Set `ι` to `Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `Ψ : (ι → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin N) (Fin N) (AE F E)` to `fun X => Matrix.of fun i j => ∑ l, X (i, j, l) • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l)`. Establish `hΨ : Continuous Ψ` using `continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun l _ => (continuous_apply (i, j, l)).smul (continuous_const : Continuous fun _ : ι → FiniteAdeleRing (𝓞 F) F => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l))`. Establish `hΨ0 : Ψ 0 = 0` using `by ext i j; simp [Ψ]`.

Establish `hpre : Ψ ⁻¹' U ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 F) F)` using `hΨ.continuousAt.preimage_mem_nhds (by rw [hΨ0]; exact hU)`. Rewrite `hpre` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hpre`. Take `⟨S, hS⟩` from `nhds_zero_finiteAdele (Filter.iInter_mem.2 fun k : ι => ht k)`. Use `⟨S, fun M hM => ?_⟩` and prove the remaining obligations.

Use `choose X hX0 hXI hXeq using fun i j => exists_repr_of_int hsep S (hM i j).1 (hM i j).2`. Establish `hmem : (fun k : ι => X k.1 k.2.1 k.2.2) ∈ I.pi t` using `fun k _ => Set.mem_iInter.1 (hS _ (hX0 _ _ _) (hXI _ _ _)) k`. Establish `hM' : Ψ (fun k : ι => X k.1 k.2.1 k.2.2) = M`. Use extensionality with `i j`. Rewrite using `[hXeq i j]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_tmul', smul_eq_mul, mul_one]`. Establish `hfin` using `hsub hmem`. Rewrite `hfin` using `[Set.mem_preimage, hM']`. Conclude with `hfin`.
-/
theorem nhds_of_sep [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)]
    (hsep : ∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) (N : ℕ)
    (U : Set (Matrix (Fin N) (Fin N) (AE F E))) (hU : U ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
      (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
      M ∈ U := by
  classical
  have := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let Ψ : (ι → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin N) (Fin N) (AE F E) :=
    fun X => Matrix.of fun i j => ∑ l, X (i, j, l) • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l)
  have hΨ : Continuous Ψ :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun l _ => (continuous_apply (i, j, l)).smul
        (continuous_const : Continuous fun _ : ι → FiniteAdeleRing (𝓞 F) F =>
          ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] intBasis E l))
  have hΨ0 : Ψ 0 = 0 := by ext i j; simp [Ψ]
  have hpre : Ψ ⁻¹' U ∈ 𝓝 (0 : ι → FiniteAdeleRing (𝓞 F) F) :=
    hΨ.continuousAt.preimage_mem_nhds (by rw [hΨ0]; exact hU)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  obtain ⟨S, hS⟩ := nhds_zero_finiteAdele (Filter.iInter_mem.2 fun k : ι => ht k)
  refine ⟨S, fun M hM => ?_⟩
  choose X hX0 hXI hXeq using fun i j => exists_repr_of_int hsep S (hM i j).1 (hM i j).2
  have hmem : (fun k : ι => X k.1 k.2.1 k.2.2) ∈ I.pi t := fun k _ =>
    Set.mem_iInter.1 (hS _ (hX0 _ _ _) (hXI _ _ _)) k
  have hM' : Ψ (fun k : ι => X k.1 k.2.1 k.2.2) = M := by
    ext i j
    rw [hXeq i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hfin := hsub hmem
  rw [Set.mem_preimage, hM'] at hfin
  exact hfin

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc _ _`. Conclude with `⟨fun N U hU => nhds_of_sep (hP F E c h2 hc).1 N U hU, int_cofinite⟩`.
-/
theorem of_placeMaps (hP : PlaceMaps.Statement) : AENeighbourhoods.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  exact ⟨fun N U hU => nhds_of_sep (hP F E c h2 hc).1 N U hU, int_cofinite⟩

/- English proof (translation)
The claim follows from `of_placeMaps hP`.
-/
theorem proof (_hT : AETopologicalRing.Statement) (hP : PlaceMaps.Statement) :
    AENeighbourhoods.Statement :=
  of_placeMaps hP

end AENeighbourhoods

end StrongApprox

end GroundTheory.Heights₂.Heights
