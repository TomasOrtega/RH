import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableLat

/- English proof (translation)
Introduce `G _ _ _ Qp LL O _ _ _ _ _ _ _ hO A`. Take `⟨⟨hDom, hDVR, hFrac⟩, -, -, hTop, hOpen⟩` from `hO`. Use `haveI := hDom`. Use `haveI := hDVR`. Use `haveI := hFrac`.

Use `haveI := hTop`. Establish `hinj : Function.Injective (algebraMap O LL)` using `IsFractionRing.injective O LL`. Set `e` to `Module.finBasis LL A.V`. Set `n` to `Module.finrank LL A.V`. Set `T₀ : Submodule O A.V` to `Submodule.span O (Set.range e)`.

Establish `hT₀fg : T₀.FG` using `Submodule.fg_span (Set.finite_range e)`. Establish `hT₀span : Submodule.span LL (T₀ : Set A.V) = ⊤`. Simplify using `only [T₀, Submodule.span_span_of_tower, e.span_eq]`. Establish `hT₀open : IsOpen (T₀ : Set A.V)` using `GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hOpen T₀ hT₀fg hT₀span`. Establish `hcov : ∀ x : A.V, ∃ b : nonZeroDivisors O, (b : O) • x ∈ T₀`.

Introduce `x`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ (fun i => e.repr x i)`. Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `hx : (b : O) • x = ∑ i, (b : O) • (e.repr x i • e i)`. Rewrite using `[← Finset.smul_sum, e.sum_repr]`.

Rewrite using `[hx]`. Use `T₀.sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hb i (Finset.mem_univ i)`. Rewrite using `[← smul_assoc, ← ha, algebraMap_smul]`. Conclude with `T₀.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)`.

Set `C : Set A.V` to `⋃ i, Set.range fun g : G => A.ρ g (e i)`. Establish `hC : IsCompact C` using `isCompact_iUnion fun i => isCompact_range (A.cont (e i))`. Set `U : nonZeroDivisors O → Set A.V` to `fun b => (fun x => (b : O) • x) ⁻¹' (T₀ : Set A.V)`. Establish `hU : ∀ b, IsOpen (U b)`. Introduce `b`.

Establish `: (fun x : A.V => (b : O) • x) = fun x => algebraMap O LL b • x`. Use function extensionality and compare the values at `x`. Rewrite using `[algebraMap_smul]`. Conclude with `hT₀open.preimage (this ▸ continuous_const_smul _)`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover U hU (fun x _ => by`.

Take `⟨b, hb⟩` from `hcov x`. Conclude with `Set.mem_iUnion.2 ⟨b, hb⟩)`. Set `b : O` to `∏ c ∈ t, (c : O)`. Establish `hb0 : b ∈ nonZeroDivisors O`. Simplify `(∏ c ∈ t, c).2` using `[b]`.

Establish `hbC : ∀ y ∈ C, b • y ∈ T₀`. Introduce `y hy`. Take `⟨c, hct, hc⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Establish `: b = (∏ d ∈ t.erase c, (d : O)) * c`. Simplify using `only [b]`.

Rewrite using `[← Finset.prod_erase_mul _ _ hct]`. Rewrite using `[this, mul_smul]`. Conclude with `T₀.smul_mem _ hc`. Set `T : Submodule O A.V` to `Submodule.span O C`. Establish `hCT : C ⊆ T` using `Submodule.subset_span`.

Establish `hstable : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T`. Introduce `g x hx`. Establish `hle : T ≤ T.comap ((A.ρ g).restrictScalars O)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hy`. Take `⟨h, rfl⟩` from `hi`. Use `show A.ρ g (A.ρ h (e i)) ∈ T`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `hCT (Set.mem_iUnion.2 ⟨i, g * h, rfl⟩)`.

Conclude with `hle hx`. Set `f : A.V →ₗ[O] A.V` to `b • LinearMap.id`. Establish `hbne : algebraMap O LL b ≠ 0`. Introduce `h`. Conclude with `nonZeroDivisors.ne_zero hb0 (hinj (by rw [h, map_zero]))`.

Establish `hf : Function.Injective f`. Introduce `x y hxy`. Establish `: algebraMap O LL b • x = algebraMap O LL b • y`. Simplify `hxy` using `[f, algebraMap_smul]`. Conclude with `smul_right_injective A.V hbne this`.

Establish `hfT : T.map f ≤ T₀`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `Submodule.span_le.2 fun y hy => ?_` and prove the remaining obligations. Simplify `hbC y hy` using `[f]`. Establish `hTfg : T.FG` using `Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hT₀fg hfT)`.

Use `haveI : NoZeroSMulDivisors O A.V := ⟨fun {c x} h => by`. Rewrite `h` using `[← algebraMap_smul LL c x]`. Break down `smul_eq_zero.1 h with h | h` into its components or cases. Use the proof step `left; exact hinj (by rw [h, map_zero])`. Use `right`.

Conclude with `h⟩`. Use `haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hTfg`. Establish `hfree : Module.Free O T` using `Module.free_of_finite_type_torsion_free'`. Establish `hspan : Submodule.span LL (T : Set A.V) = ⊤`. Rewrite using `[eq_top_iff, ← e.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `Submodule.subset_span (hCT (Set.mem_iUnion.2 ⟨i, 1, ?_⟩))` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `⟨⟨T, hstable, hTfg, hfree, hspan⟩⟩`.
-/
theorem exists_lattice : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  intro G _ _ _ Qp LL O _ _ _ _ _ _ _ hO A
  classical
  obtain ⟨⟨hDom, hDVR, hFrac⟩, -, -, hTop, hOpen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := hTop
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL

  let e := Module.finBasis LL A.V
  let n := Module.finrank LL A.V
  let T₀ : Submodule O A.V := Submodule.span O (Set.range e)
  have hT₀fg : T₀.FG := Submodule.fg_span (Set.finite_range e)
  have hT₀span : Submodule.span LL (T₀ : Set A.V) = ⊤ := by
    simp only [T₀, Submodule.span_span_of_tower, e.span_eq]
  have hT₀open : IsOpen (T₀ : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hOpen T₀ hT₀fg hT₀span

  have hcov : ∀ x : A.V, ∃ b : nonZeroDivisors O, (b : O) • x ∈ T₀ := by
    intro x
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
      (fun i => e.repr x i)
    refine ⟨b, ?_⟩
    have hx : (b : O) • x = ∑ i, (b : O) • (e.repr x i • e i) := by
      rw [← Finset.smul_sum, e.sum_repr]
    rw [hx]
    refine T₀.sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    rw [← smul_assoc, ← ha, algebraMap_smul]
    exact T₀.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)

  let C : Set A.V := ⋃ i, Set.range fun g : G => A.ρ g (e i)
  have hC : IsCompact C := isCompact_iUnion fun i => isCompact_range (A.cont (e i))
  let U : nonZeroDivisors O → Set A.V := fun b => (fun x => (b : O) • x) ⁻¹' (T₀ : Set A.V)
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    have : (fun x : A.V => (b : O) • x) = fun x => algebraMap O LL b • x := by
      funext x; rw [algebraMap_smul]
    exact hT₀open.preimage (this ▸ continuous_const_smul _)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU (fun x _ => by
    obtain ⟨b, hb⟩ := hcov x; exact Set.mem_iUnion.2 ⟨b, hb⟩)
  let b : O := ∏ c ∈ t, (c : O)
  have hb0 : b ∈ nonZeroDivisors O := by
    simpa [b] using (∏ c ∈ t, c).2
  have hbC : ∀ y ∈ C, b • y ∈ T₀ := by
    intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have : b = (∏ d ∈ t.erase c, (d : O)) * c := by
      simp only [b]; rw [← Finset.prod_erase_mul _ _ hct]
    rw [this, mul_smul]
    exact T₀.smul_mem _ hc

  let T : Submodule O A.V := Submodule.span O C
  have hCT : C ⊆ T := Submodule.subset_span
  have hstable : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T := by
    intro g x hx
    have hle : T ≤ T.comap ((A.ρ g).restrictScalars O) := by
      refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, rfl⟩ := hi
      show A.ρ g (A.ρ h (e i)) ∈ T
      rw [← Module.End.mul_apply, ← map_mul]
      exact hCT (Set.mem_iUnion.2 ⟨i, g * h, rfl⟩)
    exact hle hx

  let f : A.V →ₗ[O] A.V := b • LinearMap.id
  have hbne : algebraMap O LL b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb0 (hinj (by rw [h, map_zero]))
  have hf : Function.Injective f := by
    intro x y hxy
    have : algebraMap O LL b • x = algebraMap O LL b • y := by
      simpa [f, algebraMap_smul] using hxy
    exact smul_right_injective A.V hbne this
  have hfT : T.map f ≤ T₀ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 fun y hy => ?_
    simpa [f] using hbC y hy
  have hTfg : T.FG := Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hT₀fg hfT)
  haveI : NoZeroSMulDivisors O A.V := ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hTfg
  have hfree : Module.Free O T := Module.free_of_finite_type_torsion_free'
  have hspan : Submodule.span LL (T : Set A.V) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span (hCT (Set.mem_iUnion.2 ⟨i, 1, ?_⟩))
    simp
  exact ⟨⟨T, hstable, hTfg, hfree, hspan⟩⟩

end GlobalTheory.StableLat
