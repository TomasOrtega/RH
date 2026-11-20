import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Establish `hRF : LinearMap.range T ≤ F`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `h x`. Use `haveI : FiniteDimensional ℂ (LinearMap.range T) := FiniteDimensional.of_injective (Submodule.inclusion hRF) (Submodule.inclusion_injective hRF)`. Set `ι : LinearMap.range T →ₗ[ℂ] F` to `Submodule.inclusion hRF`.

Set `π : F →ₗ[ℂ] LinearMap.range T` to `T.rangeRestrict ∘ₗ F.subtype`. Establish `e1 : (T.restrict (p` using `LinearMap.range T) (q := LinearMap.range T) fun v _ => LinearMap.mem_range_self T v) = π ∘ₗ ι := by`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `e2 : (T.restrict (p` using `F) (q := F) fun v _ => h v) = ι ∘ₗ π := by`.

Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Conclude with `LinearMap.trace_comp_comm' ι π`.
-/
private theorem trace_range_eq {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V)
    (F : Submodule ℂ V) [FiniteDimensional ℂ F] (h : ∀ x, T x ∈ F) :
    LinearMap.trace ℂ (LinearMap.range T)
      (T.restrict (p := LinearMap.range T) (q := LinearMap.range T)
        fun v _ => LinearMap.mem_range_self T v) =
      LinearMap.trace ℂ F (T.restrict (p := F) (q := F) fun v _ => h v) := by
  have hRF : LinearMap.range T ≤ F := by
    rintro _ ⟨x, rfl⟩
    exact h x
  haveI : FiniteDimensional ℂ (LinearMap.range T) :=
    FiniteDimensional.of_injective (Submodule.inclusion hRF) (Submodule.inclusion_injective hRF)
  let ι : LinearMap.range T →ₗ[ℂ] F := Submodule.inclusion hRF
  let π : F →ₗ[ℂ] LinearMap.range T := T.rangeRestrict ∘ₗ F.subtype
  have e1 : (T.restrict (p := LinearMap.range T) (q := LinearMap.range T)
      fun v _ => LinearMap.mem_range_self T v) = π ∘ₗ ι := by
    ext x
    rfl
  have e2 : (T.restrict (p := F) (q := F) fun v _ => h v) = ι ∘ₗ π := by
    ext x
    rfl
  rw [e1, e2]
  exact LinearMap.trace_comp_comm' ι π

/- English proof (translation)
Rewrite using `[GlobalTheory.TwTrLevel.mem_fixed_iff]`. Introduce `u hu`. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`. Rewrite using `[map_sub, sub_eq_zero]`.

Establish `h1` using `(hB v (l ∘ₗ ρ u)).2`. Establish `h2` using `(hB v l).2`. Rewrite `h1` using `[LinearMap.comp_apply]`. Rewrite using `[h1, h2]`. Rewrite using `[← integral_mul_left_eq_self (μ := μ) (fun g => f g * l (ρ g v)) u]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[hf u hu g, map_mul, Module.End.mul_apply, LinearMap.comp_apply]`.
-/
private theorem op_mem_fixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V] (μ : Measure G)
    [μ.IsMulLeftInvariant] (ρ : Representation ℂ G V) (U : Subgroup G) (f : G → ℂ)
    (hf : ∀ k ∈ U, ∀ x, f (k * x) = f x) (B : V →ₗ[ℂ] V) (hB : IsIntegralOp μ ρ f B) (v : V) :
    B v ∈ fixed ρ U := by
  rw [GlobalTheory.TwTrLevel.mem_fixed_iff]
  intro u hu
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  have h1 := (hB v (l ∘ₗ ρ u)).2
  have h2 := (hB v l).2
  rw [LinearMap.comp_apply] at h1
  rw [h1, h2]
  rw [← integral_mul_left_eq_self (μ := μ) (fun g => f g * l (ρ g v)) u]
  congr 1
  funext g
  rw [hf u hu g, map_mul, Module.End.mul_apply, LinearMap.comp_apply]

/- English proof (translation)
Establish `hfs` using `GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1`. Establish `hUfin : μ (U : Set G) ≠ ⊤`. Apply `ne_top_of_le_ne_top (b := μ (K : Set G))` to reduce the goal to its premises. Rewrite using `[hK1]`. Conclude with `ENNReal.one_ne_top`.

Conclude with `measure_mono hUK`. Take `⟨hvol, hne⟩` from `GlobalTheory.HaarSum.vol_mul_relIndex μ K U hUK hKc hUo`. Establish `hKr : μ.real (K : Set G) = 1`. Rewrite using `[Measure.real_def, hK1]`. Both sides reduce to the same expression.

Rewrite `hvol` using `[hKr]`. Establish `hUr : (μ.real (U : Set G) : ℂ) = ((U.relIndex K : ℕ) : ℂ)⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Conclude with `hvol` after adjusting the coercions. Establish `hsupp : Function.support (fun q : G ⧸ U => f q.out • ρ q.out w) ⊆ ↑hfs.toFinset`.

Introduce `q hq`. Rewrite using `[Set.Finite.coe_toFinset]`. Introduce `h0`. Apply `hq` to reduce the goal to its premises. Simplify using `only [h0, zero_smul]`.

Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`. Rewrite using `[map_sub, sub_eq_zero, (hB w l).2, finsum_eq_sum_of_support_subset _ hsupp]`. Rewrite using `[GlobalTheory.HaarSum.integral_eq_sum_cosets μ U hUo hUfin (fun g => f g * l (ρ g w)) ?_ hfs.toFinset ?_]`. Rewrite using `[hUr, map_smul, map_sum, smul_eq_mul]`.

Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[map_smul, smul_eq_mul]`. Introduce `x s hs`.

Establish `hw'` using `(GlobalTheory.TwTrLevel.mem_fixed_iff ρ U w).1 hw s hs`. Rewrite using `[(hf.2 s hs x).2, map_mul, Module.End.mul_apply, hw']`. Introduce `q hq`. Establish `: f q.out = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hq (hfs.mem_toFinset.2 h0)`. Simplify using `only [this, zero_mul]`.
-/
private theorem op_eq_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V] (μ : Measure G)
    [μ.IsMulLeftInvariant] (K U : Subgroup G) (hKc : IsCompact (K : Set G)) (hK1 : μ K = 1)
    (hUo : IsOpen (U : Set G)) (hUK : U ≤ K) (ρ : Representation ℂ G V) (f : G → ℂ)
    (hf : GlobalTheory.BCT.IsHecke U f) (B : V →ₗ[ℂ] V) (hB : IsIntegralOp μ ρ f B) (w : V)
    (hw : w ∈ fixed ρ U) :
    B w = ((U.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ U, f q.out • ρ q.out w := by
  have hfs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  have hUfin : μ (U : Set G) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := μ (K : Set G))
    · rw [hK1]
      exact ENNReal.one_ne_top
    · exact measure_mono hUK
  obtain ⟨hvol, hne⟩ := GlobalTheory.HaarSum.vol_mul_relIndex μ K U hUK hKc hUo
  have hKr : μ.real (K : Set G) = 1 := by
    rw [Measure.real_def, hK1]
    rfl
  rw [hKr] at hvol
  have hUr : (μ.real (U : Set G) : ℂ) = ((U.relIndex K : ℕ) : ℂ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact_mod_cast hvol
  have hsupp : Function.support (fun q : G ⧸ U => f q.out • ρ q.out w) ⊆ ↑hfs.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply hq
    simp only [h0, zero_smul]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero, (hB w l).2, finsum_eq_sum_of_support_subset _ hsupp]
  rw [GlobalTheory.HaarSum.integral_eq_sum_cosets μ U hUo hUfin (fun g => f g * l (ρ g w)) ?_ hfs.toFinset ?_]
  · rw [hUr, map_smul, map_sum, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [map_smul, smul_eq_mul]
  · intro x s hs
    have hw' := (GlobalTheory.TwTrLevel.mem_fixed_iff ρ U w).1 hw s hs
    rw [(hf.2 s hs x).2, map_mul, Module.End.mul_apply, hw']
  · intro q hq
    have : f q.out = 0 := by
      by_contra h0
      exact hq (hfs.mem_toFinset.2 h0)
    simp only [this, zero_mul]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 V _ _ ρ hρ U hUo hUK f hf A hAf hAk B c hB hT hfd`. Establish `hleft : ∀ k ∈ U, ∀ x, f (k * x) = f x` using `fun k hk x => (hf.2 k hk x).1`. Establish `hTF : ∀ x, (B ∘ₗ A) x ∈ fixed ρ U` using `fun x => op_mem_fixed μ ρ U f hleft B hB (A x)`. Establish `hs` using `GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1`. Establish `hEq : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v = (B ∘ₗ A) v`.

Introduce `v hv`. Rewrite using `[GlobalTheory.TwTrLevel.levOp_apply ρ K U f A v hs, LinearMap.comp_apply, op_eq_sum μ K U hKc hK1 hUo hUK ρ f hf B hB (A v) (hAf v hv)]`. Establish `hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v ∈ fixed ρ U` using `fun v hv => by`. Rewrite using `[hEq v hv]`. Conclude with `hTF v`.

Take `⟨-, rfl⟩` from `hT`. Unfold `GlobalTheory.BCT.twTr`. Rewrite using `[dif_pos hmem]`. Use `haveI := hfd`. Rewrite using `[trace_range_eq (B ∘ₗ A) (fixed ρ U) hTF]`.

Use `congr 1`. Use extensionality with `v`. Simplify using `only [LinearMap.restrict_coe_apply]`. Conclude with `(hEq v v.2).symm`.
-/
theorem trSum : TrSum := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 V _ _ ρ hρ U hUo hUK f hf A hAf hAk B c hB hT hfd
  have hleft : ∀ k ∈ U, ∀ x, f (k * x) = f x := fun k hk x => (hf.2 k hk x).1
  have hTF : ∀ x, (B ∘ₗ A) x ∈ fixed ρ U := fun x => op_mem_fixed μ ρ U f hleft B hB (A x)
  have hs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  have hEq : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v = (B ∘ₗ A) v := by
    intro v hv
    rw [GlobalTheory.TwTrLevel.levOp_apply ρ K U f A v hs, LinearMap.comp_apply,
      op_eq_sum μ K U hKc hK1 hUo hUK ρ f hf B hB (A v) (hAf v hv)]
  have hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v ∈ fixed ρ U := fun v hv => by
    rw [hEq v hv]
    exact hTF v
  obtain ⟨-, rfl⟩ := hT
  unfold GlobalTheory.BCT.twTr
  rw [dif_pos hmem]
  haveI := hfd
  rw [trace_range_eq (B ∘ₗ A) (fixed ρ U) hTF]
  congr 1
  ext v
  simp only [LinearMap.restrict_coe_apply]
  exact (hEq v v.2).symm

end UpperTheory.Gal.InertialTypesAlt.L
