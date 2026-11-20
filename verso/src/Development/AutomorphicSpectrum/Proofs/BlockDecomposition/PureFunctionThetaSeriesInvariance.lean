import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

/- English proof (translation)
Introduce `F _ _ _ θ _ S T G g a _ hGc hg hST ha δ hδ`. Take `⟨N, hN, hNint⟩` from `GlobalTheory.T.bounded_denominators_compact_idele_set F {a} isCompact_singleton S (fun v => tsupport (g v)) (fun v hv => (hg v hv).2)`. Establish `h1 : ((↑a⁻¹ : AF F)).1 * (↑a : AF F).1 = 1` using `congrArg Prod.fst (Units.inv_mul a)`. Establish `h2 : θ δ⁻¹ * θ δ = 1` using `by rw [← map_mul, inv_mul_cancel₀ hδ.ne', map_one]`. Establish `hcd : ∀ z : Ainf F, θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z)) = z`.

Introduce `z`. Combine the equalities or inequalities in the displayed calculation. Establish `hK : IsCompact ((fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G)` using `hGc.image (continuous_const.mul continuous_id)`. Use `choose C hC using fun w : NumberField.InfinitePlace F => hK.exists_bound_of_continuousOn (f := fun z : NumberField.InfiniteAdeleRing F => z w) (continuous_apply w).continuousOn`. Use `((NumberField.Embeddings.finite_of_norm_le F ℂ ((N : ℝ) * ∑ w, ‖C w‖)).image (fun y => y / (N : F))).subset ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨hxT, hne⟩`. Establish `hG0` using `left_ne_zero_of_mul hne`. Establish `hpsi : ∀ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0` using `fun v hv => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) v hv`. Establish `hS : ∀ v ∈ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ tsupport (g v)`. Introduce `v hv`.

Establish `h` using `hpsi v (hST hv)`. Simplify using `only [psiA, if_pos hv] at h`. Rewrite using `[mul_comm]`. Conclude with `subset_tsupport _ h`. Establish `hnS : ∀ v ∉ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ v.adicCompletionIntegers F`.

Introduce `v hv`. Distinguish the cases in `hvT : v ∈ T`. Establish `h` using `hpsi v hvT`. Simplify using `only [psiA, if_neg hv] at h`. Rewrite using `[mul_comm]`.

Assume the negation of the conclusion as `hc`. Conclude with `h (if_neg hc)`. Conclude with `mul_mem (hxT v hvT) (ha v hvT).1`. Take `⟨y, hy⟩` from `hNint a (Set.mem_singleton a) x hS hnS`. Establish `hN0 : (N : F) ≠ 0` using `by exact_mod_cast hN.ne'`.

Establish `harch : ∀ w : NumberField.InfinitePlace F, w x ≤ C w`. Introduce `w`. Establish `hmem : (↑a : AF F).1 * (θ δ * algebraMap F (Ainf F) x) ∈ tsupport G` using `subset_tsupport _ hG0`. Establish `hx' : algebraMap F (Ainf F) x ∈ (fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G` using `⟨_, hmem, hcd _⟩`. Establish `hb` using `hC w _ hx'`.

Establish `hn : ‖(algebraMap F (NumberField.InfiniteAdeleRing F) x) w‖ = w x`. Rewrite using `[NumberField.InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_coe]`. Simplify using the standard rewrite rules. Rewrite using `[← hn]`. Conclude with `hb`.

Establish `hφ : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ ∑ w, ‖C w‖`. Introduce `φ`. Combine the equalities or inequalities in the displayed calculation. Use `⟨(N : F) * x, ⟨?_, fun φ => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`.

Conclude with `NumberField.RingOfIntegers.isIntegral_coe y`. Rewrite using `[map_mul, norm_mul, map_natCast, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (hφ φ) (Nat.cast_nonneg N)`. Clear the denominators using the available nonvanishing facts.
-/
theorem finite_contributing : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  intro F _ _ _ θ _ S T G g a _ hGc hg hST ha δ hδ
  obtain ⟨N, hN, hNint⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F {a} isCompact_singleton S (fun v => tsupport (g v))
    (fun v hv => (hg v hv).2)
  have h1 : ((↑a⁻¹ : AF F)).1 * (↑a : AF F).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
  have h2 : θ δ⁻¹ * θ δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ.ne', map_one]
  have hcd : ∀ z : Ainf F, θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z)) = z := by
    intro z
    calc θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z))
        = θ δ⁻¹ * (((↑a⁻¹ : AF F)).1 * (↑a : AF F).1) * θ δ * z := by ring
      _ = z := by rw [h1, mul_one, h2, one_mul]
  have hK : IsCompact ((fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G) :=
    hGc.image (continuous_const.mul continuous_id)
  choose C hC using fun w : NumberField.InfinitePlace F =>
    hK.exists_bound_of_continuousOn (f := fun z : NumberField.InfiniteAdeleRing F => z w)
      (continuous_apply w).continuousOn
  refine ((NumberField.Embeddings.finite_of_norm_le F ℂ ((N : ℝ) * ∑ w, ‖C w‖)).image
    (fun y => y / (N : F))).subset ?_
  rintro x ⟨hxT, hne⟩
  have hG0 := left_ne_zero_of_mul hne
  have hpsi : ∀ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0 :=
    fun v hv => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) v hv
  have hS : ∀ v ∈ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ tsupport (g v) := by
    intro v hv
    have h := hpsi v (hST hv)
    simp only [psiA, if_pos hv] at h
    rw [mul_comm]
    exact subset_tsupport _ h
  have hnS : ∀ v ∉ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    by_cases hvT : v ∈ T
    · have h := hpsi v hvT
      simp only [psiA, if_neg hv] at h
      rw [mul_comm]
      by_contra hc
      exact h (if_neg hc)
    · exact mul_mem (hxT v hvT) (ha v hvT).1
  obtain ⟨y, hy⟩ := hNint a (Set.mem_singleton a) x hS hnS
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have harch : ∀ w : NumberField.InfinitePlace F, w x ≤ C w := by
    intro w
    have hmem : (↑a : AF F).1 * (θ δ * algebraMap F (Ainf F) x) ∈ tsupport G :=
      subset_tsupport _ hG0
    have hx' : algebraMap F (Ainf F) x ∈ (fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G :=
      ⟨_, hmem, hcd _⟩
    have hb := hC w _ hx'
    have hn : ‖(algebraMap F (NumberField.InfiniteAdeleRing F) x) w‖ = w x := by
      rw [NumberField.InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_coe]
      simp
    rw [← hn]
    exact hb
  have hφ : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ ∑ w, ‖C w‖ := by
    intro φ
    calc ‖φ x‖ = NumberField.InfinitePlace.mk φ x := (NumberField.InfinitePlace.apply φ x).symm
      _ ≤ C (NumberField.InfinitePlace.mk φ) := harch _
      _ ≤ ‖C (NumberField.InfinitePlace.mk φ)‖ := Real.le_norm_self _
      _ ≤ ∑ w, ‖C w‖ := Finset.single_le_sum (f := fun w => ‖C w‖) (fun w _ => norm_nonneg _)
          (Finset.mem_univ _)
  refine ⟨(N : F) * x, ⟨?_, fun φ => ?_⟩, ?_⟩
  · rw [← hy]
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hφ φ) (Nat.cast_nonneg N)
  · field_simp

end GlobalTheory.CompanionTheory.BasePsi
