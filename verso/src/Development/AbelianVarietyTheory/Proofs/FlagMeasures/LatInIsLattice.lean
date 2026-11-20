import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorIntegralHermitianLatticeRankOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardShortVectorsLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsRest

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimCount

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_smul_mem (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpan.exists_smul_mem
  | exact _root_.GlobalTheory.SmulMemSpan.exists_smul_mem
  | (apply _root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpan.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpan.exists_smul_mem ..)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem latIn_isLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro u _
    obtain ⟨r, hr, hu⟩ := exists_smul_mem L hL (u : V)
    have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have h2 : r • u ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hu
    rw [← algebraMap_smul K r] at h2
    exact (Submodule.smul_mem_iff _ h1).1 h2

end

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem one_le_rd (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by
  have h : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * fDeg K)) (by positivity)
  unfold vInv
  linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

A detailed English derivation is pending.
-/
theorem real_bound (a : ℝ) (ha : 1 ≤ a) (n k f : ℕ) (hn : 1 ≤ n) (hf : 0 < f) :
    (1 + 2 * Real.sqrt (a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)))) ^ (2 * k * f) ≤
      (9 * a) ^ (k * f) * (n : ℝ) ^ ((k : ℝ) / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have h1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * f)) := Real.one_le_rpow hn' (by positivity)
  have e : (n : ℝ) ^ ((k : ℝ) / 2) = ((n : ℝ) ^ ((1 : ℝ) / (2 * f))) ^ (k * f) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [e, ← mul_pow, mul_assoc 2, pow_mul]
  set B := a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le ha h1
  have hs : 1 ≤ Real.sqrt B := Real.one_le_sqrt.2 hB1
  have hq : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc, ← hB]
  nlinarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ n : ℕ, 1 ≤ n → (((primSp h L 1 n).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((9 * (2 * vInv K)) ^ (Module.finrank K V * fDeg K) * (n : ℝ) ^ ((Module.finrank K V : ℝ) / 2)) ∧ (primSp h L 0 n).encard ≤ 1 := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL n hn
  constructor
  · set B : ℝ := (2 * vInv K) * (n : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hB
    have hrd := one_le_rd K
    have hB0 : 0 ≤ B := by positivity
    have hsub : primSp h L 1 n ⊆ (fun x : V => Submodule.span K {x}) ''
        {x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
      rintro U ⟨hU, hd⟩
      obtain ⟨x, hx, hx0, hxB⟩ := GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one K U (hRes h U) hK ⟨fun x y => hs.eq x y⟩
        (fun τ x hx => hp τ x (by simpa using hx)) hU (latIn U L)
        ⟨latIn_isLattice L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
      rw [hd] at hxB
      refine ⟨x, ⟨hx, hxB⟩, ?_⟩
      refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 x.2) ?_
      rw [hU, finrank_span_singleton (by simpa using hx0)]
    have h1 := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
    refine le_trans (by exact_mod_cast h1) ((GlobalTheory.T.encard_shortVectors_le' K V h hK hs hp L hL B hB0).trans ?_)
    exact ENNReal.ofReal_le_ofReal (real_bound _ hrd n _ _ hn Fintype.card_pos)
  · rw [Set.encard_le_one_iff]
    rintro U W ⟨hU, -⟩ ⟨hW, -⟩
    rw [Submodule.finrank_eq_zero.1 hU, Submodule.finrank_eq_zero.1 hW]

end GlobalTheory.Mass.PrimCount
