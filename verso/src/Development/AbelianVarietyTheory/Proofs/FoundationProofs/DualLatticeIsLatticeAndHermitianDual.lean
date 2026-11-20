import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsFurther
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualLat

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_mem_one [StarRing K] {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) :
    star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_den (x : K) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, y, hy⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) x
  exact ⟨d, nonZeroDivisors.ne_zero hd, Submodule.mem_one.2 ⟨y, hy⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_den_finset (s : Finset K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ s, d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s
  exact ⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_smul_mem {M : Submodule (𝓞 K) (Fin n → K)}
    {x : Fin n → K} (hx : x ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.DeterminantSimpLemma.main
  | exact _root_.GlobalTheory.DeterminantSimpLemma.main
  | (apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantSimpLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantSimpLemma.main ..)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLattice_dualFr (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (dualFr M) := by
  classical
  refine ⟨?_, ?_⟩
  · have h : ∀ i : Fin n, ∃ d : 𝓞 K, d ≠ 0 ∧ d • (Pi.single i (1 : K) : Fin n → K) ∈ M := fun i =>
      exists_smul_mem (by rw [hM.span_eq_top]; trivial)
    choose d hd hdM using h
    have hle : dualFr M ≤ Submodule.span (𝓞 K)
        (Set.range fun i : Fin n => (Pi.single i (algebraMap (𝓞 K) K (d i))⁻¹ : Fin n → K)) := by
      intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hφ _ (hdM i))
      have hdi : algebraMap (𝓞 K) K (d i) ≠ 0 := by simpa using hd i
      have : (Pi.single i (φ i) : Fin n → K) =
          b • (Pi.single i (algebraMap (𝓞 K) K (d i))⁻¹ : Fin n → K) := by
        rw [← Pi.single_smul, Algebra.smul_def, hb, dotProduct_smul, dotProduct_single,
          Algebra.smul_def]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  · obtain ⟨S, hS⟩ := hM.fg
    rw [eq_top_iff]
    intro x _
    obtain ⟨d, hd, h⟩ := exists_den_finset (S.image fun y => x ⬝ᵥ y)
    have hx : d • x ∈ dualFr M := by
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => rw [smul_dotProduct]; exact h _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [dotProduct_add]; exact add_mem hy hz
      | smul a y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ _ hy
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd
    have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Treat this case separately.

Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isLattice_hdualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hM : Submodule.IsLattice K M) : Submodule.IsLattice K (hdualFr G M) := by
  classical
  obtain ⟨S, hS⟩ := hM.fg
  set f : (Fin n → K) → (Fin n → K) := fun y => star y ᵥ* G with hf
  have hadd : ∀ y z, f (y + z) = f y + f z := fun y z => by
    simp only [hf, star_add, Matrix.add_vecMul]
  have hsm : ∀ (a : K) y, f (a • y) = star a • f y := fun a y => by
    simp only [hf, star_smul, Matrix.smul_vecMul]
  have h0 : f 0 = 0 := by simp [hf]
  set M' : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (f '' S) with hM'
  have hfM : ∀ y ∈ M, f y ∈ M' := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [h0]; exact zero_mem _
    | add y z _ _ hy hz => rw [hadd]; exact add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨b, hb⟩ := Submodule.mem_one.1
        (star_mem_one (Submodule.mem_one.2 ⟨a, rfl⟩ : algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K)))
      rw [← algebraMap_smul K a y, hsm, ← hb, algebraMap_smul]
      exact M'.smul_mem _ hy
  have hL : Submodule.IsLattice K M' := by
    refine ⟨Submodule.fg_span ((S.finite_toSet).image _), ?_⟩
    have key : ∀ y ∈ Submodule.span K (M : Set (Fin n → K)),
        f y ∈ Submodule.span K (M' : Set (Fin n → K)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hfM y hy)
      | zero => rw [h0]; exact zero_mem _
      | add y z _ _ hy hz => rw [hadd]; exact add_mem hy hz
      | smul a y _ hy => rw [hsm]; exact Submodule.smul_mem _ _ hy
    rw [eq_top_iff]
    intro z _
    have : z = f (star (z ᵥ* G⁻¹)) := by
      simp only [hf, star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hG, Matrix.vecMul_one]
    rw [this]
    exact key _ (by rw [hM.span_eq_top]; trivial)
  have heq : hdualFr G M = dualFr M' := by
    ext x
    constructor
    · intro hx z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        have := hx y (hS ▸ Submodule.subset_span hy)
        rwa [Matrix.dotProduct_mulVec, dotProduct_comm] at this
      | zero => simp
      | add y z _ _ hy hz => rw [dotProduct_add]; exact add_mem hy hz
      | smul a y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ _ hy
    · intro hx y hy
      rw [Matrix.dotProduct_mulVec, dotProduct_comm]
      exact hx _ (hfM y hy)
  rw [heq]
  exact isLattice_dualFr M' hL

omit [NumberField K] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem star_dot [StarRing K] (x y : Fin n → K) : star (x ⬝ᵥ y) = star y ⬝ᵥ star x := by
  simp [dotProduct, mul_comm]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hdualFr_dualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) : hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M) := by
  have key : ∀ φ ψ : Fin n → K, star φ ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ψ) = ψ ⬝ᵥ (G⁻¹ *ᵥ star φ) := by
    intro φ ψ
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  ext ψ
  constructor
  · intro h x hx
    have hφ : star (G *ᵥ x) ∈ dualFr M := by
      intro y hy
      have := star_mem_one (hx y hy)
      rwa [star_dot, star_star] at this
    have := h _ hφ
    rwa [key, star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec] at this
  · intro h φ hφ
    rw [key]
    refine h _ fun y hy => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec, ← star_dot]
    exact star_mem_one (hφ y hy)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem dualFr_lattice_and_hdual : DualFrLattice ∧ DualFrHdual :=
  ⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩,
    fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩

end GlobalTheory.DualLat
