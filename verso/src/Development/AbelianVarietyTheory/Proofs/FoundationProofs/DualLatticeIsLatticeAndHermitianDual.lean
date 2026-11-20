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
Rewrite using `[Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`. Introduce `h`.

Conclude with `⟨⟨x, h⟩, rfl⟩`.
-/
theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Rewrite `h`, the goal using `[mem_one_iff]`. Conclude with `map_isIntegral_int (starRingEnd K) h`.
-/
theorem star_mem_one [StarRing K] {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) :
    star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

/- English proof (translation)
Take `⟨⟨d, hd⟩, y, hy⟩` from `IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) x`. Conclude with `⟨d, nonZeroDivisors.ne_zero hd, Submodule.mem_one.2 ⟨y, hy⟩⟩`.
-/
theorem exists_den (x : K) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, y, hy⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) x
  exact ⟨d, nonZeroDivisors.ne_zero hd, Submodule.mem_one.2 ⟨y, hy⟩⟩

/- English proof (translation)
Take `⟨⟨d, hd⟩, hy⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s`. Conclude with `⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩`.
-/
theorem exists_den_finset (s : Finset K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ s, d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s
  exact ⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DeterminantSimpLemma.main`. Consider the case `exact _root_.GlobalTheory.DeterminantSimpLemma.main`. Consider the case `(apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DeterminantSimpLemma.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DeterminantSimpLemma.main ..)`.
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
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h : ∀ i : Fin n, ∃ d : 𝓞 K, d ≠ 0 ∧ d • (Pi.single i (1 : K) : Fin n → K) ∈ M` using `fun i => exists_smul_mem (by rw [hM.span_eq_top]; trivial) choose d hd hdM using h`. Establish `hle : dualFr M ≤ Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i (algebraMap (𝓞 K) K (d i))⁻¹ : Fin n → K))`. Introduce `φ hφ`. Rewrite using `[← Finset.univ_sum_single φ]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `Submodule.mem_one.1 (hφ _ (hdM i))`. Establish `hdi : algebraMap (𝓞 K) K (d i) ≠ 0` using `by simpa using hd i`. Establish `: (Pi.single i (φ i) : Fin n → K) = b • (Pi.single i (algebraMap (𝓞 K) K (d i))⁻¹ : Fin n → K)`. Rewrite using `[← Pi.single_smul, Algebra.smul_def, hb, dotProduct_smul, dotProduct_single, Algebra.smul_def]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Conclude with `Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle`.

Take `⟨S, hS⟩` from `hM.fg`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨d, hd, h⟩` from `exists_den_finset (S.image fun y => x ⬝ᵥ y)`. Establish `hx : d • x ∈ dualFr M`.

Introduce `y hy`. Rewrite `hy` using `[← hS]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => rw [smul_dotProduct]`. Conclude with `h _ (Finset.mem_image_of_mem _ hy)`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [dotProduct_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [dotProduct_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.

Establish `hd' : algebraMap (𝓞 K) K d ≠ 0` using `by simpa using hd`. Establish `: x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x)`. Rewrite using `[← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`.
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
Take `⟨S, hS⟩` from `hM.fg`. Use `set f : (Fin n → K) → (Fin n → K) := fun y => star y ᵥ* G with hf`. Establish `hadd : ∀ y z, f (y + z) = f y + f z` using `fun y z => by`. Simplify using `only [hf, star_add, Matrix.add_vecMul]`. Establish `hsm : ∀ (a : K) y, f (a • y) = star a • f y` using `fun a y => by`.

Simplify using `only [hf, star_smul, Matrix.smul_vecMul]`. Establish `h0 : f 0 = 0` using `by simp [hf]`. Use `set M' : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (f '' S) with hM'`. Establish `hfM : ∀ y ∈ M, f y ∈ M'`. Introduce `y hy`.

Rewrite `hy` using `[← hS]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [h0]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz => rw [hadd]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy`. Take `⟨b, hb⟩` from `Submodule.mem_one.1 (star_mem_one (Submodule.mem_one.2 ⟨a, rfl⟩ : algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K)))`. Rewrite using `[← algebraMap_smul K a y, hsm, ← hb, algebraMap_smul]`.

Conclude with `M'.smul_mem _ hy`. Establish `hL : Submodule.IsLattice K M'`. Use `⟨Submodule.fg_span ((S.finite_toSet).image _), ?_⟩` and prove the remaining obligations. Establish `key : ∀ y ∈ Submodule.span K (M : Set (Fin n → K)), f y ∈ Submodule.span K (M' : Set (Fin n → K))`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (hfM y hy)`. Consider the case `zero => rw [h0]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [hadd]`.

Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [hsm]`. Conclude with `Submodule.smul_mem _ _ hy`. Rewrite using `[eq_top_iff]`. Introduce `z _`.

Establish `: z = f (star (z ᵥ* G⁻¹))`. Simplify using `only [hf, star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hG, Matrix.vecMul_one]`. Rewrite using `[this]`. Conclude with `key _ (by rw [hM.span_eq_top]; trivial)`. Establish `heq : hdualFr G M = dualFr M'`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨y, hy, rfl⟩` from `hz`. Use `hx y (hS ▸ Submodule.subset_span hy)` as an intermediate fact. Rewrite `this` using `[Matrix.dotProduct_mulVec, dotProduct_comm]`. Then use the resulting hypothesis. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [dotProduct_add]`.

Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [dotProduct_smul]`. Conclude with `Submodule.smul_mem _ _ hy`. Introduce `hx y hy`. Rewrite using `[Matrix.dotProduct_mulVec, dotProduct_comm]`.

Conclude with `hx _ (hfM y hy)`. Rewrite using `[heq]`. Conclude with `isLattice_dualFr M' hL`.
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
Simplify using `[dotProduct, mul_comm]`.
-/
theorem star_dot [StarRing K] (x y : Fin n → K) : star (x ⬝ᵥ y) = star y ⬝ᵥ star x := by
  simp [dotProduct, mul_comm]

/- English proof (translation)
Establish `key : ∀ φ ψ : Fin n → K, star φ ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ψ) = ψ ⬝ᵥ (G⁻¹ *ᵥ star φ)`. Introduce `φ ψ`. Rewrite using `[Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]`. Use extensionality with `ψ`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Establish `hφ : star (G *ᵥ x) ∈ dualFr M`. Introduce `y hy`. Use `star_mem_one (hx y hy)` as an intermediate fact. Rewrite `this` using `[star_dot, star_star]`. Then use the resulting hypothesis.

Use `h _ hφ` as an intermediate fact. Rewrite `this` using `[key, star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `h φ hφ`. Rewrite using `[key]`. Use `h _ fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec, ← star_dot]`. Conclude with `star_mem_one (hφ y hy)`.
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
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩, fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩`.
-/
theorem dualFr_lattice_and_hdual : DualFrLattice ∧ DualFrHdual :=
  ⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩,
    fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩

end GlobalTheory.DualLat
