import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul

open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc.NSum

section Unip

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def coord (e : ι ≃ Fin a ⊕ Fin b) (g : GL ι K) : Fin a → Fin b → K :=
  fun i j => (g : Matrix ι ι K) (e.symm (Sum.inl i)) (e.symm (Sum.inr j))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[coord, uGL, uMat, Matrix.reindex_apply]`.
-/
theorem coord_uGL (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : coord e (uGL e X) = X := by
  ext i j
  simp [coord, uGL, uMat, Matrix.reindex_apply]

/- English proof (translation)
The claim follows from `Units.ext (uMat_zero e)`.
-/
theorem uGL_zero (e : ι ≃ Fin a ⊕ Fin b) : uGL e (0 : Fin a → Fin b → K) = 1 := Units.ext (uMat_zero e)

/- English proof (translation)
The claim follows from `Units.ext (uMat_add e X Y)`.
-/
theorem uGL_add (e : ι ≃ Fin a ⊕ Fin b) (X Y : Fin a → Fin b → K) :
    uGL e (X + Y) = uGL e X * uGL e Y := Units.ext (uMat_add e X Y)

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← uGL_add, neg_add_cancel, uGL_zero])`.
-/
theorem uGL_neg (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : uGL e (-X) = (uGL e X)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← uGL_add, neg_add_cancel, uGL_zero])

/- English proof (translation)
Assemble the required witnesses or components as `⟨Multiplicative.ofAdd X, rfl⟩`.
-/
theorem uGL_mem (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : uGL e X ∈ blockUni e :=
  ⟨Multiplicative.ofAdd X, rfl⟩

/- English proof (translation)
Take `⟨X, rfl⟩` from `hn`. Use `show uGL e (Multiplicative.toAdd X) = uGL e (coord e (uGL e (Multiplicative.toAdd X)))`. Rewrite using `[coord_uGL]`.
-/
theorem eq_uGL_coord (e : ι ≃ Fin a ⊕ Fin b) {n : GL ι K} (hn : n ∈ blockUni e) :
    n = uGL e (coord e n) := by
  obtain ⟨X, rfl⟩ := hn
  show uGL e (Multiplicative.toAdd X) = uGL e (coord e (uGL e (Multiplicative.toAdd X)))
  rw [coord_uGL]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(uMat e X).BlockTriangular (side e)`. Introduce `i j hij`. Simplify using `only [side] at hij`. Simplify using `only [uMat, reindex_apply, submatrix_apply, Equiv.symm_symm]`. Apply the tactic sequence `rcases hi : e i with i' | i' <;> rcases hj : e j with j' | j' <;> simp_all`.

Conclude with `absurd hij (by decide)`.
-/
theorem uGL_mem_blockPar (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : uGL e X ∈ blockPar e := by
  change (uMat e X).BlockTriangular (side e)
  intro i j hij
  simp only [side] at hij
  simp only [uMat, reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases hi : e i with i' | i' <;> rcases hj : e j with j' | j' <;> simp_all
  exact absurd hij (by decide)

def lam (e : ι ≃ Fin a ⊕ Fin b) (K' : Subgroup (GL ι K)) : AddSubgroup (Fin a → Fin b → K) where
  carrier := {X | uGL e X ∈ K'}
  add_mem' {X Y} hX hY := by simp only [Set.mem_setOf_eq, uGL_add]; exact K'.mul_mem hX hY
  zero_mem' := by simp only [Set.mem_setOf_eq, uGL_zero]; exact K'.one_mem
  neg_mem' {X} hX := by simp only [Set.mem_setOf_eq, uGL_neg]; exact K'.inv_mem hX

variable [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
Establish `hu : Continuous (uMat e : (Fin a → Fin b → K) → Matrix ι ι K)`. Unfold `uMat`. Conclude with `(Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const).matrix_reindex _ _`. Conclude with `Units.continuous_iff.2 ⟨hu, hu.comp continuous_neg⟩`.
-/
theorem continuous_uGL (e : ι ≃ Fin a ⊕ Fin b) : Continuous (uGL e : (Fin a → Fin b → K) → GL ι K) := by
  have hu : Continuous (uMat e : (Fin a → Fin b → K) → Matrix ι ι K) := by
    unfold uMat
    exact (Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const
      continuous_const).matrix_reindex _ _
  exact Units.continuous_iff.2 ⟨hu, hu.comp continuous_neg⟩

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem _ _`.
-/
theorem continuous_coord (e : ι ≃ Fin a ⊕ Fin b) : Continuous (coord e : GL ι K → Fin a → Fin b → K) :=
  continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem _ _

/- English proof (translation)
Establish `ho' : IsOpen (lam e K' : Set (Fin a → Fin b → K))` using `ho.preimage (continuous_uGL e)`. Use `⟨ho', (hc.image (continuous_coord e)).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho') ?_⟩` and prove the remaining obligations. Introduce `X hX`. Conclude with `⟨uGL e X, hX, coord_uGL e X⟩`.
-/
theorem lam_open_compact (e : ι ≃ Fin a ⊕ Fin b) (K' : Subgroup (GL ι K)) (ho : IsOpen (K' : Set (GL ι K)))
    (hc : IsCompact (K' : Set (GL ι K))) :
    IsOpen (lam e K' : Set (Fin a → Fin b → K)) ∧ IsCompact (lam e K' : Set (Fin a → Fin b → K)) := by
  have ho' : IsOpen (lam e K' : Set (Fin a → Fin b → K)) := ho.preimage (continuous_uGL e)
  refine ⟨ho', (hc.image (continuous_coord e)).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho') ?_⟩
  intro X hX
  exact ⟨uGL e X, hX, coord_uGL e X⟩

/- English proof (translation)
Establish `h : ∀ X : Fin a → Fin b → K, f X = ∑ i, ∑ j, X i j • f (Pi.single i (Pi.single j 1))`. Introduce `X`. Establish `hX : X = ∑ i, ∑ j, X i j • (Pi.single i (Pi.single j (1 : K)) : Fin a → Fin b → K)`. Use extensionality with `k l`. Simplify using `[Finset.sum_apply, Pi.single_apply, ite_apply]`.

Use `conv_lhs => rw [hX]`. Simplify using `only [map_sum, map_smul]`. Rewrite using `[show (f : _ → _) = fun X => ∑ i, ∑ j, X i j • f (Pi.single i (Pi.single j 1)) from funext h]`. Use `fun_prop`.
-/
theorem continuous_of_linear (f : (Fin a → Fin b → K) →ₗ[K] (Fin a → Fin b → K)) : Continuous f := by
  have h : ∀ X : Fin a → Fin b → K, f X = ∑ i, ∑ j, X i j • f (Pi.single i (Pi.single j 1)) := by
    intro X
    have hX : X = ∑ i, ∑ j, X i j • (Pi.single i (Pi.single j (1 : K)) : Fin a → Fin b → K) := by
      ext k l
      simp [Finset.sum_apply, Pi.single_apply, ite_apply]
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul]
  rw [show (f : _ → _) = fun X => ∑ i, ∑ j, X i j • f (Pi.single i (Pi.single j 1)) from funext h]
  fun_prop

end Unip

section Measure

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨ν, h1, h2, h3⟩ : ∃ ν : @Measure V (borel V), (∀ C, IsCompact C → ν C < ⊤) ∧ (∀ U, IsOpen U → U.Nonempty → ν U ≠ 0) ∧ ∀ (x : V) (s : Set V), ν ((fun y => x + y) ⁻¹' s) = ν s := by`. Use `letI : MeasurableSpace V := borel V`. Use `haveI : BorelSpace V := ⟨rfl⟩`. Conclude with `⟨Measure.addHaar, fun C hC => hC.measure_lt_top, fun U hU hne => hU.measure_ne_zero _ hne, fun x s => measure_preimage_add _ x s⟩`. Use `⟨ν.trim hle, ?_⟩` and prove the remaining obligations.

Conclude with `{ lt_top_of_isCompact := fun C hC => by`. Take `⟨D, hCD, hD, hDm⟩` from `hc C hC`. Use `(measure_mono hCD).trans_lt ?_` and prove the remaining obligations. Rewrite using `[trim_measurableSet_eq hle hDm]`. Conclude with `h1 D hD`.

Use `map_add_left_eq_self := fun x => by`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (measurable_const_add x) hs, trim_measurableSet_eq hle hs, trim_measurableSet_eq hle (measurable_const_add x hs), h3]`. Use `open_pos := fun U hU hne h0 => h2 U hU hne (le_antisymm (h0 ▸ le_trim hle) bot_le) }`.
-/
theorem exists_haar_of_le (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [m : MeasurableSpace V] [MeasurableAdd V] (hle : m ≤ borel V)
    (hc : ∀ C : Set V, IsCompact C → ∃ D : Set V, C ⊆ D ∧ IsCompact D ∧ MeasurableSet D) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure := by
  obtain ⟨ν, h1, h2, h3⟩ : ∃ ν : @Measure V (borel V), (∀ C, IsCompact C → ν C < ⊤) ∧
      (∀ U, IsOpen U → U.Nonempty → ν U ≠ 0) ∧ ∀ (x : V) (s : Set V), ν ((fun y => x + y) ⁻¹' s) = ν s := by
    letI : MeasurableSpace V := borel V
    haveI : BorelSpace V := ⟨rfl⟩
    exact ⟨Measure.addHaar, fun C hC => hC.measure_lt_top, fun U hU hne => hU.measure_ne_zero _ hne,
      fun x s => measure_preimage_add _ x s⟩
  refine ⟨ν.trim hle, ?_⟩
  exact
    { lt_top_of_isCompact := fun C hC => by
        obtain ⟨D, hCD, hD, hDm⟩ := hc C hC
        refine (measure_mono hCD).trans_lt ?_
        rw [trim_measurableSet_eq hle hDm]
        exact h1 D hD
      map_add_left_eq_self := fun x => by
        ext s hs
        rw [Measure.map_apply (measurable_const_add x) hs, trim_measurableSet_eq hle hs,
          trim_measurableSet_eq hle (measurable_const_add x hs), h3]
      open_pos := fun U hU hne h0 => h2 U hU hne (le_antisymm (h0 ▸ le_trim hle) bot_le) }

variable {K : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [MeasurableSpace K]
  [BorelSpace K] {a b : ℕ}

/- English proof (translation)
The claim follows from `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => Continuous.measurable (by fun_prop)`.
-/
theorem measurable_of_continuous {W : Type} [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (g : W → Fin a → Fin b → K) (hg : Continuous g) : Measurable g :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    Continuous.measurable (by fun_prop)

/- English proof (translation)
Use `exists_haar_of_le (Fin a → Fin b → K) ?_ ?_` and prove the remaining obligations. Conclude with `fun s hs => @measurable_of_continuous K _ _ _ _ _ a b (Fin a → Fin b → K) _ (borel _) (@BorelSpace.mk _ _ (borel _) rfl) id continuous_id s hs`. Introduce `C hC`. Use `⟨Set.univ.pi fun i => Set.univ.pi fun j => closure ((fun X => X i j) '' C), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun X hX i _ j _ => subset_closure ⟨X, hX, rfl⟩`.

Conclude with `isCompact_univ_pi fun i => isCompact_univ_pi fun j => (hC.image (by fun_prop)).closure`. Conclude with `MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => isClosed_closure.measurableSet`.
-/
theorem exists_haar [LocallyCompactSpace K] : ∃ μ : Measure (Fin a → Fin b → K), μ.IsAddHaarMeasure := by
  refine exists_haar_of_le (Fin a → Fin b → K) ?_ ?_
  · exact fun s hs => @measurable_of_continuous K _ _ _ _ _ a b (Fin a → Fin b → K) _ (borel _)
      (@BorelSpace.mk _ _ (borel _) rfl) id continuous_id s hs
  · intro C hC
    refine ⟨Set.univ.pi fun i => Set.univ.pi fun j => closure ((fun X => X i j) '' C), ?_, ?_, ?_⟩
    · exact fun X hX i _ j _ => subset_closure ⟨X, hX, rfl⟩
    · exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => (hC.image (by fun_prop)).closure
    · exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => isClosed_closure.measurableSet

/- English proof (translation)
Set `O : Fin a → Fin b → Set K` to `fun i j => (fun t : K => (Pi.single i (Pi.single j t) : Fin a → Fin b → K)) ⁻¹' M`. Establish `hO : ∀ i j, IsOpen (O i j)` using `fun i j => ho.preimage ((continuous_single (A := fun _ : Fin a => Fin b → K) i).comp (continuous_single (A := fun _ : Fin b => K) j))`. Set `B : Set (Fin a → Fin b → K)` to `Set.univ.pi fun i => Set.univ.pi fun j => O i j`. Establish `hBo : IsOpen B` using `isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ => hO i j`. Establish `hBm : MeasurableSet B` using `MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => (hO i j).measurableSet`.

Establish `hB0 : (0 : Fin a → Fin b → K) ∈ B` using `fun i _ j _ => by simp [O, M.zero_mem]`. Establish `hBM : ∀ X ∈ B, X ∈ M`. Introduce `X hX`. Establish `: X = ∑ i, ∑ j, (Pi.single i (Pi.single j (X i j)) : Fin a → Fin b → K)`. Use extensionality with `k l`.

Simplify using `[Finset.sum_apply, Pi.single_apply, ite_apply]`. Rewrite using `[this]`. Conclude with `M.sum_mem fun i _ => M.sum_mem fun j _ => hX i trivial j trivial`. Take `⟨t, ht⟩` from `hc.elim_finite_subcover (fun x : M => (fun y => -(x : Fin a → Fin b → K) + y) ⁻¹' B) (fun x => hBo.preimage (by fun_prop)) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simpa using hB0⟩)`. Establish `: (M : Set (Fin a → Fin b → K)) = ⋃ x ∈ t, (fun y => -(x : Fin a → Fin b → K) + y) ⁻¹' B`.

Use `ht.antisymm fun y hy => ?_` and prove the remaining obligations. Take `⟨x, -, hx⟩` from `Set.mem_iUnion₂.1 hy`. Use `M.add_mem x.2 (hBM _ hx)` as an intermediate fact. Simplify using `using this`. Rewrite using `[this]`.

Conclude with `Finset.measurableSet_biUnion _ fun x _ => measurable_const_add _ hBm`.
-/
theorem measurableSet_of_open_compact (M : AddSubgroup (Fin a → Fin b → K))
    (ho : IsOpen (M : Set (Fin a → Fin b → K))) (hc : IsCompact (M : Set (Fin a → Fin b → K))) :
    MeasurableSet (M : Set (Fin a → Fin b → K)) := by
  let O : Fin a → Fin b → Set K := fun i j =>
    (fun t : K => (Pi.single i (Pi.single j t) : Fin a → Fin b → K)) ⁻¹' M
  have hO : ∀ i j, IsOpen (O i j) := fun i j =>
    ho.preimage ((continuous_single (A := fun _ : Fin a => Fin b → K) i).comp
      (continuous_single (A := fun _ : Fin b => K) j))
  let B : Set (Fin a → Fin b → K) := Set.univ.pi fun i => Set.univ.pi fun j => O i j
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ => hO i j
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => (hO i j).measurableSet
  have hB0 : (0 : Fin a → Fin b → K) ∈ B := fun i _ j _ => by simp [O, M.zero_mem]
  have hBM : ∀ X ∈ B, X ∈ M := by
    intro X hX
    have : X = ∑ i, ∑ j, (Pi.single i (Pi.single j (X i j)) : Fin a → Fin b → K) := by
      ext k l
      simp [Finset.sum_apply, Pi.single_apply, ite_apply]
    rw [this]
    exact M.sum_mem fun i _ => M.sum_mem fun j _ => hX i trivial j trivial
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : M => (fun y => -(x : Fin a → Fin b → K) + y) ⁻¹' B)
    (fun x => hBo.preimage (by fun_prop)) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simpa using hB0⟩)
  have : (M : Set (Fin a → Fin b → K)) = ⋃ x ∈ t, (fun y => -(x : Fin a → Fin b → K) + y) ⁻¹' B := by
    refine ht.antisymm fun y hy => ?_
    obtain ⟨x, -, hx⟩ := Set.mem_iUnion₂.1 hy
    have := M.add_mem x.2 (hBM _ hx)
    simpa using this
  rw [this]
  exact Finset.measurableSet_biUnion _ fun x _ => measurable_const_add _ hBm

/- English proof (translation)
Establish `hind : ∀ q, (fun X => if -x q + X ∈ M then w q else 0) = ((fun X => -x q + X) ⁻¹' M).indicator (fun _ => w q)`. Introduce `q`. Use extensionality with `X`. Simplify using `[Set.indicator_apply]`. Establish `hmeas : ∀ q, MeasurableSet ((fun X => -x q + X) ⁻¹' M)` using `fun q => measurable_const_add _ hM`.

Establish `hvol : ∀ q, μ ((fun X => -x q + X) ⁻¹' M) = μ M` using `fun q => measure_preimage_add μ _ M`. Rewrite using `[integral_finset_sum]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hind q, integral_indicator_const _ (hmeas q), Measure.real, hvol q, Complex.real_smul]`.

Both sides reduce to the same expression. Introduce `q _`. Rewrite using `[hind q]`. Conclude with `(integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol q]; exact hfin))`.
-/
theorem integral_step {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (M : Set V) (hM : MeasurableSet M) (hfin : μ M ≠ ⊤) {Q : Type} (F : Finset Q)
    (w : Q → ℂ) (x : Q → V) :
    ∫ X, (∑ q ∈ F, if -x q + X ∈ M then w q else 0) ∂μ = μ.real M * ∑ q ∈ F, w q := by
  have hind : ∀ q, (fun X => if -x q + X ∈ M then w q else 0)
      = ((fun X => -x q + X) ⁻¹' M).indicator (fun _ => w q) := by
    intro q; ext X; simp [Set.indicator_apply]
  have hmeas : ∀ q, MeasurableSet ((fun X => -x q + X) ⁻¹' M) := fun q => measurable_const_add _ hM
  have hvol : ∀ q, μ ((fun X => -x q + X) ⁻¹' M) = μ M := fun q => measure_preimage_add μ _ M
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hind q, integral_indicator_const _ (hmeas q), Measure.real, hvol q, Complex.real_smul]
    rfl
  · intro q _
    rw [hind q]
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol q]; exact hfin))

end Measure

section Block

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

/- English proof (translation)
Establish `hpow : ∀ n : ℕ, A ^ n * X = X * B ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]`.

Establish `hp : ∀ p : Polynomial K, Polynomial.aeval A p * X = X * Polynomial.aeval B p`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [Matrix.add_mul, Matrix.mul_add, hp, hq]`. Consider the case `monomial n c`.

Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mul, Matrix.mul_smul, hpow]`. Take `⟨u, v, huv⟩` from `h`. Establish `h1 : Polynomial.aeval B (A.charpoly * u + v * B.charpoly) = 1` using `by rw [mul_comm _ u, huv, map_one]`. Rewrite `h1` using `[map_add, map_mul, map_mul, Matrix.aeval_self_charpoly B, mul_zero, add_zero]`. Establish `h2 : X * Polynomial.aeval B A.charpoly = 0`.

Rewrite using `[← hp, Matrix.aeval_self_charpoly, Matrix.zero_mul]`. Rewrite using `[← Matrix.mul_one X, ← h1, ← Matrix.mul_assoc, h2, Matrix.zero_mul]`.
-/
theorem sylvester (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (h : IsCoprime A.charpoly B.charpoly) (X : Matrix (Fin a) (Fin b) K) (hX : A * X = X * B) : X = 0 := by
  have hpow : ∀ n : ℕ, A ^ n * X = X * B ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hp : ∀ p : Polynomial K, Polynomial.aeval A p * X = X * Polynomial.aeval B p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [Matrix.add_mul, Matrix.mul_add, hp, hq]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mul, Matrix.mul_smul, hpow]
  obtain ⟨u, v, huv⟩ := h
  have h1 : Polynomial.aeval B (A.charpoly * u + v * B.charpoly) = 1 := by rw [mul_comm _ u, huv, map_one]
  rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly B, mul_zero, add_zero] at h1
  have h2 : X * Polynomial.aeval B A.charpoly = 0 := by
    rw [← hp, Matrix.aeval_self_charpoly, Matrix.zero_mul]
  rw [← Matrix.mul_one X, ← h1, ← Matrix.mul_assoc, h2, Matrix.zero_mul]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨A, C, B, hG⟩ : ∃ A C B, reindex e e (γ : Matrix ι ι K) = fromBlocks A C 0 B := by`. Establish `h21 : (reindex e e (γ : Matrix ι ι K)).toBlocks₂₁ = 0`. Use extensionality with `i j`. Establish `hγ' : (γ : Matrix ι ι K).BlockTriangular (side e)` using `hγ`. Conclude with `hγ' (i := e.symm (Sum.inr i)) (j := e.symm (Sum.inl j)) (by simp [side])`.

Conclude with `⟨_, _, _, by rw [← h21]; exact (fromBlocks_toBlocks _).symm⟩`. Establish `hγv : (γ : Matrix ι ι K) = reindex e.symm e.symm (fromBlocks A C 0 B)`. Rewrite using `[← hG]`. Use extensionality with `i j`. Simplify using `[reindex_apply]`.

Establish `hcop : IsCoprime A.charpoly B.charpoly`. Rewrite `hsep` using `[← charpoly_reindex e, hG, charpoly_fromBlocks_zero₂₁]`. Conclude with `hsep.isCoprime`. Establish `hA : IsUnit A.det`. Establish `h1 : IsUnit (γ : Matrix ι ι K).det` using `isUnits_det_units γ`.

Rewrite `h1` using `[← det_reindex_self e, hG, det_fromBlocks_zero₂₁]`. Conclude with `isUnit_of_mul_isUnit_left h1`. Set `L : Matrix (Fin a) (Fin b) K →ₗ[K] Matrix (Fin a) (Fin b) K` to `{ toFun := fun X => X - A⁻¹ * X * B map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]; abel map_smul' := fun c X => by simp [smul_sub] }`. Establish `hL : ∀ X, A * L X = A * X - X * B` using `fun X => by`. Express the relevant statement in the definitionally equal form `A * (X - A⁻¹ * X * B) = _`.

Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv A hA, Matrix.one_mul]`. Establish `hinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `X hX`. Use `hL X` as an intermediate fact.

Rewrite `this` using `[hX, Matrix.mul_zero]`. Conclude with `sylvester A B hcop X (sub_eq_zero.1 this.symm)`. Use `⟨(Matrix.ofLinearEquiv K).trans ((LinearEquiv.ofInjectiveEndo L hinj).trans (Matrix.ofLinearEquiv K).symm), fun X => Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `uMat e (-X) * (γ : Matrix ι ι K) * uMat e X = (γ : Matrix ι ι K) * uMat e (of.symm (L (of X)))`. Rewrite using `[hγv]`.

Simplify using `only [uMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Equiv.apply_symm_apply, hL]`. Use `congr 1`. Rewrite using `[← neg_of]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul]`. Use `congr 1`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_conj (e : ι ≃ Fin a ⊕ Fin b) (γ : GL ι K) (hγ : γ ∈ blockPar e)
    (hsep : (γ : Matrix ι ι K).charpoly.Separable) :
    ∃ Φ : (Fin a → Fin b → K) ≃ₗ[K] (Fin a → Fin b → K),
      ∀ X, (uGL e X)⁻¹ * γ * uGL e X = γ * uGL e (Φ X) := by
  obtain ⟨A, C, B, hG⟩ : ∃ A C B, reindex e e (γ : Matrix ι ι K) = fromBlocks A C 0 B := by
    have h21 : (reindex e e (γ : Matrix ι ι K)).toBlocks₂₁ = 0 := by
      ext i j
      have hγ' : (γ : Matrix ι ι K).BlockTriangular (side e) := hγ
      exact hγ' (i := e.symm (Sum.inr i)) (j := e.symm (Sum.inl j)) (by simp [side])
    exact ⟨_, _, _, by rw [← h21]; exact (fromBlocks_toBlocks _).symm⟩
  have hγv : (γ : Matrix ι ι K) = reindex e.symm e.symm (fromBlocks A C 0 B) := by
    rw [← hG]; ext i j; simp [reindex_apply]
  have hcop : IsCoprime A.charpoly B.charpoly := by
    rw [← charpoly_reindex e, hG, charpoly_fromBlocks_zero₂₁] at hsep
    exact hsep.isCoprime
  have hA : IsUnit A.det := by
    have h1 : IsUnit (γ : Matrix ι ι K).det := isUnits_det_units γ
    rw [← det_reindex_self e, hG, det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_left h1
  let L : Matrix (Fin a) (Fin b) K →ₗ[K] Matrix (Fin a) (Fin b) K :=
    { toFun := fun X => X - A⁻¹ * X * B
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c X => by simp [smul_sub] }
  have hL : ∀ X, A * L X = A * X - X * B := fun X => by
    change A * (X - A⁻¹ * X * B) = _
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv A hA, Matrix.one_mul]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have := hL X
    rw [hX, Matrix.mul_zero] at this
    exact sylvester A B hcop X (sub_eq_zero.1 this.symm)
  refine ⟨(Matrix.ofLinearEquiv K).trans ((LinearEquiv.ofInjectiveEndo L hinj).trans (Matrix.ofLinearEquiv K).symm),
    fun X => Units.ext ?_⟩
  change uMat e (-X) * (γ : Matrix ι ι K) * uMat e X = (γ : Matrix ι ι K) * uMat e (of.symm (L (of X)))
  rw [hγv]
  simp only [uMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Equiv.apply_symm_apply, hL]
  congr 1
  rw [← neg_of]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul]
  congr 1
  abel

end Block

/- English proof (translation)
Introduce `K _ _ _ _ _ _ ι _ _ a b e f _ _ hint K' hK'o hK'c hbi γ hγ hsep`. Take `⟨μ, hμ⟩` from `exists_haar (K := K) (a := a) (b := b)`. Take `⟨Φ, hΦ⟩` from `exists_conj e γ hγ hsep`. Establish `hΦc : Continuous Φ` using `continuous_of_linear Φ.toLinearMap`. Establish `hΦs : Continuous Φ.symm` using `continuous_of_linear Φ.symm.toLinearMap`.

Take `⟨hΛo, hΛc⟩` from `lam_open_compact e K' hK'o hK'c`. Set `M : AddSubgroup (Fin a → Fin b → K)` to `(lam e K').comap Φ.symm.toLinearMap.toAddMonoidHom`. Establish `hM : ∀ Y, Y ∈ (M : Set (Fin a → Fin b → K)) ↔ uGL e (Φ.symm Y) ∈ K'` using `fun Y => Iff.rfl`. Establish `hMo : IsOpen (M : Set (Fin a → Fin b → K))` using `hΛo.preimage hΦs`. Establish `hMc : IsCompact (M : Set (Fin a → Fin b → K))`.

Use `(hΛc.image hΦc).of_isClosed_subset (M.isClosed_of_isOpen hMo) fun Y hY => ?_` and prove the remaining obligations. Conclude with `⟨Φ.symm Y, hY, Φ.apply_symm_apply Y⟩`. Establish `hMm` using `measurableSet_of_open_compact M hMo hMc`. Use `set H : Subgroup (GL ι K) := blockUni e ⊓ (blockPar e ⊓ K') with hH`. Use `set s : GL ι K ⧸ H → ℂ := fun q => if Quotient.out q ∈ blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0 with hs`.

Distinguish the cases in `hfin : (Function.support s).Finite`. Use `swap`. Conclude with `finsum_of_infinite_support hfin`. Rewrite using `[finsum_eq_sum s hfin]`. Establish `key : ∀ Y, f (γ * uGL e Y) = ∑ q ∈ hfin.toFinset, if -(Φ (coord e (Quotient.out q))) + Y ∈ (M : Set (Fin a → Fin b → K)) then s q else 0`.

Introduce `Y`. Take `⟨X, rfl⟩` from `Φ.surjective Y`. Establish `h0 : s (QuotientGroup.mk (uGL e X)) = f (γ * uGL e (Φ X))`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H (uGL e X)`. Establish `hU : uGL e X * h ∈ blockUni e` using `(blockUni e).mul_mem (uGL_mem e X) h.2.1`.

Simplify using `only [hs, hh, hU, if_true]`. Rewrite using `[← hΦ, ← hbi _ (K'.inv_mem h.2.2.2) _ h.2.2.2 ((uGL e X)⁻¹ * γ * uGL e X)]`. Use `congr 1`. Use `group`. Establish `h1 : ∀ q ∈ hfin.toFinset, (-(Φ (coord e (Quotient.out q))) + Φ X ∈ (M : Set (Fin a → Fin b → K)) ↔ q = QuotientGroup.mk (uGL e X))`.

Introduce `q hq`. Establish `hq' : Quotient.out q ∈ blockUni e`. Assume the negation of the conclusion as `hn`. Conclude with `(hfin.mem_toFinset.1 hq) (if_neg hn)`. Establish `e1 : (Quotient.out q)⁻¹ * uGL e X = uGL e (-coord e (Quotient.out q) + X)`.

Rewrite using `[uGL_add, uGL_neg, ← eq_uGL_coord e hq']`. Rewrite using `[hM, ← map_neg, ← map_add, Φ.symm_apply_apply]`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, e1]`. Conclude with `⟨fun h => ⟨uGL_mem e _, uGL_mem_blockPar e _, h⟩, fun h => h.2.2⟩`. Rewrite using `[Finset.sum_congr rfl fun q hq => if_congr (h1 q hq) rfl rfl, Finset.sum_ite_eq', ← h0]`.

Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `Function.notMem_support.1 fun h' => h (hfin.mem_toFinset.2 h')`. Establish `hint'` using `hint μ hμ γ 1`. Simplify using `only [inv_one, one_mul, mul_one, key] at hint'`.

Rewrite `hint'` using `[integral_step μ _ hMm hMc.measure_lt_top.ne _ s (fun q => Φ (coord e (Quotient.out q)))]`. Use `(mul_eq_zero.1 hint').resolve_left ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_eq_zero]`. Conclude with `ENNReal.toReal_ne_zero.2 ⟨hMo.measure_ne_zero μ ⟨0, M.zero_mem⟩, hMc.measure_lt_top.ne⟩`.
-/
theorem finsum_conj_eq_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (f : GL ι K → ℂ),
  IsLocallyConstant f → HasCompactSupport f →
  (∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0) →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f (k * g * k') = f g) →
  ∀ γ ∈ GlobalTheory.OrbDesc.blockPar e, (γ : Matrix ι ι K).charpoly.Separable →
  ∑ᶠ q : GL ι K ⧸ (GlobalTheory.OrbDesc.blockUni e ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K')),
    (if Quotient.out q ∈ GlobalTheory.OrbDesc.blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0) = 0 := by
  intro K _ _ _ _ _ _ ι _ _ a b e f _ _ hint K' hK'o hK'c hbi γ hγ hsep
  obtain ⟨μ, hμ⟩ := exists_haar (K := K) (a := a) (b := b)
  obtain ⟨Φ, hΦ⟩ := exists_conj e γ hγ hsep
  have hΦc : Continuous Φ := continuous_of_linear Φ.toLinearMap
  have hΦs : Continuous Φ.symm := continuous_of_linear Φ.symm.toLinearMap
  obtain ⟨hΛo, hΛc⟩ := lam_open_compact e K' hK'o hK'c
  let M : AddSubgroup (Fin a → Fin b → K) := (lam e K').comap Φ.symm.toLinearMap.toAddMonoidHom
  have hM : ∀ Y, Y ∈ (M : Set (Fin a → Fin b → K)) ↔ uGL e (Φ.symm Y) ∈ K' := fun Y => Iff.rfl
  have hMo : IsOpen (M : Set (Fin a → Fin b → K)) := hΛo.preimage hΦs
  have hMc : IsCompact (M : Set (Fin a → Fin b → K)) := by
    refine (hΛc.image hΦc).of_isClosed_subset (M.isClosed_of_isOpen hMo) fun Y hY => ?_
    exact ⟨Φ.symm Y, hY, Φ.apply_symm_apply Y⟩
  have hMm := measurableSet_of_open_compact M hMo hMc
  set H : Subgroup (GL ι K) := blockUni e ⊓ (blockPar e ⊓ K') with hH
  set s : GL ι K ⧸ H → ℂ := fun q =>
    if Quotient.out q ∈ blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0 with hs
  by_cases hfin : (Function.support s).Finite
  swap
  · exact finsum_of_infinite_support hfin
  rw [finsum_eq_sum s hfin]
  have key : ∀ Y, f (γ * uGL e Y) = ∑ q ∈ hfin.toFinset,
      if -(Φ (coord e (Quotient.out q))) + Y ∈ (M : Set (Fin a → Fin b → K)) then s q else 0 := by
    intro Y
    obtain ⟨X, rfl⟩ := Φ.surjective Y
    have h0 : s (QuotientGroup.mk (uGL e X)) = f (γ * uGL e (Φ X)) := by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (uGL e X)
      have hU : uGL e X * h ∈ blockUni e := (blockUni e).mul_mem (uGL_mem e X) h.2.1
      simp only [hs, hh, hU, if_true]
      rw [← hΦ, ← hbi _ (K'.inv_mem h.2.2.2) _ h.2.2.2 ((uGL e X)⁻¹ * γ * uGL e X)]
      congr 1
      group
    have h1 : ∀ q ∈ hfin.toFinset, (-(Φ (coord e (Quotient.out q))) + Φ X ∈ (M : Set (Fin a → Fin b → K))
        ↔ q = QuotientGroup.mk (uGL e X)) := by
      intro q hq
      have hq' : Quotient.out q ∈ blockUni e := by
        by_contra hn
        exact (hfin.mem_toFinset.1 hq) (if_neg hn)
      have e1 : (Quotient.out q)⁻¹ * uGL e X = uGL e (-coord e (Quotient.out q) + X) := by
        rw [uGL_add, uGL_neg, ← eq_uGL_coord e hq']
      rw [hM, ← map_neg, ← map_add, Φ.symm_apply_apply]
      conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, e1]
      exact ⟨fun h => ⟨uGL_mem e _, uGL_mem_blockPar e _, h⟩, fun h => h.2.2⟩
    rw [Finset.sum_congr rfl fun q hq => if_congr (h1 q hq) rfl rfl, Finset.sum_ite_eq', ← h0]
    split_ifs with h
    · rfl
    · exact Function.notMem_support.1 fun h' => h (hfin.mem_toFinset.2 h')
  have hint' := hint μ hμ γ 1
  simp only [inv_one, one_mul, mul_one, key] at hint'
  rw [integral_step μ _ hMm hMc.measure_lt_top.ne _ s (fun q => Φ (coord e (Quotient.out q)))] at hint'
  refine (mul_eq_zero.1 hint').resolve_left ?_
  rw [Complex.ofReal_eq_zero]
  exact ENNReal.toReal_ne_zero.2 ⟨hMo.measure_ne_zero μ ⟨0, M.zero_mem⟩, hMc.measure_lt_top.ne⟩

end GlobalTheory.OrbDesc.NSum
