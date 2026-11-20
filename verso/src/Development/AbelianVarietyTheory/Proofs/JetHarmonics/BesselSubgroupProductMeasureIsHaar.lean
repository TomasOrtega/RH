import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ProdHaar

open PI

/- English proof (translation)
Establish `him : ∀ A : Set X, MeasurableSet A → MeasurableSet (f '' (A ∩ T))` using `fun A hA => (hA.inter hT).image_of_continuousOn_injOn hf.continuousOn (hinj.mono Set.inter_subset_right)`. Establish `himT : MeasurableSet (f '' T)` using `by simpa using him Set.univ MeasurableSet.univ`. Use `⟨⟨⟨fun n => f '' (spanningSets μ n ∩ T) ∪ (f '' T)ᶜ, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hf.measurable ((him _ (measurableSet_spanningSets μ n)).union himT.compl)]`. Establish `hsub : f ⁻¹' (f '' (spanningSets μ n ∩ T) ∪ (f '' T)ᶜ) ⊆ spanningSets μ n ∪ Tᶜ`.

Introduce `x hx`. Distinguish the cases in `hxT : x ∈ T`. Break down `hx with ⟨y, hy, hyx⟩ | hx` into its components or cases. Use `left`. Rewrite using `[← hinj hy.2 hxT hyx]`.

Conclude with `hy.1`. Conclude with `absurd ⟨x, hxT, rfl⟩ hx`. Conclude with `Or.inr hxT`. Use `lt_of_le_of_lt ((measure_mono hsub).trans (measure_union_le _ _)) ?_` and prove the remaining obligations. Rewrite using `[h0, add_zero]`.

Conclude with `measure_spanningSets_lt_top μ n`. Apply `Set.eq_univ_of_forall` to reduce the goal to its premises. Introduce `y`. Distinguish the cases in `hy : y ∈ f '' T`. Take `⟨x, hx, rfl⟩` from `hy`.

Establish `: x ∈ ⋃ n, spanningSets μ n` using `by rw [iUnion_spanningSets]; trivial`. Take `⟨n, hn⟩` from `Set.mem_iUnion.1 this`. Conclude with `Set.mem_iUnion.2 ⟨n, Or.inl ⟨x, ⟨hn, hx⟩, rfl⟩⟩`. Conclude with `Set.mem_iUnion.2 ⟨0, Or.inr hy⟩`.
-/
theorem sigmaFinite_map_of_injOn {X Y : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [SigmaFinite μ] {f : X → Y} (hf : Continuous f) {T : Set X}
    (hT : MeasurableSet T) (hinj : Set.InjOn f T) (h0 : μ Tᶜ = 0) : SigmaFinite (μ.map f) := by
  have him : ∀ A : Set X, MeasurableSet A → MeasurableSet (f '' (A ∩ T)) := fun A hA =>
    (hA.inter hT).image_of_continuousOn_injOn hf.continuousOn (hinj.mono Set.inter_subset_right)
  have himT : MeasurableSet (f '' T) := by simpa using him Set.univ MeasurableSet.univ
  refine ⟨⟨⟨fun n => f '' (spanningSets μ n ∩ T) ∪ (f '' T)ᶜ, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [Measure.map_apply hf.measurable ((him _ (measurableSet_spanningSets μ n)).union himT.compl)]
    have hsub : f ⁻¹' (f '' (spanningSets μ n ∩ T) ∪ (f '' T)ᶜ) ⊆ spanningSets μ n ∪ Tᶜ := by
      intro x hx
      by_cases hxT : x ∈ T
      · rcases hx with ⟨y, hy, hyx⟩ | hx
        · left
          rw [← hinj hy.2 hxT hyx]; exact hy.1
        · exact absurd ⟨x, hxT, rfl⟩ hx
      · exact Or.inr hxT
    refine lt_of_le_of_lt ((measure_mono hsub).trans (measure_union_le _ _)) ?_
    rw [h0, add_zero]
    exact measure_spanningSets_lt_top μ n
  · apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' T
    · obtain ⟨x, hx, rfl⟩ := hy
      have : x ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 this
      exact Set.mem_iUnion.2 ⟨n, Or.inl ⟨x, ⟨hn, hx⟩, rfl⟩⟩
    · exact Set.mem_iUnion.2 ⟨0, Or.inr hy⟩

variable {m : ℕ}

noncomputable def mulP (p : MtM m × MtM m) : MtM m :=
  fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

/- English proof (translation)
Establish `h1 : Continuous (fun p : MtM m × MtM m => (Matrix.of p.1 : Matrix (Fin m) (Fin m) ℂ))` using `continuous_fst`. Establish `h2 : Continuous (fun p : MtM m × MtM m => (Matrix.of p.2 : Matrix (Fin m) (Fin m) ℂ))` using `continuous_snd`. Conclude with `h1.matrix_mul h2`.
-/
theorem continuous_mulP : Continuous (mulP (m := m)) := by
  have h1 : Continuous (fun p : MtM m × MtM m => (Matrix.of p.1 : Matrix (Fin m) (Fin m) ℂ)) := continuous_fst
  have h2 : Continuous (fun p : MtM m × MtM m => (Matrix.of p.2 : Matrix (Fin m) (Fin m) ℂ)) := continuous_snd
  exact h1.matrix_mul h2

/- English proof (translation)
The claim follows from `(continuous_mulP.comp (continuous_const.prodMk continuous_id : Continuous fun x : MtM m => ((a : MtM m), x))).measurable`.
-/
theorem measurable_lmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Measurable (lmulQ a) :=
  (continuous_mulP.comp (continuous_const.prodMk continuous_id : Continuous fun x : MtM m => ((a : MtM m), x))).measurable

/- English proof (translation)
The claim follows from `(continuous_mulP.comp (continuous_id.prodMk continuous_const : Continuous fun x : MtM m => (x, (a : MtM m)))).measurable`.
-/
theorem measurable_rmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Measurable (rmulQ a) :=
  (continuous_mulP.comp (continuous_id.prodMk continuous_const : Continuous fun x : MtM m => (x, (a : MtM m)))).measurable

/- English proof (translation)
Rewrite using `[Measure.map_apply continuous_mulP.measurable hB, Measure.prod_apply (continuous_mulP.measurable hB)]`. Both sides reduce to the same expression.
-/
theorem map_mulP_apply (μ ν : Measure (MtM m)) [SFinite ν] {B : Set (MtM m)} (hB : MeasurableSet B) :
    ((μ.prod ν).map mulP) B = ∫⁻ h, ν (lmulQ (Matrix.of h) ⁻¹' B) ∂μ := by
  rw [Measure.map_apply continuous_mulP.measurable hB, Measure.prod_apply (continuous_mulP.measurable hB)]
  rfl

/- English proof (translation)
The claim follows from `measurable_measure_prodMk_left (ν := ν) (continuous_mulP.measurable hB)`.
-/
theorem measurable_slice (ν : Measure (MtM m)) [SFinite ν] {B : Set (MtM m)} (hB : MeasurableSet B) :
    Measurable fun h : MtM m => ν (lmulQ (Matrix.of h) ⁻¹' B) :=
  measurable_measure_prodMk_left (ν := ν) (continuous_mulP.measurable hB)

/- English proof (translation)
Use extensionality with `B hB`. Rewrite using `[Measure.map_apply (measurable_lmulQ a) hB, map_mulP_apply _ _ (measurable_lmulQ a hB), map_mulP_apply _ _ hB]`. Use `conv_rhs => rw [← ha]`. Rewrite using `[lintegral_map (measurable_slice ν hB) (measurable_lmulQ a)]`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `x`. Establish `: lmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of (lmulQ a h)) x` using `(Matrix.mul_assoc a (Matrix.of h) (Matrix.of x)).symm`. Simplify using `only [Set.mem_preimage, this]`.
-/
theorem matrixPairProduct_map_left_invariant_first (μ ν : Measure (MtM m)) [SFinite ν] {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : μ.map (lmulQ a) = μ) : ((μ.prod ν).map mulP).map (lmulQ a) = (μ.prod ν).map mulP := by
  ext B hB
  rw [Measure.map_apply (measurable_lmulQ a) hB, map_mulP_apply _ _ (measurable_lmulQ a hB),
    map_mulP_apply _ _ hB]
  conv_rhs => rw [← ha]
  rw [lintegral_map (measurable_slice ν hB) (measurable_lmulQ a)]
  refine lintegral_congr fun h => ?_
  congr 1
  ext x
  have : lmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of (lmulQ a h)) x :=
    (Matrix.mul_assoc a (Matrix.of h) (Matrix.of x)).symm
  simp only [Set.mem_preimage, this]

/- English proof (translation)
Use extensionality with `B hB`. Rewrite using `[Measure.map_apply (measurable_rmulQ a) hB, map_mulP_apply _ _ (measurable_rmulQ a hB), map_mulP_apply _ _ hB]`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← ha]`. Rewrite using `[Measure.map_apply (measurable_rmulQ a) (measurable_lmulQ _ hB)]`.

Use `congr 1`. Use extensionality with `x`. Establish `: rmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of h) (rmulQ a x)` using `Matrix.mul_assoc (Matrix.of h) (Matrix.of x) a`. Simplify using `only [Set.mem_preimage, this]`.
-/
theorem right_N (μ ν : Measure (MtM m)) [SFinite ν] {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : ν.map (rmulQ a) = ν) : ((μ.prod ν).map mulP).map (rmulQ a) = (μ.prod ν).map mulP := by
  ext B hB
  rw [Measure.map_apply (measurable_rmulQ a) hB, map_mulP_apply _ _ (measurable_rmulQ a hB),
    map_mulP_apply _ _ hB]
  refine lintegral_congr fun h => ?_
  conv_rhs => rw [← ha]
  rw [Measure.map_apply (measurable_rmulQ a) (measurable_lmulQ _ hB)]
  congr 1
  ext x
  have : rmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of h) (rmulQ a x) :=
    Matrix.mul_assoc (Matrix.of h) (Matrix.of x) a
  simp only [Set.mem_preimage, this]

/- English proof (translation)
Use extensionality with `B hB`. Rewrite using `[Measure.map_apply (measurable_lmulQ a) hB, map_mulP_apply _ _ (measurable_lmulQ a hB), map_mulP_apply _ _ hB]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ha] with h ⟨b, hb, hν⟩`. Use `conv_rhs => rw [← hν]`.

Rewrite using `[Measure.map_apply (measurable_lmulQ b) (measurable_lmulQ _ hB)]`. Use `congr 1`. Use extensionality with `x`. Establish `: lmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of h) (lmulQ b x)` using `by show a * (Matrix.of h * Matrix.of x) = Matrix.of h * (b * Matrix.of x)`. Rewrite using `[← Matrix.mul_assoc, hb, Matrix.mul_assoc]`.

Simplify using `only [Set.mem_preimage, this]`.
-/
theorem left_N (μ ν : Measure (MtM m)) [SFinite ν] {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : ∀ᵐ h ∂μ, ∃ b : Matrix (Fin m) (Fin m) ℂ, a * Matrix.of h = Matrix.of h * b ∧
      ν.map (lmulQ b) = ν) : ((μ.prod ν).map mulP).map (lmulQ a) = (μ.prod ν).map mulP := by
  ext B hB
  rw [Measure.map_apply (measurable_lmulQ a) hB, map_mulP_apply _ _ (measurable_lmulQ a hB),
    map_mulP_apply _ _ hB]
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with h ⟨b, hb, hν⟩
  conv_rhs => rw [← hν]
  rw [Measure.map_apply (measurable_lmulQ b) (measurable_lmulQ _ hB)]
  congr 1
  ext x
  have : lmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of h) (lmulQ b x) := by
    show a * (Matrix.of h * Matrix.of x) = Matrix.of h * (b * Matrix.of x)
    rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc]
  simp only [Set.mem_preimage, this]

/- English proof (translation)
Establish `hc : Measurable (fun x : MtM m => (fun i j => (b * Matrix.of x * a) i j : MtM m))` using `(measurable_rmulQ a).comp (measurable_lmulQ b)`. Use extensionality with `B hB`. Rewrite using `[Measure.map_apply (measurable_rmulQ a) hB, map_mulP_apply _ _ (measurable_rmulQ a hB), map_mulP_apply _ _ hB]`. Use `conv_rhs => rw [← ha]`. Rewrite using `[lintegral_map (measurable_slice ν hB) (measurable_rmulQ a)]`.

Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← hν]`. Rewrite using `[Measure.map_apply hc (measurable_lmulQ _ hB)]`. Use `congr 1`. Use extensionality with `x`.

Establish `: rmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of (rmulQ a h)) (fun i j => (b * Matrix.of x * a) i j : MtM m)` using `by show (Matrix.of h * Matrix.of x) * a = (Matrix.of h * a) * (b * Matrix.of x * a)`. Rewrite using `[Matrix.mul_assoc (Matrix.of h) a, ← Matrix.mul_assoc a, ← Matrix.mul_assoc a, hab, Matrix.one_mul, Matrix.mul_assoc]`. Simplify using `only [Set.mem_preimage, this]`.
-/
theorem matrixPairProduct_map_right_invariant_first (μ ν : Measure (MtM m)) [SFinite ν] {a b : Matrix (Fin m) (Fin m) ℂ}
    (hab : a * b = 1) (ha : μ.map (rmulQ a) = μ)
    (hν : ν.map (fun x : MtM m => (fun i j => (b * Matrix.of x * a) i j : MtM m)) = ν) :
    ((μ.prod ν).map mulP).map (rmulQ a) = (μ.prod ν).map mulP := by
  have hc : Measurable (fun x : MtM m => (fun i j => (b * Matrix.of x * a) i j : MtM m)) :=
    (measurable_rmulQ a).comp (measurable_lmulQ b)
  ext B hB
  rw [Measure.map_apply (measurable_rmulQ a) hB, map_mulP_apply _ _ (measurable_rmulQ a hB),
    map_mulP_apply _ _ hB]
  conv_rhs => rw [← ha]
  rw [lintegral_map (measurable_slice ν hB) (measurable_rmulQ a)]
  refine lintegral_congr fun h => ?_
  conv_rhs => rw [← hν]
  rw [Measure.map_apply hc (measurable_lmulQ _ hB)]
  congr 1
  ext x
  have : rmulQ a (lmulQ (Matrix.of h) x) = lmulQ (Matrix.of (rmulQ a h))
      (fun i j => (b * Matrix.of x * a) i j : MtM m) := by
    show (Matrix.of h * Matrix.of x) * a = (Matrix.of h * a) * (b * Matrix.of x * a)
    rw [Matrix.mul_assoc (Matrix.of h) a, ← Matrix.mul_assoc a, ← Matrix.mul_assoc a, hab,
      Matrix.one_mul, Matrix.mul_assoc]
  simp only [Set.mem_preimage, this]

end GlobalTheory.ProdHaar

namespace GlobalTheory.ProdHaar

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
The claim follows from `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
theorem isClosed_UH : IsClosed (UH (Hpk k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

/- English proof (translation)
Unfold `Nset`. Simplify using `only [Set.setOf_and, Set.setOf_forall]`. Use `isClosed_UH.inter (IsClosed.inter ?_ ?_)` and prove the remaining obligations. Use `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`.

Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`.
-/
theorem isClosed_Nset : IsClosed (Nset k r) := by
  unfold Nset
  simp only [Set.setOf_and, Set.setOf_forall]
  refine isClosed_UH.inter (IsClosed.inter ?_ ?_)
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const

/- English proof (translation)
Use `haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.1 (unitary_weyl_compact k r z hz hT)`. Establish `hc : Continuous fun p : UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Hpk k r * (p.1.1)ᴴ * Hpk k r * p.2` using `((continuous_const.matrix_mul (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_snd`. Establish `h` using `isClosedMap_snd_of_compactSpace _ (isClosed_Nset.preimage hc)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `s`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, n, hn, rfl⟩`. Use `⟨(⟨h, hh⟩, h * n), ?_, rfl⟩` and prove the remaining obligations. Use `show Hpk k r * hᴴ * Hpk k r * (h * n) ∈ Nset k r`. Rewrite using `[← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]`.

Conclude with `hn`. Introduce and unpack `⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩`. Use `⟨h, hh, _, hp, ?_⟩` and prove the remaining obligations. Use `show s' = h * (Hpk k r * hᴴ * Hpk k r * s')`. Rewrite using `[← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]`.
-/
theorem isClosed_Sset (hz : inWb k r z) (hT : 0 < Tz k r z) : IsClosed (Sset k r z) := by
  haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.1 (unitary_weyl_compact k r z hz hT)
  have hc : Continuous fun p : UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Hpk k r * (p.1.1)ᴴ * Hpk k r * p.2 :=
    ((continuous_const.matrix_mul (continuous_subtype_val.comp
      continuous_fst).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_snd
  have h := isClosedMap_snd_of_compactSpace _ (isClosed_Nset.preimage hc)
  convert h using 1
  ext s
  constructor
  · rintro ⟨h, hh, n, hn, rfl⟩
    refine ⟨(⟨h, hh⟩, h * n), ?_, rfl⟩
    show Hpk k r * hᴴ * Hpk k r * (h * n) ∈ Nset k r
    rw [← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]; exact hn
  · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
    refine ⟨h, hh, _, hp, ?_⟩
    show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
    rw [← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `hij : inW k r i ∧ inW k r j`. Conclude with `h2.2.2 i j hij.2.1 hij.2.2 hij.1.1`. Conclude with `uw_block h1 i j hij`.
-/
theorem eq_one_of_mem {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h1 : g ∈ UWset k r z) (h2 : g ∈ Nset k r) : g = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hij : inW k r i ∧ inW k r j
  · exact h2.2.2 i j hij.2.1 hij.2.2 hij.1.1
  · exact uw_block h1 i j hij

/- English proof (translation)
Establish `e1 : h'⁻¹ * h = n' * n⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_inv_UH hn.1, Matrix.mul_one]`. Use `_ = n' * n⁻¹ := by rw [e, ← Matrix.mul_assoc, inv_mul_UH' hh'.1, Matrix.one_mul]`. Establish `e2 : h'⁻¹ * h = 1` using `eq_one_of_mem (mul_mem_UW (inv_mem_UW hh') hh) (e1 ▸ (nilpotent_subgroup k r).2.1 _ hn' _ ((nilpotent_subgroup k r).2.2 _ hn))`.

Establish `e3 : h = h'`. Combine the equalities or inequalities in the displayed calculation. Substitute `e3` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_injective {h h' n n' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (e : h * n = h' * n') : h = h' ∧ n = n' := by
  have e1 : h'⁻¹ * h = n' * n⁻¹ := by
    calc h'⁻¹ * h = h'⁻¹ * (h * n) * n⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_inv_UH hn.1, Matrix.mul_one]
      _ = n' * n⁻¹ := by rw [e, ← Matrix.mul_assoc, inv_mul_UH' hh'.1, Matrix.one_mul]
  have e2 : h'⁻¹ * h = 1 := eq_one_of_mem (mul_mem_UW (inv_mem_UW hh') hh)
    (e1 ▸ (nilpotent_subgroup k r).2.1 _ hn' _ ((nilpotent_subgroup k r).2.2 _ hn))
  have e3 : h = h' := by
    calc h = h' * (h'⁻¹ * h) := by rw [← Matrix.mul_assoc, mul_inv_UH hh'.1, Matrix.one_mul]
      _ = h' := by rw [e2, Matrix.mul_one]
  subst e3
  refine ⟨rfl, ?_⟩
  calc n = h⁻¹ * (h * n) := by rw [← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]
    _ = n' := by rw [e, ← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]

/- English proof (translation)
Introduce and unpack `_ ⟨h, hh, n, hn, rfl⟩`. Conclude with `mul_mem_UH hh.1 hn.1`.
-/
theorem Sset_subset : Sset k r z ⊆ UH (Hpk k r) := by
  rintro _ ⟨h, hh, n, hn, rfl⟩
  exact mul_mem_UH hh.1 hn.1

/- English proof (translation)
Use `⟨isClosed_Sset hz hT, uw_sub_S one_mem_UW, ?_, fun a ha => ⟨?_, mul_inv_UH (Sset_subset ha)⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, n, hn, rfl⟩ _ ⟨h', hh', n', hn', rfl⟩`. Use `⟨h * h', mul_mem_UW hh hh', h'⁻¹ * n * h'⁻¹⁻¹ * n', (nilpotent_subgroup k r).2.1 _ (hnorm _ (inv_mem_UW hh') _ hn) _ hn', ?_⟩` and prove the remaining obligations. Rewrite using `[inv_inv_UH hh'.1]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc h' h'⁻¹, mul_inv_UH hh'.1, Matrix.one_mul]`. Take `⟨h, hh, n, hn, rfl⟩` from `ha`. Use `⟨h⁻¹, inv_mem_UW hh, h * n⁻¹ * h⁻¹, hnorm _ hh _ ((nilpotent_subgroup k r).2.2 _ hn), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]`.
-/
theorem isMatGroup_Sset (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hnorm : ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h * n * h⁻¹ ∈ Nset k r) :
    IsMatGroup (Sset k r z) := by
  refine ⟨isClosed_Sset hz hT, uw_sub_S one_mem_UW, ?_, fun a ha => ⟨?_, mul_inv_UH (Sset_subset ha)⟩⟩
  · rintro _ ⟨h, hh, n, hn, rfl⟩ _ ⟨h', hh', n', hn', rfl⟩
    refine ⟨h * h', mul_mem_UW hh hh', h'⁻¹ * n * h'⁻¹⁻¹ * n',
      (nilpotent_subgroup k r).2.1 _ (hnorm _ (inv_mem_UW hh') _ hn) _ hn', ?_⟩
    rw [inv_inv_UH hh'.1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h' h'⁻¹, mul_inv_UH hh'.1, Matrix.one_mul]
  · obtain ⟨h, hh, n, hn, rfl⟩ := ha
    refine ⟨h⁻¹, inv_mem_UW hh, h * n⁻¹ * h⁻¹, hnorm _ hh _ ((nilpotent_subgroup k r).2.2 _ hn), ?_⟩
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_UH' hh.1, Matrix.one_mul]

/- English proof (translation)
Take `⟨hμs, hμ0, hμc, hμl⟩` from `hμ`. Take `⟨hνs, hν0, hνc, hνl⟩` from `hν`. Use `set T : Set (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) := {x | Matrix.of x ∈ UWset k r z} ×ˢ {x | Matrix.of x ∈ Nset k r} with hTdef`. Establish `hW : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ UWset k r z}` using `(unitary_weyl_compact k r z hz hT).isClosed`. Establish `hN : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ Nset k r}` using `isClosed_Nset`.

Establish `hS : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ Sset k r z}` using `isClosed_Sset hz hT`. Establish `hTm : MeasurableSet T` using `hW.measurableSet.prod hN.measurableSet`. Establish `hT0 : (μ.prod ν) Tᶜ = 0`. Rewrite using `[hTdef, Set.compl_prod_eq_union]`. Use `measure_union_null ?_ ?_` and prove the remaining obligations.

Rewrite using `[Measure.prod_prod]`. Conclude with `mul_eq_zero_of_left hμc _`. Rewrite using `[Measure.prod_prod]`. Conclude with `mul_eq_zero_of_right _ hνc`. Use `⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `haveI : PolishSpace (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) := { toSecondCountableTopology := inferInstance toIsCompletelyMetrizableSpace := MetricSpace.toIsCompletelyMetrizableSpace }`. Use `sigmaFinite_map_of_injOn _ continuous_mulP hTm ?_ hT0` and prove the remaining obligations. Introduce `p hp q hq e`. Take `⟨e1, e2⟩` from `mul_injective hp.1 hq.1 hp.2 hq.2 e`. Conclude with `Prod.ext e1 e2`.

Introduce `h0`. Rewrite `h0` using `[Measure.map_eq_zero_iff continuous_mulP.measurable.aemeasurable]`. Establish `hu` using `congrArg (fun ρ : Measure (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) => ρ Set.univ) h0`. Simplify using `only [Measure.coe_zero, Pi.zero_apply] at hu`. Rewrite `hu` using `[← Set.univ_prod_univ, Measure.prod_prod]`.

Break down `mul_eq_zero.mp hu with h | h` into its components or cases. Conclude with `hμ0 (Measure.measure_univ_eq_zero.mp h)`. Conclude with `hν0 (Measure.measure_univ_eq_zero.mp h)`. Use `Measure.map_apply (μ := μ.prod ν) continuous_mulP.measurable hS.measurableSet.compl` as an intermediate fact. Use `this.trans (measure_mono_null ?_ hT0)` and prove the remaining obligations.

Introduce `p hp hpT`. Conclude with `hp ⟨_, hpT.1, _, hpT.2, rfl⟩`. Introduce and unpack `_ ⟨h, hh, n, hn, rfl⟩`. Establish `e : lmulQ (h * n) = lmulQ h ∘ lmulQ n` using `funext fun x => Matrix.mul_assoc h n (Matrix.of x)`. Rewrite using `[e, ← Measure.map_map (measurable_lmulQ h) (measurable_lmulQ n), left_N, matrixPairProduct_map_left_invariant_first _ _ (hμl h hh)]`.

Establish `hae : ∀ᵐ x ∂μ, Matrix.of x ∈ UWset k r z` using `ae_iff.2 hμc`. Use `filter_upwards [hae] with x hx`. Use `⟨_, ?_, hνl _ (hnorm _ (inv_mem_UW hx) _ hn)⟩` and prove the remaining obligations. Rewrite using `[inv_inv_UH hx.1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_inv_UH hx.1, Matrix.one_mul]`. Introduce and unpack `_ ⟨h, hh, n, hn, rfl⟩`.

Establish `e : rmulQ (h * n) = rmulQ n ∘ rmulQ h`. Use function extensionality and compare the values at `fun x => (Matrix.mul_assoc (Matrix.of x) h n).symm`. Establish `hc` using `hconj _ (inv_mem_UW hh)`. Rewrite `hc` using `[inv_inv_UH hh.1]`. Rewrite using `[e, ← Measure.map_map (measurable_rmulQ n) (measurable_rmulQ h), matrixPairProduct_map_right_invariant_first _ _ (mul_inv_UH hh.1) (hμr h hh) hc, right_N _ _ (hνr n hn)]`.
-/
theorem haar_prod (hz : inWb k r z) (hT : 0 < Tz k r z) (μ ν : Measure (MtM (2 * r + k + 1)))
    (hμ : IsHaarOnM (UWset k r z) μ) (hν : IsHaarOnM (Nset k r) ν)
    (hμr : IsRightInvM (UWset k r z) μ) (hνr : IsRightInvM (Nset k r) ν)
    (hnorm : ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h * n * h⁻¹ ∈ Nset k r)
    (hconj : ∀ h ∈ UWset k r z, ν.map (fun x : MtM (2 * r + k + 1) =>
      (fun i j => (h * Matrix.of x * h⁻¹) i j : MtM (2 * r + k + 1))) = ν) :
    IsHaarOnM (Sset k r z) ((μ.prod ν).map mulP) ∧ IsRightInvM (Sset k r z) ((μ.prod ν).map mulP) := by
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  set T : Set (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) :=
    {x | Matrix.of x ∈ UWset k r z} ×ˢ {x | Matrix.of x ∈ Nset k r} with hTdef
  have hW : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ UWset k r z} :=
    (unitary_weyl_compact k r z hz hT).isClosed
  have hN : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ Nset k r} := isClosed_Nset
  have hS : IsClosed {x : MtM (2 * r + k + 1) | Matrix.of x ∈ Sset k r z} := isClosed_Sset hz hT
  have hTm : MeasurableSet T := hW.measurableSet.prod hN.measurableSet
  have hT0 : (μ.prod ν) Tᶜ = 0 := by
    rw [hTdef, Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod]; exact mul_eq_zero_of_left hμc _
    · rw [Measure.prod_prod]; exact mul_eq_zero_of_right _ hνc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · haveI : PolishSpace (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) :=
      { toSecondCountableTopology := inferInstance
        toIsCompletelyMetrizableSpace := MetricSpace.toIsCompletelyMetrizableSpace }
    refine sigmaFinite_map_of_injOn _ continuous_mulP hTm ?_ hT0
    intro p hp q hq e
    obtain ⟨e1, e2⟩ := mul_injective hp.1 hq.1 hp.2 hq.2 e
    exact Prod.ext e1 e2
  · intro h0
    rw [Measure.map_eq_zero_iff continuous_mulP.measurable.aemeasurable] at h0
    have hu := congrArg (fun ρ : Measure (MtM (2 * r + k + 1) × MtM (2 * r + k + 1)) => ρ Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at hu
    rw [← Set.univ_prod_univ, Measure.prod_prod] at hu
    rcases mul_eq_zero.mp hu with h | h
    · exact hμ0 (Measure.measure_univ_eq_zero.mp h)
    · exact hν0 (Measure.measure_univ_eq_zero.mp h)
  · have := Measure.map_apply (μ := μ.prod ν) continuous_mulP.measurable hS.measurableSet.compl
    refine this.trans (measure_mono_null ?_ hT0)
    intro p hp hpT
    exact hp ⟨_, hpT.1, _, hpT.2, rfl⟩
  · rintro _ ⟨h, hh, n, hn, rfl⟩
    have e : lmulQ (h * n) = lmulQ h ∘ lmulQ n := funext fun x => Matrix.mul_assoc h n (Matrix.of x)
    rw [e, ← Measure.map_map (measurable_lmulQ h) (measurable_lmulQ n), left_N, matrixPairProduct_map_left_invariant_first _ _ (hμl h hh)]
    have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ UWset k r z := ae_iff.2 hμc
    filter_upwards [hae] with x hx
    refine ⟨_, ?_, hνl _ (hnorm _ (inv_mem_UW hx) _ hn)⟩
    rw [inv_inv_UH hx.1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_inv_UH hx.1, Matrix.one_mul]
  · rintro _ ⟨h, hh, n, hn, rfl⟩
    have e : rmulQ (h * n) = rmulQ n ∘ rmulQ h :=
      funext fun x => (Matrix.mul_assoc (Matrix.of x) h n).symm
    have hc := hconj _ (inv_mem_UW hh)
    rw [inv_inv_UH hh.1] at hc
    rw [e, ← Measure.map_map (measurable_rmulQ n) (measurable_rmulQ h),
      matrixPairProduct_map_right_invariant_first _ _ (mul_inv_UH hh.1) (hμr h hh) hc, right_N _ _ (hνr n hn)]

end GlobalTheory.ProdHaar

/- English proof (translation)
Introduce `k r z μW μN hz hT hW hN`. Take `⟨h1, -, h3, h4, h5⟩` from `GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN`. Establish `h` using `GlobalTheory.ProdHaar.haar_prod (k := k) (r := r) (z := z) hz hT μW μN hW hN h1 h3 h4 h5`. Conclude with `⟨GlobalTheory.ProdHaar.isMatGroup_Sset (k := k) (r := r) (z := z) hz hT h4, GlobalTheory.ProdHaar.Sset_subset (k := k) (r := r) (z := z), h.1, h.2⟩`.
-/
theorem GlobalTheory.muSof_isHaar : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsMatGroup (Formalism.QuantumDeterminants.Sset k r z) ∧ Formalism.QuantumDeterminants.Sset k r z ⊆ GG k r ∧ PI.IsHaarOnM (Formalism.QuantumDeterminants.Sset k r z) (muSof μW μN) ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Sset k r z) (muSof μW μN) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨h1, -, h3, h4, h5⟩ := GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN
  have h := GlobalTheory.ProdHaar.haar_prod (k := k) (r := r) (z := z) hz hT μW μN hW hN h1 h3 h4 h5
  exact ⟨GlobalTheory.ProdHaar.isMatGroup_Sset (k := k) (r := r) (z := z) hz hT h4,
    GlobalTheory.ProdHaar.Sset_subset (k := k) (r := r) (z := z), h.1, h.2⟩
