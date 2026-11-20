import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Establish `h` using `(hpkFacts k r).2.1`. Establish `h2 : (Hpk k r).det * (Hpk k r).det = 1` using `by rw [← Matrix.det_mul, h, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ h2`.
-/
lemma hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := (hpkFacts k r).2.1
  have h2 : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ h2

/- English proof (translation)
Take `⟨h1, hm, hi⟩` from `uHGroup _ (Hpk k r) (hpk_unit k r)`. Use `⟨⟨h1, fun v _ => Matrix.one_mulVec v⟩, ?_, ?_, fun a ha => (hi a ha.1).1, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Use `⟨hm a ha.1 b hb.1, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, hb.2 v hv, ha.2 v hv]`.

Introduce `a ha`. Use `⟨(hi a ha.1).2, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h` using `ha.2 v hv`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : IsClosed {g : Mat k r | g ∈ GV k r}`.

Apply `isClosed_eq` to reduce the goal to its premises. Use `fun_prop`. Conclude with `continuous_const`. Establish `hc2 : IsClosed {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v}`. Establish `: {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v} = ⋂ v ∈ F, {g : Mat k r | g *ᵥ v = v}`.

Use extensionality with `g`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `isClosed_biInter fun v _ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Conclude with `Continuous.matrix_mulVec continuous_id continuous_const`.

Conclude with `hc1.inter hc2`.
-/
lemma closed_stab (k r : ℕ) (F : Set (Fin (2 * r + k + 1) → ℂ)) :
    IsClosedSubgroup {g : Mat k r | g ∈ GV k r ∧ ∀ v ∈ F, g *ᵥ v = v} := by
  obtain ⟨h1, hm, hi⟩ := uHGroup _ (Hpk k r) (hpk_unit k r)
  refine ⟨⟨h1, fun v _ => Matrix.one_mulVec v⟩, ?_, ?_, fun a ha => (hi a ha.1).1, ?_⟩
  · intro a ha b hb
    refine ⟨hm a ha.1 b hb.1, fun v hv => ?_⟩
    rw [← Matrix.mulVec_mulVec, hb.2 v hv, ha.2 v hv]
  · intro a ha
    refine ⟨(hi a ha.1).2, fun v hv => ?_⟩
    have h := ha.2 v hv
    calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [h]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hi a ha.1).1, Matrix.one_mulVec]
  · have hc1 : IsClosed {g : Mat k r | g ∈ GV k r} := by
      apply isClosed_eq
      · fun_prop
      · exact continuous_const
    have hc2 : IsClosed {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v} := by
      have : {g : Mat k r | ∀ v ∈ F, g *ᵥ v = v} = ⋂ v ∈ F, {g : Mat k r | g *ᵥ v = v} := by
        ext g; simp
      rw [this]
      refine isClosed_biInter fun v _ => isClosed_eq ?_ continuous_const
      exact Continuous.matrix_mulVec continuous_id continuous_const
    exact hc1.inter hc2

/- English proof (translation)
Introduce `k r z`. Establish `h` using `closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)) ∪ {z})`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce and unpack `v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl)`. Conclude with `(h2 a).1`. Conclude with `(h2 a).2`.

Conclude with `h3`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a => ⟨h2 _ (Or.inl (Or.inl ⟨a, rfl⟩)), h2 _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩, h2 _ (Or.inr rfl)⟩`.
-/
theorem closedW : ClosedW := by
  intro k r z
  have h := closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)) ∪ {z})
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl)
    · exact (h2 a).1
    · exact (h2 a).2
    · exact h3
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => ⟨h2 _ (Or.inl (Or.inl ⟨a, rfl⟩)), h2 _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩, h2 _ (Or.inr rfl)⟩

/- English proof (translation)
Introduce `k r`. Establish `h` using `closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce and unpack `v (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `(h2 a).1`. Conclude with `(h2 a).2`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a => ⟨h2 _ (Or.inl ⟨a, rfl⟩), h2 _ (Or.inr ⟨a, rfl⟩)⟩⟩`.
-/
theorem closedWb : ClosedWb := by
  intro k r
  have h := closed_stab k r (Set.range (fun a => bvec (eI k r a)) ∪ Set.range (fun a => bvec (esI k r a)))
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro v (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact (h2 a).1
    · exact (h2 a).2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => ⟨h2 _ (Or.inl ⟨a, rfl⟩), h2 _ (Or.inr ⟨a, rfl⟩)⟩⟩

/- English proof (translation)
Establish `hmeas : Measurable φ` using `hφ.continuous.measurable`. Establish `hUc : @IsClosed (Mt k r) _ U` using `hU ▸ hφ.isClosed_range`. Establish `hUm : @MeasurableSet (Mt k r) _ U` using `hUc.measurableSet`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hmeas hUm.compl]`.

Establish `: φ ⁻¹' (U : Set (Mt k r))ᶜ = ∅`. Apply `Set.eq_empty_of_forall_notMem` to reduce the goal to its premises. Introduce `x hx`. Conclude with `hx (hU ▸ ⟨x, rfl⟩)`. Rewrite using `[this, measure_empty]`.

Introduce `a ha`. Rewrite `ha` using `[← hU]`. Take `⟨γ, rfl⟩` from `ha`. Establish `hl : Measurable (lmulM (k` using `k) (r := r) (φ γ)) := by`. Establish `: Continuous (lmulM (k` using `k) (r := r) (φ γ)) := by`.

Unfold `lmulM`. Conclude with `Continuous.matrix_mul continuous_const continuous_id`. Conclude with `this.measurable`. Rewrite using `[Measure.map_map hl hmeas]`. Establish `: lmulM (φ γ) ∘ φ = φ ∘ (fun x => γ * x)`.

Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, lmulM, hmul]`. Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map hmeas (measurable_const_mul γ), map_mul_left_eq_self]`. Introduce `a ha`.

Rewrite `ha` using `[← hU]`. Take `⟨γ, rfl⟩` from `ha`. Establish `hl : Measurable (rmulF (φ γ))`. Establish `: Continuous (rmulF (φ γ))`. Unfold `rmulF`.

Conclude with `Continuous.matrix_mul continuous_id continuous_const`. Conclude with `this.measurable`. Rewrite using `[Measure.map_map hl hmeas]`. Establish `: rmulF (φ γ) ∘ φ = φ ∘ (fun x => x * γ)`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp, rmulF, hmul]`. Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map hmeas (measurable_mul_const γ), map_mul_right_eq_self]`. Introduce `K hK`. Rewrite using `[Measure.map_apply hmeas hK.isClosed.measurableSet]`.

Conclude with `(hφ.isCompact_preimage hK).measure_lt_top`. Introduce `h0`. Apply `hm0` to reduce the goal to its premises. Use `congrArg (fun μ => μ Set.univ) h0` as an intermediate fact. Simplify using `only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this`.

Conclude with `Measure.measure_univ_eq_zero.mp this`.
-/
lemma haar_push {k r : ℕ} {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    (m : Measure Γ) [m.IsMulLeftInvariant] [m.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m] (hm0 : m ≠ 0)
    (φ : Γ → Mt k r) (hφ : IsClosedEmbedding φ)
    (hmul : ∀ a b : Γ, φ (a * b) = (Matrix.of (φ a) * Matrix.of (φ b) : Mat k r))
    (U : Set (Mat k r)) (hU : Set.range φ = U) : IsHaarOn U (m.map φ) := by
  have hmeas : Measurable φ := hφ.continuous.measurable
  have hUc : @IsClosed (Mt k r) _ U := hU ▸ hφ.isClosed_range
  have hUm : @MeasurableSet (Mt k r) _ U := hUc.measurableSet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hmeas hUm.compl]
    have : φ ⁻¹' (U : Set (Mt k r))ᶜ = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      exact hx (hU ▸ ⟨x, rfl⟩)
    rw [this, measure_empty]
  · intro a ha
    rw [← hU] at ha
    obtain ⟨γ, rfl⟩ := ha
    have hl : Measurable (lmulM (k := k) (r := r) (φ γ)) := by
      have : Continuous (lmulM (k := k) (r := r) (φ γ)) := by
        unfold lmulM
        exact Continuous.matrix_mul continuous_const continuous_id
      exact this.measurable
    rw [Measure.map_map hl hmeas]
    have : lmulM (φ γ) ∘ φ = φ ∘ (fun x => γ * x) := by
      funext x
      simp only [Function.comp, lmulM, hmul]
      rfl
    rw [this, ← Measure.map_map hmeas (measurable_const_mul γ), map_mul_left_eq_self]
  · intro a ha
    rw [← hU] at ha
    obtain ⟨γ, rfl⟩ := ha
    have hl : Measurable (rmulF (φ γ)) := by
      have : Continuous (rmulF (φ γ)) := by
        unfold rmulF
        exact Continuous.matrix_mul continuous_id continuous_const
      exact this.measurable
    rw [Measure.map_map hl hmeas]
    have : rmulF (φ γ) ∘ φ = φ ∘ (fun x => x * γ) := by
      funext x
      simp only [Function.comp, rmulF, hmul]
      rfl
    rw [this, ← Measure.map_map hmeas (measurable_mul_const γ), map_mul_right_eq_self]
  · intro K hK
    rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact (hφ.isCompact_preimage hK).measure_lt_top
  · intro h0
    apply hm0
    have := congrArg (fun μ => μ Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.mp this

/- English proof (translation)
Introduce `h`. Use `isOpen_univ.measure_pos m ⟨1, trivial⟩` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
lemma haar_ne_zero {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ]
    (m : Measure Γ) [m.IsOpenPosMeasure] : m ≠ 0 := by
  intro h
  have := isOpen_univ.measure_pos m ⟨1, trivial⟩
  rw [h] at this
  simp at this

/- English proof (translation)
Introduce `k r`. Take `⟨-, -, -, ε, -, P, hP, hPH⟩` from `hpkFacts k r`. Establish `: (muG ε).IsMulRightInvariant` using `⟨fun g => unimodular _ ε g⟩`. Establish `hemb` using `uJEmb _ ε`. Set `c : Mt k r → Mt k r` to `fun x => (P⁻¹ * Matrix.of x * P : Mat k r)`.

Set `c' : Mt k r → Mt k r` to `fun x => (P * Matrix.of x * P⁻¹ : Mat k r)`. Establish `hc : Continuous c` using `(Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)`. Establish `hc' : Continuous c'` using `(Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)`. Establish `h1 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ hP`. Establish `h2 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hP`.

Establish `hli : Function.LeftInverse c' c`. Introduce `x`. Use `show (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = x`. Establish `: (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = (P * P⁻¹) * Matrix.of x * (P * P⁻¹)`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[this, h2, Matrix.one_mul, Matrix.mul_one]`. Both sides reduce to the same expression. Establish `hce : IsClosedEmbedding c` using `hli.isClosedEmbedding hc' hc`. Set `ι : UJ ε → Mt k r` to `fun g => ((g : (Mat k r)ˣ) : Mat k r)`. Establish `hι : IsClosedEmbedding ι` using `hemb.1`.

Establish `hιr : ∀ x : Mat k r, inUJ ε x ↔ ∃ g, ι g = x` using `fun x => by`. Use `Set.ext_iff.mp hemb.2 x` as an intermediate fact. Conclude with `this.symm`. Use `⟨(muG ε).map (c ∘ ι), ?_⟩` and prove the remaining obligations. Apply `haar_push (muG ε) (haar_ne_zero _) _ (hce.comp hι)` to reduce the goal to its premises.

Introduce `a b show (P⁻¹ * ((a : (Mat k r)ˣ) * (b : (Mat k r)ˣ) : Mat k r) * P : Mat k r) = (P⁻¹ * ((a : (Mat k r)ˣ) : Mat k r) * P) * (P⁻¹ * ((b : (Mat k r)ˣ) : Mat k r) * P)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Matrix.one_mul]`. Use `_ = _ := by rw [← h2]; simp only [Matrix.mul_assoc]`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Apply `(uHConj _ ε _ P hP hPH _).mpr` to reduce the goal to its premises. Establish `: (P * Matrix.of (c (ι x)) * P⁻¹ : Mat k r) = Matrix.of (ι x)` using `hli (ι x)`. Use `show inUJ ε (P * Matrix.of (c (ι x)) * P⁻¹)`.

Rewrite using `[this]`. Conclude with `(hιr _).mpr ⟨x, rfl⟩`. Introduce `hg`. Take `⟨x, hx⟩` from `(hιr _).mp ((uHConj _ ε _ P hP hPH g).mp hg)`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Use `show (P⁻¹ * Matrix.of (ι x) * P : Mat k r) = g`. Rewrite using `[hx]`. Use `show (P⁻¹ * (P * Matrix.of g * P⁻¹) * P : Mat k r) = Matrix.of g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Matrix.of g := by rw [h1, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem haarG : HaarGExists := by
  intro k r
  obtain ⟨-, -, -, ε, -, P, hP, hPH⟩ := hpkFacts k r
  have : (muG ε).IsMulRightInvariant := ⟨fun g => unimodular _ ε g⟩
  have hemb := uJEmb _ ε
  let c : Mt k r → Mt k r := fun x => (P⁻¹ * Matrix.of x * P : Mat k r)
  let c' : Mt k r → Mt k r := fun x => (P * Matrix.of x * P⁻¹ : Mat k r)
  have hc : Continuous c := (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)
  have hc' : Continuous c' := (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have hli : Function.LeftInverse c' c := by
    intro x
    show (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = x
    have : (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = (P * P⁻¹) * Matrix.of x * (P * P⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.one_mul, Matrix.mul_one]; rfl
  have hce : IsClosedEmbedding c := hli.isClosedEmbedding hc' hc
  let ι : UJ ε → Mt k r := fun g => ((g : (Mat k r)ˣ) : Mat k r)
  have hι : IsClosedEmbedding ι := hemb.1
  have hιr : ∀ x : Mat k r, inUJ ε x ↔ ∃ g, ι g = x := fun x => by
    have := Set.ext_iff.mp hemb.2 x
    exact this.symm
  refine ⟨(muG ε).map (c ∘ ι), ?_⟩
  apply haar_push (muG ε) (haar_ne_zero _) _ (hce.comp hι)
  · intro a b
    show (P⁻¹ * ((a : (Mat k r)ˣ) * (b : (Mat k r)ˣ) : Mat k r) * P : Mat k r) =
      (P⁻¹ * ((a : (Mat k r)ˣ) : Mat k r) * P) * (P⁻¹ * ((b : (Mat k r)ˣ) : Mat k r) * P)
    calc (P⁻¹ * ((a : (Mat k r)ˣ) * (b : (Mat k r)ˣ) : Mat k r) * P : Mat k r)
        = P⁻¹ * ((a : (Mat k r)ˣ) : Mat k r) * 1 * ((b : (Mat k r)ˣ) : Mat k r) * P := by
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by rw [← h2]; simp only [Matrix.mul_assoc]
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      apply (uHConj _ ε _ P hP hPH _).mpr
      have : (P * Matrix.of (c (ι x)) * P⁻¹ : Mat k r) = Matrix.of (ι x) := hli (ι x)
      show inUJ ε (P * Matrix.of (c (ι x)) * P⁻¹)
      rw [this]; exact (hιr _).mpr ⟨x, rfl⟩
    · intro hg
      obtain ⟨x, hx⟩ := (hιr _).mp ((uHConj _ ε _ P hP hPH g).mp hg)
      refine ⟨x, ?_⟩
      show (P⁻¹ * Matrix.of (ι x) * P : Mat k r) = g
      rw [hx]
      show (P⁻¹ * (P * Matrix.of g * P⁻¹) * P : Mat k r) = Matrix.of g
      calc (P⁻¹ * (P * Matrix.of g * P⁻¹) * P : Mat k r) = (P⁻¹ * P) * Matrix.of g * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.of g := by rw [h1, Matrix.one_mul, Matrix.mul_one]

def Grp {k r : ℕ} (U : Set (Mat k r)) (_h : IsClosedSubgroup U) : Type := U

namespace Grp
variable {k r : ℕ} {U : Set (Mat k r)} {h : IsClosedSubgroup U}

def val (a : Grp U h) : Mat k r := Subtype.val a
/- English proof (translation)
The claim follows from `Subtype.property a`.
-/
lemma mem (a : Grp U h) : a.val ∈ U := Subtype.property a
def mk (x : Mat k r) (hx : x ∈ U) : Grp U h := (⟨x, hx⟩ : U)
/- English proof (translation)
The claim follows from `Subtype.ext e`.
-/
lemma ext' {a b : Grp U h} (e : a.val = b.val) : a = b := Subtype.ext e

instance : Group (Grp U h) where
  mul a b := mk (a.val * b.val) (h.mul_mem _ a.mem _ b.mem)
  one := mk 1 h.one_mem
  inv a := mk (a.val⁻¹) (h.inv_mem _ a.mem)
  mul_assoc a b c := ext' (Matrix.mul_assoc _ _ _)
  one_mul a := ext' (Matrix.one_mul _)
  mul_one a := ext' (Matrix.mul_one _)
  inv_mul_cancel a := ext' (Matrix.nonsing_inv_mul _ (h.unit _ a.mem))

instance : TopologicalSpace (Grp U h) := inferInstanceAs (TopologicalSpace U)
instance : MeasurableSpace (Grp U h) := borel _
instance : BorelSpace (Grp U h) := ⟨rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma val_mul (a b : Grp U h) : (a * b).val = a.val * b.val := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma val_inv (a : Grp U h) : (a⁻¹).val = a.val⁻¹ := rfl

/- English proof (translation)
The claim follows from `h.closed.isClosedEmbedding_subtypeVal`.
-/
lemma emb : IsClosedEmbedding (val : Grp U h → Mat k r) := h.closed.isClosedEmbedding_subtypeVal

/- English proof (translation)
The claim follows from `Subtype.range_val`.
-/
lemma range_val : Set.range (val : Grp U h → Mat k r) = U := Subtype.range_val

instance : IsTopologicalGroup (Grp U h) where
  continuous_mul := by
    rw [emb.isInducing.continuous_iff]
    exact Continuous.matrix_mul (emb.continuous.comp continuous_fst) (emb.continuous.comp continuous_snd)
  continuous_inv := by
    rw [emb.isInducing.continuous_iff]
    have : (val ∘ fun a : Grp U h => a⁻¹) = fun a : Grp U h => (a.val.det)⁻¹ • a.val.adjugate := by
      funext a
      show a.val⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    have hv : Continuous (val : Grp U h → Mat k r) := emb.continuous
    refine Continuous.smul (Continuous.inv₀ hv.matrix_det fun a => (h.unit _ a.mem).ne_zero) hv.matrix_adjugate

instance : LocallyCompactSpace (Grp U h) :=
  have : LocallyCompactSpace (Mat k r) := inferInstanceAs (LocallyCompactSpace (Mt k r))
  emb.locallyCompactSpace
instance : T2Space (Grp U h) := emb.isEmbedding.t2Space

end Grp

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (fun x => x * g) m) m`. Establish `hu : (Measure.map (fun x => x * g) m) Set.univ = m Set.univ`. Rewrite using `[Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]`. Establish `h2` using `hu`.

Rewrite `h2` using `[h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hpos : m Set.univ ≠ 0` using `(isOpen_univ.measure_pos m ⟨1, trivial⟩).ne'`. Establish `hfin : m Set.univ ≠ ⊤` using `(isCompact_univ.measure_lt_top).ne`. Establish `h3 : ((Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m : ℝ≥0) : ℝ≥0∞) * m Set.univ = 1 * m Set.univ`. Rewrite using `[h2, one_mul]`.

Rewrite `h3` using `[ENNReal.mul_left_inj hpos hfin]`. Rewrite using `[h]`. Establish `h4 : Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m = 1` using `by exact_mod_cast h3`. Rewrite using `[h4, one_smul]`.
-/
lemma compact_right_inv {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [CompactSpace Γ] (m : Measure Γ) [m.IsHaarMeasure] : m.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (fun x => x * g) m) m
  have hu : (Measure.map (fun x => x * g) m) Set.univ = m Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h2 := hu
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have hpos : m Set.univ ≠ 0 := (isOpen_univ.measure_pos m ⟨1, trivial⟩).ne'
  have hfin : m Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have h3 : ((Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m : ℝ≥0) : ℝ≥0∞) * m Set.univ = 1 * m Set.univ := by
    rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos hfin] at h3
  rw [h]
  have h4 : Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m = 1 := by exact_mod_cast h3
  rw [h4, one_smul]

/- English proof (translation)
Introduce `k r U h hc`. Establish `: CompactSpace (Grp U h)` using `isCompact_iff_compactSpace.mp hc`. Establish `: (Measure.haar : Measure (Grp U h)).IsMulRightInvariant` using `compact_right_inv _`. Use `⟨(Measure.haar : Measure (Grp U h)).map (Grp.val : Grp U h → Mt k r), ?_⟩` and prove the remaining obligations. Conclude with `haar_push _ (haar_ne_zero _) _ Grp.emb (fun a b => rfl) U Grp.range_val`.
-/
theorem compactHaar : CompactHaarExists := by
  intro k r U h hc
  have : CompactSpace (Grp U h) := isCompact_iff_compactSpace.mp hc
  have : (Measure.haar : Measure (Grp U h)).IsMulRightInvariant := compact_right_inv _
  refine ⟨(Measure.haar : Measure (Grp U h)).map (Grp.val : Grp U h → Mt k r), ?_⟩
  exact haar_push _ (haar_ne_zero _) _ Grp.emb (fun a b => rfl) U Grp.range_val

variable {k r : ℕ}

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

/- English proof (translation)
Use `hi` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [wI, midx]`. Use linear arithmetic over natural numbers and integers.
-/
lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

/- English proof (translation)
Use `m.isLt` as an intermediate fact. Apply the tactic sequence `constructor <;> simp only [wI] <;> omega`.
-/
lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [wI, midx]`. Use linear arithmetic over natural numbers and integers.
-/
lemma midx_wI (m : Fin (k + 1)) : midx (mid_wI (r := r) m) = m := by
  apply Fin.ext
  simp only [wI, midx]
  omega

/- English proof (translation)
Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [wI] at this`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_neg (fun h => hj h.2)]`. Distinguish the cases in `h : q = j`. Substitute `h` using the available equality. Rewrite using `[if_pos ⟨rfl, hj⟩, if_pos rfl]`.

Rewrite using `[if_neg (fun h' => h h'.1), if_neg h]`.
-/
lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_neg (fun h => hq h.1)]`. Distinguish the cases in `h : q = j`. Rewrite using `[if_pos ⟨h, hq⟩, if_pos h]`. Rewrite using `[if_neg (fun h' => h h'.1), if_neg h]`.
-/
lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_pos ⟨hq, hj⟩]`. Both sides reduce to the same expression.
-/
lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dif_pos ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (midx hi)]`. Rewrite using `[Em, if_pos (wI_midx hi).symm, one_mul]`. Introduce `b _ hb`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hi, h]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`.

Conclude with `hi (h ▸ mid_wI b)`.
-/
lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (midx hj)]`. Rewrite using `[Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]`. Introduce `b _ hb`. Rewrite using `[Matrix.transpose_apply, Em, if_neg, mul_zero]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hj, h]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Matrix.transpose_apply, Em, if_neg, mul_zero]`. Introduce `h`.

Conclude with `hj (h ▸ mid_wI b)`.
-/
lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]`. Simplify using `only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]`. Introduce `i _ hi`. Simplify using `only [Matrix.transpose_apply, Em]`. Rewrite using `[if_neg hi (c := i = wI k r a), zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma Em_conjT : (Em k r)ᴴ = (Em k r)ᵀ := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← Em_conjT, Matrix.conjTranspose_conjTranspose]`.
-/
lemma EmT_conjT : ((Em k r)ᵀ)ᴴ = Em k r := by
  rw [← Em_conjT, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]`. Distinguish the cases in `hj : mid k r j`. Rewrite using `[mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]`. Distinguish the cases in `hi : mid k r i`.

Rewrite using `[Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]`. Establish `: Em k r i (midx hj) = if i = j then 1 else 0` using `by rw [Em, wI_midx hj]`. Rewrite using `[this, sub_self, add_zero]`. Rewrite using `[Em_mul_out _ i _ hi, emb_out_row μ i j hi]`. Establish `: Em k r i (midx hj) = if i = j then 1 else 0` using `by rw [Em, wI_midx hj]`.

Rewrite using `[this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]`. Rewrite using `[mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring

/- English proof (translation)
Use extensionality with `i m`. Establish `h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]`. Rewrite using `[Em, if_pos rfl, mul_one]`. Introduce `b _ hb`.

Rewrite using `[Em, if_neg hb, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h1]`. Establish `hm` using `m.isLt`.

Establish `hil` using `i.isLt`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[Em_mul_mid _ i _ hi]`. Establish `h0` using `hi`. Unfold `Hpk Hb`.

Rewrite using `[Matrix.diagonal_apply]`. Simplify using `only [wI, midx, Fin.ext_iff, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[Em_mul_out _ i _ hi]`. Unfold `Hpk`.

Simplify using `only [wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma Hpk_Em : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  have h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]
    · rw [Em, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Em, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have hm := m.isLt
  have hil := i.isLt
  by_cases hi : mid k r i
  · rw [Em_mul_mid _ i _ hi]
    have h0 := hi
    unfold Hpk Hb
    rw [Matrix.diagonal_apply]
    simp only [wI, midx, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [Em_mul_out _ i _ hi]
    unfold Hpk
    simp only [wI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]`.
-/
lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

/- English proof (translation)
Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]`.
-/
lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

/- English proof (translation)
Rewrite using `[emb_eq, emb_eq]`. Use `set E := Em k r with hE`. Use `set Q := 1 - E * Eᵀ with hQ`. Establish `t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ`. Combine the equalities or inequalities in the displayed calculation.

Establish `t2 : E * a * Eᵀ * M * Q = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `t3 : Q * M * (E * b * Eᵀ) = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]`.
-/
lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_eq, emb_eq]
  set E := Em k r with hE
  set Q := 1 - E * Eᵀ with hQ
  have t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ := by
    calc E * a * Eᵀ * M * (E * b * Eᵀ) = E * a * (Eᵀ * M) * E * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * E) * b * Eᵀ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = E * (a * N * b) * Eᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have t2 : E * a * Eᵀ * M * Q = 0 := by
    calc E * a * Eᵀ * M * Q = E * a * (Eᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * Q) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [EmT_Q, Matrix.mul_zero]
  have t3 : Q * M * (E * b * Eᵀ) = 0 := by
    calc Q * M * (E * b * Eᵀ) = Q * (M * E) * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * E) * N * b * Eᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Q_Em]; simp only [Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[emb_eq, Matrix.mul_one, add_sub_cancel]`.
-/
lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

/- English proof (translation)
Establish `h` using `sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])`. Rewrite `h` using `[Matrix.mul_one]`. Rewrite using `[h, emb_eq, Matrix.mul_one, Matrix.mul_one]`. Use `congr 1`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]`.
-/
lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  have h := sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.mul_one] at h
  rw [h, emb_eq, Matrix.mul_one, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]

/- English proof (translation)
Rewrite using `[emb_eq, emb_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT, Matrix.mul_assoc]`.
-/
lemma emb_conjT (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (embWb k r a)ᴴ = embWb k r aᴴ := by
  rw [emb_eq, emb_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT, Matrix.mul_assoc]

/- English proof (translation)
Unfold `Hb`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : j = Fin.last k <;> simp [h]`.
-/
lemma Hb_conjT : (Hb k)ᴴ = Hb k := by
  unfold Hb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]

/- English proof (translation)
Establish `h` using `congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, (hpkFacts k r).1, Hb_conjT]`. Conclude with `h`.
-/
lemma EmT_Hpk : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, (hpkFacts k r).1, Hb_conjT] at h
  exact h

/- English proof (translation)
Rewrite using `[emb_conjT]`. Conclude with `sandwich _ _ _ _ Hpk_Em EmT_Hpk`.
-/
lemma emb_form (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (embWb k r a)ᴴ * Hpk k r * embWb k r a =
      Em k r * (aᴴ * Hb k * a) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_conjT]
  exact sandwich _ _ _ _ Hpk_Em EmT_Hpk

/- English proof (translation)
Establish `h` using `emb_form (k := k) (r := r) 1`. Rewrite `h` using `[emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Conclude with `h`.
-/
lemma Hpk_eq : Hpk k r =
      Em k r * Hb k * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  have h := emb_form (k := k) (r := r) 1
  rw [emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one] at h
  exact h

/- English proof (translation)
Establish `h2 : (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = (Em k r)ᵀ * (Em k r * b * (Em k r)ᵀ) * Em k r` using `by rw [h]`. Establish `e : ∀ c : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = c`. Introduce `c`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = c := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]`. Rewrite `h2` using `[e, e]`. Then use the resulting hypothesis.
-/
lemma sand_inj {a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : Em k r * a * (Em k r)ᵀ = Em k r * b * (Em k r)ᵀ) :
    a = b := by
  have h2 : (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = (Em k r)ᵀ * (Em k r * b * (Em k r)ᵀ) * Em k r := by rw [h]
  have e : ∀ c : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = c := by
    intro c
    calc (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * c * ((Em k r)ᵀ * Em k r) := by
          simp only [Matrix.mul_assoc]
      _ = c := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]
  rwa [e, e] at h2

/- English proof (translation)
Use `show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _`. Rewrite using `[emb_form]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))`.

Introduce `h`. Rewrite using `[h]`. Conclude with `Hpk_eq.symm`.
-/
lemma emb_mem (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r a ∈ GV k r ↔ aᴴ * Hb k * a = Hb k := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _
  rw [emb_form]
  constructor
  · intro h
    exact sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))
  · intro h
    rw [h]
    exact Hpk_eq.symm

/- English proof (translation)
Rewrite using `[emb_eq, Matrix.mul_add, Matrix.add_mul, EmT_Q, Matrix.zero_mul, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = a := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]`.
-/
lemma emb_linv (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (Em k r)ᵀ * embWb k r a * Em k r = a := by
  rw [emb_eq, Matrix.mul_add, Matrix.add_mul, EmT_Q, Matrix.zero_mul, add_zero]
  calc (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * a * ((Em k r)ᵀ * Em k r) := by
        simp only [Matrix.mul_assoc]
    _ = a := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
lemma mulVec_bvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) : (A *ᵥ bvec j) l = A l j := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `[bvec, Pi.single_apply]`.
-/
lemma bvec_apply {n : ℕ} (j l : Fin n) : bvec j l = if l = j then 1 else 0 := by
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Use extensionality with `l`. Rewrite using `[mulVec_bvec, bvec_apply]`. Use `a.isLt` as an intermediate fact. Use `l.isLt` as an intermediate fact. Unfold `Hpk`.

Simplify using `only [eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  ext l
  rw [mulVec_bvec, bvec_apply]
  have := a.isLt
  have := l.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use extensionality with `l`. Rewrite using `[mulVec_bvec, bvec_apply]`. Use `a.isLt` as an intermediate fact. Use `l.isLt` as an intermediate fact. Unfold `Hpk`.

Simplify using `only [eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext l
  rw [mulVec_bvec, bvec_apply]
  have := a.isLt
  have := l.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Distinguish the cases in `h : i.val < r`. Conclude with `⟨⟨i.val, h⟩, Or.inl rfl⟩`. Use `⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_cases (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) : ∃ a : Fin r, i = eI k r a ∨ i = esI k r a := by
  have := i.isLt
  by_cases h : i.val < r
  · exact ⟨⟨i.val, h⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [esI]
    omega

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `show ¬ (r ≤ a.val ∧ a.val ≤ r + k)`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_e (a : Fin r) : ¬ mid k r (eI k r a) := by
  have := a.isLt
  show ¬ (r ≤ a.val ∧ a.val ≤ r + k)
  omega

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k)`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_es (a : Fin r) : ¬ mid k r (esI k r a) := by
  have := a.isLt
  show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k)
  omega

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma fix_dual {g : Mat k r} (hg : g ∈ GV k r) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc gᴴ *ᵥ (Hpk k r *ᵥ f) = gᴴ *ᵥ (Hpk k r *ᵥ (g *ᵥ f)) := by rw [hf]
    _ = (gᴴ * Hpk k r * g) *ᵥ f := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Hpk k r *ᵥ f := by rw [hg']

/- English proof (translation)
Take `⟨a, rfl | rfl⟩` from `not_mid_cases i hi`. Rewrite using `[← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]`. Rewrite using `[← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]`.
-/
lemma uwb_col {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · rw [← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]
  · rw [← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]

/- English proof (translation)
Establish `key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0`. Introduce `j hj`. Establish `h` using `congrFun hj l`. Rewrite `h` using `[mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply]`. Establish `h2` using `congrArg star h`.

Rewrite `h2` using `[star_star]`. Rewrite using `[h2]`. Distinguish the cases in `e : l = j`. Rewrite using `[if_pos e, if_pos e.symm, star_one]`. Rewrite using `[if_neg e, if_neg (fun e' => e e'.symm), star_zero]`.

Take `⟨a, rfl | rfl⟩` from `not_mid_cases i hi`. Apply `key` to reduce the goal to its premises. Use `fix_dual hg.1 (hg.2 a).2` as an intermediate fact. Rewrite `this` using `[hpk_es]`. Then use the resulting hypothesis. Apply `key` to reduce the goal to its premises.

Use `fix_dual hg.1 (hg.2 a).1` as an intermediate fact. Rewrite `this` using `[hpk_e]`. Then use the resulting hypothesis.
-/
lemma uwb_row {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g i l = if i = l then 1 else 0 := by
  have key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0 := by
    intro j hj
    have h := congrFun hj l
    rw [mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply] at h
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : l = j
    · rw [if_pos e, if_pos e.symm, star_one]
    · rw [if_neg e, if_neg (fun e' => e e'.symm), star_zero]
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · apply key
    have := fix_dual hg.1 (hg.2 a).2
    rwa [hpk_es] at this
  · apply key
    have := fix_dual hg.1 (hg.2 a).1
    rwa [hpk_e] at this

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hj : mid k r j`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]`. Rewrite using `[emb_out_row _ i j hi, uwb_row hg i j hi]`.

Rewrite using `[emb_out_col _ i j hj, uwb_col hg j i hj]`.
-/
lemma uwb_eq_emb {g : Mat k r} (hg : g ∈ UWb k r) : g = embWb k r (g.submatrix (wI k r) (wI k r)) := by
  ext i j
  by_cases hj : mid k r j
  · by_cases hi : mid k r i
    · rw [emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]
    · rw [emb_out_row _ i j hi, uwb_row hg i j hi]
  · rw [emb_out_col _ i j hj, uwb_col hg j i hj]

/- English proof (translation)
Use extensionality with `l`. Rewrite using `[mulVec_bvec, bvec_apply, emb_out_col _ l i hi]`.
-/
lemma emb_fix (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    embWb k r a *ᵥ bvec i = bvec i := by
  ext l
  rw [mulVec_bvec, bvec_apply, emb_out_col _ l i hi]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `h` using `uwb_eq_emb hg`. Use `⟨_, ?_, h.symm⟩` and prove the remaining obligations. Rewrite using `[← emb_mem (r := r), ← h]`.

Conclude with `hg.1`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨(emb_mem a).mpr ha, fun b => ⟨emb_fix a _ (not_mid_e b), emb_fix a _ (not_mid_es b)⟩⟩`.
-/
lemma uwb_iff (g : Mat k r) : g ∈ UWb k r ↔ ∃ a, aᴴ * Hb k * a = Hb k ∧ embWb k r a = g := by
  constructor
  · intro hg
    have h := uwb_eq_emb hg
    refine ⟨_, ?_, h.symm⟩
    rw [← emb_mem (r := r), ← h]
    exact hg.1
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(emb_mem a).mpr ha, fun b => ⟨emb_fix a _ (not_mid_e b), emb_fix a _ (not_mid_es b)⟩⟩

def εb (k : ℕ) : Fin (k + 1) → Bool := fun j => decide (j ≠ Fin.last k)

/- English proof (translation)
Unfold `Jm Hb εb`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : j = Fin.last k <;> simp [h]`.
-/
lemma Jm_εb : Jm (εb k) = Hb k := by
  unfold Jm Hb εb
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]

/- English proof (translation)
Establish `: (fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) = fun x => (Em k r * Matrix.of x * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) : Mat k r)`. Use function extensionality and compare the values at `x`. Rewrite using `[emb_eq]`. Rewrite using `[this]`. Conclude with `(Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const).add continuous_const`.
-/
lemma emb_cont : Continuous fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
  have : (fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) =
      fun x => (Em k r * Matrix.of x * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) : Mat k r) := by
    funext x
    rw [emb_eq]
  rw [this]
  exact (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const).add
    continuous_const

/- English proof (translation)
Set `c' : Mt k r → (Fin (k + 1) → Fin (k + 1) → ℂ)` to `fun y => ((Em k r)ᵀ * Matrix.of y * Em k r : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)`. Establish `hc' : Continuous c'` using `Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const`. Establish `hli : Function.LeftInverse c' fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)`. Introduce `x`. Conclude with `emb_linv (Matrix.of x)`.

Conclude with `hli.isClosedEmbedding hc' emb_cont`.
-/
lemma emb_closedEmb :
    IsClosedEmbedding fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
  let c' : Mt k r → (Fin (k + 1) → Fin (k + 1) → ℂ) :=
    fun y => ((Em k r)ᵀ * Matrix.of y * Em k r : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  have hc' : Continuous c' :=
    Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const
  have hli : Function.LeftInverse c' fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
    intro x
    exact emb_linv (Matrix.of x)
  exact hli.isClosedEmbedding hc' emb_cont

/- English proof (translation)
Introduce `k r`. Establish `: (muG (εb k)).IsMulRightInvariant` using `⟨fun g => unimodular _ (εb k) g⟩`. Establish `hemb` using `uJEmb _ (εb k)`. Set `ι : UJ (εb k) → (Fin (k + 1) → Fin (k + 1) → ℂ)` to `fun g => ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)`. Establish `hι : IsClosedEmbedding ι` using `hemb.1`.

Establish `hιr : ∀ x : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, inUJ (εb k) x ↔ ∃ g, ι g = x` using `fun x => by`. Use `Set.ext_iff.mp hemb.2 x` as an intermediate fact. Conclude with `this.symm`. Use `⟨(muG (εb k)).map ((fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) ∘ ι), ?_⟩` and prove the remaining obligations. Apply `haar_push (muG (εb k)) (haar_ne_zero _) _ (emb_closedEmb.comp hι)` to reduce the goal to its premises.

Introduce `a b`. Conclude with `emb_mul _ _`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Apply `(uwb_iff _).mpr` to reduce the goal to its premises. Use `⟨Matrix.of (ι x), ?_, rfl⟩` and prove the remaining obligations. Use `(hιr (Matrix.of (ι x))).mpr ⟨x, rfl⟩` as an intermediate fact. Unfold `inUJ at this`. Rewrite `this` using `[Jm_εb]`. Then use the resulting hypothesis.

Introduce `hg`. Take `⟨a, ha, hag⟩` from `(uwb_iff _).mp hg`. Establish `h2 : inUJ (εb k) a`. Unfold `inUJ`. Rewrite using `[Jm_εb]` and apply the resulting hypothesis.

Take `⟨x, hx⟩` from `(hιr a).mp h2`. Use `⟨x, ?_⟩` and prove the remaining obligations. Use `show embWb k r (Matrix.of (ι x)) = g`. Rewrite using `[hx]`. Conclude with `hag`.
-/
theorem haarWb : HaarWbExists := by
  intro k r
  have : (muG (εb k)).IsMulRightInvariant := ⟨fun g => unimodular _ (εb k) g⟩
  have hemb := uJEmb _ (εb k)
  let ι : UJ (εb k) → (Fin (k + 1) → Fin (k + 1) → ℂ) :=
    fun g => ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  have hι : IsClosedEmbedding ι := hemb.1
  have hιr : ∀ x : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, inUJ (εb k) x ↔ ∃ g, ι g = x := fun x => by
    have := Set.ext_iff.mp hemb.2 x
    exact this.symm
  refine ⟨(muG (εb k)).map ((fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) ∘ ι), ?_⟩
  apply haar_push (muG (εb k)) (haar_ne_zero _) _ (emb_closedEmb.comp hι)
  · intro a b
    exact emb_mul _ _
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      apply (uwb_iff _).mpr
      refine ⟨Matrix.of (ι x), ?_, rfl⟩
      have := (hιr (Matrix.of (ι x))).mpr ⟨x, rfl⟩
      unfold inUJ at this
      rwa [Jm_εb] at this
    · intro hg
      obtain ⟨a, ha, hag⟩ := (uwb_iff _).mp hg
      have h2 : inUJ (εb k) a := by
        unfold inUJ
        rwa [Jm_εb]
      obtain ⟨x, hx⟩ := (hιr a).mp h2
      refine ⟨x, ?_⟩
      show embWb k r (Matrix.of (ι x)) = g
      rw [hx]
      exact hag

/- English proof (translation)
Unfold `Hb`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply, if_true]`. Establish `h : ∀ i : Fin k, (if i.castSucc = Fin.last k then (-1 : ℂ) else 1) = 1` using `fun i => if_neg (Fin.castSucc_lt_last i).ne`. Simplify using `only [h, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hb_form (v w : Fin (k + 1) → ℂ) :
    star w ⬝ᵥ (Hb k *ᵥ v) =
      (∑ i : Fin k, star (w i.castSucc) * v i.castSucc) - star (w (Fin.last k)) * v (Fin.last k) := by
  unfold Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply, if_true]
  have h : ∀ i : Fin k, (if i.castSucc = Fin.last k then (-1 : ℂ) else 1) = 1 := fun i =>
    if_neg (Fin.castSucc_lt_last i).ne
  simp only [h, one_mul]
  ring

/- English proof (translation)
Use `set X := ∑ i : Fin k, ‖u i.castSucc‖ ^ 2 with hX`. Use `set Y := ∑ i : Fin k, ‖z i.castSucc‖ ^ 2 with hY`. Use `set A := ‖u (Fin.last k)‖ with hA`. Use `set B := ‖z (Fin.last k)‖ with hB`. Establish `hA0 : 0 ≤ A` using `norm_nonneg _`.

Establish `hB0 : 0 ≤ B` using `norm_nonneg _`. Establish `hY0 : 0 ≤ Y` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `hX0 : 0 ≤ X` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `hBpos : 0 < B`. Break down `hB0.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Rewrite `hT` using `[← h]`. Evaluate the numerical expressions using `at hT`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy : √Y < B` using `(Real.sqrt_lt' hBpos).mpr hT`.

Establish `hy0 : 0 ≤ √Y` using `Real.sqrt_nonneg _`. Establish `hx : √X ≤ 1 + A`. Rewrite using `[Real.sqrt_le_iff]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities. Establish `hS : ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ √Y * √X`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`.

Use `_ ≤ √Y * √X := Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Establish `hBA : B * A ≤ τ + √Y * √X`. Establish `e : B * A = ‖star (z (Fin.last k)) * u (Fin.last k)‖` using `by rw [norm_mul, norm_star]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ + ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ := norm_sub_le _ _`. Use `_ ≤ τ + √Y * √X := by linarith`. Establish `hd : 0 < B - √Y` using `by linarith`.

Establish `hAle : A ≤ (τ + √Y) / (B - √Y)`. Rewrite using `[le_div_iff₀ hd]`. Establish `: √Y * √X ≤ √Y * (1 + A)` using `mul_le_mul_of_nonneg_left hx hy0`. Use the polynomial consequences of the given equalities and inequalities. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj : ‖u j.castSucc‖ ^ 2 ≤ X` using `Finset.single_le_sum (f := fun i : Fin k => ‖u i.castSucc‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)`. Establish `: ‖u j.castSucc‖ ≤ √X` using `Real.le_sqrt_of_sq_le hj`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma real_bound (u z : Fin (k + 1) → ℂ) (τ : ℝ)
    (h1 : (∑ i : Fin k, ‖u i.castSucc‖ ^ 2) - ‖u (Fin.last k)‖ ^ 2 ≤ 1)
    (h2 : ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ ≤ τ)
    (hT : (∑ i : Fin k, ‖z i.castSucc‖ ^ 2) < ‖z (Fin.last k)‖ ^ 2) (i : Fin (k + 1)) :
    ‖u i‖ ≤ 1 + (τ + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) := by
  set X := ∑ i : Fin k, ‖u i.castSucc‖ ^ 2 with hX
  set Y := ∑ i : Fin k, ‖z i.castSucc‖ ^ 2 with hY
  set A := ‖u (Fin.last k)‖ with hA
  set B := ‖z (Fin.last k)‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => by positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => by positivity
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hT; norm_num at hT; linarith
  have hy : √Y < B := (Real.sqrt_lt' hBpos).mpr hT
  have hy0 : 0 ≤ √Y := Real.sqrt_nonneg _
  have hx : √X ≤ 1 + A := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hS : ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ √Y * √X := by
    calc ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ ∑ i : Fin k, ‖star (z i.castSucc) * u i.castSucc‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin k, ‖z i.castSucc‖ * ‖u i.castSucc‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star]
      _ ≤ √Y * √X := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hBA : B * A ≤ τ + √Y * √X := by
    have e : B * A = ‖star (z (Fin.last k)) * u (Fin.last k)‖ := by rw [norm_mul, norm_star]
    rw [e]
    calc ‖star (z (Fin.last k)) * u (Fin.last k)‖
        = ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) -
            ((∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k))‖ := by
          congr 1; ring
      _ ≤ ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ +
            ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ :=
          norm_sub_le _ _
      _ ≤ τ + √Y * √X := by linarith
  have hd : 0 < B - √Y := by linarith
  have hAle : A ≤ (τ + √Y) / (B - √Y) := by
    rw [le_div_iff₀ hd]
    have : √Y * √X ≤ √Y * (1 + A) := mul_le_mul_of_nonneg_left hx hy0
    nlinarith
  refine Fin.lastCases ?_ (fun j => ?_) i
  · linarith
  · have hj : ‖u j.castSucc‖ ^ 2 ≤ X :=
      Finset.single_le_sum (f := fun i : Fin k => ‖u i.castSucc‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
    have : ‖u j.castSucc‖ ≤ √X := Real.le_sqrt_of_sq_le hj
    linarith

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.
-/
lemma normsq_eq (x : ℂ) : star x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/- English proof (translation)
Rewrite using `[hb_form]`. Simplify using `only [normsq_eq]`. Rewrite using `[← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]`.
-/
lemma hb_self_re (v : Fin (k + 1) → ℂ) :
    (star v ⬝ᵥ (Hb k *ᵥ v)).re = (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) - ‖v (Fin.last k)‖ ^ 2 := by
  rw [hb_form]
  simp only [normsq_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]

/- English proof (translation)
Rewrite `hT` using `[hb_self_re]`. Use `⟨1 + ((∑ j, ‖z j‖) + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)), fun μ hμ hz i j => ?_⟩` and prove the remaining obligations. Establish `hu : ∀ l, (μ *ᵥ Pi.single j 1) l = μ l j` using `fun l => by`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hHb : ∀ l, (Hb k *ᵥ Pi.single j 1) l = Hb k l j` using `fun l => by`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `key : ∀ w : Fin (k + 1) → ℂ, star (μ *ᵥ w) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1)) = star w ⬝ᵥ (Hb k *ᵥ Pi.single j 1)`. Introduce `w`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]`. Establish `hHbn : ∀ l, ‖Hb k l j‖ ≤ 1`.

Introduce `l`. Unfold `Hb`. Rewrite using `[Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `a1` using `key (Pi.single j 1)`.

Establish `a2` using `key z`. Rewrite `a2` using `[hz]`. Establish `b1 : (star (μ *ᵥ Pi.single j 1) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))).re ≤ 1`. Rewrite using `[a1]`. Establish `: star (Pi.single j 1 : Fin (k + 1) → ℂ) ⬝ᵥ (Hb k *ᵥ Pi.single j 1) = Hb k j j`.

Rewrite using `[← hHb j]`. Simplify using `[dotProduct, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `(Complex.re_le_norm _).trans (hHbn j)`. Rewrite `b1` using `[hb_self_re]`.

Establish `b2 : ‖star z ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))‖ ≤ ∑ j, ‖z j‖`. Rewrite using `[a2, dotProduct]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[hHb, norm_mul, Pi.star_apply, norm_star]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hHbn l)`.

Rewrite `b2` using `[hb_form]`. Use `real_bound (μ *ᵥ Pi.single j 1) z _ b1 b2 (by linarith) i` as an intermediate fact. Rewrite `this` using `[hu]`. Then use the resulting hypothesis.
-/
lemma col_bound (z : Fin (k + 1) → ℂ) (hT : (star z ⬝ᵥ (Hb k *ᵥ z)).re < 0) :
    ∃ R : ℝ, ∀ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k → μ *ᵥ z = z → ∀ i j, ‖μ i j‖ ≤ R := by
  rw [hb_self_re] at hT
  refine ⟨1 + ((∑ j, ‖z j‖) + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) /
    (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)), fun μ hμ hz i j => ?_⟩
  have hu : ∀ l, (μ *ᵥ Pi.single j 1) l = μ l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hHb : ∀ l, (Hb k *ᵥ Pi.single j 1) l = Hb k l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ w : Fin (k + 1) → ℂ, star (μ *ᵥ w) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1)) = star w ⬝ᵥ (Hb k *ᵥ Pi.single j 1) := by
    intro w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]
  have hHbn : ∀ l, ‖Hb k l j‖ ≤ 1 := by
    intro l
    unfold Hb
    rw [Matrix.diagonal_apply]
    split_ifs <;> simp
  have a1 := key (Pi.single j 1)
  have a2 := key z
  rw [hz] at a2
  have b1 : (star (μ *ᵥ Pi.single j 1) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))).re ≤ 1 := by
    rw [a1]
    have : star (Pi.single j 1 : Fin (k + 1) → ℂ) ⬝ᵥ (Hb k *ᵥ Pi.single j 1) = Hb k j j := by
      rw [← hHb j]
      simp [dotProduct, Pi.single_apply]
    rw [this]
    exact (Complex.re_le_norm _).trans (hHbn j)
  rw [hb_self_re] at b1
  have b2 : ‖star z ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))‖ ≤ ∑ j, ‖z j‖ := by
    rw [a2, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [hHb, norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hHbn l)
  rw [hb_form] at b2
  have := real_bound (μ *ᵥ Pi.single j 1) z _ b1 b2 (by linarith) i
  rwa [hu] at this

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (wI k r m)]`. Rewrite using `[Matrix.transpose_apply, Em, if_pos rfl, one_mul]`. Introduce `b _ hb`. Rewrite using `[Matrix.transpose_apply, Em, if_neg hb, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma EmT_mulVec (z : Fin (2 * r + k + 1) → ℂ) (m : Fin (k + 1)) : ((Em k r)ᵀ *ᵥ z) m = z (wI k r m) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (wI k r m)]
  · rw [Matrix.transpose_apply, Em, if_pos rfl, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (midx hi)]`. Rewrite using `[Em, if_pos (wI_midx hi).symm, one_mul, EmT_mulVec, wI_midx]`. Introduce `b _ hb`.

Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hi, h]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hz i (by omega)]`. Rewrite using `[Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`. Conclude with `hi (h ▸ mid_wI b)`.
-/
lemma Em_EmT_mulVec (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : Em k r *ᵥ ((Em k r)ᵀ *ᵥ z) = z := by
  ext i
  by_cases hi : mid k r i
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (midx hi)]
    · rw [Em, if_pos (wI_midx hi).symm, one_mul, EmT_mulVec, wI_midx]
    · intro b _ hb
      rw [Em, if_neg, zero_mul]
      intro h
      apply hb
      apply wI_inj (r := r)
      rw [wI_midx hi, h]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hz i (by omega)]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro b _
    rw [Em, if_neg, zero_mul]
    intro h
    exact hi (h ▸ mid_wI b)

/- English proof (translation)
Establish `key : ∀ w : Fin (k + 1) → ℂ, herm (Hpk k r) (Em k r *ᵥ w) (Em k r *ᵥ w) = star w ⬝ᵥ (Hb k *ᵥ w)`. Introduce `w`. Unfold `herm`. Rewrite using `[Matrix.mulVec_mulVec, Hpk_Em, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Em_conjT, EmT_Em, Matrix.one_mulVec]`. Rewrite using `[← key, Em_EmT_mulVec z hz]`.
-/
lemma herm_wb (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = star ((Em k r)ᵀ *ᵥ z) ⬝ᵥ (Hb k *ᵥ ((Em k r)ᵀ *ᵥ z)) := by
  have key : ∀ w : Fin (k + 1) → ℂ, herm (Hpk k r) (Em k r *ᵥ w) (Em k r *ᵥ w) = star w ⬝ᵥ (Hb k *ᵥ w) := by
    intro w
    unfold herm
    rw [Matrix.mulVec_mulVec, Hpk_Em, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Em_conjT, EmT_Em, Matrix.one_mulVec]
  rw [← key, Em_EmT_mulVec z hz]

/- English proof (translation)
Introduce `k r z hz hT`. Use `set zb := (Em k r)ᵀ *ᵥ z with hzb`. Establish `hT' : (star zb ⬝ᵥ (Hb k *ᵥ zb)).re < 0`. Rewrite using `[hzb, ← herm_wb z hz]`. Unfold `Tz at hT`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨R, hR⟩` from `col_bound zb hT'`. Establish `hK0 : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) => Set.pi Set.univ fun _ : Fin (k + 1) => Metric.closedBall (0 : ℂ) R)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hK` using `hK0.image (emb_cont (k := k) (r := r))`. Use `IsCompact.of_isClosed_subset hK (closedW k r z).closed ?_` and prove the remaining obligations.

Introduce `g hg`. Take `⟨a, ha, hag⟩` from `(uwb_iff g).mp ⟨hg.1, hg.2.1⟩`. Establish `hfix : a *ᵥ zb = zb`. Establish `e : a = (Em k r)ᵀ * g * Em k r` using `by rw [← hag, emb_linv]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzb, Em_EmT_mulVec z hz, hg.2.2]`.

Use `⟨a, ?_, hag⟩` and prove the remaining obligations. Introduce `i _ j _`. Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `hR a ha hfix i j`.
-/
theorem compactW : CompactW := by
  intro k r z hz hT
  set zb := (Em k r)ᵀ *ᵥ z with hzb
  have hT' : (star zb ⬝ᵥ (Hb k *ᵥ zb)).re < 0 := by
    rw [hzb, ← herm_wb z hz]
    unfold Tz at hT
    linarith
  obtain ⟨R, hR⟩ := col_bound zb hT'
  have hK0 : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) => Set.pi Set.univ fun _ : Fin (k + 1) =>
      Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK := hK0.image (emb_cont (k := k) (r := r))
  refine IsCompact.of_isClosed_subset hK (closedW k r z).closed ?_
  intro g hg
  obtain ⟨a, ha, hag⟩ := (uwb_iff g).mp ⟨hg.1, hg.2.1⟩
  have hfix : a *ᵥ zb = zb := by
    have e : a = (Em k r)ᵀ * g * Em k r := by rw [← hag, emb_linv]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzb, Em_EmT_mulVec z hz, hg.2.2]
  refine ⟨a, ?_, hag⟩
  intro i _ j _
  rw [mem_closedBall_zero_iff]
  exact hR a ha hfix i j

/- English proof (translation)
Introduce `k r z hz hT` and use `compactHaar k r _ (closedW k r z) (compactW k r z hz hT)`.
-/
theorem haarW : HaarWExists := fun k r z hz hT => compactHaar k r _ (closedW k r z) (compactW k r z hz hT)

end Formalism.FourierDecayAlt.P.B2x3

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `B2x3.closedW`.
-/
theorem weyl_subgroup_closed : Formalism.FourierDecayAlt.B2.ClosedW := B2x3.closedW

/- English proof (translation)
The claim follows from `B2x3.closedWb`.
-/
theorem opposite_weyl_subgroup_closed : Formalism.FourierDecayAlt.B2.ClosedWb := B2x3.closedWb

/- English proof (translation)
The claim follows from `B2x3.compactW`.
-/
theorem weyl_subgroup_compact : Formalism.FourierDecayAlt.B2.CompactW := B2x3.compactW

/- English proof (translation)
The claim follows from `B2x3.haarG`.
-/
theorem unitary_group_haar_exists : Formalism.FourierDecayAlt.B2.HaarGExists := B2x3.haarG

/- English proof (translation)
The claim follows from `B2x3.haarWb`.
-/
theorem opposite_weyl_haar_exists : Formalism.FourierDecayAlt.B2.HaarWbExists := B2x3.haarWb

/- English proof (translation)
The claim follows from `B2x3.haarW`.
-/
theorem weyl_haar_exists : Formalism.FourierDecayAlt.B2.HaarWExists := B2x3.haarW

end Formalism.FourierDecayAlt.P
