import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLHaarAdd

/- English proof (translation)
Use `⟨fun L hL => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hL.elim_finite_subcover (fun x : G => (fun y => -x + y) ⁻¹' K) (fun x => hKo.preimage (by fun_prop)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using h0⟩)`. Establish `hb : ∀ x : G, dx ((fun y => -x + y) ⁻¹' K) = 1` using `fun x => by`. Rewrite using `[measure_preimage_add dx (-x) K, h1]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hb]`. Simplify using `[ENNReal.mul_lt_top]`.
-/
theorem finite_on_compacts {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hKo : IsOpen K) (h0 : (0 : G) ∈ K)
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx K = 1) : IsFiniteMeasureOnCompacts dx := by
  refine ⟨fun L hL => ?_⟩
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun x : G => (fun y => -x + y) ⁻¹' K)
    (fun x => hKo.preimage (by fun_prop))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using h0⟩)
  have hb : ∀ x : G, dx ((fun y => -x + y) ⁻¹' K) = 1 := fun x => by
    rw [measure_preimage_add dx (-x) K, h1]
  calc dx L ≤ dx (⋃ x ∈ t, (fun y => -x + y) ⁻¹' K) := measure_mono ht
    _ ≤ ∑ x ∈ t, dx ((fun y => -x + y) ⁻¹' K) := measure_biUnion_finset_le t _
    _ < ⊤ := by
      simp only [hb]
      simp [ENNReal.mul_lt_top]

/- English proof (translation)
Use `haveI := finite_on_compacts hKo h0 dx h1`. Take `⟨c, h⟩ : ∃ c : NNReal, dx = c • Measure.addHaarMeasure K₀` from `⟨_, Measure.isAddLeftInvariant_eq_smul dx (Measure.addHaarMeasure K₀)⟩`. Establish `h2 : (c • Measure.addHaarMeasure K₀) (K₀ : Set G) = 1` using `by rw [← h]; exact h1`. Establish `hc : c = 1`. Rewrite `h2` using `[Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one]`.

Conclude with `h2` after adjusting the coercions. Rewrite `h` using `[hc, one_smul]`. Conclude with `h`.
-/
theorem eq_addHaar {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (K₀ : TopologicalSpace.PositiveCompacts G) (hKo : IsOpen (K₀ : Set G)) (h0 : (0 : G) ∈ (K₀ : Set G))
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx (K₀ : Set G) = 1) :
    dx = Measure.addHaarMeasure K₀ := by
  haveI := finite_on_compacts hKo h0 dx h1
  obtain ⟨c, h⟩ : ∃ c : NNReal, dx = c • Measure.addHaarMeasure K₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul dx (Measure.addHaarMeasure K₀)⟩
  have h2 : (c • Measure.addHaarMeasure K₀) (K₀ : Set G) = 1 := by rw [← h]; exact h1
  have hc : c = 1 := by
    rw [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
    exact_mod_cast h2
  rw [hc, one_smul] at h
  exact h

/- English proof (translation)
Introduce `F _ _ _ _ _ _ O ϖ nrm q hLF n m`. Take `⟨hOo, hOc, hsc, -, -, -⟩` from `GlobalTheory.T.localField_topology_norm_balls hLF`. Use `haveI : IsTopologicalRing F := inferInstance`. Use `haveI : T2Space F := by`. Set `` to `IsTopologicalAddGroup.rightUniformSpace F`.

Use `haveI := isUniformAddGroup_of_addCommGroup (G := F)`. Use `infer_instance`. Establish `hset : intMat O n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin m => (O : Set F)))`. Use extensionality with `y`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`.

Establish `hopen : IsOpen (intMat O n m)`. Rewrite using `[hset]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hOo`. Establish `hcomp : IsCompact (intMat O n m)`. Rewrite using `[hset]`.

Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc`. Establish `h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ intMat O n m` using `fun _ _ => O.zero_mem`. Use `haveI hB : BorelSpace (Matrix (Fin n) (Fin m) F) := inferInstanceAs (BorelSpace (Fin n → Fin m → F))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) F) := inferInstanceAs (SecondCountableTopology (Fin n → Fin m → F))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) F) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin m → F))`.

Set `K₀ : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) F)` to `⟨⟨intMat O n m, hcomp⟩, ⟨0, mem_interior_iff_mem_nhds.2 (hopen.mem_nhds h0)⟩⟩`. Establish `key : ∀ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx = Measure.addHaarMeasure K₀` using `fun dx _ h => eq_addHaar K₀ hopen h0 dx h`. Use `⟨hB, hopen, hcomp, ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `dx hi h`. Rewrite using `[key dx hi h]`.

Use `infer_instance`. Introduce `dx hi h dy hj h'`. Rewrite using `[key dx hi h, key dy hj h']`.
-/
theorem haarAdd_intMat : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, BorelSpace (Matrix (Fin n) (Fin m) F) ∧ IsOpen (intMat O n m) ∧ IsCompact (intMat O n m) ∧ (∃ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant ∧ dx (intMat O n m) = 1) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx.IsAddHaarMeasure) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → ∀ (dy : Measure (Matrix (Fin n) (Fin m) F)), dy.IsAddLeftInvariant → dy (intMat O n m) = 1 → dx = dy) := by
  intro F _ _ _ _ _ _ O ϖ nrm q hLF n m
  obtain ⟨hOo, hOc, hsc, -, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls hLF
  haveI : IsTopologicalRing F := inferInstance
  haveI : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hset : intMat O n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin m => (O : Set F))) := by
    ext y; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hopen : IsOpen (intMat O n m) := by
    rw [hset]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hcomp : IsCompact (intMat O n m) := by
    rw [hset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ intMat O n m := fun _ _ => O.zero_mem
  haveI hB : BorelSpace (Matrix (Fin n) (Fin m) F) :=
    inferInstanceAs (BorelSpace (Fin n → Fin m → F))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin m → F))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) F) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin m → F))
  let K₀ : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) F) :=
    ⟨⟨intMat O n m, hcomp⟩, ⟨0, mem_interior_iff_mem_nhds.2 (hopen.mem_nhds h0)⟩⟩
  have key : ∀ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 →
      dx = Measure.addHaarMeasure K₀ := fun dx _ h => eq_addHaar K₀ hopen h0 dx h
  refine ⟨hB, hopen, hcomp, ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩, ?_, ?_⟩
  · intro dx hi h
    rw [key dx hi h]
    infer_instance
  · intro dx hi h dy hj h'
    rw [key dx hi h, key dy hj h']

end GlobalTheory.CompanionTheory.QLHaarAdd
