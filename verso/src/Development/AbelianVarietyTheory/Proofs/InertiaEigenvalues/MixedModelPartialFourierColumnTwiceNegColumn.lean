import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PartialInv

def intLat (F : Type) [NormedField F] [IsUltrametricDist F] (r : ℕ) : AddSubgroup (Fin r → F) where
  carrier := Set.univ.pi fun _ => Metric.closedBall (0 : F) 1
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro a b ha hb i _
    have h1 := ha i trivial
    have h2 := hb i trivial
    simp only [mem_closedBall_zero_iff] at h1 h2 ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  neg_mem' := by
    intro a ha i _
    have h1 := ha i trivial
    simpa using h1

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _`. Simplify using `[Set.mem_pi]`.
-/
theorem mem_intLat {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by
  change x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _
  simp [Set.mem_pi]

/- English proof (translation)
Establish `hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F)` using `by fun_prop`. Use `⟨hf.1.comp_continuous hc, ?_⟩` and prove the remaining obligations. Establish `he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F)`. Use `Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc` and prove the remaining obligations. Conclude with `hf.2.comp_isClosedEmbedding he`.
-/
theorem isTest_slice {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by
  have hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by fun_prop
  refine ⟨hf.1.comp_continuous hc, ?_⟩
  have he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc
  exact hf.2.comp_isClosedEmbedding he

/- English proof (translation)
Use `letI := M.mF`. Use `haveI := M.bF`. Use `haveI := M.haarF`. Use `haveI : IsUltrametricDist F := Unram.ultraF E`. Use `haveI : LocallyCompactSpace F := Unram.lcF E`.

Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Establish `hcond` using `((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1`. Establish `hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F))` using `⟨fun x y => by simp [dotProduct_comm]⟩`. Establish `hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F))`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Use extensionality with `i`. Simplify using `using hx (Pi.single i 1)`. Introduce `x hx`. Use extensionality with `i`.

Simplify using `using hx (Pi.single i 1)`. Establish `hopen : IsOpen (intLat F r : Set (Fin r → F))` using `isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero`. Establish `hcpt : IsCompact (intLat F r : Set (Fin r → F))` using `isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1`. Express the relevant statement in the definitionally equal form `(Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1`.

Rewrite using `[Measure.pi_pi]`. Simplify using `[M.volF]`. Establish `hdual : {y : Fin r → F | ∀ x ∈ intLat F r, ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F))`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `(hcond (y i)).1 fun e he => ?_` and prove the remaining obligations. Use `h (Pi.single i e) (fun j => by` as an intermediate fact. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `using he`. Simplify using `[hj])`. Simplify using `using this`. Introduce `h x hx`.

Use `hψ.1 _ ?_` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hx i) (norm_nonneg _) (h i)`. Establish `key` using `((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1`.

Rewrite `key` using `[hdual, hvol]`. Conclude with `key.2 (mul_one 1)`.
-/
theorem selfDual_pi (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  have hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) :=
    ⟨fun x y => by simp [dotProduct_comm]⟩
  have hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) := by
    constructor
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
  have hopen : IsOpen (intLat F r : Set (Fin r → F)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hcpt : IsCompact (intLat F r : Set (Fin r → F)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1 := by
    change (Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1
    rw [Measure.pi_pi]
    simp [M.volF]
  have hdual : {y : Fin r → F | ∀ x ∈ intLat F r,
      ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]
    constructor
    · intro h i
      refine (hcond (y i)).1 fun e he => ?_
      have := h (Pi.single i e) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using he
        · simp [hj])
      simpa using this
    · intro h x hx
      refine hψ.1 _ ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (h i)
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd
    (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1
  rw [hdual, hvol] at key
  exact key.2 (mul_one 1)

/- English proof (translation)
Use function extensionality and compare the values at `Y`. Conclude with `(selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1`.
-/
theorem ptrB_ptrB (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (f : Gl r F → ℂ) (hf : IsTest f) : WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  funext Y
  exact (selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1

end GlobalTheory.JR.PartialInv
