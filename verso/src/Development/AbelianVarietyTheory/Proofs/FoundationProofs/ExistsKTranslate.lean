import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattnerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMemberStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecondStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCentralCircleDistinctGradedEigenStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGKStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGKStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCoverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEquivariantTensorMapOfCyclicCommutingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantInnerFormsProportionalWeightLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRangeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInConeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockIntertwinerCommutesUnitaryAndExtendsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestKTypeOfIrreducibleGeneratedModuleStatement

noncomputable section

namespace GlobalTheory.HarmModule

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory GlobalTheory.FockTensor
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

section Gen

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}

/- English proof (translation)
The claim follows from `sInf_le ⟨h, hN⟩`.
-/
theorem genSub_le {S : Set V} {N : Submodule ℂ V} (h : S ⊆ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) :
    genSub act S ≤ N := sInf_le ⟨h, hN⟩

/- English proof (translation)
Introduce `_ hx` and use `Submodule.mem_sInf.2 fun _ hN => hN.1 hx`.
-/
theorem subset_genSub (S : Set V) : S ⊆ genSub act S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.1 hx

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)`.
-/
theorem genSub_stable (S : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act S) :
    act Z y ∈ genSub act S :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)

/- English proof (translation)
Rewrite using `[Matrix.matrix_eq_sum_single Z]`. Simplify using `only [map_sum, LinearMap.sum_apply]`. Use `N.sum_mem fun a _ => N.sum_mem fun b _ => ?_` and prove the remaining obligations. Establish `: Matrix.single a b (Z a b) = Z a b • Eab a b`. Rewrite using `[Eab, Matrix.smul_single, smul_eq_mul, mul_one]`.

Rewrite using `[this, map_smul, LinearMap.smul_apply]`. Conclude with `N.smul_mem _ (h a b x hx)`.
-/
theorem stable_of_units {N : Submodule ℂ V} (h : ∀ a b, ∀ x ∈ N, act (Eab a b) x ∈ N) (Z : Mat p q)
    (x : V) (hx : x ∈ N) : act Z x ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : Matrix.single a b (Z a b) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b x hx)

/- English proof (translation)
Introduce `_ hZ x hx` and use `GlobalTheory.TensorHW.kc_ind act N x (fun a b hab => h a b hab x hx) hZ`.
-/
theorem kStable_of_units {N : Submodule ℂ V}
    (h : ∀ a b, sameBlock a b → ∀ x ∈ N, act (Eab a b) x ∈ N) : KStable act N :=
  fun _ hZ x hx => GlobalTheory.TensorHW.kc_ind act N x (fun a b hab => h a b hab x hx) hZ

/- English proof (translation)
Assemble the required witnesses or components as `⟨sameBlock_self, by rintro (a | a) (b | b) h <;> simp_all [sameBlock], by rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]⟩`.
-/
theorem equiv_sameBlock : Equivalence (sameBlock : Ix p q → Ix p q → Prop) :=
  ⟨sameBlock_self, by rintro (a | a) (b | b) h <;> simp_all [sameBlock],
    by rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]⟩

end Gen

variable {p q : ℕ}

/- English proof (translation)
Establish `eT : Equivalence (fun _ _ : Ix p q => True)` using `⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩`. Establish `htop : ∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, True → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → ⊤ ≤ U'` using `fun U' h1 h2 => hgen ▸ genSub_le (by simpa using h1) (stable_of_units fun a b => h2 a b trivial)`. Take `⟨U, hU1, hU2, -, hU4, -⟩` from `GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ eT r hr μ v hv fun a b _ h => hup a b h`. Establish `hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v` using `fun x hx => hU4 x (htop U hU1 hU2 trivial) hx`. Use `⟨⟨nontrivial_of_ne v 0 hv0, fun N hN => GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ eT μ v ⊤ hv htop (fun x _ hx => hline x hx) N le_top fun a b _ => hN _⟩, hline, ?_⟩` and prove the remaining obligations.

Take `⟨W, hW1, hW2, hW3, -, -⟩` from `GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ equiv_sameBlock r hr μ v hv fun a b _ h => hup a b h`. Establish `hmin : ∀ W' : Submodule ℂ M.V, v ∈ W' → KStable M.act W' → W ≤ W'` using `fun W' h1 h2 => hW3 W' h1 fun a b hab _ => h2 _ (isKC_Eab (equiv_sameBlock.symm hab))`. Take `⟨W₀, hf, h0, hs⟩` from `M.kfin v`. Use `⟨W, hW1, Submodule.finiteDimensional_of_le (hmin W₀ h0 hs), kStable_of_units hW2, fun N hN hN' => ?_, hmin⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ equiv_sameBlock μ v W hv (fun U' h1 h2 => hmin U' h1 (kStable_of_units h2)) (fun x _ hx => hline x hx) N hN fun a b hab => hN' _ (isKC_Eab hab)`.
-/
theorem cyclic (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : Function.Injective E)
    (hadj : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y)))
    (r : Ix p q → ℕ) (hr : Function.Injective r) (μ : Ix p q → ℚ) (v : M.V) (hv0 : v ≠ 0)
    (hv : v ∈ wtSub M.act μ) (hup : ∀ a b, r a < r b → M.act (Eab a b) v = 0)
    (hgen : genSub M.act {v} = ⊤) :
    IrrGK M ∧ (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) ∧
      ∃ W : Submodule ℂ M.V, v ∈ W ∧ FiniteDimensional ℂ W ∧ KStable M.act W ∧
        (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) ∧
        ∀ W' : Submodule ℂ M.V, v ∈ W' → KStable M.act W' → W ≤ W' := by
  have eT : Equivalence (fun _ _ : Ix p q => True) := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  have htop : ∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, True → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → ⊤ ≤ U' :=
    fun U' h1 h2 => hgen ▸ genSub_le (by simpa using h1) (stable_of_units fun a b => h2 a b trivial)
  obtain ⟨U, hU1, hU2, -, hU4, -⟩ := GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ eT r hr μ v hv fun a b _ h => hup a b h
  have hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v := fun x hx => hU4 x (htop U hU1 hU2 trivial) hx
  refine ⟨⟨nontrivial_of_ne v 0 hv0, fun N hN => GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ eT μ v ⊤ hv htop
    (fun x _ hx => hline x hx) N le_top fun a b _ => hN _⟩, hline, ?_⟩
  obtain ⟨W, hW1, hW2, hW3, -, -⟩ := GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ equiv_sameBlock r hr μ v hv
    fun a b _ h => hup a b h
  have hmin : ∀ W' : Submodule ℂ M.V, v ∈ W' → KStable M.act W' → W ≤ W' := fun W' h1 h2 =>
    hW3 W' h1 fun a b hab _ => h2 _ (isKC_Eab (equiv_sameBlock.symm hab))
  obtain ⟨W₀, hf, h0, hs⟩ := M.kfin v
  refine ⟨W, hW1, Submodule.finiteDimensional_of_le (hmin W₀ h0 hs), kStable_of_units hW2, fun N hN hN' => ?_, hmin⟩
  exact GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ equiv_sameBlock μ v W hv
    (fun U' h1 h2 => hmin U' h1 (kStable_of_units h2)) (fun x _ hx => hline x hx) N hN
    fun a b hab => hN' _ (isKC_Eab hab)

/- English proof (translation)
Take `⟨M, i, h1, h2, h3⟩` from `GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable p q P (genSub P.act {Δ}) (genSub_stable _)`. Establish `hΔ : Δ ∈ LinearMap.range i` using `h2 ▸ subset_genSub _ rfl`. Take `⟨v, hv⟩` from `hΔ`. Use `⟨M, i, v, h1, hv, h3, eq_top_iff.2 fun x _ => ?_⟩` and prove the remaining obligations. Establish `hle : genSub P.act {Δ} ≤ (genSub M.act {v}).map i`.

Use `genSub_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `⟨v, subset_genSub _ rfl, hv⟩`. Introduce and unpack `Z _ ⟨y, hy, rfl⟩`. Conclude with `⟨_, genSub_stable _ Z y hy, h3 Z y⟩`.

Take `⟨y, hy, hxy⟩` from `hle (h2 ▸ LinearMap.mem_range_self i x)`. Conclude with `h1 hxy ▸ hy`.
-/
theorem exists_cyclic_sub (P : GKMod p q) (Δ : P.V) : ∃ (M : GKMod p q) (i : M.V →ₗ[ℂ] P.V) (v : M.V),
    Function.Injective i ∧ i v = Δ ∧ (∀ Z x, i (M.act Z x) = P.act Z (i x)) ∧ genSub M.act {v} = ⊤ := by
  obtain ⟨M, i, h1, h2, h3⟩ := GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable p q P (genSub P.act {Δ}) (genSub_stable _)
  have hΔ : Δ ∈ LinearMap.range i := h2 ▸ subset_genSub _ rfl
  obtain ⟨v, hv⟩ := hΔ
  refine ⟨M, i, v, h1, hv, h3, eq_top_iff.2 fun x _ => ?_⟩
  have hle : genSub P.act {Δ} ≤ (genSub M.act {v}).map i := by
    refine genSub_le ?_ ?_
    · rintro _ rfl
      exact ⟨v, subset_genSub _ rfl, hv⟩
    · rintro Z _ ⟨y, hy, rfl⟩
      exact ⟨_, genSub_stable _ Z y hy, h3 Z y⟩
  obtain ⟨y, hy, hxy⟩ := hle (h2 ▸ LinearMap.mem_range_self i x)
  exact h1 hxy ▸ hy

/- English proof (translation)
Take `⟨σ, j, J, hd, hJ, hG, hD⟩` from `GlobalTheory.T.exists_subrep_closure_analytic_vectors p q T (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 πU M.V M.act E hder hbd`. Establish `hj : Function.Injective j` using `fun x y h => hE (by rw [← hJ, ← hJ, h])`. Take `⟨k, hk, lam, hl, hlam⟩` from `GlobalTheory.T.exists_central_circle_distinct_graded_eigen p q T σ M j hD N c heig`. Conclude with `⟨σ, j, J, GlobalTheory.T.irreducible_completion_of_graded_irreducible_gK p q T σ M j hj hd hD hirr N k lam hN htop hk hl hlam, GlobalTheory.T.isHCModule_of_graded_dense_gK p q hpq T σ M j hj hd hD N k lam hN htop hk hl hlam, hd, hJ, hG⟩`.
-/
theorem globalize (hpq : 1 ≤ p + q) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (E : M.V →ₗ[ℂ] πU.H)
    (hE : Function.Injective E)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (M.act Y x)) 0)
    (hbd : ∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((M.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (hirr : IrrGK M) (N : ℕ → Submodule ℂ M.V) (c : ℚ) (hN : ∀ m, FiniteDimensional ℂ (N m))
    (htop : (⨆ m, N m) = ⊤)
    (heig : ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) :
    ∃ (σ : URep T) (j : M.V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), IrrU σ ∧ IsHCMod σ M j ∧
      Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ ∀ g y, J (σ.π g y) = πU.π g (J y) := by
  obtain ⟨σ, j, J, hd, hJ, hG, hD⟩ := GlobalTheory.T.exists_subrep_closure_analytic_vectors p q T (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 πU M.V M.act E hder hbd
  have hj : Function.Injective j := fun x y h => hE (by rw [← hJ, ← hJ, h])
  obtain ⟨k, hk, lam, hl, hlam⟩ := GlobalTheory.T.exists_central_circle_distinct_graded_eigen p q T σ M j hD N c heig
  exact ⟨σ, j, J, GlobalTheory.T.irreducible_completion_of_graded_irreducible_gK p q T σ M j hj hd hD hirr N k lam hN htop hk hl hlam,
    GlobalTheory.T.isHCModule_of_graded_dense_gK p q hpq T σ M j hj hd hD N k lam hN htop hk hl hlam, hd, hJ, hG⟩

/- English proof (translation)
Use `haveI : T2Space T.G := T.emb.t2Space`. Use `haveI := (GlobalTheory.HolDS.haar_unimodular p q T).1`. Take `⟨h1, d, hd, h2⟩` from `GlobalTheory.Published.schurOrthogonalitySquareIntegrable' T.G T.haar σ.H σ.π σ.isom σ.cont hσ.2 ⟨v, v, hv, hv, h⟩`. Use `⟨d, hd, fun x y => ⟨(memLp_two_iff_integrable_sq_norm (h1 x y).1).1 (h1 x y), ?_⟩⟩` and prove the remaining obligations. Establish `h3` using `(h2 x y x y).2`.

Establish `e : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [e] at h3`. Rewrite `h3` using `[integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem exists_fdeg (T : GrpData p q) (σ : URep T) (hσ : IrrU σ) (v : σ.H) (hv : v ≠ 0)
    (h : MemLp (fun g => inner ℂ v (σ.π g v)) 2 T.haar) :
    ∃ d : ℝ, 0 < d ∧ ∀ x y : σ.H, Integrable (fun g => ‖inner ℂ y (σ.π g x)‖ ^ 2) T.haar ∧
      ∫ g, ‖inner ℂ y (σ.π g x)‖ ^ 2 ∂T.haar = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  haveI : T2Space T.G := T.emb.t2Space
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).1
  obtain ⟨h1, d, hd, h2⟩ := GlobalTheory.Published.schurOrthogonalitySquareIntegrable' T.G T.haar σ.H σ.π σ.isom σ.cont
    hσ.2 ⟨v, v, hv, hv, h⟩
  refine ⟨d, hd, fun x y => ⟨(memLp_two_iff_integrable_sq_norm (h1 x y).1).1 (h1 x y), ?_⟩⟩
  have h3 := (h2 x y x y).2
  have e : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e] at h3
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  apply Complex.ofReal_injective
  rw [h3]
  simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]`.
-/
theorem pow_intw {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (i : V →ₗ[ℂ] V')
    (a : Module.End ℂ V) (b : Module.End ℂ V') (h : ∀ x, i (a x) = b (i x)) (k : ℕ) (x : V) :
    i ((a ^ k) x) = (b ^ k) (i x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

section Fock

variable {r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

@[reducible] def repFst (F : FockData T0 T1 T2) : URep T1 where
  H := F.H
  π := F.π.comp (MonoidHom.inl _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).1.comp (continuous_id.prodMk continuous_const))

@[reducible] def repSnd (F : FockData T0 T1 T2) : URep T2 where
  H := F.H
  π := F.π.comp (MonoidHom.inr _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).1.comp (continuous_const.prodMk continuous_id))

@[reducible] def polFst (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  kfin P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
  wts P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).2

@[reducible] def polSnd (p q r s : ℕ) : GKMod r s where
  V := Pol p q r s
  act := fockAct2 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1
  kfin P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).1
  wts P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).2

/- English proof (translation)
Use `⟨(2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖, 4 * (∑ l, ∑ l', ‖Z l l'‖) + 1, by positivity, by positivity, fun k => ?_⟩` and prove the remaining obligations. Establish `h` using `(GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (GlobalTheory.FockAlg.isFockIsometry_of_fockData F) Z Q.totalDegree k Q le_rfl).2`. Use `h.trans ?_` and prove the remaining obligations. Establish `h2 : (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k ≤ (4 * (∑ l, ∑ l', ‖Z l l'‖) + 1) ^ k` using `pow_le_pow_left₀ (by positivity) (by linarith) k`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem om_bound (F : FockData T0 T1 T2) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (Q : Pol p q r s) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ,
      ‖F.ι ((omAct p q r s Z ^ k) Q)‖ ≤ C * ρ ^ k * (k.factorial : ℝ) := by
  refine ⟨(2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖, 4 * (∑ l, ∑ l', ‖Z l l'‖) + 1,
    by positivity, by positivity, fun k => ?_⟩
  have h := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (GlobalTheory.FockAlg.isFockIsometry_of_fockData F) Z Q.totalDegree k Q
    le_rfl).2
  refine h.trans ?_
  have h2 : (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k ≤ (4 * (∑ l, ∑ l', ‖Z l l'‖) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc _ = (2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖ * (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k *
        (k.factorial : ℝ) := by ring
    _ ≤ _ := by gcongr

/- English proof (translation)
The claim follows from `GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 (repFst F) (polFst p q r s) F.ι (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1 Z x y`.
-/
theorem adj_fst (F : FockData T0 T1 T2) (Z : Mat p q) (x y : Pol p q r s) :
    inner ℂ (F.ι (fockAct1 p q r s Z x)) (F.ι y) = inner ℂ (F.ι x) (F.ι (fockAct1 p q r s (adjZ Z) y)) :=
  GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 (repFst F) (polFst p q r s) F.ι
    (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1 Z x y

/- English proof (translation)
The claim follows from `GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint r s T2 (repSnd F) (polSnd p q r s) F.ι (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.2 Z x y`.
-/
theorem adj_snd (F : FockData T0 T1 T2) (Z : Mat r s) (x y : Pol p q r s) :
    inner ℂ (F.ι (fockAct2 p q r s Z x)) (F.ι y) = inner ℂ (F.ι x) (F.ι (fockAct2 p q r s (adjZ Z) y)) :=
  GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint r s T2 (repSnd F) (polSnd p q r s) F.ι
    (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.2 Z x y

end Fock

section Transfer

variable {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {M : GKMod p q}
  {i : M.V →ₗ[ℂ] V}

/- English proof (translation)
Simplify using `only [GlobalTheory.TensorHW.mem_wt, ← h, ← map_smul, hi.eq_iff]`.
-/
theorem wt_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {μ : Ix p q → ℚ} {x : M.V} :
    x ∈ wtSub M.act μ ↔ i x ∈ wtSub act μ := by
  simp only [GlobalTheory.TensorHW.mem_wt, ← h, ← map_smul, hi.eq_iff]

/- English proof (translation)
Rewrite using `[← h, map_eq_zero_iff i hi]`.
-/
theorem zero_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {Z : Mat p q} {x : M.V} :
    M.act Z x = 0 ↔ act Z (i x) = 0 := by
  rw [← h, map_eq_zero_iff i hi]

/- English proof (translation)
Simplify using `only [GlobalTheory.TensorHW.mem_hw, ← h, ← map_smul, hi.eq_iff, map_eq_zero_iff i hi]`.
-/
theorem hw_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {μ : Ix p q → ℚ} {x : M.V} :
    x ∈ hwSub M.act μ ↔ i x ∈ hwSub act μ := by
  simp only [GlobalTheory.TensorHW.mem_hw, ← h, ← map_smul, hi.eq_iff, map_eq_zero_iff i hi]

end Transfer

section Pair

variable {n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

def rkCompact (n : ℕ) : Ix n 0 → ℕ := Sum.elim (fun c => c.1) (fun c => c.elim0)

/- English proof (translation)
Introduce and unpack `(a | a) (b | b) h`. Conclude with `congrArg _ (Fin.ext h)`. Conclude with `b.elim0`. Conclude with `a.elim0`. Conclude with `a.elim0`.
-/
theorem rkCompact_inj : Function.Injective (rkCompact n) := by
  rintro (a | a) (b | b) h
  · exact congrArg _ (Fin.ext h)
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

/- English proof (translation)
Break down `a with a | a` into its components or cases. Break down `b with b | b` into its components or cases. Conclude with `h`. Conclude with `b.elim0`. Conclude with `a.elim0`.
-/
theorem rkCompact_lt {a b : Ix n 0} (h : rkCompact n a < rkCompact n b) : posC a b := by
  rcases a with a | a
  · rcases b with b | b
    · exact h
    · exact b.elim0
  · exact a.elim0

/- English proof (translation)
Take `⟨M, i, v, hi, hv, he, hgen⟩` from `exists_cyclic_sub (polSnd p q n 0) (delta hn ap am)`. Establish `hΔ` using `GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham`. Establish `hΔ0` using `(GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham).1`. Establish `hv0 : v ≠ 0` using `fun h => hΔ0 (by rw [← hv, h, map_zero])`. Establish `hvw : v ∈ hwSub M.act (wtH n ap am)` using `(hw_iff hi he).2 (hv ▸ hΔ)`.

Establish `hE : Function.Injective (F.ι ∘ₗ i)` using `F.ι_inj.comp hi`. Take `⟨hirr, -, W, hW1, hW2, hW3, hW4, -⟩` from `cyclic M F.H (F.ι ∘ₗ i) hE (fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_snd F Z (i x) (i y)) (rkCompact n) rkCompact_inj _ v hv0 hvw.1 (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hvw).2 a b (rkCompact_lt h)) hgen`. Take `⟨-, -, N, hN1, hN2, hN3⟩` from `GlobalTheory.T.lowestKType_of_irreducible_generated_module n 0 M (wtH n ap am) W hirr hW2 hW3 hW4 ⟨v, hW1, hv0, hvw⟩ (fun e _ a b => b.elim0) (eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _)))`. Take `⟨τ, j, J, h1, h2, -, -, -⟩` from `globalize (p := n) (q := 0) (by omega) T2 (repSnd F) M (F.ι ∘ₗ i) hE (fun Y hY x => by`. Simplify using `only [LinearMap.comp_apply, he]`.

Conclude with `(GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.2 Y hY (i x))`. Use the proof step `(fun Y _ y => by`. Simplify using `only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]`. Conclude with `om_bound F _ (i y))`. Use `hirr N _ hN1 hN2 hN3`.

Use `⟨M, i, v, hirr, ⟨hv0, hvw⟩, hv, he, τ, j, ((‖j v‖⁻¹ : ℝ) : ℂ) • v, h1, h2, ?_⟩` and prove the remaining obligations. Establish `h0 : ‖j v‖ ≠ 0` using `norm_ne_zero_iff.2 ((map_ne_zero_iff j h2.1).2 hv0)`. Use `⟨⟨smul_ne_zero (by simpa using h0) hv0, Submodule.smul_mem _ _ hvw⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, norm_smul]`. Simplify using `[h0]`.
-/
theorem exists_compact (F : FockData T0 T1 T2) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    ∃ (M : GKMod n 0) (i : M.V →ₗ[ℂ] Pol p q n 0) (v : M.V), IrrGK M ∧ IsHW M.act (wtH n ap am) v ∧
      i v = delta hn ap am ∧ (∀ Z x, i (M.act Z x) = fockAct2 p q n 0 Z (i x)) ∧
      ∃ (τ : URep T2) (j : M.V →ₗ[ℂ] τ.H) (v0 : M.V), IsCompactType τ M j (wtH n ap am) v0 := by
  obtain ⟨M, i, v, hi, hv, he, hgen⟩ := exists_cyclic_sub (polSnd p q n 0) (delta hn ap am)
  have hΔ := GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham
  have hΔ0 := (GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham).1
  have hv0 : v ≠ 0 := fun h => hΔ0 (by rw [← hv, h, map_zero])
  have hvw : v ∈ hwSub M.act (wtH n ap am) := (hw_iff hi he).2 (hv ▸ hΔ)
  have hE : Function.Injective (F.ι ∘ₗ i) := F.ι_inj.comp hi
  obtain ⟨hirr, -, W, hW1, hW2, hW3, hW4, -⟩ := cyclic M F.H (F.ι ∘ₗ i) hE
    (fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_snd F Z (i x) (i y))
    (rkCompact n) rkCompact_inj _ v hv0 hvw.1
    (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hvw).2 a b (rkCompact_lt h)) hgen
  obtain ⟨-, -, N, hN1, hN2, hN3⟩ := GlobalTheory.T.lowestKType_of_irreducible_generated_module n 0 M (wtH n ap am) W hirr hW2 hW3 hW4 ⟨v, hW1, hv0, hvw⟩
    (fun e _ a b => b.elim0)
    (eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _)))
  obtain ⟨τ, j, J, h1, h2, -, -, -⟩ := globalize (p := n) (q := 0) (by omega) T2 (repSnd F) M (F.ι ∘ₗ i) hE
    (fun Y hY x => by
      simp only [LinearMap.comp_apply, he]
      exact (GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.2 Y hY (i x))
    (fun Y _ y => by
      simp only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]
      exact om_bound F _ (i y))
    hirr N _ hN1 hN2 hN3
  refine ⟨M, i, v, hirr, ⟨hv0, hvw⟩, hv, he, τ, j, ((‖j v‖⁻¹ : ℝ) : ℂ) • v, h1, h2, ?_⟩
  have h0 : ‖j v‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff j h2.1).2 hv0)
  refine ⟨⟨smul_ne_zero (by simpa using h0) hv0, Submodule.smul_mem _ _ hvw⟩, ?_⟩
  rw [map_smul, norm_smul]
  simp [h0]

def rkExt (p q : ℕ) : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.rev.1)

/- English proof (translation)
Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h`. Conclude with `congrArg _ (Fin.ext (by omega))`. Use `b.rev.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `a.rev.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `congrArg _ (Fin.rev_injective (Fin.ext h))`.
-/
theorem rkExt_inj : Function.Injective (rkExt p q) := by
  rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg _ (Fin.ext (by omega))
  · have := b.rev.2; omega
  · have := a.rev.2; omega
  · exact congrArg _ (Fin.rev_injective (Fin.ext h))

/- English proof (translation)
Take `⟨M, i, v, hi, hv, he, hgen⟩` from `exists_cyclic_sub (polFst p q n 0) (delta hn ap am)`. Establish `hΔ2` using `GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham`. Take `⟨hΔ0, hΔw, hΔa, hΔb, hΔk⟩` from `GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham`. Establish `hv0 : v ≠ 0` using `fun h => hΔ0 (by rw [← hv, h, map_zero])`. Establish `hvw : v ∈ wtSub M.act (wtExt n ap am)` using `(wt_iff hi he).2 (hv ▸ hΔw)`.

Establish `hE : Function.Injective (F.ι ∘ₗ i)` using `F.ι_inj.comp hi`. Establish `hadj : ∀ Z x y, inner ℂ ((F.ι ∘ₗ i) (M.act Z x)) ((F.ι ∘ₗ i) y) = inner ℂ ((F.ι ∘ₗ i) x) ((F.ι ∘ₗ i) (M.act (adjZ Z) y))` using `fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_fst F Z (i x) (i y)`. Establish `hvk : KilledByLower M.act v` using `fun a b => (zero_iff hi he).2 (hv ▸ hΔk a b)`. Take `⟨hirr, hline, W, hW1, hW2, hW3, hW4, hW5⟩` from `cyclic M F.H (F.ι ∘ₗ i) hE hadj (rkExt p q) rkExt_inj _ v hv0 hvw (by`. Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h`.

Conclude with `(zero_iff hi he).2 (hv ▸ hΔa a b (by omega))`. Use `b.rev.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hvk b a`. Conclude with `(zero_iff hi he).2 (hv ▸ hΔb b a (Fin.rev_lt_rev.1 h))) hgen`.

Establish `hWk : ∀ e ∈ W, KilledByLower M.act e`. Set `K : Submodule ℂ M.V` to `⨅ a, ⨅ b, LinearMap.ker (M.act (Eab (Sum.inr b) (Sum.inl a)))`. Establish `hK : ∀ x, x ∈ K ↔ KilledByLower M.act x` using `fun x => by`. Simplify using `only [K, Submodule.mem_iInf, LinearMap.mem_ker, KilledByLower]`. Conclude with `fun e h => (hK e).1 (hW5 K ((hK v).2 hvk) (fun Z hZ x hx => (hK _).2 (GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal p q M.V M.act M.lie Z hZ x ((hK x).1 hx))) h)`.

Establish `hcomm : ∀ Y Z (P : Pol p q n 0), fockAct2 p q n 0 Z (fockAct1 p q n 0 Y P) = fockAct1 p q n 0 Y (fockAct2 p q n 0 Z P)` using `fun Y Z P => (LinearMap.congr_fun ((GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 Y Z) P).symm`. Establish `hW2' : ∀ e ∈ W, i e ∈ hwSub (fockAct2 p q n 0) (wtH n ap am)` using `fun e h => hW5 ((hwSub (fockAct2 p q n 0) (wtH n ap am)).comap i) (by simpa [hv] using hΔ2) (fun Z _ x hx => by`. Establish `hx'` using `GlobalTheory.TensorHW.mem_hw.1 (Submodule.mem_comap.1 hx)`. Use `Submodule.mem_comap.2 (GlobalTheory.TensorHW.mem_hw.2 ⟨fun a => ?_, fun a b hab => ?_⟩)` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `(hcomm _ _ _).trans (by rw [hx'.1 a, map_smul])`. Rewrite using `[he]`. Conclude with `(hcomm _ _ _).trans (by rw [hx'.2 a b hab, map_zero])) h`. Take `⟨μ, e, heW, he0, heh⟩` from `GlobalTheory.T.exists_highestWeight_vector_of_KStable p q M W hW2 hW3 fun h => hv0 (by simpa [h] using hW1)`. Establish `hμ : μ = wtK n ap am` using `GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight p q n hn ap am μ (i e) ⟨(map_ne_zero_iff i hi).2 he0, (hw_iff hi he).1 heh⟩ (hW2' e heW) fun a b => (zero_iff hi he).1 (hWk e heW a b)`.

Substitute `hμ` using the available equality. Establish `hgW : genSub M.act (W : Set M.V) = ⊤` using `eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _))`. Establish `hge : genSub M.act {e} = ⊤` using `(hirr.2 _ (genSub_stable _)).resolve_left fun h => he0 (by simpa [h] using subset_genSub (act := M.act) {e} rfl)`. Take `⟨hlow, hone, hN⟩` from `GlobalTheory.T.lowestKType_of_irreducible_generated_module p q M _ W hirr hW2 hW3 hW4 ⟨e, heW, he0, heh⟩ hWk hgW`. Take `⟨-, hbl, hlt⟩` from `GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1`.

Use `⟨M, i, v, W, hi, hv, he, hW1, hv0, hvw, hline, hlow, hone, fun x => ?_, fun ν u hu => ?_, hN⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq p q n ap am]`. Conclude with `GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower p q M.V M.act M.lie _ e heh (hWk e heW) hge x`. Take `⟨m, hm1, hm2⟩` from `GlobalTheory.T.kTypes_unitary_lowestWeight_in_cone p q M F.H _ hE hadj _ e heh (hWk e heW) hge ν u hu`. Use `⟨m, fun a b hab => ?_, hbl ▸ hm2⟩` and prove the remaining obligations.

Take `⟨a', b', rfl, rfl⟩` from `hm1 a b hab`. Conclude with `hlt a' b'`.
-/
theorem exists_lowest (F : FockData T0 T1 T2) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (hap : Antitone ap) (ham : Antitone am) (hap1 : ∀ i, 1 ≤ ap i) (ham1 : ∀ i, 1 ≤ am i) :
    ∃ (M : GKMod p q) (i : M.V →ₗ[ℂ] Pol p q n 0) (v : M.V) (W : Submodule ℂ M.V), Function.Injective i ∧
      i v = delta hn ap am ∧ (∀ Z x, i (M.act Z x) = fockAct1 p q n 0 Z (i x)) ∧ v ∈ W ∧ v ≠ 0 ∧
      v ∈ wtSub M.act (wtExt n ap am) ∧ (∀ x ∈ wtSub M.act (wtExt n ap am), ∃ c : ℂ, x = c • v) ∧
      IsLowestType M (wtK n ap am) W ∧ Module.finrank ℂ ↥(hwSub M.act (wtK n ap am)) = 1 ∧
      (∀ x, casimir M.act x = (((normSq (hcParam n ap am) - rhoSq (p + q) : ℚ)) : ℂ) • x) ∧
      ConeTypes M (hcParam n ap am) ∧
      ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m,
        ∑ a : Fin p, M.act (Eab (Sum.inl a) (Sum.inl a)) x =
          (((∑ a : Fin p, wtK n ap am (Sum.inl a) : ℚ) : ℂ) + m) • x := by
  obtain ⟨M, i, v, hi, hv, he, hgen⟩ := exists_cyclic_sub (polFst p q n 0) (delta hn ap am)
  have hΔ2 := GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham
  obtain ⟨hΔ0, hΔw, hΔa, hΔb, hΔk⟩ := GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham
  have hv0 : v ≠ 0 := fun h => hΔ0 (by rw [← hv, h, map_zero])
  have hvw : v ∈ wtSub M.act (wtExt n ap am) := (wt_iff hi he).2 (hv ▸ hΔw)
  have hE : Function.Injective (F.ι ∘ₗ i) := F.ι_inj.comp hi
  have hadj : ∀ Z x y, inner ℂ ((F.ι ∘ₗ i) (M.act Z x)) ((F.ι ∘ₗ i) y) =
      inner ℂ ((F.ι ∘ₗ i) x) ((F.ι ∘ₗ i) (M.act (adjZ Z) y)) :=
    fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_fst F Z (i x) (i y)
  have hvk : KilledByLower M.act v := fun a b => (zero_iff hi he).2 (hv ▸ hΔk a b)
  obtain ⟨hirr, hline, W, hW1, hW2, hW3, hW4, hW5⟩ := cyclic M F.H (F.ι ∘ₗ i) hE hadj
    (rkExt p q) rkExt_inj _ v hv0 hvw (by
      rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h
      · exact (zero_iff hi he).2 (hv ▸ hΔa a b (by omega))
      · have := b.rev.2; omega
      · exact hvk b a
      · exact (zero_iff hi he).2 (hv ▸ hΔb b a (Fin.rev_lt_rev.1 h))) hgen
  have hWk : ∀ e ∈ W, KilledByLower M.act e := by
    let K : Submodule ℂ M.V := ⨅ a, ⨅ b, LinearMap.ker (M.act (Eab (Sum.inr b) (Sum.inl a)))
    have hK : ∀ x, x ∈ K ↔ KilledByLower M.act x := fun x => by
      simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, KilledByLower]
    exact fun e h => (hK e).1 (hW5 K ((hK v).2 hvk)
      (fun Z hZ x hx => (hK _).2 (GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal p q M.V M.act M.lie Z hZ x ((hK x).1 hx))) h)
  have hcomm : ∀ Y Z (P : Pol p q n 0), fockAct2 p q n 0 Z (fockAct1 p q n 0 Y P) =
      fockAct1 p q n 0 Y (fockAct2 p q n 0 Z P) := fun Y Z P =>
    (LinearMap.congr_fun ((GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 Y Z) P).symm
  have hW2' : ∀ e ∈ W, i e ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := fun e h =>
    hW5 ((hwSub (fockAct2 p q n 0) (wtH n ap am)).comap i) (by simpa [hv] using hΔ2) (fun Z _ x hx => by
      have hx' := GlobalTheory.TensorHW.mem_hw.1 (Submodule.mem_comap.1 hx)
      refine Submodule.mem_comap.2 (GlobalTheory.TensorHW.mem_hw.2 ⟨fun a => ?_, fun a b hab => ?_⟩)
      · rw [he]
        exact (hcomm _ _ _).trans (by rw [hx'.1 a, map_smul])
      · rw [he]
        exact (hcomm _ _ _).trans (by rw [hx'.2 a b hab, map_zero])) h
  obtain ⟨μ, e, heW, he0, heh⟩ := GlobalTheory.T.exists_highestWeight_vector_of_KStable p q M W hW2 hW3 fun h => hv0 (by simpa [h] using hW1)
  have hμ : μ = wtK n ap am := GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight p q n hn ap am μ (i e)
    ⟨(map_ne_zero_iff i hi).2 he0, (hw_iff hi he).1 heh⟩ (hW2' e heW)
    fun a b => (zero_iff hi he).1 (hWk e heW a b)
  subst hμ
  have hgW : genSub M.act (W : Set M.V) = ⊤ :=
    eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _))
  have hge : genSub M.act {e} = ⊤ := (hirr.2 _ (genSub_stable _)).resolve_left fun h =>
    he0 (by simpa [h] using subset_genSub (act := M.act) {e} rfl)
  obtain ⟨hlow, hone, hN⟩ := GlobalTheory.T.lowestKType_of_irreducible_generated_module p q M _ W hirr hW2 hW3 hW4 ⟨e, heW, he0, heh⟩ hWk hgW
  obtain ⟨-, hbl, hlt⟩ := GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1
  refine ⟨M, i, v, W, hi, hv, he, hW1, hv0, hvw, hline, hlow, hone, fun x => ?_, fun ν u hu => ?_, hN⟩
  · rw [GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq p q n ap am]
    exact GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower p q M.V M.act M.lie _ e heh (hWk e heW) hge x
  · obtain ⟨m, hm1, hm2⟩ := GlobalTheory.T.kTypes_unitary_lowestWeight_in_cone p q M F.H _ hE hadj _ e heh (hWk e heW) hge ν u hu
    refine ⟨m, fun a b hab => ?_, hbl ▸ hm2⟩
    obtain ⟨a', b', rfl, rfl⟩ := hm1 a b hab
    exact hlt a' b'

end Pair

/- English proof (translation)
Establish `h : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q)` using `(GlobalTheory.RealPar.KStabLie.isKC_iff _).1 hk`. Use `(GlobalTheory.RealPar.KStabLie.isKC_iff _).2 ?_` and prove the remaining obligations. Rewrite using `[map_inv]`. Conclude with `h.units_inv_left`.
-/
theorem inv_mem_Kset (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) : k⁻¹ ∈ T.Kset := by
  have h : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q) := (GlobalTheory.RealPar.KStabLie.isKC_iff _).1 hk
  refine (GlobalTheory.RealPar.KStabLie.isKC_iff _).2 ?_
  rw [map_inv]
  exact h.units_inv_left

/- English proof (translation)
The claim follows from `(GlobalTheory.RealPar.KStabLie.isKC_iff _).2 (by simp)`.
-/
theorem one_mem_Kset (T : GrpData p q) : (1 : T.G) ∈ T.Kset :=
  (GlobalTheory.RealPar.KStabLie.isKC_iff _).2 (by simp)

/- English proof (translation)
Take `⟨e', h, -⟩` from `GlobalTheory.RealPar.pair_kEquivariant_of_lie p q T (GlobalTheory.CoverKGen.kset_gen p q hpq T) σ σ W (fun Y => if h : IsKC Y then (M.act Y).restrict (hW Y h) else 0) (j ∘ₗ W.subtype) (j ∘ₗ W.subtype) (fun Y hY hK w => by`. Simplify using `only [dif_pos hK, and_self]`. Conclude with `hder Y hY w) k hk e`. Conclude with `⟨e', h⟩`.
-/
theorem exists_k_translate (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W) {k : T.G} (hk : k ∈ T.Kset) (e : W) :
    ∃ e' : W, σ.π k (j e) = j e' := by
  classical
  obtain ⟨e', h, -⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie p q T (GlobalTheory.CoverKGen.kset_gen p q hpq T) σ σ W
    (fun Y => if h : IsKC Y then (M.act Y).restrict (hW Y h) else 0) (j ∘ₗ W.subtype) (j ∘ₗ W.subtype)
    (fun Y hY hK w => by
      simp only [dif_pos hK, and_self]
      exact hder Y hY w) k hk e
  exact ⟨e', h⟩

section Pair

variable {n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

/- English proof (translation)
Introduce `k₁ h₁ k₂ h₂ X hX e e'`. Take `⟨f, hf⟩` from `exists_k_translate hpq T1 σ M j hder W hW h₂ e`. Take `⟨f', hf'⟩` from `exists_k_translate hpq T1 σ M j hder W hW (inv_mem_Kset T1 h₁) e'`. Establish `hP : ∀ e ∈ W, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.KilledByPMinus (i e)` using `fun e he a b => by`. Use `hk e he a b` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero]`. Then use the resulting hypothesis. Establish `h` using `hdec p q n T0 T1 T2 F X hX (i f) (i f') (hP f f.2) (hP f' f'.2)`. Establish `e1 : inner ℂ (j e') (σ.π (k₁ * T1.expt X * k₂) (j e)) = GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef F X (i f) (i f')`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef, ← hJ, ← hJ, ← hG, J.inner_map_map, ← hf, ← hf', inner_pi_left, inv_inv, map_mul, map_mul]`. Both sides reduce to the same expression.

Establish `e2 : decay n X = ∏ i : Fin (min p q), Real.cosh (GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal X i) ^ (-(n : ℤ))`. Rewrite using `[decay, Finset.prod_range]`. Simplify using `only [zpow_neg, zpow_natCast, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal]`. Rewrite using `[e1, e2]`. Rewrite `h` using `[← hJ, ← hJ, J.norm_map, J.norm_map, ← hf, ← hf', σ.isom, σ.isom]`. Then use the resulting hypothesis.
-/
theorem coef_decay (hdec : GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.HarmonicDecay) (hpq : 1 ≤ p + q) (F : FockData T0 T1 T2) (σ : URep T1)
    (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T1.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    (i : M.V →ₗ[ℂ] Pol p q n 0) (J : σ.H →ₗᵢ[ℂ] F.H) (hJ : ∀ x, J (j x) = F.ι (i x))
    (hG : ∀ g y, J (σ.π g y) = F.π (g, 1) (J y)) (hk : ∀ e ∈ W, KilledByLower (fockAct1 p q n 0) (i e)) :
    ∀ k₁ ∈ T1.Kset, ∀ k₂ ∈ T1.Kset, ∀ X ∈ pR p q, ∀ e e' : W,
      ‖inner ℂ (j e') (σ.π (k₁ * T1.expt X * k₂) (j e))‖ ≤ decay n X * ‖j e‖ * ‖j e'‖ := by
  intro k₁ h₁ k₂ h₂ X hX e e'
  obtain ⟨f, hf⟩ := exists_k_translate hpq T1 σ M j hder W hW h₂ e
  obtain ⟨f', hf'⟩ := exists_k_translate hpq T1 σ M j hder W hW (inv_mem_Kset T1 h₁) e'
  have hP : ∀ e ∈ W, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.KilledByPMinus (i e) := fun e he a b => by
    have := hk e he a b
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
  have h := hdec p q n T0 T1 T2 F X hX (i f) (i f') (hP f f.2) (hP f' f'.2)
  have e1 : inner ℂ (j e') (σ.π (k₁ * T1.expt X * k₂) (j e)) = GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef F X (i f) (i f') := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef, ← hJ, ← hJ, ← hG, J.inner_map_map, ← hf, ← hf', inner_pi_left, inv_inv,
      map_mul, map_mul]
    rfl
  have e2 : decay n X = ∏ i : Fin (min p q), Real.cosh (GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal X i) ^ (-(n : ℤ)) := by
    rw [decay, Finset.prod_range]
    simp only [zpow_neg, zpow_natCast, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal]
  rw [e1, e2]
  rwa [← hJ, ← hJ, J.norm_map, J.norm_map, ← hf, ← hf', σ.isom, σ.isom] at h

/- English proof (translation)
Take `⟨-, -, hWs, hWi, -, -, hWk, hWg, -⟩` from `hW`. Take `⟨u1, u2, u3⟩` from `GlobalTheory.T.fock_tensor_intertwiner_unique_and_range p q n T0 T1 T2 F D.HK W M I e0 v0 hWg hWs hWi hirr he0 hv0 hI`. Take `⟨g1, g2⟩` from `GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends p q n T0 T1 T2 F hn D τ M j I v0 hτ hM hv0 hI hJ0`. Establish `hio : ∀ (e : W) (v : M.V), (I ∘ₗ TensorProduct.map W.subtype LinearMap.id) (e ⊗ₜ v) = I ((e : D.HK.V) ⊗ₜ v)` using `fun e v => by simp`. Establish `hcoef : ∀ (g : T1.G) (x x' : D.HK.V) (v v' : M.V), inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.π (g, 1) (F.ι (I (x ⊗ₜ v)))) = ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.U.π g (D.ι x)) * inner ℂ (j v') (j v)`.

Introduce `g x x' v v'`. Take `⟨J, hJ1, hJ2⟩` from `g2 v`. Rewrite using `[← hJ1, hJ2]`. Use `DenseRange.induction_on (p := fun y => inner ℂ (F.ι (I (x' ⊗ₜ v'))) (J y) = ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') y * inner ℂ (j v') (j v)) hd _ (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_` and prove the remaining obligations. Rewrite using `[hJ1, hip]`.

Use `⟨(hio _ _).trans h0, ⟨fun Z _ e e' v h => ?_, fun Y e v => ?_⟩, fun io' h h' => u1 io' h (h'.trans h0.symm), fun k _ h e e' v v' he hv => ?_, fun e e' v v' => ?_, fun y a b => ?_, fun e v => (hio e v).symm, hI, fun I' h h' => u2 I' h fun e v => (h' e v).trans (hio e v), fun v hv …` and prove the remaining obligations. Rewrite using `[hio, hio, hI.1, h]`. Rewrite using `[hio, hio, hI.2]`. Take `⟨J, hJ1, hJ2⟩` from `g2 v'`. Establish `: (k, h) = ((k, 1) : T1.G × T2.G) * (1, h)` using `by simp`.

Rewrite using `[hio, hio, this, map_mul, ContinuousLinearMap.mul_apply, g1 h e v v' hv, ← hJ1, hJ2, ← he, hJ1]`. Rewrite using `[hio, hio, hip]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e v => rw [hio, hI.1, hWk e e.2 a b, TensorProduct.zero_tmul, map_zero]`.

Consider the case `add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]`. Establish `h1` using `hip (x - x') (x - x') v v`. Establish `h2 : I ((x - x') ⊗ₜ v) = 0`. Rewrite using `[TensorProduct.sub_tmul, map_sub]`. Conclude with `sub_eq_zero.2 hx`.

Rewrite `h1` using `[h2, map_zero, inner_zero_left]`. Establish `h3 : ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) ≠ 0`. Simplify using `using (map_ne_zero_iff F.ι F.ι_inj).2 hΔ`. Establish `h4 : inner ℂ (j v) (j v) ≠ 0` using `inner_self_ne_zero.2 ((map_ne_zero_iff j hM.1).2 hv)`. Establish `h5` using `((mul_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_right h4)).resolve_left h3)`.

Conclude with `sub_eq_zero.1 ((map_eq_zero_iff D.ι D.ι_inj).1 (inner_self_eq_zero.1 h5))`. Simplify using `only [hio]`. Conclude with `u3 v`. Rewrite using `[hio, hio, hcoef]`. Establish `e1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ)` using `fun z => by`.

Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `e2 : inner ℂ (j v) (j v) = 1` using `by rw [inner_self_eq_norm_sq_to_K, hv]; simp`. Take `⟨s1, s2⟩` from `D.schur (D.ι e) (D.ι e')`. Simplify using `only [hio, hcoef, e2, mul_one, mul_assoc, e1]`. Use `⟨(s1.ofReal (𝕜 := ℂ)).const_mul _, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_const_mul, integral_complex_ofReal, s2, he, he']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem harmonicMaps_of (hn : 1 ≤ n) (F : FockData T0 T1 T2) (D : DSRep T1) (W : Submodule ℂ D.HK.V)
    (Λ : Ix p q → ℚ) (hW : IsLowestType D.HK Λ W) (hd : Dense (Set.range D.ι)) (τ : URep T2)
    (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (Δ : Pol p q n 0) (hΔ : Δ ≠ 0) (e0 : W) (v0 : M.V) (hτ : IrrU τ)
    (hM : IsHCMod τ M j) (hirr : IrrGK M) (he0 : e0 ≠ 0) (hv0 : v0 ≠ 0)
    (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (hI : IsGIntw F D.HK M I) (h0 : I ((e0 : D.HK.V) ⊗ₜ v0) = Δ)
    (hip : ∀ (x x' : D.HK.V) (v v' : M.V), inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.ι (I (x ⊗ₜ v))) =
      ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.ι x) * inner ℂ (j v') (j v))
    (hJ0 : ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v0))) ∧
      ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) :
    HarmonicMaps F D W τ M j Δ e0 v0 (I ∘ₗ TensorProduct.map W.subtype LinearMap.id) I := by
  obtain ⟨-, -, hWs, hWi, -, -, hWk, hWg, -⟩ := hW
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.T.fock_tensor_intertwiner_unique_and_range p q n T0 T1 T2 F D.HK W M I e0 v0 hWg hWs hWi hirr he0 hv0 hI
  obtain ⟨g1, g2⟩ := GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends p q n T0 T1 T2 F hn D τ M j I v0 hτ hM hv0 hI hJ0
  have hio : ∀ (e : W) (v : M.V), (I ∘ₗ TensorProduct.map W.subtype LinearMap.id) (e ⊗ₜ v) =
      I ((e : D.HK.V) ⊗ₜ v) := fun e v => by simp
  have hcoef : ∀ (g : T1.G) (x x' : D.HK.V) (v v' : M.V),
      inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.π (g, 1) (F.ι (I (x ⊗ₜ v)))) =
        ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.U.π g (D.ι x)) * inner ℂ (j v') (j v) := by
    intro g x x' v v'
    obtain ⟨J, hJ1, hJ2⟩ := g2 v
    rw [← hJ1, hJ2]
    refine DenseRange.induction_on (p := fun y => inner ℂ (F.ι (I (x' ⊗ₜ v'))) (J y) =
      ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') y * inner ℂ (j v') (j v)) hd _
      (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [hJ1, hip]
  refine ⟨(hio _ _).trans h0, ⟨fun Z _ e e' v h => ?_, fun Y e v => ?_⟩, fun io' h h' => u1 io' h (h'.trans h0.symm),
    fun k _ h e e' v v' he hv => ?_, fun e e' v v' => ?_, fun y a b => ?_, fun e v => (hio e v).symm, hI,
    fun I' h h' => u2 I' h fun e v => (h' e v).trans (hio e v), fun v hv => ⟨fun x x' hx => ?_, ?_⟩, hip, g1, g2,
    fun g e e' v v' => ?_, fun e e' v he he' hv => ?_⟩
  · rw [hio, hio, hI.1, h]
  · rw [hio, hio, hI.2]
  · obtain ⟨J, hJ1, hJ2⟩ := g2 v'
    have : (k, h) = ((k, 1) : T1.G × T2.G) * (1, h) := by simp
    rw [hio, hio, this, map_mul, ContinuousLinearMap.mul_apply, g1 h e v v' hv, ← hJ1, hJ2, ← he, hJ1]
  · rw [hio, hio, hip]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e v => rw [hio, hI.1, hWk e e.2 a b, TensorProduct.zero_tmul, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  · have h1 := hip (x - x') (x - x') v v
    have h2 : I ((x - x') ⊗ₜ v) = 0 := by
      rw [TensorProduct.sub_tmul, map_sub]
      exact sub_eq_zero.2 hx
    rw [h2, map_zero, inner_zero_left] at h1
    have h3 : ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simpa using (map_ne_zero_iff F.ι F.ι_inj).2 hΔ
    have h4 : inner ℂ (j v) (j v) ≠ 0 := inner_self_ne_zero.2 ((map_ne_zero_iff j hM.1).2 hv)
    have h5 := ((mul_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_right h4)).resolve_left h3)
    exact sub_eq_zero.1 ((map_eq_zero_iff D.ι D.ι_inj).1 (inner_self_eq_zero.1 h5))
  · simp only [hio]
    exact u3 v
  · rw [hio, hio, hcoef]
  · have e1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e2 : inner ℂ (j v) (j v) = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
    obtain ⟨s1, s2⟩ := D.schur (D.ι e) (D.ι e')
    simp only [hio, hcoef, e2, mul_one, mul_assoc, e1]
    refine ⟨(s1.ofReal (𝕜 := ℂ)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_complex_ofReal, s2, he, he']
    push_cast
    ring

end Pair

/- English proof (translation)
Introduce `p q n hn hpq ap am hap ham hap1 ham1 T0 T1 T2 F`. Take `⟨M₁, i, v, W, hi, hv, he, hvW, hv0, hvw, hline, hlow, hone, hcas, hcone, N, hN1, hN2, hN3⟩` from `exists_lowest F hn ap am hap ham hap1 ham1`. Take `⟨σ, j₁, J, hσ, hHC, hd, hJ, hG⟩` from `globalize hpq T1 (repFst F) M₁ (F.ι ∘ₗ i) (F.ι_inj.comp hi) (fun Y hY x => by`. Simplify using `only [LinearMap.comp_apply, he]`. Conclude with `(GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.1 Y hY (i x))`.

Use the proof step `(fun Y _ y => by`. Simplify using `only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]`. Conclude with `om_bound F _ (i y))`. Use the proof step `hlow.1 N _ hN1 hN2 hN3`. Use `haveI := hlow.2.1`.

Establish `hdecay` using `coef_decay hdec hpq F σ M₁ j₁ hHC.2.2 W hlow.2.2.1 i J hJ hG fun e h a b => (zero_iff hi he).1 (hlow.2.2.2.2.2.2.1 e h a b)`. Establish `hjv : j₁ v ≠ 0` using `(map_ne_zero_iff j₁ hHC.1).2 hv0`. Take `⟨d, hd0, hschur⟩` from `exists_fdeg T1 σ hσ (j₁ v) hjv (GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover hint p q n hn T1 _ (‖j₁ v‖ * ‖j₁ v‖) (continuous_const.inner (σ.cont _)) fun k hk X hX => by`. Use `hdecay k hk 1 (one_mem_Kset T1) X hX ⟨v, hvW⟩ ⟨v, hvW⟩` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `this.trans_eq (by ring))`. Set `D : DSRep T1` to `{ U := σ, nontriv := hσ.1, irred := hσ.2, fdeg := d, fdeg_pos := hd0, schur := hschur, HK := M₁, ι := j₁ ι_inj := hHC.1, ι_range := hHC.2.1, der := hHC.2.2 }`. Take `⟨hpar, hbl, -⟩` from `GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1`. Take `⟨M₂, i₂, v₂, hirr₂, hv₂, hi₂, he₂, τ₀, j₀, w₀, hτ₀⟩` from `exists_compact F hn ap am hap ham`. Use `⟨D, W, hlow, hbl, ⟨hpar, hbl ▸ hone, hcas, hcone⟩, hdecay, ?_, ⟨τ₀, M₂, j₀, w₀, hτ₀⟩, ?_⟩` and prove the remaining obligations.

Establish `h0 : ‖j₁ v‖ ≠ 0` using `norm_ne_zero_iff.2 hjv`. Use `⟨⟨((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v, W.smul_mem _ hvW⟩, Submodule.smul_mem _ _ hvw, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖j₁ (((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v)‖ = 1`. Rewrite using `[map_smul, norm_smul]`. Simplify using `[h0]`.

Introduce and unpack `τ M j v0 ⟨hτ, hM, hv0', hv1⟩ e0 he0w he01`. Express the relevant statement in the definitionally equal form `‖j₁ (e0 : M₁.V)‖ = 1 at he01`. Establish `he0 : (e0 : M₁.V) ≠ 0` using `fun h => by simp [h] at he01`. Take `⟨-, hirr, -, -⟩` from `GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible n (by omega) T2 τ M j hτ hM (nontrivial_of_ne v0 0 hv0'.1)`. Take `⟨f, hf1, hf2⟩` from `GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact n M M₂ _ v0 v₂ hirr hirr₂ hv0' hv₂`.

Take `⟨c, hc⟩` from `hline _ he0w`. Establish `hc0 : c ≠ 0` using `fun h => he0 (by rw [hc, h, zero_smul])`. Establish `hve : v = c⁻¹ • (e0 : M₁.V)` using `by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Establish `gen : ∀ {a b : ℕ} (A : GKMod a b), IrrGK A → ∀ x : A.V, x ≠ 0 → genSub A.act {x} = ⊤` using `fun A hA x hx => (hA.2 _ (genSub_stable _)).resolve_left fun h => hx (by simpa [h] using subset_genSub (act := A.act) {x} rfl)`. Establish `hg1` using `gen M₁ hlow.1 _ he0`.

Establish `hg2` using `gen M hirr _ hv0'.1`. Establish `hΔ : (c⁻¹ • i) (e0 : M₁.V) = delta hn ap am`. Rewrite using `[← hv, hve, map_smul, LinearMap.smul_apply]`. Establish `hΔ' : (i₂ ∘ₗ f) v0 = delta hn ap am` using `by rw [LinearMap.comp_apply, hf1, hi₂]`. Establish `he₂' : ∀ Z y, (i₂ ∘ₗ f) (M.act Z y) = fockAct2 p q n 0 Z ((i₂ ∘ₗ f) y)` using `fun Z y => by`.

Simplify using `only [LinearMap.comp_apply, hf2, he₂]`. Take `⟨I, hI1, hI2, hI3, hI4⟩` from `GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting p q n 0 (Pol p q n 0) _ _ (GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 M₁ M (c⁻¹ • i) (i₂ ∘ₗ f) (fun Z x => by simp only [LinearMap.smul_apply, he, map_smul]) he₂' e0 v0 hg1 hg2 (hΔ.trans …`. Establish `hline2 : ∀ x ∈ wtSub M.act (wtH n ap am), ∃ c : ℂ, x = c • v0` using `(cyclic M τ.H j hM.1 (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2) (rkCompact n) rkCompact_inj _ v0 hv0'.1 hv0'.2.1 (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hv0'.2).2 a b (rkCompact_lt h)) hg2).2.1`. Establish `hf₂` using `GlobalTheory.T.invariant_inner_forms_proportional_weight_line n 0 M τ.H F.H j (F.ι ∘ₗ i₂ ∘ₗ f) (F.ι ∘ₗ i₂ ∘ₗ f) (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2) (fun Z x y => by`. Simplify using `only [LinearMap.comp_apply (f := F.ι), he₂']`.

Conclude with `adj_snd F Z _ _) _ v0 hv0'.2.1 hline2 hg2 hv1`. Simplify using `only [LinearMap.comp_apply (f := F.ι), hΔ'] at hf₂`. Use `⟨_, I, harmonicMaps_of (by omega) F D W _ hlow hd τ M j _ (fun h => hv0 (hi (by rw [hv, h, map_zero]))) e0 v0 hτ hM hirr (fun h => he0 (by rw [h]; rfl)) hv0'.1 I ⟨hI1, hI2⟩ ((hI3 _).trans hΔ) (fun x x' w w' => ?_) ⟨c⁻¹ • J.toContinuousLinearMap, fun x => ?_, fun g y => ?_⟩⟩` and prove the remaining obligations. Establish `hf₁` using `GlobalTheory.T.invariant_inner_forms_proportional_weight_line p q M₁ σ.H F.H j₁ (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w') (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w) (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 σ M₁ j₁ hHC.2.2) (fun Z x y => by`. Simplify using `only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, ← hI1]`.

Conclude with `adj_fst F Z _ _) _ e0 he0w`. Use the proof step `(fun y hy => by`. Take `⟨a, ha⟩` from `hline y hy`. Conclude with `⟨a * c⁻¹, by rw [ha, mul_smul, ← hve]⟩) hg1 he01 x' x`. Simplify using `only [LinearMap.comp_apply (f := F.ι), LinearMap.comp_apply (f := I), LinearMap.flip_apply, TensorProduct.mk_apply, hI4, hf₂] at hf₁`.

Use `hf₁.trans ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K, mul_right_comm]`. Use `push_cast`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `c⁻¹ • J (j₁ x) = F.ι (I (x ⊗ₜ v0))`.

Rewrite using `[hI3, hJ, LinearMap.smul_apply, map_smul]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `F.π (g, 1) (c⁻¹ • J y) = c⁻¹ • J (σ.π g y)`. Rewrite using `[map_smul, hG]`. Both sides reduce to the same expression.
-/
theorem harmonicModule_of (hdec : GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.HarmonicDecay) (hint : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral) :
    HarmonicModule := by
  intro p q n hn hpq ap am hap ham hap1 ham1 T0 T1 T2 F
  obtain ⟨M₁, i, v, W, hi, hv, he, hvW, hv0, hvw, hline, hlow, hone, hcas, hcone, N, hN1, hN2, hN3⟩ :=
    exists_lowest F hn ap am hap ham hap1 ham1
  obtain ⟨σ, j₁, J, hσ, hHC, hd, hJ, hG⟩ := globalize hpq T1 (repFst F) M₁ (F.ι ∘ₗ i) (F.ι_inj.comp hi)
    (fun Y hY x => by
      simp only [LinearMap.comp_apply, he]
      exact (GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.1 Y hY (i x))
    (fun Y _ y => by
      simp only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]
      exact om_bound F _ (i y))
    hlow.1 N _ hN1 hN2 hN3
  haveI := hlow.2.1
  have hdecay := coef_decay hdec hpq F σ M₁ j₁ hHC.2.2 W hlow.2.2.1 i J hJ hG
    fun e h a b => (zero_iff hi he).1 (hlow.2.2.2.2.2.2.1 e h a b)
  have hjv : j₁ v ≠ 0 := (map_ne_zero_iff j₁ hHC.1).2 hv0
  obtain ⟨d, hd0, hschur⟩ := exists_fdeg T1 σ hσ (j₁ v) hjv
    (GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover hint p q n hn T1 _ (‖j₁ v‖ * ‖j₁ v‖) (continuous_const.inner (σ.cont _)) fun k hk X hX => by
      have := hdecay k hk 1 (one_mem_Kset T1) X hX ⟨v, hvW⟩ ⟨v, hvW⟩
      rw [mul_one] at this
      exact this.trans_eq (by ring))
  let D : DSRep T1 :=
    { U := σ, nontriv := hσ.1, irred := hσ.2, fdeg := d, fdeg_pos := hd0, schur := hschur, HK := M₁, ι := j₁
      ι_inj := hHC.1, ι_range := hHC.2.1, der := hHC.2.2 }
  obtain ⟨hpar, hbl, -⟩ := GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1
  obtain ⟨M₂, i₂, v₂, hirr₂, hv₂, hi₂, he₂, τ₀, j₀, w₀, hτ₀⟩ := exists_compact F hn ap am hap ham
  refine ⟨D, W, hlow, hbl, ⟨hpar, hbl ▸ hone, hcas, hcone⟩, hdecay, ?_, ⟨τ₀, M₂, j₀, w₀, hτ₀⟩, ?_⟩
  · have h0 : ‖j₁ v‖ ≠ 0 := norm_ne_zero_iff.2 hjv
    refine ⟨⟨((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v, W.smul_mem _ hvW⟩, Submodule.smul_mem _ _ hvw, ?_⟩
    change ‖j₁ (((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v)‖ = 1
    rw [map_smul, norm_smul]
    simp [h0]
  rintro τ M j v0 ⟨hτ, hM, hv0', hv1⟩ e0 he0w he01
  change ‖j₁ (e0 : M₁.V)‖ = 1 at he01
  have he0 : (e0 : M₁.V) ≠ 0 := fun h => by simp [h] at he01
  obtain ⟨-, hirr, -, -⟩ := GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible n (by omega) T2 τ M j hτ hM (nontrivial_of_ne v0 0 hv0'.1)
  obtain ⟨f, hf1, hf2⟩ := GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact n M M₂ _ v0 v₂ hirr hirr₂ hv0' hv₂
  obtain ⟨c, hc⟩ := hline _ he0w
  have hc0 : c ≠ 0 := fun h => he0 (by rw [hc, h, zero_smul])
  have hve : v = c⁻¹ • (e0 : M₁.V) := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have gen : ∀ {a b : ℕ} (A : GKMod a b), IrrGK A → ∀ x : A.V, x ≠ 0 → genSub A.act {x} = ⊤ :=
    fun A hA x hx => (hA.2 _ (genSub_stable _)).resolve_left fun h =>
      hx (by simpa [h] using subset_genSub (act := A.act) {x} rfl)
  have hg1 := gen M₁ hlow.1 _ he0
  have hg2 := gen M hirr _ hv0'.1
  have hΔ : (c⁻¹ • i) (e0 : M₁.V) = delta hn ap am := by
    rw [← hv, hve, map_smul, LinearMap.smul_apply]
  have hΔ' : (i₂ ∘ₗ f) v0 = delta hn ap am := by rw [LinearMap.comp_apply, hf1, hi₂]
  have he₂' : ∀ Z y, (i₂ ∘ₗ f) (M.act Z y) = fockAct2 p q n 0 Z ((i₂ ∘ₗ f) y) := fun Z y => by
    simp only [LinearMap.comp_apply, hf2, he₂]
  obtain ⟨I, hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting p q n 0 (Pol p q n 0) _ _ (GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 M₁ M
    (c⁻¹ • i) (i₂ ∘ₗ f) (fun Z x => by simp only [LinearMap.smul_apply, he, map_smul]) he₂' e0 v0 hg1 hg2
    (hΔ.trans hΔ'.symm)
  have hline2 : ∀ x ∈ wtSub M.act (wtH n ap am), ∃ c : ℂ, x = c • v0 :=
    (cyclic M τ.H j hM.1 (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2) (rkCompact n)
      rkCompact_inj _ v0 hv0'.1 hv0'.2.1
      (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hv0'.2).2 a b (rkCompact_lt h)) hg2).2.1
  have hf₂ := GlobalTheory.T.invariant_inner_forms_proportional_weight_line n 0 M τ.H F.H j (F.ι ∘ₗ i₂ ∘ₗ f) (F.ι ∘ₗ i₂ ∘ₗ f)
    (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2)
    (fun Z x y => by
      simp only [LinearMap.comp_apply (f := F.ι), he₂']
      exact adj_snd F Z _ _) _ v0 hv0'.2.1 hline2 hg2 hv1
  simp only [LinearMap.comp_apply (f := F.ι), hΔ'] at hf₂
  refine ⟨_, I, harmonicMaps_of (by omega) F D W _ hlow hd τ M j _ (fun h => hv0 (hi (by rw [hv, h, map_zero])))
    e0 v0 hτ hM hirr (fun h => he0 (by rw [h]; rfl)) hv0'.1 I ⟨hI1, hI2⟩ ((hI3 _).trans hΔ)
    (fun x x' w w' => ?_) ⟨c⁻¹ • J.toContinuousLinearMap, fun x => ?_, fun g y => ?_⟩⟩
  · have hf₁ := GlobalTheory.T.invariant_inner_forms_proportional_weight_line p q M₁ σ.H F.H j₁ (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w')
      (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w)
      (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 σ M₁ j₁ hHC.2.2)
      (fun Z x y => by
        simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, ← hI1]
        exact adj_fst F Z _ _) _ e0 he0w
      (fun y hy => by
        obtain ⟨a, ha⟩ := hline y hy
        exact ⟨a * c⁻¹, by rw [ha, mul_smul, ← hve]⟩) hg1 he01 x' x
    simp only [LinearMap.comp_apply (f := F.ι), LinearMap.comp_apply (f := I), LinearMap.flip_apply,
      TensorProduct.mk_apply, hI4, hf₂] at hf₁
    refine hf₁.trans ?_
    rw [inner_self_eq_norm_sq_to_K, mul_right_comm]
    push_cast
    rfl
  · change c⁻¹ • J (j₁ x) = F.ι (I (x ⊗ₜ v0))
    rw [hI3, hJ, LinearMap.smul_apply, map_smul]
    rfl
  · change F.π (g, 1) (c⁻¹ • J y) = c⁻¹ • J (σ.π g y)
    rw [map_smul, hG]
    rfl

end GlobalTheory.HarmModule

end
