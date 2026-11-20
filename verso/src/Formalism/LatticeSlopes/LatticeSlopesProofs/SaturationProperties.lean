import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality

open Module Submodule

noncomputable section

namespace Formalism.F

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem rank_eq_finrank_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : Submodule ℤ E) [hN : DiscreteTopology N] :
    rk N = finrank ℝ (span ℝ (N : Set E)) := by

  let V := span ℝ (N : Set E)
  let N' : Submodule ℤ V := N.comap (V.subtype.restrictScalars ℤ)
  let φ : N' ≃ₗ[ℤ] N :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology N' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : N' => (⟨((x : V) : E), x.2⟩ : N))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ N' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ N')

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem saturation_properties : SaturProps := by
  intro E _ _ _ L N hL hNL
  haveI := hL
  have hSL : satur L N ≤ L := inf_le_left
  have hNS : N ≤ satur L N := fun x hx => ⟨hNL hx, Submodule.subset_span hx⟩
  have hspan : span ℝ (satur L N : Set E) = span ℝ (N : Set E) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      exact fun x hx => hx.2
    · exact Submodule.span_mono hNS
  refine ⟨⟨hSL, fun x hx hxs => ⟨hx, ?_⟩⟩, hNS, ?_⟩
  · rw [hspan] at hxs
    exact hxs
  · haveI : DiscreteTopology (satur L N) := DiscreteTopology.of_subset (s := (L : Set E)) hL hSL
    haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
    rw [rank_eq_finrank_span, rank_eq_finrank_span, hspan]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem linearIndependent_coe_basis_of_discrete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR,
    ← rank_eq_finrank_span L]
  exact (Module.finrank_eq_card_basis e).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem covol_anti_same_rank : CovolAntiSameRank := by
  intro E _ _ _ N N' hN' hle hrk
  haveI := hN'
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (N' : Set E)) hN' hle
  let e := Module.finBasis ℤ N'
  let f : Basis (Fin (Module.finrank ℤ N')) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hrk)
  let M : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    fun i j => e.repr ⟨(f j : E), hle (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M.map (Int.cast : ℤ → ℝ)) i j • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hle (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    show (f j : E) = ∑ i, ((M i j : ℤ) : ℝ) • (e i : E)
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm

  have hgram : Matrix.gram ℝ (fun j => (f j : E))
      = (M.map (Int.cast : ℤ → ℝ)).transpose * Matrix.gram ℝ (fun i => (e i : E))
        * M.map (Int.cast : ℤ → ℝ) := by
    rw [← gram_sum_smul_eq_transpose_mul]
    congr 1
    funext j
    exact hfj j
  have hdetM : (M.map (Int.cast : ℤ → ℝ)).det = ((M.det : ℤ) : ℝ) := by
    rw [← eq_intCast (Int.castRingHom ℝ), RingHom.map_det]
    rfl
  have hdet : (Matrix.gram ℝ (fun j => (f j : E))).det
      = ((M.det : ℤ) : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (e i : E))).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetM]
    ring
  have hfpos : 0 < (Matrix.gram ℝ (fun j => (f j : E))).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis_of_discrete N f)).det_pos
  have hepos : 0 < (Matrix.gram ℝ (fun i => (e i : E))).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis_of_discrete N' e)).det_pos
  have hM0 : M.det ≠ 0 := by
    intro h0
    rw [hdet, h0] at hfpos
    simp at hfpos
  have hM1 : (1 : ℝ) ≤ ((M.det : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |M.det| := Int.one_le_abs hM0
    have h2 : (1 : ℤ) ≤ M.det ^ 2 := by
      rw [← sq_abs]
      nlinarith
    exact_mod_cast h2
  have hcovN' : covol N' = Real.sqrt (Matrix.gram ℝ (fun i => (e i : E))).det := by
    rw [covol, dif_pos hN']
  have hcovN : covol N = Real.sqrt (Matrix.gram ℝ (fun j => (f j : E))).det := by
    rw [covol, dif_pos hN, det_gram_basis_eq N (Module.finBasis ℤ N) f]
  rw [hcovN', hcovN, hdet]
  apply Real.sqrt_le_sqrt
  nlinarith

end Formalism.F
