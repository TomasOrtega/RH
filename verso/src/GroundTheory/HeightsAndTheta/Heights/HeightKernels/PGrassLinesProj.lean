import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace GrassmannianLinesProjective

def single (m : ℕ) (c : Fin (m + 1)) : PlIdx 1 m :=
  ⟨{Fin.cast (Nat.add_comm m 1) c}, Finset.card_singleton _⟩

/- English proof (translation)
Introduce `c c' h`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[single]`.
-/
theorem single_injective (m : ℕ) : Function.Injective (single m) := by
  intro c c' h
  have := congrArg Subtype.val h
  simpa [single] using this

/- English proof (translation)
Introduce and unpack `⟨I, hI⟩`. Take `⟨a, rfl⟩` from `Finset.card_eq_one.mp hI`. Conclude with `⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩`.
-/
theorem single_surjective (m : ℕ) : Function.Surjective (single m) := by
  rintro ⟨I, hI⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩

def blk : Unit → Fin 1 := fun _ => 0

def coordMap (m : ℕ) : (Σ _ : Unit, Fin (m + 1)) → (Σ _ : Fin 1, PlIdx 1 m) :=
  fun p => ⟨0, single m p.2⟩

/- English proof (translation)
Introduce and unpack `⟨k, I⟩`. Take `⟨c, rfl⟩` from `single_surjective m I`. Use `⟨⟨(), c⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim k 0]`. Both sides reduce to the same expression.
-/
theorem coordMap_surjective (m : ℕ) : Function.Surjective (coordMap m) := by
  rintro ⟨k, I⟩
  obtain ⟨c, rfl⟩ := single_surjective m I
  refine ⟨⟨(), c⟩, ?_⟩
  rw [Subsingleton.elim k 0]
  rfl

/- English proof (translation)
Use `⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h`. Simplify using `only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h`. Rewrite using `[single_injective m h]`.
-/
theorem isBlockMap (m : ℕ) : IsBlockMap blk (coordMap m) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [single_injective m h]

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]`.
-/
theorem card_plIdx (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]

/- English proof (translation)
Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, Nat.card_eq_fintype_card]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ringKrullDim_mring {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ringKrullDim (MRing ι) = ((1 + Fintype.card (Σ k, ι k) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card]
  push_cast
  rfl

/- English proof (translation)
Establish `hA` using `GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hle` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m)) Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)`. Rewrite `hle` using `[hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma]`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle`. Establish `h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞)`. Conclude with `hle` after adjusting the coercions. Establish `h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1)` using `by exact_mod_cast h'`. Use linear arithmetic over natural numbers and integers.
-/
theorem grassIdeal_eq_bot (m : ℕ) : grassIdeal 1 1 m = ⊥ := by
  have hA := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle
  have h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hle
  have h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1) := by exact_mod_cast h'
  omega

/- English proof (translation)
Use `⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Conclude with `X_ne_zero _`. Conclude with `Ideal.comap_bot_of_injective _ (C_injective _ _)`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem isArithVar_bot (m : ℕ) : IsArithVar (⊥ : Ideal (MRing (PBlk (m + 1)))) (m + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]
    congr 1
    simp
    omega

/- English proof (translation)
Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[Subsingleton.elim k (blk ())]`. Use `show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())`. Conclude with `(Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm`.

Simplify using `only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]`. Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Use `congr 1`. Conclude with `((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm`.
-/
theorem isPullHerm (m : ℕ) :
    IsPullHerm blk (coordMap m) (fsMulti (PBlk (m + 1))) (fsMulti (plBlocks 1 1 m)) := by
  refine ⟨?_, fun z => ?_⟩
  · funext k
    rw [Subsingleton.elim k (blk ())]
    show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())
    exact (Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm
  · simp only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact ((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp
      (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm

/- English proof (translation)
Use `IntermediateField.adjoin_le_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `t ⟨p, q, -, rfl⟩`. Take `⟨p', rfl⟩` from `coordMap_surjective m p`. Take `⟨q', rfl⟩` from `coordMap_surjective m q`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩`.
-/
theorem blockFnField_le (m : ℕ) :
    blockFnField (grassCoord 1 1 m) ≤ blockFnField (grassCoord 1 1 m ∘ coordMap m) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro t ⟨p, q, -, rfl⟩
  obtain ⟨p', rfl⟩ := coordMap_surjective m p
  obtain ⟨q', rfl⟩ := coordMap_surjective m q
  exact IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩

end GrassmannianLinesProjective

open GrassmannianLinesProjective in

/- English proof (translation)
Introduce `m II hII`. Establish `hd : 1 * 1 * m + 1 = m + 1` using `by ring`. Establish `hA : IsArithVar (grassIdeal 1 1 m) (m + 1)`. Rewrite using `[← hd]`. Conclude with `GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl`.

Establish `himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥`. Rewrite using `[grassIdeal_eq_bot]`. Conclude with `Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)`. Establish `hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1)`. Rewrite using `[himg]`.

Conclude with `isArithVar_bot m`. Establish `h` using `hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m) (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m)) (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)`. Rewrite `h` using `[IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m), show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul]`. Rewrite using `[hd]`. Conclude with `h`.
-/
theorem GrassLinesProj.proof (hPF : PFCoordStatement) : GrassLinesProj.Statement := by
  intro m II hII
  have hd : 1 * 1 * m + 1 = m + 1 := by ring
  have hA : IsArithVar (grassIdeal 1 1 m) (m + 1) := by
    rw [← hd]
    exact GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  have himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥ := by
    rw [grassIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)
  have hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1) := by
    rw [himg]
    exact isArithVar_bot m
  have h := hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m)
    (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m))
    (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m),
    show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul] at h
  rw [hd]
  exact h

/- English proof (translation)
The claim follows from `GrassmannianLinesProjective.isBlockMap 1`.
-/
example : IsBlockMap GrassmannianLinesProjective.blk (GrassmannianLinesProjective.coordMap 1) :=
  GrassmannianLinesProjective.isBlockMap 1

end

end GroundTheory.Heights₂.Heights
