import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldTwoVocabulariesDictionaryStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `GlobalTheory.PrinTwo.NoFix.exists_unif k`. Establish `hex : ∃ p : kˣ, valuation k (p : k) < 1 ∧ ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k)`. Use `⟨ϖ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hϖ]`. Conclude with `uniformizer_lt_one (R := k)`.

Introduce `x hx`. Rewrite using `[hϖ]`. Conclude with `le_uniformizer_iff.mpr hx`. Establish `hs` using `Classical.epsilon_spec hex`. Unfold `unif`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_uniformizer_iff.mpr hs.1`. Rewrite using `[← hϖ]`. Use `hs.2 _ ?_` and prove the remaining obligations. Rewrite using `[hϖ]`.

Conclude with `uniformizer_lt_one (R := k)`.
-/
private theorem unif_valuation : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hex : ∃ p : kˣ, valuation k (p : k) < 1 ∧
      ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := by
    refine ⟨ϖ, ?_, ?_⟩
    · rw [hϖ]
      exact uniformizer_lt_one (R := k)
    · intro x hx
      rw [hϖ]
      exact le_uniformizer_iff.mpr hx
  have hs := Classical.epsilon_spec hex
  unfold unif
  apply le_antisymm
  · exact le_uniformizer_iff.mpr hs.1
  · rw [← hϖ]
    refine hs.2 _ ?_
    rw [hϖ]
    exact uniformizer_lt_one (R := k)

/- English proof (translation)
Rewrite using `[val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one unif_valuation]`. Use `push_cast`. Rewrite using `[Complex.cpow_neg_one, zpow_neg_one, inv_inv]`. Both sides reduce to the same expression.
-/
private theorem absPow_neg_one_unif :
    (((absPow k (-1)) (unif k) : ℂˣ) : ℂ) = (GroundTheory.LocalField.residueCard k : ℂ) := by
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one unif_valuation]
  push_cast
  rw [Complex.cpow_neg_one, zpow_neg_one, inv_inv]
  rfl

/- English proof (translation)
Introduce `hj`. Establish `hi : ω i ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i))` using `⟨hω i, Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩⟩`. Establish `hj' : ω j ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i))` using `⟨hω j, Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩⟩`. Establish `h0 : absPow k (-1) * absPow k 1 = 1`. Rewrite using `[← absPow_add]`.

Use extensionality with `x`. Simplify using `[val_absPow]`. Establish `hq : ω i * (ω j)⁻¹ = absPow k (-1)`. Rewrite using `[hj, mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]`. Conclude with `(eq_inv_of_mul_eq_one_left h0).symm`.

Apply `h (ω i) hi (ω j) hj'` to reduce the goal to its premises. Rewrite using `[hq]`. Conclude with `isUnram_absPow k (-1)`. Rewrite using `[hq]`. Conclude with `absPow_neg_one_unif`.
-/
private theorem ne_mul_absPow {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : Unl (GroundTheory.LocalField.residueCard k) (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)))
    (i j : Fin n) : ω j ≠ ω i * absPow k 1 := by
  intro hj
  have hi : ω i ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) :=
    ⟨hω i, Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩⟩
  have hj' : ω j ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) :=
    ⟨hω j, Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩⟩
  have h0 : absPow k (-1) * absPow k 1 = 1 := by
    rw [← absPow_add]
    ext x
    simp [val_absPow]
  have hq : ω i * (ω j)⁻¹ = absPow k (-1) := by
    rw [hj, mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    exact (eq_inv_of_mul_eq_one_left h0).symm
  apply h (ω i) hi (ω j) hj'
  · rw [hq]
    exact isUnram_absPow k (-1)
  · rw [hq]
    exact absPow_neg_one_unif

/- English proof (translation)
Establish `hd : ∑ a : Fin n, (IrrGL.ofChar (ω a) (hω a)).fst = n`. Simplify using `[IrrGL.ofChar]`. Establish `hirr : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).IsIrreducible`. Use `GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (IrrGL.ofChar (ω i) (hω i)) (IrrGL.isCusp_ofChar _ _)) _ hd ?_ ?_` and prove the remaining obligations. Introduce `i j`.

Apply `GlobalTheory.CompanionTheory.BZPair.not_linked_single` to reduce the goal to its premises. Unfold `IrrGL.nu`. Rewrite using `[IrrGL.tw_ofChar]`. Introduce `he`. Conclude with `h i j (IrrGL.ofChar_inj.mp he)`.

Unfold `IrrGL.nu`. Rewrite using `[IrrGL.tw_ofChar]`. Introduce `he`. Conclude with `h j i (IrrGL.ofChar_inj.mp he)`. Introduce `i`.

Conclude with `(single_spec (IrrGL.isCusp_ofChar (ω i) (hω i))).2.1`. Set `e1` to `stdBlocks (fun a => (IrrGL.ofChar (ω a) (hω a)).fst) hd`. Establish `E1 : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).Equiv (multiProd e1 fun a => detRep (Fin 1) (ω a))` using `multiProdEquiv e1 (fun a => (equivRep (IrrRep.det (Fin 1) (ω a) (hω a))).symm)`. Take `⟨E2⟩` from `(Placing.parInd_jac_placing k (Fin n) (Fin n) (fun _ => Fin 1) e1 (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) _).1 (piTensor fun a => detRep (Fin 1) (ω a))`. Establish `hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun a => detRep (Fin 1) (ω a)).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr`.

Use `haveI := nontrivial_of_irreducible hM`. Use `haveI := nontrivial_of_isSubquotient (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ω)`. Take `⟨E3⟩` from `equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv E3 hM`.
-/
private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  classical
  have hd : ∑ a : Fin n, (IrrGL.ofChar (ω a) (hω a)).fst = n := by
    simp [IrrGL.ofChar]
  have hirr : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).IsIrreducible := by
    refine GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n
      (fun i => Segment.single (IrrGL.ofChar (ω i) (hω i)) (IrrGL.isCusp_ofChar _ _)) _ hd ?_ ?_
    · intro i j
      apply GlobalTheory.CompanionTheory.BZPair.not_linked_single
      · unfold IrrGL.nu
        rw [IrrGL.tw_ofChar]
        intro he
        exact h i j (IrrGL.ofChar_inj.mp he)
      · unfold IrrGL.nu
        rw [IrrGL.tw_ofChar]
        intro he
        exact h j i (IrrGL.ofChar_inj.mp he)
    · intro i
      exact (single_spec (IrrGL.isCusp_ofChar (ω i) (hω i))).2.1
  let e1 := stdBlocks (fun a => (IrrGL.ofChar (ω a) (hω a)).fst) hd
  have E1 : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).Equiv
      (multiProd e1 fun a => detRep (Fin 1) (ω a)) :=
    multiProdEquiv e1 (fun a => (equivRep (IrrRep.det (Fin 1) (ω a) (hω a))).symm)
  obtain ⟨E2⟩ := (Placing.parInd_jac_placing k (Fin n) (Fin n) (fun _ => Fin 1) e1
    (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) _).1 (piTensor fun a => detRep (Fin 1) (ω a))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      fun a => detRep (Fin 1) (ω a)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr
  haveI := nontrivial_of_irreducible hM
  haveI := nontrivial_of_isSubquotient
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ω)
  obtain ⟨E3⟩ := equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E3 hM

end Loc

/- English proof (translation)
Introduce `k _ _ _ _ _ n V _ _ π ω hω hs hu`. Take `⟨hi, hq⟩` from `(UpperTheory.Gal.LocD.ofSupport_holds k n V π ω hω).1 hs`. Take `⟨E⟩` from `hq.nonempty_equiv hi (prinSeries_irreducible ω hω (ne_mul_absPow ω hω hu))`. Conclude with `⟨E.symm⟩`.
-/
theorem unlFull : UnlFull := by
  intro k _ _ _ _ _ n V _ _ π ω hω hs hu
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V π ω hω).1 hs
  obtain ⟨E⟩ := hq.nonempty_equiv hi (prinSeries_irreducible ω hω (ne_mul_absPow ω hω hu))
  exact ⟨E.symm⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
