import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

/- English proof (translation)
Use `letI := f.toAlgebra`. Take `⟨k, g, hg⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf`. Use `⟨k, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]

/- English proof (translation)
Use `haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n`. Take `⟨U, hU, hyU, -⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)`. Use `⟨U, hyU, ?_⟩` and prove the remaining obligations. Establish `hZ` using `AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))`. Establish `hft` using `AlgebraicGeometry.LocallyOfFiniteType.finiteType_of_affine_subset (mpStr ℤ m n) hZ hU (by simp)`.

Use `haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) := isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv`. Take `⟨N, hN⟩` from `exists_ringKrullDim_le_add_of_finiteType _ hft`. Establish `hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]`. Establish `h1` using `Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)`.

Conclude with `h1` after adjusting the coercions. Use `haveI := hU.isOpenImmersion_fromSpec`. Establish `htop : topologicalKrullDim (U : Set (MP ℤ m n)) = ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))`. Rewrite using `[GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]`. Conclude with `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _`.

Use `⟨N + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[htop]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.LocallyOfFiniteType.finiteType_of_affine_subset (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

/- English proof (translation)
Use `haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n`. Use `haveI : CompactSpace (MP ℤ m n) := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)`. Use `choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n))) (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)`. Use `⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy, hzy⟩` from `Set.mem_iUnion₂.mp (ht (Set.mem_univ z))`. Use `⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩` and prove the remaining obligations. Conclude with `Finset.le_sup (f := N) hy` after adjusting the coercions.
-/
private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_topologicalKrullDim_MP_le (m := m) (n := n)`. Establish `hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d` using `(topologicalKrullDim_subspace_le _ _).trans hd`. Establish `hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n)))` using `by haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) := ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))}, isIrreducible_singleton.closure, isClosed_closure⟩⟩`. Unfold `topologicalKrullDim`. Conclude with `Order.krullDim_nonneg`.

Generalize the expression as in `topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))`. Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`.

Consider the case `top`. It suffices to derive a contradiction. Establish `h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞)` using `hle`. Conclude with `ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))`. Consider the case `coe e => exact ⟨e, rfl⟩`.
-/
theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

/- English proof (translation)
Introduce `m n x d hc`. Use `⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `exists_dim_closure_eq x`. Establish `h'` using `GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he`. Establish `h1` using `h.2.2.2`.

Establish `h2` using `h'.2.2.2`. Establish `hde : d = e`. Establish `h3` using `h1.symm.trans h2`. Establish `h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1))` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[he, hde]`.
-/
theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
