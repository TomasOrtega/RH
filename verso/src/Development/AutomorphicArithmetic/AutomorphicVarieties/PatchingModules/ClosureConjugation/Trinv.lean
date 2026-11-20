import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DQuotDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnopMemCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

/- English proof (translation)
Introduce `l _ F n O _ _ _ _ _ r B _ _ _ u hΦ hn Z hZ`. Use `letI := F.grp`. Use `letI := F.top`. Use `haveI := F.tgrp`. Use `haveI := F.cpt`.

Use `haveI := F.tdisc`. Use `haveI : CompactSpace F.G₀ := by`. Establish `hc : IsClosed (F.η.ker : Set F.Γ)` using `Subgroup.isClosed_of_isOpen _ F.η_open`. Conclude with `isCompact_iff_compactSpace.mp hc.isCompact`. Take `⟨DE, hCH, hpull⟩` from `d_quotDet u.D u.cont Z (fun z hz => (hZ z hz).1)`.

Establish `hl : ((l : ℕ) : B) ∈ maximalIdeal B`. Establish `h1 : ((l : ℕ) : O) ∈ maximalIdeal O` using `by haveI := (IsCoef.char (l := l) (O := O))`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `CharP.cast_eq_zero _ l`. Rewrite using `[← map_natCast (algebraMap O B), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `fun hu => ((IsLocalRing.mem_maximalIdeal _).mp h1) (isUnit_of_map_unit (algebraMap O B) _ hu)`. Establish `hM : Submodule.span B ((MonoidHom.mrange (MonoidAlgebra.of B F.G₀) : Submonoid (MonoidAlgebra B F.G₀)) : Set (MonoidAlgebra B F.G₀)) = ⊤`. Rewrite using `[Submodule.eq_top_iff']`. Introduce `x`. Use `MonoidAlgebra.induction_on x ?_ ?_ ?_` and prove the remaining obligations.

Introduce `m`. Conclude with `Submodule.subset_span ⟨m, rfl⟩`. Introduce `x y hx hy`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `b x hx`.

Conclude with `Submodule.smul_mem _ b hx`. Establish `hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of B F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n → u.D.toDet.lam i (MulOpposite.unop (F.starOp O B n x)) = u.D.toDet.lam i x`. Introduce and unpack `_ ⟨g, rfl⟩ i _ _`. Rewrite using `[(d_toDet u.D _).2.1, (d_toDet u.D _).2.1]`. Conclude with `u.P i g`.

Take `⟨hop, hCHs, -⟩` from `d_star u.D.toDet (F.starOp O B n) _ hM hlam`. Establish `hstarCH : ∀ z ∈ u.D.CH, F.star O B n z ∈ TwoSidedIdeal.span (u.D.CH ∪ Z)`. Introduce `z hz`. Establish `hz' : z ∈ u.D.toDet.CH`. Rewrite using `[d_toDet_CH]`.

Conclude with `TwoSidedIdeal.subset_span hz`. Establish `h2` using `hCHs z hz'`. Rewrite `h2` using `[d_toDet_CH]`. Conclude with `TwoSidedIdeal.span_mono Set.subset_union_left h2`. Establish `hI : ∀ y, y ∈ u.D.chBar Z → F.star O B n y ∈ u.D.chBar Z`.

Unfold `GDet.chBar`. Use `star_closure F n O B (maximalIdeal B) (u.D.CH ∪ Z) hl ?_` and prove the remaining obligations. Introduce and unpack `z (hz | hz)`. Conclude with `hstarCH z hz`. Conclude with `TwoSidedIdeal.subset_span (Or.inr (hZ z hz).2)`.

Establish `hq : ∀ a b, u.D.toQuot Z a = u.D.toQuot Z b ↔ a - b ∈ u.D.chBar Z`. Introduce `a b`. Unfold `GDet.toQuot`. Conclude with `Iff.trans (RingCon.eq _) (TwoSidedIdeal.rel_iff _ _ _)`. Establish `hsurj : Function.Surjective (u.D.toQuot Z)` using `RingCon.mkₐ_surjective _`.

Set `ψ : u.D.CHQuot Z →ₐ[B] (u.D.CHQuot Z)ᵐᵒᵖ` to `RingCon.liftₐ (u.D.chBar Z).ringCon ((AlgHom.op (u.D.toQuot Z)).comp (F.starOp O B n)) (by`. Introduce `a b hab`. Rewrite `hab` using `[TwoSidedIdeal.rel_iff]`. Use `show MulOpposite.op (u.D.toQuot Z (F.star O B n a)) = MulOpposite.op (u.D.toQuot Z (F.star O B n b))`. Use `congr 1`.

Rewrite using `[hq, ← (star_basic F n O B).2.2.2.2.2.1]`. Conclude with `hI _ hab)`. Establish `hψ : ∀ y, MulOpposite.unop (ψ (u.D.toQuot Z y)) = u.D.toQuot Z (F.star O B n y)` using `fun y => rfl`. Take `⟨t, ht⟩` from `(d_tr DE).1 hn`. Establish `htq : ∀ w, DE.tr (u.D.toQuot Z w) = u.D.toDet.tr w`.

Introduce `w`. Use `show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi w).coeff (n - 1)`. Rewrite using `[← hpull, (d_pull DE (u.D.toQuot Z)).1 w]`. Establish `hinv : ∀ w, u.D.toDet.chi (F.star O B n w) = u.D.toDet.chi w`. Introduce `w`.

Use `conv_rhs => rw [← hop]`. Rewrite using `[(d_pull _ (F.starOp O B n)).1 w]`. Conclude with `((d_op _).1 (F.star O B n w)).symm`. Use `⟨DE, { st := { toFun := fun x => MulOpposite.unop (ψ x) map_add' := fun x y => by simp map_smul' := fun b x => by simp } st_mul := fun x y => by simp st_st := ?_ tr := t tr_comm := ?_ tr_st := ?_ }, hCH, hpull, fun y => hψ y, fun y => ht y⟩` and prove the remaining obligations. Introduce `x`.

Take `⟨y, rfl⟩` from `hsurj x`. Express the relevant statement in the definitionally equal form `MulOpposite.unop (ψ (MulOpposite.unop (ψ (u.D.toQuot Z y)))) = u.D.toQuot Z y`. Rewrite using `[hψ, hψ, (star_basic F n O B).1]`. Introduce `x y`. Rewrite using `[ht, ht]`.

Conclude with `(d_tr DE).2.1 1 x y`. Introduce `x`. Take `⟨y, rfl⟩` from `hsurj x`. Express the relevant statement in the definitionally equal form `t (MulOpposite.unop (ψ (u.D.toQuot Z y))) = t (u.D.toQuot Z y)`. Rewrite using `[hψ, ht, ht, htq, htq]`.

Use `show (-1) ^ 1 * (u.D.toDet.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi y).coeff (n - 1)`. Rewrite using `[hinv]`.
-/
theorem UpperTheory.V.Pa.trinv :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → 1 ≤ n → ∀ Z : Set (MonoidAlgebra B F.G₀), (∀ z ∈ Z, u.D.Kills z ∧ F.star O B n z ∈ Z) → ∃ (DE : Det n B (u.D.CHQuot Z)) (T : TrInv B (u.D.CHQuot Z)), DE.IsCH ∧ DE.pull (u.D.toQuot Z) = u.D.toDet ∧ (∀ y, T.st (u.D.toQuot Z y) = u.D.toQuot Z (F.star O B n y)) ∧ ∀ y, T.tr y = DE.tr y := by
  intro l _ F n O _ _ _ _ _ r B _ _ _ u hΦ hn Z hZ
  letI := F.grp
  letI := F.top
  haveI := F.tgrp
  haveI := F.cpt
  haveI := F.tdisc
  haveI : CompactSpace F.G₀ := by
    have hc : IsClosed (F.η.ker : Set F.Γ) := Subgroup.isClosed_of_isOpen _ F.η_open
    exact isCompact_iff_compactSpace.mp hc.isCompact
  obtain ⟨DE, hCH, hpull⟩ := d_quotDet u.D u.cont Z (fun z hz => (hZ z hz).1)
  have hl : ((l : ℕ) : B) ∈ maximalIdeal B := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      haveI := (IsCoef.char (l := l) (O := O))
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    rw [← map_natCast (algebraMap O B), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp h1) (isUnit_of_map_unit (algebraMap O B) _ hu)
  have hM : Submodule.span B
      ((MonoidHom.mrange (MonoidAlgebra.of B F.G₀) : Submonoid (MonoidAlgebra B F.G₀)) :
        Set (MonoidAlgebra B F.G₀)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    refine MonoidAlgebra.induction_on x ?_ ?_ ?_
    · intro m
      exact Submodule.subset_span ⟨m, rfl⟩
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro b x hx
      exact Submodule.smul_mem _ b hx
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of B F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      u.D.toDet.lam i (MulOpposite.unop (F.starOp O B n x)) = u.D.toDet.lam i x := by
    rintro _ ⟨g, rfl⟩ i _ _
    rw [(d_toDet u.D _).2.1, (d_toDet u.D _).2.1]
    exact u.P i g
  obtain ⟨hop, hCHs, -⟩ := d_star u.D.toDet (F.starOp O B n) _ hM hlam
  have hstarCH : ∀ z ∈ u.D.CH, F.star O B n z ∈ TwoSidedIdeal.span (u.D.CH ∪ Z) := by
    intro z hz
    have hz' : z ∈ u.D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    have h2 := hCHs z hz'
    rw [d_toDet_CH] at h2
    exact TwoSidedIdeal.span_mono Set.subset_union_left h2
  have hI : ∀ y, y ∈ u.D.chBar Z → F.star O B n y ∈ u.D.chBar Z := by
    unfold GDet.chBar
    refine star_closure F n O B (maximalIdeal B) (u.D.CH ∪ Z) hl ?_
    rintro z (hz | hz)
    · exact hstarCH z hz
    · exact TwoSidedIdeal.subset_span (Or.inr (hZ z hz).2)
  have hq : ∀ a b, u.D.toQuot Z a = u.D.toQuot Z b ↔ a - b ∈ u.D.chBar Z := by
    intro a b
    unfold GDet.toQuot
    exact Iff.trans (RingCon.eq _) (TwoSidedIdeal.rel_iff _ _ _)
  have hsurj : Function.Surjective (u.D.toQuot Z) := RingCon.mkₐ_surjective _
  let ψ : u.D.CHQuot Z →ₐ[B] (u.D.CHQuot Z)ᵐᵒᵖ :=
    RingCon.liftₐ (u.D.chBar Z).ringCon ((AlgHom.op (u.D.toQuot Z)).comp (F.starOp O B n)) (by
      intro a b hab
      rw [TwoSidedIdeal.rel_iff] at hab
      show MulOpposite.op (u.D.toQuot Z (F.star O B n a)) = MulOpposite.op (u.D.toQuot Z (F.star O B n b))
      congr 1
      rw [hq, ← (star_basic F n O B).2.2.2.2.2.1]
      exact hI _ hab)
  have hψ : ∀ y, MulOpposite.unop (ψ (u.D.toQuot Z y)) = u.D.toQuot Z (F.star O B n y) := fun y => rfl
  obtain ⟨t, ht⟩ := (d_tr DE).1 hn
  have htq : ∀ w, DE.tr (u.D.toQuot Z w) = u.D.toDet.tr w := by
    intro w
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (u.D.toQuot Z)).1 w]
  have hinv : ∀ w, u.D.toDet.chi (F.star O B n w) = u.D.toDet.chi w := by
    intro w
    conv_rhs => rw [← hop]
    rw [(d_pull _ (F.starOp O B n)).1 w]
    exact ((d_op _).1 (F.star O B n w)).symm
  refine ⟨DE,
    { st := { toFun := fun x => MulOpposite.unop (ψ x)
              map_add' := fun x y => by simp
              map_smul' := fun b x => by simp }
      st_mul := fun x y => by simp
      st_st := ?_
      tr := t
      tr_comm := ?_
      tr_st := ?_ }, hCH, hpull, fun y => hψ y, fun y => ht y⟩
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change MulOpposite.unop (ψ (MulOpposite.unop (ψ (u.D.toQuot Z y)))) = u.D.toQuot Z y
    rw [hψ, hψ, (star_basic F n O B).1]
  · intro x y
    rw [ht, ht]
    exact (d_tr DE).2.1 1 x y
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    change t (MulOpposite.unop (ψ (u.D.toQuot Z y))) = t (u.D.toQuot Z y)
    rw [hψ, ht, ht, htq, htq]
    show (-1) ^ 1 * (u.D.toDet.chi _).coeff (n - 1) = (-1) ^ 1 * (u.D.toDet.chi y).coeff (n - 1)
    rw [hinv]
