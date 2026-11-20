import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareIdxNOfCovBy
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareCardOfInvolution
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SubCount

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.set_biUnion_insert]`. Use `le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_` and prove the remaining obligations.

Rewrite using `[ENat.toENNReal_add]`. Use `gcongr`.
-/
theorem encard_biUnion_le_sum {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    ((⋃ i ∈ s, Y i).encard : ℝ≥0∞) ≤ ∑ i ∈ s, ((Y i).encard : ℝ≥0∞) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_
    rw [ENat.toENNReal_add]
    gcongr

/- English proof (translation)
Break down `S.finite_or_infinite with hS | hS` into its components or cases. Use `lift S to Finset ι using hS`. Use `(encard_biUnion_le_sum S Y).trans ((Finset.sum_le_card_nsmul S _ c h).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[Set.encard_coe_eq_coe_finsetCard, nsmul_eq_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hc]`. Conclude with `le_top`.
-/
theorem encard_biUnion_le_mul {ι β : Type} (S : Set ι) (Y : ι → Set β) (c : ℝ≥0∞) (hc : c ≠ 0)
    (h : ∀ i ∈ S, ((Y i).encard : ℝ≥0∞) ≤ c) :
    ((⋃ i ∈ S, Y i).encard : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * c := by
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset ι using hS
    refine (encard_biUnion_le_sum S Y).trans ((Finset.sum_le_card_nsmul S _ c h).trans (le_of_eq ?_))
    rw [Set.encard_coe_eq_coe_finsetCard, nsmul_eq_mul]
    simp
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hc]
    exact le_top

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM`. Use `haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V`. Use `haveI : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation`. Establish `hr : finrank (𝓞 K) M ≤ finrank K V`.

Use `Module.finrank_le_of_rank_le ((Submodule.rank_le M).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[Module.finrank_eq_rank, IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]`. Take `⟨h1, h2⟩` from `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (finrank K V) j hj hr`. Use `le_trans ?_ (ENNReal.ofReal_le_ofReal h2)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, h1.cast_ncard_eq, ENat.toENNReal_le]`.

Use `Set.encard_le_encard_of_injOn (f := fun P => P.comap M.subtype) (fun P hP => hP.2) ?_` and prove the remaining obligations. Introduce `P hP Q hQ e`. Use `congrArg (Submodule.map M.subtype) e` as an intermediate fact. Simplify `this` using `only [Submodule.map_comap_subtype, inf_eq_right.2 hP.1, inf_eq_right.2 hQ.1]`.
-/
theorem index_eq (M : Submodule (𝓞 K) V) (hM : M.FG) (j : ℕ) (hj : 1 ≤ j) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((j : ℝ) ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : finrank (𝓞 K) M ≤ finrank K V := by
    refine Module.finrank_le_of_rank_le ((Submodule.rank_le M).trans (le_of_eq ?_))
    rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
  obtain ⟨h1, h2⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (finrank K V) j hj hr
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal h2)
  rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, h1.cast_ncard_eq, ENat.toENNReal_le]
  refine Set.encard_le_encard_of_injOn (f := fun P => P.comap M.subtype) (fun P hP => hP.2) ?_
  intro P hP Q hQ e
  have := congrArg (Submodule.map M.subtype) e
  simpa only [Submodule.map_comap_subtype, inf_eq_right.2 hP.1, inf_eq_right.2 hQ.1] using this

/- English proof (translation)
Establish `he : 0 ≤ (finrank K V : ℝ) + Real.logb 2 (finrank ℚ K)` using `add_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos))`. Combine the equalities or inequalities in the displayed calculation. Use `ENat.toENNReal_le.2 (Set.encard_le_encard fun P hP => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨_, Finset.mem_Icc.2 ⟨hP.2.1, Nat.le_floor hP.2.2⟩, hP.1, rfl⟩`.

Use `_ ≤ _ := encard_biUnion_le_sum _ _`. Use `_ ≤ (Finset.Icc 1 ⌊x⌋₊).card • ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by`. Use `Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Use `(index_eq M hM j h1).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations.

Conclude with `Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.le_floor_iff hx.le).1 h2) he`. Use `_ ≤ _ := by`. Rewrite using `[Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.rpow_add_one hx.ne', ENNReal.ofReal_mul' hx.le, mul_comm, ← ENNReal.ofReal_natCast]`. Use `gcongr`. Conclude with `Nat.floor_le hx.le`.
-/
theorem index_le (M : Submodule (𝓞 K) V) (hM : M.FG) (x : ℝ) (hx : 0 < x) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
      (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ x}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) + 1)) := by
  have he : 0 ≤ (finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) :=
    add_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos))
  calc _ ≤ ((⋃ j ∈ Finset.Icc 1 ⌊x⌋₊,
        {P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard fun P hP => ?_)
        simp only [Set.mem_iUnion]
        exact ⟨_, Finset.mem_Icc.2 ⟨hP.2.1, Nat.le_floor hP.2.2⟩, hP.1, rfl⟩
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ (Finset.Icc 1 ⌊x⌋₊).card • ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
        refine (index_eq M hM j h1).trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.le_floor_iff hx.le).1 h2) he
    _ ≤ _ := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.rpow_add_one hx.ne',
          ENNReal.ofReal_mul' hx.le, mul_comm, ← ENNReal.ofReal_natCast]
        gcongr
        exact Nat.floor_le hx.le

end Index

/- English proof (translation)
Introduce `D L hpos hk hL hint n De hDe`. Establish `hf : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ)`. Rewrite using `[(GlobalTheory.real_places_facts D).2.1]`. Use `push_cast`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Use `ENat.toENNReal_le.2 (Set.encard_le_encard ?_)` and prove the remaining obligations. Introduce and unpack `P ⟨hP, hr, hd⟩`. Establish `hS : sat D L P ≤ L` using `inf_le_left`. Establish `hPS : P ≤ sat D L P` using `fun x hx => ⟨hP hx, Submodule.subset_span hx⟩`.

Establish `hfg : (sat D L P).FG` using `hL.of_le hS`. Establish `hi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P)` using `fun x hx y hy => hint x (hS hx) y (hS hy)`. Establish `hsp : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) = Submodule.span D.host.E (P : Set (D.sp.X 0).V)` using `le_antisymm (Submodule.span_le.2 fun x hx => hx.2) (Submodule.span_mono hPS)`. Establish `hrk : rkW D P = rkW D (sat D L P)` using `by unfold rkW; rw [hsp]`. Take `⟨h4, h5⟩` from `(GlobalTheory.LoopC.DetCard.main D _ hfg hpos hi).2.2 P hPS hrk`.

Establish `ha : ∀ x : (D.sp.X 0).V, (D.sp.X 0).hT x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Take `⟨τ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Use `hpos τ x h0` as an intermediate fact.

Rewrite `this` using `[hx]`. Simplify using `at this`. Take `⟨de, h1, h2⟩` from `GlobalTheory.Mass.DetNat.main D.host.E (D.sp.X 0) D.sp.cm.cmUnram.2.1 (GlobalTheory.InertSquareNorm.isSquare_absNorm _ D.sp.cm.cmUnram) ha _ hfg fun x hx => ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => hi y hy x hx, Submodule.subset_span hx⟩`. Establish `h3 : detW D (sat D L P) = de` using `h2`. Establish `hde : (1 : ℝ) ≤ de` using `by exact_mod_cast h1`.

Establish `hj : (1 : ℝ) ≤ idxW D (sat D L P) P` using `by exact_mod_cast h4`. Rewrite `hd` using `[h5, h3]`. Simplify using `only [Set.mem_iUnion]`. Use `⟨de, Finset.mem_Icc.2 ⟨h1, Nat.le_floor (by nlinarith)⟩, sat D L P, ⟨⟨hS, by rw [hsp]; rfl⟩, hrk.symm.trans hr, h2⟩, hPS, h4, ?_⟩` and prove the remaining obligations. Rewrite using `[le_div_iff₀' (by linarith)]`.

Conclude with `hd`. Use `_ ≤ _ := encard_biUnion_le_sum _ _`. Use `_ ≤ _ := by`. Use `Finset.sum_le_sum fun de hde => ?_` and prove the remaining obligations. Establish `h1 : (0 : ℝ) < de` using `by exact_mod_cast (Finset.mem_Icc.1 hde).1`.

Establish `hx : 0 < De / (de : ℝ)` using `div_pos (by linarith) h1`. Use `encard_biUnion_le_mul _ _ _ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne' fun M hM => ?_` and prove the remaining obligations. Use `index_le (K := D.host.E) M (hL.of_le hM.1.1) _ hx` as an intermediate fact. Rewrite `this` using `[hk, hf]`. Then use the resulting hypothesis.
-/
theorem main : ∀ (D : D7) (L : LatW D), IsPosDef (D.sp.X 0).hT → finrank D.host.E (D.sp.X 0).V = D.R.k → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → ∀ (n : ℕ) (De : ℝ), 1 ≤ De → (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ De} : ℝ≥0∞) ≤ ∑ de ∈ Finset.Icc 1 ⌊De⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) * ENNReal.ofReal ((De / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  intro D L hpos hk hL hint n De hDe
  have hf : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [(GlobalTheory.real_places_facts D).2.1]; push_cast; rfl
  calc _ ≤ ((⋃ de ∈ Finset.Icc 1 ⌊De⌋₊, ⋃ M ∈ PrimSubs (D.sp.X 0).hT L n de,
        {P : LatW D | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
          (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ De / (de : ℝ)}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro P ⟨hP, hr, hd⟩
        have hS : sat D L P ≤ L := inf_le_left
        have hPS : P ≤ sat D L P := fun x hx => ⟨hP hx, Submodule.subset_span hx⟩
        have hfg : (sat D L P).FG := hL.of_le hS
        have hi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) :=
          fun x hx y hy => hint x (hS hx) y (hS hy)
        have hsp : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) =
            Submodule.span D.host.E (P : Set (D.sp.X 0).V) :=
          le_antisymm (Submodule.span_le.2 fun x hx => hx.2) (Submodule.span_mono hPS)
        have hrk : rkW D P = rkW D (sat D L P) := by unfold rkW; rw [hsp]
        obtain ⟨h4, h5⟩ := (GlobalTheory.LoopC.DetCard.main D _ hfg hpos hi).2.2 P hPS hrk
        have ha : ∀ x : (D.sp.X 0).V, (D.sp.X 0).hT x x = 0 → x = 0 := by
          intro x hx
          by_contra h0
          obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
          have := hpos τ x h0
          rw [hx] at this
          simp at this
        obtain ⟨de, h1, h2⟩ := GlobalTheory.Mass.DetNat.main D.host.E (D.sp.X 0) D.sp.cm.cmUnram.2.1
          (GlobalTheory.InertSquareNorm.isSquare_absNorm _ D.sp.cm.cmUnram) ha _ hfg fun x hx =>
            ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => hi y hy x hx, Submodule.subset_span hx⟩
        have h3 : detW D (sat D L P) = de := h2
        have hde : (1 : ℝ) ≤ de := by exact_mod_cast h1
        have hj : (1 : ℝ) ≤ idxW D (sat D L P) P := by exact_mod_cast h4
        rw [h5, h3] at hd
        simp only [Set.mem_iUnion]
        refine ⟨de, Finset.mem_Icc.2 ⟨h1, Nat.le_floor (by nlinarith)⟩, sat D L P,
          ⟨⟨hS, by rw [hsp]; rfl⟩, hrk.symm.trans hr, h2⟩, hPS, h4, ?_⟩
        rw [le_div_iff₀' (by linarith)]
        exact hd
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun de hde => ?_
        have h1 : (0 : ℝ) < de := by exact_mod_cast (Finset.mem_Icc.1 hde).1
        have hx : 0 < De / (de : ℝ) := div_pos (by linarith) h1
        refine encard_biUnion_le_mul _ _ _ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne' fun M hM => ?_
        have := index_le (K := D.host.E) M (hL.of_le hM.1.1) _ hx
        rwa [hk, hf] at this

end GlobalTheory.LoopC.SubCount
