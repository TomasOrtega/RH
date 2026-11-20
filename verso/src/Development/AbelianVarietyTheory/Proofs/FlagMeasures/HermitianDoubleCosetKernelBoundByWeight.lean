import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimatesStatement

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernelWeight

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
/- English proof (translation)
Establish `h` using `_root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y`. Rewrite `h` using `[add_sub_cancel_right]`. Take the linear combination `-h`.
-/
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y`.
-/
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y

def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y

/- English proof (translation)
Establish `hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j)`. Apply `Subgroup.inv_mem` to reduce the goal to its premises. Conclude with `Subgroup.mem_iInf.1 hn.1.2 j`. Establish `h1 : n⁻¹ x ∈ S.spanTo g (j + 1)` using `(hu.1 x).2 hx`. Establish `h2 : n⁻¹ x - x ∈ S.spanTo g j` using `hu.2 x hx`.

Establish `h3 : n⁻¹ x ∈ Submodule.span E (Set.range g)` using `Submodule.span_mono (Set.image_subset_range _ _) h1`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 h3`. Establish `h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Establish `hi' : (i : ℕ) < j` using `hi`. Establish `: i ≠ j.castSucc`. Introduce and unpack `rfl`. Simplify using `at hi'`. Use `show hf L S.Hm (g i) (gs j) = 0`.

Rewrite using `[hd, if_neg this]`. Establish `h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x`. Use `h4 h2` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations.

Establish `: x = n (n⁻¹ x)` using `(n.apply_symm_apply x).symm`. Rewrite using `[this, ← hc, map_sum]`. Simplify using the standard rewrite rules. Use `show _ = hfLin L S.Hm (gs j) x`. Rewrite using `[← h5, ← hc, map_sum]`.

Establish `: ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0`. Introduce `i`. Rewrite using `[map_smul]`. Use `show c i * hf L S.Hm (g i) (gs j) = _`. Apply the tactic sequence `rw [hd]; split_ifs <;> simp`.

Simplify using `[this]`.
-/
theorem exists_coord {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j) := by
    apply Subgroup.inv_mem
    exact Subgroup.mem_iInf.1 hn.1.2 j
  have h1 : n⁻¹ x ∈ S.spanTo g (j + 1) := (hu.1 x).2 hx
  have h2 : n⁻¹ x - x ∈ S.spanTo g j := hu.2 x hx
  have h3 : n⁻¹ x ∈ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _) h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h3
  have h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    have : i ≠ j.castSucc := by
      rintro rfl
      simp at hi'
    show hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg this]
  have h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x := by
    have := h4 h2
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  refine ⟨c, ?_, ?_⟩
  · have : x = n (n⁻¹ x) := (n.apply_symm_apply x).symm
    rw [this, ← hc, map_sum]
    simp
  · show _ = hfLin L S.Hm (gs j) x
    rw [← h5, ← hc, map_sum]
    have : ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0 := by
      intro i
      rw [map_smul]
      show c i * hf L S.Hm (g i) (gs j) = _
      rw [hd]; split_ifs <;> simp
    simp [this]

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF`. Establish `hW` using `(GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).2.1`. Establish `hom : ‖S.om d Λ‖ = 1` using `(GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ _ _ hW).2.2.2.2`. Establish `hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1` using `fun b u => (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _`. Establish `hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧ S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1`.

Introduce `w hw`. Take `⟨Λ₁, h1, h2, -, -, h5⟩` from `GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF _ _ _ _ hw`. Use `⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩` and prove the remaining obligations. Take `⟨al, hal, hal1⟩` from `exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1`. Take `⟨al', hal', hal1'⟩` from `exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1`.

Rewrite using `[h5 al al' hal hal', hal1, hal1']`. Both sides reduce to the same expression. Establish `huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂` using `fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)`. Set `P : Submodule L.O S.V → Prop` to `fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y`. Set `G : S.MW → ℂ` to `fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0`.

Take `⟨hGn, hGs⟩` from `(GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G (by`. Introduce `w Λ₁ hw`. Distinguish the cases in `hP : P Λ₁`. Take `⟨Λ₂, h1, -, h3⟩` from `hmove w hw.1`. Rewrite using `[if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]`.

Conclude with `if_pos ⟨Λ₁, hw, hP⟩`. Rewrite using `[if_neg hP]`. Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨Λ₂, h1, h2⟩`. Conclude with `hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))`.

Use the proof step `(by`. Introduce `w hw`. Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨Λ₂, h1, -⟩`. Conclude with `hw h1.1)`.

Take `⟨-, hLn, hHn, -, hLb, hHb⟩` from `GlobalTheory.T.hermitianMoves_total_measure_estimates L r k S hk j β βJ d Λ hT hF`. Take `⟨hadd, hsm, -, -⟩` from `GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)`. Use `set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH`. Take `⟨hn2, hc2⟩` from `hsm (-S.om d Λ) H hHn`. Take `⟨hn3, hc3, -⟩` from `hadd G _ hGn hn2`.

Establish `hb` using `(hadd _ _ hn3 hLn).2.2 (by`. Introduce `w`. Simplify using `only [Pi.add_apply, hH, ind, G]`. Distinguish the cases in `hw : S.Mv (j + 1) d Λ w`. Distinguish the cases in `hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁`.

Apply the tactic sequence `rw [if_pos hex, if_pos hw] split_ifs <;> simp`. Establish `hl : ¬ S.NoLeak Λ w.2.1`. Introduce `hl`. Take `⟨Λ₁, h1, h2, -⟩` from `hmove w hw`. Conclude with `hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩`.

Rewrite using `[if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]`. Simplify using `[hom, hchi]`. Establish `hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁`. Introduce and unpack `⟨Λ₂, h1, -⟩`. Conclude with `hw h1.1`.

Rewrite using `[if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]`. Use the proof step `simp)`. Rewrite `hb` using `[hc3, hc2]`. Establish `hcK : 0 ≤ S.cK β βJ`. Unfold `Frames.cK`.

Check the signs of the components of the expression. Establish `hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤ (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re + ‖cint (S.refA (j + 1) Λ) H‖`. Establish `e : cint (S.refA (j + 1) Λ) G = (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) + S.om d Λ * cint (S.refA (j + 1) Λ) H` using `by ring`. Rewrite using `[e]`. Use `(norm_add_le _ _).trans (add_le_add hb ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, hom, one_mul]`. Use `mul_le_mul_of_nonneg_left hG hcK` as an intermediate fact. Use `show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _`. Rewrite using `[hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kernel_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  have hW := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).2.1
  have hom : ‖S.om d Λ‖ = 1 := (GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ _ _ hW).2.2.2.2
  have hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1 := fun b u =>
    (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _

  have hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧
      S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1 := by
    intro w hw
    obtain ⟨Λ₁, h1, h2, -, -, h5⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF _ _ _ _ hw
    refine ⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩
    obtain ⟨al, hal, hal1⟩ := exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1
    obtain ⟨al', hal', hal1'⟩ := exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1
    rw [h5 al al' hal hal', hal1, hal1']
    rfl
  have huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂ :=
    fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)
  let P : Submodule L.O S.V → Prop := fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y
  let G : S.MW → ℂ := fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then
    S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0
  obtain ⟨hGn, hGs⟩ := (GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G
    (by
      intro w Λ₁ hw
      by_cases hP : P Λ₁
      · obtain ⟨Λ₂, h1, -, h3⟩ := hmove w hw.1
        rw [if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]
        exact if_pos ⟨Λ₁, hw, hP⟩
      · rw [if_neg hP]
        refine if_neg ?_
        rintro ⟨Λ₂, h1, h2⟩
        exact hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))
    (by
      intro w hw
      refine if_neg ?_
      rintro ⟨Λ₂, h1, -⟩
      exact hw h1.1)
  obtain ⟨-, hLn, hHn, -, hLb, hHb⟩ := GlobalTheory.T.hermitianMoves_total_measure_estimates L r k S hk j β βJ d Λ hT hF
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)
  set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH
  obtain ⟨hn2, hc2⟩ := hsm (-S.om d Λ) H hHn
  obtain ⟨hn3, hc3, -⟩ := hadd G _ hGn hn2
  have hb := (hadd _ _ hn3 hLn).2.2 (by
    intro w
    simp only [Pi.add_apply, hH, ind, G]
    by_cases hw : S.Mv (j + 1) d Λ w
    · by_cases hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁
      · rw [if_pos hex, if_pos hw]
        split_ifs <;> simp
      · have hl : ¬ S.NoLeak Λ w.2.1 := by
          intro hl
          obtain ⟨Λ₁, h1, h2, -⟩ := hmove w hw
          exact hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩
        rw [if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]
        simp [hom, hchi]
    · have hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ := by
        rintro ⟨Λ₂, h1, -⟩
        exact hw h1.1
      rw [if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]
      simp)
  rw [hc3, hc2] at hb
  have hcK : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  have hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤
      (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re +
        ‖cint (S.refA (j + 1) Λ) H‖ := by
    have e : cint (S.refA (j + 1) Λ) G =
        (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) +
          S.om d Λ * cint (S.refA (j + 1) Λ) H := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hb ?_)
    rw [norm_mul, hom, one_mul]
  have := mul_le_mul_of_nonneg_left hG hcK
  show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _
  rw [hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]
  linarith

end GlobalTheory.HL.KernelWeight
