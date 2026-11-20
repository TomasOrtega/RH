import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BadPlaces

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k)

end Local

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.HL.Frames.q _root_.GlobalTheory.HL.resQ`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer S.ϖ).1 S.ϖ_irr]`. Use `show 2 ≤ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)`. Conclude with `Finite.one_lt_card_iff_nontrivial.2 inferInstance`.
-/
private lemma two_le_q' : 2 ≤ S.q := by
  unfold _root_.GlobalTheory.HL.Frames.q _root_.GlobalTheory.HL.resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer S.ϖ).1
    S.ϖ_irr]
  show 2 ≤ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)
  exact Finite.one_lt_card_iff_nontrivial.2 inferInstance

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Establish `hq : (2 : ℝ) ≤ S.q`. Conclude with `two_le_q' S` after adjusting the coercions. Establish `h1 : 1 ≤ S.Hp` using `(_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.1`. Establish `hH : S.Hp = (S.q : ℝ) ^ (S.vth + S.a + S.vD)` using `rfl`. Break down `le_or_gt (S.vth + S.a + S.vD) 0 with hn | hn` into its components or cases.

Conclude with `absurd (le_antisymm (hH ▸ zpow_le_one_of_nonpos₀ (by linarith) hn) h1) hne`. Rewrite using `[hH]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma q_le_Hp_of_Hp_ne_one {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) (hne : S.Hp ≠ 1) :
    (S.q : ℝ) ≤ S.Hp := by
  have hq : (2 : ℝ) ≤ S.q := by
    exact_mod_cast two_le_q' S
  have h1 : 1 ≤ S.Hp :=
    (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.1
  have hH : S.Hp = (S.q : ℝ) ^
      (S.vth + S.a + S.vD) := rfl
  rcases le_or_gt (S.vth + S.a + S.vD) 0
    with hn | hn
  · exact absurd (le_antisymm (hH ▸ zpow_le_one_of_nonpos₀ (by linarith) hn) h1) hne
  · rw [hH]
    calc (S.q : ℝ)
        = (S.q : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ _ := zpow_le_zpow_right₀ (by linarith) (by omega)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.HL.vE`. Establish `hmem : (0 : ℤ) ∈ {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y}` using `⟨x, hx, by simp⟩`. Distinguish the cases in `hb : BddAbove {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y}`. Conclude with `le_csSup hb hmem`. Rewrite using `[Int.csSup_of_not_bddAbove hb]`.
-/
private lemma vE_nonneg_of_mem_O (ϖ : (ValuativeRel.valuation F).integer) {x : E}
    (hx : x ∈ L.O) : 0 ≤ _root_.GlobalTheory.HL.vE L ϖ x := by
  unfold _root_.GlobalTheory.HL.vE
  have hmem : (0 : ℤ) ∈ {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y} :=
    ⟨x, hx, by simp⟩
  by_cases hb : BddAbove {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y}
  · exact le_csSup hb hmem
  · rw [Int.csSup_of_not_bddAbove hb]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Take `⟨ha, hvD, hD, -⟩` from `_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h`. Establish `hq2` using `two_le_q' S`. Establish `hq : (1 : ℝ) < S.q` using `by exact_mod_cast (by omega : 1 < S.q)`. Establish `hn : S.vth + S.a + S.vD = 0`. Establish `hpow : (S.q : ℝ) ^ (S.vth + S.a + S.vD) = (S.q : ℝ) ^ (0 : ℤ)`.

Rewrite using `[zpow_zero]`. Conclude with `h1`. Conclude with `zpow_right_injective₀ (by linarith) hq.ne' hpow`. Establish `hth : 0 ≤ S.vth`. Apply the tactic sequence `unfold _root_.GlobalTheory.HL.Frames.vth; split_ifs <;> norm_num`.

Establish `hth0 : S.vth = 0` using `by omega`. Establish `ha0 : S.a = 0` using `by omega`. Establish `hvD0 : S.vD = 0` using `by omega`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Consider the cases of `hg : S.gg`.

Both sides reduce to the same expression. Simplify using `[_root_.GlobalTheory.HL.Frames.vth, hg] at hth0`. Establish `h2` using `ha0`. Unfold `_root_.GlobalTheory.HL.Frames.a at h2`. Rewrite `h2` using `[hth0]`.

Simplify using `using h2`. Introduce `l hl`. Distinguish the cases in `hl0 : l = 0`. Substitute `hl0` using the available equality. Establish `hD0 : S.D 0 = 1`.

Simplify using `[_root_.GlobalTheory.HL.Frames.D, _root_.GlobalTheory.HL.lead]`. Rewrite using `[hD0, map_one, one_mul]`. Simplify using `using _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L S.ϖ_irr 0 1`. Establish `hsum` using `hvD0`. Unfold `_root_.GlobalTheory.HL.Frames.vD at hsum`.

Rewrite `hsum` using `[Finset.sum_eq_zero_iff_of_nonneg]`. Simplify `hsum l (Finset.mem_univ _)` using `[hl0, hl]`. Introduce `i _ split_ifs`. Conclude with `vE_nonneg_of_mem_O _ (L.O.mul_mem (hD i) (_root_.GlobalTheory.HL.Inhab.cj_int L (hD i)))`. Conclude with `le_rfl`.
-/
private lemma gg_false_and_vE_eq_zero_of_Hp_eq_one {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) (h1 : S.Hp = 1) :
    S.gg = false ∧
      _root_.GlobalTheory.HL.vE L S.ϖ S.G = 0 ∧
      ∀ l, S.D l ≠ 0 →
        _root_.GlobalTheory.HL.vE L S.ϖ
          (S.D l * L.cj (S.D l)) = 0 := by
  obtain ⟨ha, hvD, hD, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h
  have hq2 := two_le_q' S
  have hq : (1 : ℝ) < S.q := by exact_mod_cast (by omega : 1 < S.q)
  have hn : S.vth + S.a + S.vD = 0 := by
    have hpow : (S.q : ℝ) ^
        (S.vth + S.a + S.vD) =
        (S.q : ℝ) ^ (0 : ℤ) := by
      rw [zpow_zero]; exact h1
    exact zpow_right_injective₀ (by linarith) hq.ne' hpow
  have hth : 0 ≤ S.vth := by
    unfold _root_.GlobalTheory.HL.Frames.vth; split_ifs <;> norm_num
  have hth0 : S.vth = 0 := by omega
  have ha0 : S.a = 0 := by omega
  have hvD0 : S.vD = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · cases hg : S.gg
    · rfl
    · simp [_root_.GlobalTheory.HL.Frames.vth, hg] at hth0
  · have h2 := ha0
    unfold _root_.GlobalTheory.HL.Frames.a at h2
    rw [hth0] at h2
    simpa using h2
  · intro l hl
    by_cases hl0 : l = 0
    · subst hl0
      have hD0 : S.D 0 = 1 := by
        simp [_root_.GlobalTheory.HL.Frames.D, _root_.GlobalTheory.HL.lead]
      rw [hD0, map_one, one_mul]
      simpa using _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L S.ϖ_irr 0 1
    · have hsum := hvD0
      unfold _root_.GlobalTheory.HL.Frames.vD at hsum
      rw [Finset.sum_eq_zero_iff_of_nonneg] at hsum
      · simpa [hl0, hl] using hsum l (Finset.mem_univ _)
      · intro i _
        split_ifs
        · exact vE_nonneg_of_mem_O _
            (L.O.mul_mem (hD i) (_root_.GlobalTheory.HL.Inhab.cj_int L (hD i)))
        · exact le_rfl

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Use `haveI := _root_.GlobalTheory.HL.Model.nontrivial L`. Take `⟨c, hc⟩` from `_root_.GlobalTheory.UnramOrder.exists_norm L hx`. Establish `hc0 : (c : F) ≠ 0`. Introduce `h0`. Establish `hu : IsUnit (x * L.cj x)` using `hxu.mul (hxu.map L.cj)`.

Rewrite `hu` using `[hc, h0, map_zero]`. Conclude with `not_isUnit_zero hu`. Take `⟨m, u, hmu⟩` from `_root_.GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc0`. Establish `hm : m = 0`. Establish `hval` using `_root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ m u`.

Rewrite `hval` using `[← hmu, ← hc, hv]`. Conclude with `hval.symm`. Substitute `hm` using the available equality. Establish `hu1 : ((u : (ValuativeRel.valuation F).integer) : F) * ((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) = 1`. Conclude with `congrArg (fun z : (ValuativeRel.valuation F).integer => (z : F)) u.mul_inv` after adjusting the coercions.

Use `⟨L.cj x * algebraMap F E (((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) : F), L.O.mul_mem (_root_.GlobalTheory.HL.Inhab.cj_int L hx) ((_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.prop _)), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hc, ← map_mul, hmu, zpow_zero, one_mul, hu1, map_one]`.
-/
private lemma exists_inv_mem_O_of_vE_mul_cj_eq_zero (ϖ : (ValuativeRel.valuation F).integer)
    (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) (hxu : IsUnit x)
    (hv : _root_.GlobalTheory.HL.vE L ϖ (x * L.cj x) = 0) : ∃ y ∈ L.O, x * y = 1 := by
  haveI := _root_.GlobalTheory.HL.Model.nontrivial L
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hx
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have hu : IsUnit (x * L.cj x) := hxu.mul (hxu.map L.cj)
    rw [hc, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨m, u, hmu⟩ := _root_.GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc0
  have hm : m = 0 := by
    have hval := _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ m u
    rw [← hmu, ← hc, hv] at hval
    exact hval.symm
  subst hm
  have hu1 : ((u : (ValuativeRel.valuation F).integer) : F) *
      ((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) = 1 := by
    exact_mod_cast congrArg (fun z : (ValuativeRel.valuation F).integer => (z : F)) u.mul_inv
  refine ⟨L.cj x * algebraMap F E
      (((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) : F),
    L.O.mul_mem (_root_.GlobalTheory.HL.Inhab.cj_int L hx) ((_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.prop _)), ?_⟩
  rw [← mul_assoc, hc, ← map_mul, hmu, zpow_zero, one_mul, hu1, map_one]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Take `⟨hgg, hG, hDl⟩` from `gg_false_and_vE_eq_zero_of_Hp_eq_one S h h1`. Take `⟨hBB, -, -, hmass01⟩` from `_root_.GlobalTheory.HL.GoodPlace.equality L r k S hk hgg hG hDl`. Establish `ha : S.a = 0`. Simplify using `[_root_.GlobalTheory.HL.Frames.a, _root_.GlobalTheory.HL.Frames.vth, hgg, hG]`. Establish `hDO` using `(_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.1`.

Establish `hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1` using `fun l hl => ⟨hDO l, exists_inv_mem_O_of_vE_mul_cj_eq_zero S.ϖ S.ϖ_irr (hDO l) ((_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.1 l hl) (hDl l hl)⟩`. Establish `hcls : ∃ C0, ∀ C, S.IsIntCls C → ∃ g ∈ S.St, C = g • C0` using `⟨_, (_root_.GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit).2.2⟩`. Take `⟨C0, hcls⟩` from `hcls`. Take `⟨Λ', hΛ'⟩` from `hd'`. Establish `hexists : ∀ C, S.IsIntCls C → ∃ Λ0, S.IsTerm d' Λ0 ∧ S.Fr d' Λ0 = C ∧ ∃ g ∈ S.St, Λ0 = g • Λ'`.

Introduce `C hC`. Take `⟨g2, hg2, rfl⟩` from `hcls C hC`. Take `⟨g1, hg1, he1⟩` from `hcls _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ' hΛ').2.2.2.2.2.2.1`. Establish `hg : g2 * g1⁻¹ ∈ S.St` using `mul_mem hg2 (inv_mem hg1)`. Establish `hact` using `_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ hg`.

Use `⟨(g2 * g1⁻¹) • Λ', hact.1, ?_, _, hg, rfl⟩` and prove the remaining obligations. Rewrite using `[hact.2.2.2.2.1, he1, smul_smul, inv_mul_cancel_right]`. Establish `horbit : ∀ Λ2, S.IsTerm d' Λ2 → ∃ g ∈ S.St, Λ2 = g • Λ'`. Introduce `Λ2 h2`. Take `⟨Λ0, hT0, hF0, hg⟩` from `hexists _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ2 h2).2.2.2.2.2.2.1`.

Rewrite using `[← (_root_.GlobalTheory.HL.UnimodTerm.term_unique L r k S d' Λ2 h2 ha).2 Λ0 hT0 hF0]`. Conclude with `hg`. Use `set o0 : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V)) Λ' with ho0`. Establish `hne : ∀ o, o ≠ o0 → ¬ S.IsTerm d' (Quotient.out o)`. Introduce `o ho hT`.

Take `⟨g, hg, he⟩` from `horbit _ hT`. Establish `hq : Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V)) (Quotient.out o) = o0`. Rewrite using `[he]`. Conclude with `Quotient.sound ⟨⟨g, hg⟩, rfl⟩`. Conclude with `ho ((Quotient.out_eq o).symm.trans hq)`.

Take `⟨m, hm⟩` from `Quotient.exact (Quotient.out_eq o0)`. Establish `hT2 : S.IsTerm d' (Quotient.out o0)`. Rewrite using `[← hm]`. Conclude with `(_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ m.2).1`. Establish `hmass : S.mass d' (fun _ => True) = ENNReal.ofReal (S.mu (Quotient.out o0))`.

Unfold `_root_.GlobalTheory.HL.Frames.mass`. Rewrite using `[tsum_eq_single o0]`. Rewrite using `[if_pos ⟨hT2, trivial⟩]`. Introduce `o ho`. Rewrite using `[if_neg]`.

Conclude with `fun hc => hne o ho hc.1`. Establish `hpos : 0 < S.mu (Quotient.out o0)`. Take `⟨hA, hB, -⟩` from `(_root_.GlobalTheory.HL.volSt L r k S).1 _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2).1.1`. Unfold `_root_.GlobalTheory.HL.Frames.mu _root_.GlobalTheory.HL.invVol`. Conclude with `div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hB)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))`.

Establish `hmass1 : S.mass d' (fun _ => True) = 1`. Break down `hmass01 d' with h0 | h0` into its components or cases. Rewrite `h0` using `[hmass, ENNReal.ofReal_eq_zero]`. Conclude with `absurd h0 (not_le.2 hpos)`. Conclude with `h0`.

Establish `hmu : S.mu (Quotient.out o0) = 1`. Rewrite `hmass` using `[hmass1, eq_comm, ENNReal.ofReal_eq_one]`. Conclude with `hmass`. Use `⟨?_, hmass1⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.HL.Frames.amp`.

Rewrite using `[tsum_eq_single o0]`. Use `swap`. Introduce `o ho`. Rewrite using `[if_neg]`. Conclude with `fun hc => hne o ho hc.1`.

Rewrite using `[if_pos ⟨hT2, hBB _ _ hT2⟩, hmu]`. Take `⟨-, hW, -⟩` from `_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2`. Simplify using `using (_root_.GlobalTheory.HL.WitIndep.witness_independence L r k S d' _ _ _ hW).2.2.2.2`.
-/
private lemma norm_amp_BBzero_eq_one_and_mass_eq_one_of_Hp_eq_one (hk : 4 * r + 7 ≤ k) {d : S.Datum}
    {Λ : Submodule L.O S.V} (h : S.IsTerm d Λ) (h1 : S.Hp = 1) (d' : S.Datum)
    (hd' : ∃ Λ', S.IsTerm d' Λ') :
    ‖S.amp d' (S.BBzero d')‖ = 1 ∧
      S.mass d' (fun _ => True) = 1 := by
  obtain ⟨hgg, hG, hDl⟩ := gg_false_and_vE_eq_zero_of_Hp_eq_one S h h1
  obtain ⟨hBB, -, -, hmass01⟩ := _root_.GlobalTheory.HL.GoodPlace.equality L r k S hk hgg hG hDl
  have ha : S.a = 0 := by
    simp [_root_.GlobalTheory.HL.Frames.a, _root_.GlobalTheory.HL.Frames.vth,
      hgg, hG]
  have hDO := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.1
  have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧
      ∃ y ∈ L.O, S.D l * y = 1 := fun l hl =>
    ⟨hDO l, exists_inv_mem_O_of_vE_mul_cj_eq_zero S.ϖ
      S.ϖ_irr (hDO l)
      ((_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.1 l hl) (hDl l hl)⟩
  have hcls : ∃ C0, ∀ C, S.IsIntCls C →
      ∃ g ∈ S.St, C = g • C0 :=
    ⟨_, (_root_.GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit).2.2⟩
  obtain ⟨C0, hcls⟩ := hcls
  obtain ⟨Λ', hΛ'⟩ := hd'
  have hexists : ∀ C, S.IsIntCls C → ∃ Λ0, S.IsTerm d' Λ0 ∧
      S.Fr d' Λ0 = C ∧ ∃ g ∈ S.St, Λ0 = g • Λ' := by
    intro C hC
    obtain ⟨g2, hg2, rfl⟩ := hcls C hC
    obtain ⟨g1, hg1, he1⟩ :=
      hcls _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ' hΛ').2.2.2.2.2.2.1
    have hg : g2 * g1⁻¹ ∈ S.St := mul_mem hg2 (inv_mem hg1)
    have hact := _root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ hg
    refine ⟨(g2 * g1⁻¹) • Λ', hact.1, ?_, _, hg, rfl⟩
    rw [hact.2.2.2.2.1, he1, smul_smul, inv_mul_cancel_right]
  have horbit : ∀ Λ2, S.IsTerm d' Λ2 → ∃ g ∈ S.St, Λ2 = g • Λ' := by
    intro Λ2 h2
    obtain ⟨Λ0, hT0, hF0, hg⟩ :=
      hexists _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ2 h2).2.2.2.2.2.2.1
    rw [← (_root_.GlobalTheory.HL.UnimodTerm.term_unique L r k S d' Λ2 h2 ha).2 Λ0 hT0 hF0]
    exact hg
  set o0 : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) :=
    Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V)) Λ' with ho0
  have hne : ∀ o, o ≠ o0 → ¬ S.IsTerm d' (Quotient.out o) := by
    intro o ho hT
    obtain ⟨g, hg, he⟩ := horbit _ hT
    have hq : Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V))
        (Quotient.out o) = o0 := by
      rw [he]; exact Quotient.sound ⟨⟨g, hg⟩, rfl⟩
    exact ho ((Quotient.out_eq o).symm.trans hq)
  obtain ⟨m, hm⟩ := Quotient.exact (Quotient.out_eq o0)
  have hT2 : S.IsTerm d' (Quotient.out o0) := by
    rw [← hm]; exact (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ m.2).1
  have hmass : S.mass d' (fun _ => True) =
      ENNReal.ofReal (S.mu (Quotient.out o0)) := by
    unfold _root_.GlobalTheory.HL.Frames.mass
    rw [tsum_eq_single o0]
    · rw [if_pos ⟨hT2, trivial⟩]
    · intro o ho
      rw [if_neg]
      exact fun hc => hne o ho hc.1
  have hpos : 0 < S.mu (Quotient.out o0) := by
    obtain ⟨hA, hB, -⟩ := (_root_.GlobalTheory.HL.volSt L r k S).1 _
      (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2).1.1
    unfold _root_.GlobalTheory.HL.Frames.mu _root_.GlobalTheory.HL.invVol
    exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hB)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))
  have hmass1 : S.mass d' (fun _ => True) = 1 := by
    rcases hmass01 d' with h0 | h0
    · rw [hmass, ENNReal.ofReal_eq_zero] at h0
      exact absurd h0 (not_le.2 hpos)
    · exact h0
  have hmu : S.mu (Quotient.out o0) = 1 := by
    rw [hmass1, eq_comm, ENNReal.ofReal_eq_one] at hmass
    exact hmass
  refine ⟨?_, hmass1⟩
  unfold _root_.GlobalTheory.HL.Frames.amp
  rw [tsum_eq_single o0]
  swap
  · intro o ho
    rw [if_neg]
    exact fun hc => hne o ho hc.1
  rw [if_pos ⟨hT2, hBB _ _ hT2⟩, hmu]
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2
  simpa using (_root_.GlobalTheory.HL.WitIndep.witness_independence L r k S d' _ _ _ hW).2.2.2.2

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G hk d Λ hT`. Establish `hlf : ∀ p, IsNonarchimedeanLocalField (A.loc p).Fp` using `fun p => (A.loc p).lf`. Establish `hch : ∀ p, CharZero (A.loc p).Fp` using `fun p => (A.loc p).char0`. Establish `hloc : ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ)` using `hT.2`. Establish `hmemOm : ∀ p, p ∈ G.Om ↔ (G.S p).Hp ≠ 1` using `fun p => Iff.rfl`.

Establish `h1 : ∀ p, 1 ≤ (G.S p).Hp` using `fun p => haveI := hlf p`. Use `haveI := hch p (_root_.GlobalTheory.HL.Defect.exponents_and_defect _ r k (G.S p) _ _ (hloc p)).2.2.2.2.1`. Establish `hfin : G.Om.Finite` using `(_root_.GlobalTheory.HL.StdPlace.coordinate_lattice_standard A r k G hk).subset fun p hp hgood => (hmemOm p).1 hp hgood.2.1`. Establish `hbad : ∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧ ((G.S p).q : ℝ) ≤ (G.S p).Hp` using `fun p hp => haveI := hlf p`. Use `haveI := hch p ⟨two_le_q' _, q_le_Hp_of_Hp_ne_one _ (hloc p) ((hmemOm p).1 hp)⟩`.

Use `⟨hfin, h1, hbad, ?_, ?_⟩` and prove the remaining obligations. Establish `hHt : G.Ht = ∏ p ∈ hfin.toFinset, (G.S p).Hp`. Unfold `_root_.GlobalTheory.HL.GFrames.Ht`. Apply `finprod_eq_prod_of_mulSupport_subset` to reduce the goal to its premises. Introduce `p hp`.

Simplify `hp` using `[hmemOm]`. Rewrite using `[hHt, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]`. Apply `Finset.prod_le_prod (fun _ _ => by norm_num)` to reduce the goal to its premises. Introduce `p hp`. Establish `hb` using `hbad p (hfin.mem_toFinset.1 hp)`.

Combine the equalities or inequalities in the displayed calculation. Introduce `p hp haveI := hlf p`. Use `haveI := hch p`. Establish `hH : (G.S p).Hp = 1`. Assume the negation of the conclusion as `hne`.

Conclude with `hp ((hmemOm p).2 hne)`. Take `⟨hgg, hG, hDl⟩` from `gg_false_and_vE_eq_zero_of_Hp_eq_one _ (hloc p) hH`. Use `⟨(_root_.GlobalTheory.HL.GoodPlace.equality _ r k (G.S p) hk hgg hG hDl).1, ?_⟩` and prove the remaining obligations. Introduce `d' hd'`. Conclude with `norm_amp_BBzero_eq_one_and_mass_eq_one_of_Hp_eq_one _ hk (hloc p) hH d' hd'`.
-/
theorem _root_.GlobalTheory.HL.BadPlaces.bad_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (r k : ℕ) (G : _root_.GlobalTheory.HL.GFrames A r k), 4 * r + 7 ≤ k → ∀ d Λ, G.IsTerm d Λ → G.Om.Finite ∧ (∀ p, 1 ≤ (G.S p).Hp) ∧ (∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧ ((G.S p).q : ℝ) ≤ (G.S p).Hp) ∧ (2 : ℝ) ^ G.Om.ncard ≤ G.Ht ∧ ∀ p ∉ G.Om, (∀ d' Λ', (G.S p).IsTerm d' Λ' → (G.S p).BBzero d' Λ') ∧ ∀ d', (∃ Λ', (G.S p).IsTerm d' Λ') → ‖(G.S p).amp d' ((G.S p).BBzero d')‖ = 1 ∧ (G.S p).mass d' (fun _ => True) = 1 := by
  intro F E _ _ _ _ _ sig A r k G hk d Λ hT
  have hlf : ∀ p, IsNonarchimedeanLocalField (A.loc p).Fp := fun p => (A.loc p).lf
  have hch : ∀ p, CharZero (A.loc p).Fp := fun p => (A.loc p).char0
  have hloc : ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ) := hT.2
  have hmemOm : ∀ p, p ∈ G.Om ↔ (G.S p).Hp ≠ 1 := fun p => Iff.rfl
  have h1 : ∀ p, 1 ≤ (G.S p).Hp := fun p =>
    haveI := hlf p; haveI := hch p
    (_root_.GlobalTheory.HL.Defect.exponents_and_defect _ r k (G.S p) _ _ (hloc p)).2.2.2.2.1
  have hfin : G.Om.Finite :=
    (_root_.GlobalTheory.HL.StdPlace.coordinate_lattice_standard A r k G hk).subset
      fun p hp hgood => (hmemOm p).1 hp hgood.2.1
  have hbad : ∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧
      ((G.S p).q : ℝ) ≤ (G.S p).Hp := fun p hp =>
    haveI := hlf p; haveI := hch p
    ⟨two_le_q' _, q_le_Hp_of_Hp_ne_one _ (hloc p) ((hmemOm p).1 hp)⟩
  refine ⟨hfin, h1, hbad, ?_, ?_⟩
  · have hHt : G.Ht = ∏ p ∈ hfin.toFinset, (G.S p).Hp := by
      unfold _root_.GlobalTheory.HL.GFrames.Ht
      apply finprod_eq_prod_of_mulSupport_subset
      intro p hp
      simpa [hmemOm] using hp
    rw [hHt, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    have hb := hbad p (hfin.mem_toFinset.1 hp)
    calc (2 : ℝ) ≤ (G.S p).q := by exact_mod_cast hb.1
      _ ≤ _ := hb.2
  · intro p hp
    haveI := hlf p; haveI := hch p
    have hH : (G.S p).Hp = 1 := by
      by_contra hne; exact hp ((hmemOm p).2 hne)
    obtain ⟨hgg, hG, hDl⟩ := gg_false_and_vE_eq_zero_of_Hp_eq_one _ (hloc p) hH
    refine ⟨(_root_.GlobalTheory.HL.GoodPlace.equality _ r k (G.S p) hk hgg hG hDl).1, ?_⟩
    intro d' hd'
    exact norm_amp_BBzero_eq_one_and_mass_eq_one_of_Hp_eq_one _ hk (hloc p) hH d' hd'

end GlobalTheory.HL.BadPlaces
