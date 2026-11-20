import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfDMain
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfTNatCastUnit
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.IsAdicCompleteMax
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrystallineLatticeOfJumpPoints
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

/- English proof (translation)
Establish `hv : 0 ≤ P.v LL ζ`. Establish `h1 : P.v LL (ζ ^ l) = 0` using `by rw [hζ.pow_eq_one, AddValuation.map_one]`. Rewrite `h1` using `[AddValuation.map_pow]`. Consider the cases of `hq : P.v LL ζ using WithTop.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Rewrite `h1` using `[hq]`. Take `⟨k, hk⟩ : ∃ k, l = k + 1` from `⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩`. Rewrite `h1` using `[hk, succ_nsmul, WithTop.add_top]`. Conclude with `WithTop.top_ne_zero h1`.

Consider the case `coe q`. Rewrite `h1` using `[hq]`. Establish `h2 : ((l • q : ℚ) : WithTop ℚ) = 0` using `by rw [WithTop.coe_nsmul]; exact h1`. Establish `h3 : l • q = 0` using `by exact_mod_cast h2`. Rewrite `h3` using `[nsmul_eq_mul, mul_eq_zero]`.

Break down `h3 with h3 | h3` into its components or cases. Conclude with `absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero`. Rewrite using `[h3]`. Conclude with `le_refl _`. Use `⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩` and prove the remaining obligations.

Conclude with `IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective`.
-/
theorem u2ringPf_zetaO {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) {ζ : ↥LL.1}
    (hζ : IsPrimitiveRoot ζ l) : ∃ z : ↥(OL LL), IsPrimitiveRoot z l := by
  have hv : 0 ≤ P.v LL ζ := by
    have h1 : P.v LL (ζ ^ l) = 0 := by rw [hζ.pow_eq_one, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    cases hq : P.v LL ζ using WithTop.recTopCoe with
    | top =>
      exfalso
      rw [hq] at h1
      obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩
      rw [hk, succ_nsmul, WithTop.add_top] at h1
      exact WithTop.top_ne_zero h1
    | coe q =>
      rw [hq] at h1
      have h2 : ((l • q : ℚ) : WithTop ℚ) = 0 := by rw [WithTop.coe_nsmul]; exact h1
      have h3 : l • q = 0 := by exact_mod_cast h2
      rw [nsmul_eq_mul, mul_eq_zero] at h3
      rcases h3 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero
      · rw [h3]; exact le_refl _
  refine ⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective

/- English proof (translation)
Introduce `D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c`. Establish `hlp : l.Prime` using `Fact.out`. Establish `: IsDiscreteValuationRing ↥(OL LL)` using `GenPf.isDVR (D.loc l) LL`. Establish `: CharZero ↥(OL LL)` using `Formalism.MainNotions.UnusedSlot80.levg_charZero LL`. Establish `hpl : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`.

Establish `hs1 : ((HW l).W K 1 LL hG).s = 1` using `(HW l).W_s K 1 LL hG`. Establish `hp2 : ((D.loc l).PD K).p ≠ 2` using `by rw [hpl]; exact hl`. Establish `: FiniteDimensional ℚ_[l] ↥(K0 K)` using `((D.loc l).PD K).finK₀`. Establish `: NeZero (Module.finrank ℚ_[l] ↥(K0 K))` using `⟨Module.finrank_pos.ne'⟩`. Establish `hV` using `Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL`.

Establish `hpu` using `Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV`. Establish `hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL)` using `(IsLocalRing.mem_maximalIdeal _).2 hpu`. Establish `hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0` using `Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)`. Establish `: IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL)`. Rewrite using `[hpl]`.

Conclude with `Formalism.MainNotions.WachCoordinates.Br.complete_OL LL`. Establish `: IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL)` using `AdicCompletionMax.isAdicComplete_max hp0 hpm`. Establish `hs : 1 ≤ sK l K` using `DescentValuation.u3downPf_sK_pos hl K LL hG`. Establish `hd` using `DvdPf.dvdCondition l hl K LL hG`. Establish `hes : eK K * sK l K = ((D.loc l).PD K).p - 1` using `by rw [hpl]; exact Nat.mul_div_cancel' hd`.

Take `⟨ζL, hζL⟩` from `Formalism.MainNotions.N.zeta_of_good (D.loc l) hG`. Take `⟨ζ, hζ⟩` from `u2ringPf_zetaO (D.loc l) LL hζL`. Establish `hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p` using `by rw [hpl]; exact hζ`. Establish `hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1)` using `Subtype.val_injective`. Establish `hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y`.

Introduce `y`. Rewrite using `[(D.loc l).v_O LL y]`. Conclude with `⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩`. Take `⟨a, r, ha, hrm, hE, hnr⟩` from `u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv`. Conclude with `u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r hrm hE hnr h' hh'`.
-/
theorem u2ring_pf : SecondRingHypothesis := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c
  have hlp : l.Prime := Fact.out
  have : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) :=
    (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := AdicCompletionMax.isAdicComplete_max hp0 hpm
  have hs : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hd := DvdPf.dvdCondition l hl K LL hG
  have hes : eK K * sK l K = ((D.loc l).PD K).p - 1 := by rw [hpl]; exact Nat.mul_div_cancel' hd
  obtain ⟨ζL, hζL⟩ := Formalism.MainNotions.N.zeta_of_good (D.loc l) hG
  obtain ⟨ζ, hζ⟩ := u2ringPf_zetaO (D.loc l) LL hζL
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hpl]; exact hζ
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  obtain ⟨a, r, ha, hrm, hE, hnr⟩ := u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv
  exact u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r
    hrm hE hnr h' hh'

end Formalism.MainNotions.N.Ln34
