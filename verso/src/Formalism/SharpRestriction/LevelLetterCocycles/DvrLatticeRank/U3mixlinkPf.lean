import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MixLocal
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.DescentValuation

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW Fo Cm CA CB CK hA hdr hrk hMF l hlp hl K LL hG π' E hp T₁ T₂ F S η m h' up b c α β hfr hN he`. Take `⟨hc1, hc2, hon, hd1, hd2, hηb, hbS, hh, -, -⟩` from `hN`. Establish `hpl : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Establish `hJ1 : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')` using `fun τ => u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hd1 τ) (hηb τ) (hbS τ)`. Establish `hJ2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h')` using `fun τ => u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hd2 τ) (hηb τ) (hbS τ)`.

Establish `hs1 : 1 ≤ sK l K` using `u3downPf_sK_pos hl K LL hG`. Establish `hM : 1 ≤ MK l K h'` using `u3upPf_MK_pos hl K LL hG h' hh`. Establish `hF'` using `hMF l hl K LL hG π' E hp h' hh c α β hfr`. Establish `hs : ((HW l).W K 1 LL hG).s = 1` using `(HW l).W_s K 1 LL hG`. Establish `hp2 : ((D.loc l).PD K).p ≠ 2` using `by rw [hpl]; exact hl`.

Establish `hgk : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam` using `((HW l).W K 1 LL hG).gamK_eq_one hs hp2`. Establish `hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p`. Introduce `τ ζ hpt`. Rewrite using `[hpl]`. Conclude with `framepf_pt_prim D HW hG c ζ τ hpt`.

Establish `hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1)` using `Subtype.val_injective`. Establish `hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y`. Introduce `y`. Rewrite using `[(D.loc l).v_O LL y]`. Conclude with `⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩`.

Establish `hDVR : IsDiscreteValuationRing ↥(OL LL)` using `GenPf.isDVR (D.loc l) LL`. Establish `hcpl : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL)`. Rewrite using `[hpl]`. Conclude with `FrobeniusSpanLemma.phib_OL_complete LL`. Establish `hfact : Fact ((D.loc l).PD K).p.Prime` using `⟨((D.loc l).PD K).hp⟩`.

Take `⟨-, -, p3, p4, -, -, -, -, p9, -⟩` from `hA.1 l K 1 LL hG`. Establish `hV : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → LevelExpansions.ValH ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c`. Introduce `T hT`. Take `⟨⟨hfc, -⟩, hfd⟩` from `hA.2.2.2.2.2.2.2.2.2.2.1 l K LL T`. Establish `: FiniteDimensional ↥LL.1 ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c))` using `Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)`.

Establish `: FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c)`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.ιDi`. Use `infer_instance`. Take `⟨π₀, E₀, -, hm⟩` from `(p9 T hT hs hp2).2.1`. Conclude with `LevelExpansions.valH_of ((Cm l).C K 1 LL hG).tie hinj T _ c hs hT hprim hp hs1 hm (p3 T hT) (p4 T hT) (fun τ => (hfd τ).1) fun τ => by rw [hrk l K LL hG T hT c, hdr l K LL ⟨1, hG⟩ T hT τ]`.

Establish `hp' : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) 2 (sK l K) π' E` using `he ▸ hp`. Establish `h2s : 2 * sK l K = ((D.loc l).PD K).p - 1`. Rewrite using `[hpl, ← he]`. Conclude with `Nat.mul_div_cancel' (DvdPf.dvdCondition l hl K LL hG)`. Use `LevelExpansions.mix_local ((HW l).W K 1 LL hG) hinj F hp' h2s hs1 hprim (fun ζ hζ => ?_) (fun τ ζ hpt => ?_) (fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt) ?_ ?_ hc1 hc2 hd1 hd2 hηb hbS hh hfr (hF' T₁ hc1 hJ1) (hF' T₂ hc2 hJ2) hM (hV T₁ hc1) (hV T₂ hc2) (w_pf D HW Fo Cm CA CB …` and prove the remaining obligations.

Establish `hi : IsIntegral ℤ_[l] ζ`. Use `IsIntegral.of_pow ((D.loc l).PD K).hp.pos ?_` and prove the remaining obligations. Rewrite using `[hζ.pow_eq_one]`. Conclude with `isIntegral_one`. Conclude with `⟨⟨ζ, hi⟩, rfl⟩`.

Use `⟨algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)), (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero), fun a => ?_⟩` and prove the remaining obligations. Establish `hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1))`. Rewrite using `[hgk, Nat.cast_one, Nat.cast_one, ((HW l).W K 1 LL hG).gam_gen, hs, Nat.cast_one]`. Establish `h1' : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1)` using `by rw [pow_one]; exact hprim τ ζ hpt`. Conclude with `((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 h1' hv (by rw [pow_one]) a`.

Introduce `τ τ' τ'' h h' h'' hne`. Establish `: FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Establish `: FiniteDimensional ↥(K0 K) ↥K.1` using `Module.Finite.of_restrictScalars_finite ℚ_[l] _ _`. Establish `hcd` using `kapPiPf_card ((HW l).W K 1 LL hG) c`. Rewrite `hcd` using `[show finrank ↥(K0 K) ↥K.1 = 2 from he]`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h3 : 2 < Nat.card {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c}`. Use `Fintype.ofFinite {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c}` as an intermediate fact. Rewrite using `[Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]`.

Conclude with `⟨⟨τ, h⟩, ⟨τ', h'⟩, ⟨τ'', h''⟩, fun e => hne (congrArg Subtype.val e), fun e => hcon.1 (congrArg Subtype.val e).symm, fun e => hcon.2 (congrArg Subtype.val e).symm⟩`. Use linear arithmetic over natural numbers and integers. Introduce `k hk`. Rewrite `hk` using `[hpl]`. Conclude with `gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hinj hRv l hlp.out ((D.loc l).v_l LL) k hk`.

Introduce `b' B hb hbB hBb`. Rewrite using `[hpl]`. Conclude with `LevelExpansions.yc_bound l b' B η h' hb hbB hBb`.
-/
theorem u3mixlink_pf : MixedSlotOfModels := by
  intro D HW Fo Cm CA CB CK hA hdr hrk hMF l hlp hl K LL hG π' E hp T₁ T₂ F S η m h' up b c α β hfr hN he
  obtain ⟨hc1, hc2, hon, hd1, hd2, hηb, hbS, hh, -, -⟩ := hN
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hJ1 : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hd1 τ) (hηb τ) (hbS τ)
  have hJ2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hd2 τ) (hηb τ) (hbS τ)
  have hs1 : 1 ≤ sK l K := u3downPf_sK_pos hl K LL hG
  have hM : 1 ≤ MK l K h' := u3upPf_MK_pos hl K LL hG h' hh
  have hF' := hMF l hl K LL hG π' E hp h' hh c α β hfr
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hgk : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs hp2
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hDVR : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have hcpl : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact FrobeniusSpanLemma.phib_OL_complete LL
  have hfact : Fact ((D.loc l).PD K).p.Prime := ⟨((D.loc l).PD K).hp⟩
  obtain ⟨-, -, p3, p4, -, -, -, -, p9, -⟩ := hA.1 l K 1 LL hG
  have hV : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ →
      LevelExpansions.ValH ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c := by
    intro T hT
    obtain ⟨⟨hfc, -⟩, hfd⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL T
    have : FiniteDimensional ↥LL.1
        ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
      Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
    have : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
      unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
      infer_instance
    obtain ⟨π₀, E₀, -, hm⟩ := (p9 T hT hs hp2).2.1
    exact LevelExpansions.valH_of ((Cm l).C K 1 LL hG).tie hinj T _ c hs hT hprim hp hs1 hm (p3 T hT) (p4 T hT)
      (fun τ => (hfd τ).1) fun τ => by rw [hrk l K LL hG T hT c, hdr l K LL ⟨1, hG⟩ T hT τ]
  have hp' : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) 2 (sK l K) π' E := he ▸ hp
  have h2s : 2 * sK l K = ((D.loc l).PD K).p - 1 := by
    rw [hpl, ← he]
    exact Nat.mul_div_cancel' (DvdPf.dvdCondition l hl K LL hG)
  refine LevelExpansions.mix_local ((HW l).W K 1 LL hG) hinj F hp' h2s hs1 hprim (fun ζ hζ => ?_)
    (fun τ ζ hpt => ?_) (fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt) ?_ ?_ hc1 hc2 hd1 hd2 hηb hbS
    hh hfr (hF' T₁ hc1 hJ1) (hF' T₂ hc2 hJ2) hM (hV T₁ hc1) (hV T₂ hc2)
    (w_pf D HW Fo Cm CA CB CK hA l hl K LL hG π' E hp T₁ T₂ F h' hc1 hc2 hon hJ1)
    (ninlam_pf D HW Fo Cm CA CB CK hA l hl K LL hG π' E hp T₁ h' hc1 hJ1)
    (gamPiCondition D HW Fo Cm CA CB CK hA l hl K LL hG π' E hp T₁ hc1)
    (gamPiCondition D HW Fo Cm CA CB CK hA l hl K LL hG π' E hp T₂ hc2) ?_
  · have hi : IsIntegral ℤ_[l] ζ := by
      refine IsIntegral.of_pow ((D.loc l).PD K).hp.pos ?_
      rw [hζ.pow_eq_one]
      exact isIntegral_one
    exact ⟨⟨ζ, hi⟩, rfl⟩
  · refine ⟨algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)),
      (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK).isUnit.map
        (algebraMap ↥(OL LL) ↥LL.1)).ne_zero), fun a => ?_⟩
    have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
        (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
      rw [hgk, Nat.cast_one, Nat.cast_one, ((HW l).W K 1 LL hG).gam_gen, hs, Nat.cast_one]
    have h1' : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by rw [pow_one]; exact hprim τ ζ hpt
    exact ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 h1' hv (by rw [pow_one]) a
  · intro τ τ' τ'' h h' h'' hne
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ↥(K0 K) ↥K.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
    have hcd := kapPiPf_card ((HW l).W K 1 LL hG) c
    rw [show finrank ↥(K0 K) ↥K.1 = 2 from he] at hcd
    by_contra hcon
    push Not at hcon
    have h3 : 2 < Nat.card {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 //
        Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c} := by
      have := Fintype.ofFinite {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 //
        Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c}
      rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
      exact ⟨⟨τ, h⟩, ⟨τ', h'⟩, ⟨τ'', h''⟩, fun e => hne (congrArg Subtype.val e),
        fun e => hcon.1 (congrArg Subtype.val e).symm, fun e => hcon.2 (congrArg Subtype.val e).symm⟩
    omega
  · intro k hk
    rw [hpl] at hk
    exact gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hinj hRv l hlp.out
      ((D.loc l).v_l LL) k hk
  · intro b' B hb hbB hBb
    rw [hpl]
    exact LevelExpansions.yc_bound l b' B η h' hb hbB hBb

end Formalism.MainNotions.N.Ln34

end
