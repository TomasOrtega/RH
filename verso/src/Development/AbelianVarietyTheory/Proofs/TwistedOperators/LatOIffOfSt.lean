import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.CutStdLat

open GlobalTheory.FunObj Matrix

/- English proof (translation)
Unfold `stdLatO`. Conclude with `GlobalTheory.VecInv.mem_latO_iff (S := G.V (.top j)) (T := G.V (.top (j + 1))) hβS hβT (g := 1) (h := g) (by rw [map_one]; exact one_mem _) hT x`.
-/
theorem latO_iff_of_St {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (j : ℕ) (βS : GL (Fin (G.V (.top j)).rank) (Lev.EAf D))
    (βT : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) (hβS : IsFrame βS (colLat (S.N.fr (.top j))))
    (hβT : IsFrame βT (colLat (S.N.fr (.top (j + 1))))) (g : GA D (G.V (.top (j + 1))))
    (hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT) (x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  unfold stdLatO
  exact GlobalTheory.VecInv.mem_latO_iff (S := G.V (.top j)) (T := G.V (.top (j + 1))) hβS hβT (g := 1) (h := g)
    (by rw [map_one]; exact one_mem _) hT x

/- English proof (translation)
Introduce `D T L sc G W U S t ht Φ β j hj k hk e he g hg x`. Take `⟨βS, hβS⟩` from `frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top j))) (GlobalTheory.FunObj.VecEx.isLattice_colLat _)`. Take `⟨βT, hβT⟩` from `frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top (j + 1)))) (GlobalTheory.FunObj.VecEx.isLattice_colLat _)`. Use `set a : AE D := e + cA D e with ha`. Use `set b : Lev.EAf D := toEAf D (1 - a) with hbdef`.

Establish `hcb : ∀ w, GlobalTheory.StdFrames.cpt (D` using `D) w b = 1 - GlobalTheory.StdFrames.cpt (D := D) w (toEAf D a) := fun w => by`. Rewrite using `[hbdef, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one]`. Establish `hca` using `GlobalTheory.T.idempotentSum_add_conj_component_indicator he`. Establish `hb : b * b = b` using `GlobalTheory.StdFrames.cpt_ext fun w => by`. Rewrite using `[RingHom.map_mul, hcb]`.

Distinguish the cases in `h1 : w ∈ locPl G t ∨ GlobalTheory.IdemSupport.cP w ∈ locPl G t`. Rewrite using `[(hca w).1 h1]`. Expand and normalize the polynomial expressions, which then agree. Use `push_neg at h1`. Rewrite using `[(hca w).2 h1.1 h1.2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfh : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))`. Establish `e0 : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))) = finG (G.V (.top (j + 1))) ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)))` using `rfl`. Rewrite using `[e0, map_mul, map_mul, map_inv]`. Establish `hfg : Lev.finE (G.V (.top (j + 1))) g = GlobalTheory.UnitaryIdemCut.cutGL b hb ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.UnitaryIdemCut.cutGL_val, ← hfh, GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]`. Use extensionality with `i l`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, hbdef, RingHom.map_sub, RingHom.map_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp only [RingHom.map_one, RingHom.map_zero] <;> ring`.

Take `⟨Pu, eu, heu, hsu, hoff⟩` from `S.N.u_supp (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)`. Establish `hnot : ∀ Q ∈ Pu, ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) = Q.under (𝓞 D.host.F) → w ∉ locPl G t`. Introduce `Q hQ w hw hwl`. Take `⟨h1, h2, -⟩` from `S.N.off Q (hoff Q hQ)`. Unfold `locPl at hwl`.

Break down `Finset.mem_union.1 hwl with h3 | h3` into its components or cases. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 h3`. Establish `h4` using `G.pl.w_over v hv`. Conclude with `h1 ((hw.symm.trans h4) ▸ hv)`. Conclude with `h2 t ht w h3 hw.symm`.

Establish `hub : b * toEAf D (eu + cA D eu) = toEAf D (eu + cA D eu)` using `GlobalTheory.StdFrames.cpt_ext fun w => by`. Rewrite using `[RingHom.map_mul, hcb]`. Establish `hu` using `GlobalTheory.T.idempotentSum_add_conj_component_indicator heu w`. Distinguish the cases in `h1 : w ∈ Pu ∨ GlobalTheory.IdemSupport.cP w ∈ Pu`. Rewrite using `[hu.1 h1]`.

Establish `hw1 : w ∉ locPl G t`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `hnot w h1 w rfl`. Conclude with `hnot _ h1 w (GlobalTheory.IdemSupport.under_cP w).symm`. Establish `hw2 : GlobalTheory.IdemSupport.cP w ∉ locPl G t`.

Break down `h1 with h1 | h1` into its components or cases. Conclude with `hnot w h1 _ (GlobalTheory.IdemSupport.under_cP w)`. Conclude with `hnot _ h1 _ rfl`. Rewrite using `[(hca w).2 hw1 hw2]`. Expand and normalize the polynomial expressions, which then agree.

Use `push_neg at h1`. Rewrite using `[hu.2 h1.1 h1.2, mul_zero]`. Establish `hU : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) = finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.UnitaryIdemCut.cutGL_val]`.

Use `show b • (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val + (1 - b) • 1 = (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val`. Rewrite using `[GlobalTheory.VecInv.finE_val]`. Use extensionality with `i l`. Establish `h0` using `hsu i l`. Establish `h3 : b * toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) = toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l)`.

Rewrite using `[← h0, RingHom.map_mul, ← mul_assoc, hub]`. Establish `h4 : toEAf D ((1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (AE D)) i l) = (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) i l`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite `h3` using `[Matrix.sub_apply, RingHom.map_sub, h4]`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Take the linear combination `h3`. Establish `hK : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) ∈ St (S.βp (j + 1))` using `GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel _ _ _ _ _ hk b hb fun w ⟨PP, hPP, hw⟩ => by`. Rewrite using `[hcb]`. Break down `GlobalTheory.IdemSupport.eq_or_eq_cP hw with rfl | rfl` into its components or cases. Rewrite using `[(hca _).1 (Or.inl hPP)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[(hca _).1 (Or.inr (by rwa [GlobalTheory.StdFrames.cP_cP]))]; ring`. Establish `hcut : Lev.finE (G.V (.top (j + 1))) g = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))`. Rewrite using `[hfg, map_mul, map_mul, map_inv, hU]`. Establish `hp` using `S.βp_is (j + 1) (by omega)`.

Establish `hl` using `S.N.u_lat (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)`. Establish `keep : ∀ X ∈ St (S.βp (j + 1)), ∀ y ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) (colLat (S.N.fr (.top (j + 1)))), ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) := by`. Introduce `X hX y hy`. Establish `h1 : (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) (G.Λ (.top (j + 1))) := (hl y).1 hy`. Establish `h2` using `((GlobalTheory.LevSplit.mem_St_iff _ _ hp X).1 hX).1 _ h1`.

Use `(hl _).2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ _ ∈ _`. Generalize the expression as in `finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h2 ⊢`. Establish `e3 : Uu.val * (Uu⁻¹ * X * Uu).val = X.val * Uu.val`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`.

Use `congr 1`. Use `group`. Rewrite using `[Matrix.mulVec_mulVec y Uu.val (Uu⁻¹ * X * Uu).val, e3, ← Matrix.mulVec_mulVec y X.val Uu.val]`. Conclude with `h2`. Establish `st : ∀ X ∈ St (S.βp (j + 1)), (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) ∈ St βT`.

Introduce `X hX`. Use `(GlobalTheory.LevSplit.mem_St_iff _ _ hβT _).2 ⟨keep X hX, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h5` using `keep _ (inv_mem hX) y hy`. Generalize the expression as in `finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h5 ⊢`. Establish `e1 : (Uu⁻¹ * X * Uu)⁻¹ = Uu⁻¹ * X⁻¹ * Uu` using `by group`.

Rewrite using `[e1]`. Conclude with `h5`. Establish `hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT`. Rewrite using `[hcut]`. Conclude with `st _ hK`.

Conclude with `latO_iff_of_St S j βS βT hβS hβT g hT x`.
-/
theorem keep_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ g : GA D (G.V (.top (j + 1))),
      Formalism.L2.Theta.mt _ g = (1 - (e + cA D e)) • Formalism.L2.Theta.mt _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) :
        FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) + (e + cA D e) • (1 : Matrix (Fin (G.V (.top (j + 1))).rank)
        (Fin (G.V (.top (j + 1))).rank) (AE D)) →
      ∀ x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)),
        x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he g hg x
  classical
  obtain ⟨βS, hβS⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top j))) (GlobalTheory.FunObj.VecEx.isLattice_colLat _)
  obtain ⟨βT, hβT⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top (j + 1)))) (GlobalTheory.FunObj.VecEx.isLattice_colLat _)
  set a : AE D := e + cA D e with ha
  set b : Lev.EAf D := toEAf D (1 - a) with hbdef
  have hcb : ∀ w, GlobalTheory.StdFrames.cpt (D := D) w b = 1 - GlobalTheory.StdFrames.cpt (D := D) w (toEAf D a) := fun w => by
    rw [hbdef, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one]
  have hca := GlobalTheory.T.idempotentSum_add_conj_component_indicator he
  have hb : b * b = b := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    by_cases h1 : w ∈ locPl G t ∨ GlobalTheory.IdemSupport.cP w ∈ locPl G t
    · rw [(hca w).1 h1]; ring
    · push_neg at h1; rw [(hca w).2 h1.1 h1.2]; ring
  have hfh : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
      GA D (G.V (.top (j + 1)))) = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    have e0 : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
        GA D (G.V (.top (j + 1)))) = finG (G.V (.top (j + 1))) ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) := rfl
    rw [e0, map_mul, map_mul, map_inv]
  have hfg : Lev.finE (G.V (.top (j + 1))) g = GlobalTheory.UnitaryIdemCut.cutGL b hb
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val, ← hfh, GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, hbdef,
      RingHom.map_sub, RingHom.map_one, Matrix.one_apply]
    split_ifs <;> simp only [RingHom.map_one, RingHom.map_zero] <;> ring
  obtain ⟨Pu, eu, heu, hsu, hoff⟩ := S.N.u_supp (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have hnot : ∀ Q ∈ Pu, ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) = Q.under (𝓞 D.host.F) → w ∉ locPl G t := by
    intro Q hQ w hw hwl
    obtain ⟨h1, h2, -⟩ := S.N.off Q (hoff Q hQ)
    unfold locPl at hwl
    rcases Finset.mem_union.1 hwl with h3 | h3
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h3
      have h4 := G.pl.w_over v hv
      exact h1 ((hw.symm.trans h4) ▸ hv)
    · exact h2 t ht w h3 hw.symm
  have hub : b * toEAf D (eu + cA D eu) = toEAf D (eu + cA D eu) := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    have hu := GlobalTheory.T.idempotentSum_add_conj_component_indicator heu w
    by_cases h1 : w ∈ Pu ∨ GlobalTheory.IdemSupport.cP w ∈ Pu
    · rw [hu.1 h1]
      have hw1 : w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 w rfl
        · exact hnot _ h1 w (GlobalTheory.IdemSupport.under_cP w).symm
      have hw2 : GlobalTheory.IdemSupport.cP w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 _ (GlobalTheory.IdemSupport.under_cP w)
        · exact hnot _ h1 _ rfl
      rw [(hca w).2 hw1 hw2]; ring
    · push_neg at h1; rw [hu.2 h1.1 h1.2, mul_zero]
  have hU : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) = finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val]
    show b • (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val + (1 - b) • 1 = (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val
    rw [GlobalTheory.VecInv.finE_val]
    ext i l
    have h0 := hsu i l
    have h3 : b * toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) =
        toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) := by
      rw [← h0, RingHom.map_mul, ← mul_assoc, hub]
    have h4 : toEAf D ((1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (AE D)) i l) =
        (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) i l := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.sub_apply, RingHom.map_sub, h4] at h3
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h3
  have hK : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) ∈ St (S.βp (j + 1)) :=
    GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel _ _ _ _ _ hk b hb fun w ⟨PP, hPP, hw⟩ => by
      rw [hcb]
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hw with rfl | rfl
      · rw [(hca _).1 (Or.inl hPP)]; ring
      · rw [(hca _).1 (Or.inr (by rwa [GlobalTheory.StdFrames.cP_cP]))]; ring
  have hcut : Lev.finE (G.V (.top (j + 1))) g = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) *
      finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    rw [hfg, map_mul, map_mul, map_inv, hU]
  have hp := S.βp_is (j + 1) (by omega)
  have hl := S.N.u_lat (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have keep : ∀ X ∈ St (S.βp (j + 1)), ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) := by
    intro X hX y hy
    have h1 : (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top (j + 1))) := (hl y).1 hy
    have h2 := ((GlobalTheory.LevSplit.mem_St_iff _ _ hp X).1 hX).1 _ h1
    refine (hl _).2 ?_
    change (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ _ ∈ _
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h2 ⊢
    have e3 : Uu.val * (Uu⁻¹ * X * Uu).val = X.val * Uu.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec y Uu.val (Uu⁻¹ * X * Uu).val, e3, ← Matrix.mulVec_mulVec y X.val Uu.val]
    exact h2
  have st : ∀ X ∈ St (S.βp (j + 1)),
      (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) ∈ St βT := by
    intro X hX
    refine (GlobalTheory.LevSplit.mem_St_iff _ _ hβT _).2 ⟨keep X hX, fun y hy => ?_⟩
    have h5 := keep _ (inv_mem hX) y hy
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h5 ⊢
    have e1 : (Uu⁻¹ * X * Uu)⁻¹ = Uu⁻¹ * X⁻¹ * Uu := by group
    rw [e1]
    exact h5
  have hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT := by
    rw [hcut]
    exact st _ hK
  exact latO_iff_of_St S j βS βT hβS hβT g hT x

end GlobalTheory.CutStdLat

end
