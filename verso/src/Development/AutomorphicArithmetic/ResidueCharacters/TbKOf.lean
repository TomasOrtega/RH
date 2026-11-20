import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
import Development.AutomorphicArithmetic.ResidueCharacters.LocRes
import Development.AutomorphicArithmetic.ResidueCharacters.TransferMemBlochKatoCocycles
import Development.AutomorphicArithmetic.ResidueCharacters.TbTop
import Development.AutomorphicArithmetic.ResidueCharacters.TwistDef

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `N h n t K LL hC ht J U hn hb hJ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ`. Take `⟨K', hKK, hg, hKs, hnor, hidx⟩` from `LocNum.exists_up hC`. Establish `hle : GK K' ≤ GK K` using `GK_le hKK`.

Establish `hε` using `TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat`. Set `Yt : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := Vy, ρ := ρy, cont := hcy, L := Ly }`. Set `VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := Ve, ρ := ρe, cont := hce, L := Le }`. Take `⟨r1, j1⟩` from `LocRes.res_crys D.loc hres hF hKK hle Yt hcrys`. Establish `hχ : ∀ (g : ↥(GK K')) x, (LocRes.res hle VeL).ρ g x = ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K').χ g : ℚ_[l]))⁻¹) ^ e • x` using `fun g x => by`.

Rewrite using `[(D.loc l).PD_χ]`. Use `hε.2 (Subgroup.inclusion hle g) x` as an intermediate fact. Rewrite `this` using `[(D.loc l).PD_χ]`. Conclude with `this`. Take `⟨c, hcle, key⟩` from `tb_top D HW F l h4 hCo hW hF N h n t e _ K' LL hg hKs U hn hb he ht hidx (LocRes.res hle Yt) (LocRes.res hle VeL) r1 (fun τ a ha => hJ _ (hjmp _ a ((j1 τ a).1 ha))) p (fun g v => hp _ v) hint e₀ he₀ hpe hε.1 hχ φ (fun g y hy hy0 => hφ _ y hy hy0)`.

Use `haveI := K.2`. Use `haveI := K'.2`. Establish `hix` using `GlobalTheory.InducedSectionsSpanStatement.inclusion_GK_index K' K hle`. Establish `hpos : 0 < Module.finrank ℚ_[l] ↥K'.1` using `Module.finrank_pos`. Establish `hpos' : 0 < Module.finrank ℚ_[l] ↥K.1` using `Module.finrank_pos`.

Establish `hgi : Module.finrank ℚ_[l] ↥K'.1 / Module.finrank ℚ_[l] ↥K.1 = (Subgroup.inclusion hle).range.index`. Rewrite using `[← hix, Nat.mul_div_cancel _ hpos']`. Establish `hi0 : (Subgroup.inclusion hle).range.index ≠ 0` using `fun h => by rw [h, zero_mul] at hix; omega`. Use `haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨hi0⟩`. Establish `hcoc : ∀ a b, φ (ρy (a * b) e₀ - e₀) = φ (ρy a e₀ - e₀) + actD Le a (φ (ρy b e₀ - e₀))` using `fun a b => by`.

Rewrite using `[← hφ a _ (Ly.T.sub_mem (Ly.stable b e₀ he₀) he₀) (by rw [map_sub, hp, sub_self]), ← map_add, map_sub, map_mul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hcor` using `CorD.index_smul_mem ((D.loc l).PD K') ((D.loc l).PD K) (Subgroup.inclusion hle) (continuous_subtype_val.subtype_mk _) (Topology.IsEmbedding.inclusion hle) (by rw [Subgroup.inclusion_range]`. Conclude with `(IntermediateField.fixingSubgroup_isOpen K'.1).preimage continuous_subtype_val)`.

Use the proof step `(fun g b => by rw [(D.loc l).PD_actB, (D.loc l).PD_actB]; rfl) VeL`. Use the proof step `(((l : ↥(OL LL)) ^ c) • fun g => φ (ρy g e₀ - e₀))`. Use the proof step `(fun a b => by show ((l : ↥(OL LL)) ^ c) • φ (ρy (a * b) e₀ - e₀) = ((l : ↥(OL LL)) ^ c) • φ (ρy a e₀ - e₀) + actD Le a (((l : ↥(OL LL)) ^ c) • φ (ρy b e₀ - e₀))`. Rewrite using `[hcoc, smul_add, map_smul])`. Use `key`.

Establish `hfin` using `LocRes.pow_val_smul_mem LL _ hi0 hcor`. Rewrite `hcle` using `[hgi]`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hcle`. Rewrite using `[(D.loc l).PD_p, hd, pow_add, mul_comm, mul_smul, pow_add, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hfin`.

Introduce `e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat`. Establish `hε` using `TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat`. Set `VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := Ve, ρ := ρe, cont := hce, L := Le }`. Establish `hT` using `hE K LL e VeL hε.1 hε.2`. Conclude with `TBLoc.tbe_clauses ((D.loc l).PD K) Le _ _ rfl e _ hT.2.1 hT.2.2 (hT.1 _)`.
-/
theorem tbK_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h4 : LocalSituation.Conclusion4 D HW F) (hCo : CrysOnCond D HW F)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hE : ∀ K LL : FinExt l, TwistK.TBe ((D.loc l).PD K) ↥LL.1 ↥(OL LL) (IK K))
    (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : TBK (D.loc l) := by
  intro N h n t K LL hC ht J U hn hb hJ
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
    have hle : GK K' ≤ GK K := GK_le hKK
    have hε := TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat
    let Yt : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Ve, ρ := ρe, cont := hce, L := Le }
    obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle Yt hcrys
    have hχ : ∀ (g : ↥(GK K')) x, (LocRes.res hle VeL).ρ g x =
        ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K').χ g : ℚ_[l]))⁻¹) ^ e • x := fun g x => by
      rw [(D.loc l).PD_χ]
      have := hε.2 (Subgroup.inclusion hle g) x
      rw [(D.loc l).PD_χ] at this
      exact this
    obtain ⟨c, hcle, key⟩ := tb_top D HW F l h4 hCo hW hF N h n t e _ K' LL hg hKs U hn hb he ht hidx
      (LocRes.res hle Yt) (LocRes.res hle VeL) r1 (fun τ a ha => hJ _ (hjmp _ a ((j1 τ a).1 ha))) p
      (fun g v => hp _ v) hint e₀ he₀ hpe hε.1 hχ φ (fun g y hy hy0 => hφ _ y hy hy0)
    haveI := K.2
    haveI := K'.2
    have hix := GlobalTheory.InducedSectionsSpanStatement.inclusion_GK_index K' K hle
    have hpos : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
    have hpos' : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
    have hgi : Module.finrank ℚ_[l] ↥K'.1 / Module.finrank ℚ_[l] ↥K.1 = (Subgroup.inclusion hle).range.index := by
      rw [← hix, Nat.mul_div_cancel _ hpos']
    have hi0 : (Subgroup.inclusion hle).range.index ≠ 0 := fun h => by rw [h, zero_mul] at hix; omega
    haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨hi0⟩
    have hcoc : ∀ a b, φ (ρy (a * b) e₀ - e₀) = φ (ρy a e₀ - e₀) + actD Le a (φ (ρy b e₀ - e₀)) := fun a b => by
      rw [← hφ a _ (Ly.T.sub_mem (Ly.stable b e₀ he₀) he₀) (by rw [map_sub, hp, sub_self]), ← map_add, map_sub, map_mul]
      congr 1
      simp
    have hcor := CorD.index_smul_mem ((D.loc l).PD K') ((D.loc l).PD K) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Topology.IsEmbedding.inclusion hle)
      (by rw [Subgroup.inclusion_range]
          exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage continuous_subtype_val)
      (fun g b => by rw [(D.loc l).PD_actB, (D.loc l).PD_actB]; rfl) VeL
      (((l : ↥(OL LL)) ^ c) • fun g => φ (ρy g e₀ - e₀))
      (fun a b => by
        show ((l : ↥(OL LL)) ^ c) • φ (ρy (a * b) e₀ - e₀) =
          ((l : ↥(OL LL)) ^ c) • φ (ρy a e₀ - e₀) + actD Le a (((l : ↥(OL LL)) ^ c) • φ (ρy b e₀ - e₀))
        rw [hcoc, smul_add, map_smul])
      key
    have hfin := LocRes.pow_val_smul_mem LL _ hi0 hcor
    rw [hgi] at hcle
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcle
    rw [(D.loc l).PD_p, hd, pow_add, mul_comm, mul_smul, pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hfin
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hε := TBLoc.eps_lat ((D.loc l).PD K) (O := ↥(OL LL)) Le.T e hMat
    let VeL : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hE K LL e VeL hε.1 hε.2
    exact TBLoc.tbe_clauses ((D.loc l).PD K) Le _ _ rfl e _ hT.2.1 hT.2.2 (hT.1 _)

end UpperTheory.N

end
