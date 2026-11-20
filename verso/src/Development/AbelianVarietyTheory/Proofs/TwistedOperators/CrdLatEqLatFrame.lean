import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.ConjPlaceRed

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E` to `((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)`. Establish `hts : t = σ s` using `Subtype.ext ht`. Establish `h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ`. Use `Ideal.map_le_iff_le_comap.2 fun c hcw => ?_` and prove the remaining obligations. Take `⟨c', hc', hcc⟩` from `hc c hcw`.

Establish `: σ (oToS F E c) = oToS F E c'`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _`. Rewrite using `[hcc]`. Both sides reduce to the same expression.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, this]`. Conclude with `Ideal.mem_map_of_mem _ hc'`. Rewrite using `[hts]`. Rewrite `hs`, the goal using `[GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]`. Conclude with `h3 hs`.
-/
theorem resS_conj_zero (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (hs : resS F w s = 0) : resS F w' t = 0 := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hs ⊢
  exact h3 hs

/- English proof (translation)
Set `c : Formalism.L2.Herm.intAf F E` to `if b then 1 else 0`. Establish `hc1 : resS F w c = if b then 1 else 0`. Apply the tactic sequence `simp only [c]; split_ifs <;> simp`. Establish `hc2 : resS F w' c = if b then 1 else 0`. Apply the tactic sequence `simp only [c]; split_ifs <;> simp`.

Establish `hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F)`. Apply the tactic sequence `simp only [c]; split_ifs <;> simp`. Establish `h0` using `resS_conj_zero τ w w' hc (s - c) (t - c) (by`. Rewrite using `[AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by`. Rewrite using `[map_sub, hs, hc1, sub_self])`.

Rewrite `h0` using `[map_sub, sub_eq_zero, hc2]`. Conclude with `h0`.
-/
theorem resS_conj_ite (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (b : Prop) [Decidable b] (hs : resS F w s = if b then 1 else 0) : resS F w' t = if b then 1 else 0 := by
  let c : Formalism.L2.Herm.intAf F E := if b then 1 else 0
  have hc1 : resS F w c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hc2 : resS F w' c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [c]; split_ifs <;> simp
  have h0 := resS_conj_zero τ w w' hc (s - c) (t - c) (by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by
    rw [map_sub, hs, hc1, sub_self])
  rw [map_sub, sub_eq_zero, hc2] at h0
  exact h0

end General

variable {D : D7}

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[GlobalTheory.PlaceModel.mem_latFrame]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Establish `e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v` using `V.frame.sum_equivFun v`.

Use `show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0`. Rewrite using `[e]`. Conclude with `hv`. Introduce `hy`. Use `⟨_, hy, ?_⟩` and prove the remaining obligations.

Use `show V.frame.equivFun (∑ i, y i • V.frame i) = y`. Rewrite using `[← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem crdLat_eq_latFrame (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = GlobalTheory.PlaceModel.latFrame V := by
  ext y
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v := V.frame.sum_equivFun v
    show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0
    rw [e]; exact hv
  · intro hy
    refine ⟨_, hy, ?_⟩
    show V.frame.equivFun (∑ i, y i • V.frame i) = y
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjPlaceRed

namespace GlobalTheory.ConjPlaceRed

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Formalism.L2.SG.InstExistsPf.mem_Lv]`. Conclude with `(GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm`.
-/
theorem Lv_eq_latFrame (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := by
  ext y
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv]
  exact (GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm

/- English proof (translation)
Rewrite using `[Lv_eq_latFrame]`. Conclude with `(Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm`.
-/
theorem mem_Lf (D : D7) (v : Fin (Yc D 0).rank → EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) ↔
      v ∈ lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) := by
  rw [Lv_eq_latFrame]
  exact (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm

/- English proof (translation)
Establish `hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔ (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf` using `hx`. Establish `hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔ (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf` using `(Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx`. Use `(GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)), fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩` and prove the remaining obligations.
-/
theorem mem_St_of_Kset (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (hβ : IsFrame β (GlobalTheory.PlaceModel.latFrame (Yc D 0))) (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) :
    x.1 ∈ St β := by
  have hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := hx
  have hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈
        (Formalism.L2.SG.InstExistsPf.instOf D).Lf :=
    (Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx
  refine (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)),
    fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D β x PP PP' hβ hx hc h1`. Rewrite `hβ` using `[crdLat_eq_latFrame]`. Establish `hsd` using `GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)`. Take `⟨m, s, s', hs, hd⟩` from `GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd`. Take `⟨G, hG⟩` from `GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd`.

Take `⟨h, hh⟩` from `mem_St_of_Kset D β x hβ hx`. Establish `hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈ Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((Yc D 0).gram.map (Formalism.UG.inclE (F` using `D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by`. Establish `e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1` using `hh`. Rewrite using `[e]`. Conclude with `x.2`.

Establish `key` using `GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU`. Rewrite `h1`, the goal using `[← hh, redFn_frGL]`. Establish `h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1` using `by rw [map_inv, h1, inv_one]`. Establish `h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Establish `hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0`. Establish `e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i = resS D.host.F PP' ((h⁻¹).val j i)` using `rfl`. Rewrite using `[← e, h1', Units.val_one, Matrix.one_apply]`. Establish `h0` using `resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz`.

Use `h0.trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_one, Matrix.one_apply]`. Conclude with `if_congr eq_comm rfl rfl`. Rewrite `h2` using `[map_mul, map_mul, map_inv]`. Conclude with `conj_eq_one_iff.1 h2`.
-/
theorem redFn_conj_eq_one : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (PP PP' : Formalism.L2.DIV.Pl D.host.E),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset →
    IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' x.1 = 1 → Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  intro D β x PP PP' hβ hx hc h1
  rw [crdLat_eq_latFrame] at hβ
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := mem_St_of_Kset D β x hβ hx
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Yc D 0).gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1 := hh
    rw [e]
    exact x.2
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i =
          resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRed
