import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinAdeleAlgebraMapInj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColClass

/- English proof (translation)
Introduce `D X u F Tr hK hsig hLM`. Establish `hW : WittX X u Tr.wt` using `⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩`. Establish `hA : IsAdeleIso X Tr.ιA` using `⟨Tr.ιA_rat, Tr.ιA_int⟩`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hsig`. Take `⟨h1, h2, -⟩` from `GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ`.

Establish `hc : ∀ c, Tr.hc c = Φ.symm (F.cls0.y c * Tr.h0⁻¹)` using `fun c => by`. Rewrite using `[MulEquiv.eq_symm_apply]`. Conclude with `(hΦ _ _).1 (Tr.hc_rep c)`. Establish `hKu : ∀ h : Hfin X u, h ∈ Ku X u hK ↔ (((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) : GL _ _) ∈ F.cls0.lev.U` using `fun h => (hLM.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1`. Establish `key` using `GlobalTheory.ClassDict.classReps_dictionary D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hfin X u) (iotaF X u) (Ku X u hK) Φ Tr.h0 hKu h1 h2 ((D.mem u).C.cls 0) F.cls0.y F.cls0.y_bij`.

Use `⟨fun h => ?_, fun hst c => ?_⟩` and prove the remaining obligations. Take `⟨c, hc1, hc2⟩` from `key.1 h`. Use `⟨c, ?_, fun c' hc' => hc2 c' ?_⟩` and prove the remaining obligations. Take `⟨γ, κ, e⟩` from `hc1`. Conclude with `⟨γ, κ, by rw [hc]; exact e⟩`.

Take `⟨γ, κ, e⟩` from `hc'`. Conclude with `⟨γ, κ, by rw [← hc]; exact e⟩`. Establish `hsub : Subsingleton ((D.mem u).C.stab 0 c)`. Use `⟨fun s t => ?_⟩` and prove the remaining obligations. Establish `h1' : ∀ s : (D.mem u).C.stab 0 c, s = 1`.

Introduce `s`. Apply `F.cls0.stabI_inj c` to reduce the goal to its premises. Rewrite using `[map_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hr` using `(F.cls0.stabI_range c (F.cls0.stabI c s)).1 ⟨s, rfl⟩`.

Conclude with `key.2 hst c _ (F.cls0.stabI c s).2 hr`. Rewrite using `[h1' s, h1' t]`. Establish `: Nat.card ((D.mem u).C.stab 0 c) = 1` using `by haveI : Unique ((D.mem u).C.stab 0 c) := uniqueOfSubsingleton 1`. Conclude with `Nat.card_unique`. Simplify using `[Formalism.BasicNotions.ColumnChain.wt, this]`.
-/
theorem classes_and_weight : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  intro D X u F Tr hK hsig hLM
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hsig
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  have hc : ∀ c, Tr.hc c = Φ.symm (F.cls0.y c * Tr.h0⁻¹) := fun c => by
    rw [MulEquiv.eq_symm_apply]
    exact (hΦ _ _).1 (Tr.hc_rep c)
  have hKu : ∀ h : Hfin X u, h ∈ Ku X u hK ↔
      (((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) : GL _ _) ∈ F.cls0.lev.U :=
    fun h => (hLM.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1
  have key := GlobalTheory.ClassDict.classReps_dictionary D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hfin X u) (iotaF X u) (Ku X u hK)
    Φ Tr.h0 hKu h1 h2 ((D.mem u).C.cls 0) F.cls0.y F.cls0.y_bij
  refine ⟨fun h => ?_, fun hst c => ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := key.1 h
    refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
    · obtain ⟨γ, κ, e⟩ := hc1
      exact ⟨γ, κ, by rw [hc]; exact e⟩
    · obtain ⟨γ, κ, e⟩ := hc'
      exact ⟨γ, κ, by rw [← hc]; exact e⟩
  · have hsub : Subsingleton ((D.mem u).C.stab 0 c) := by
      refine ⟨fun s t => ?_⟩
      have h1' : ∀ s : (D.mem u).C.stab 0 c, s = 1 := by
        intro s
        apply F.cls0.stabI_inj c
        rw [map_one]
        apply Subtype.ext
        have hr := (F.cls0.stabI_range c (F.cls0.stabI c s)).1 ⟨s, rfl⟩
        exact key.2 hst c _ (F.cls0.stabI c s).2 hr
      rw [h1' s, h1' t]
    have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
      haveI : Unique ((D.mem u).C.stab 0 c) := uniqueOfSubsingleton 1
      exact Nat.card_unique
    simp [Formalism.BasicNotions.ColumnChain.wt, this]

end GlobalTheory.ColClass
