import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Topology
open Filter

namespace GlobalTheory.LatFixMod

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/- English proof (translation)
Use `set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef`. Establish `hfg` using `GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT`. Take `⟨G, hG, hGl, hgen⟩` from `hfg`. Establish `hev` using `GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩`. Establish `hall` using `(Filter.eventually_all_finite hG).2 fun u hu => hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN`.

Use `filter_upwards [hev.1, hall] with p hk hp`. Use `⟨hk, fun w hw => ?_⟩` and prove the remaining obligations. Set `U : AddSubgroup (WO S T)` to `{ carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l} zero_mem' := ⟨0, L.zero_mem, by`. Use `GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`.

Rewrite using `[this, smul_zero, add_zero]⟩`. Use the proof step `add_mem' := by`. Introduce and unpack `a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩`. Use `⟨la + lb, L.add_mem hla hlb, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]`.

Normalize the expressions using the abelian group laws. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨la, hla, ea⟩`. Use `⟨-la, L.neg_mem hla, ?_⟩` and prove the remaining obligations. Establish `h0` using `GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)`.

Establish `hz : actO S T p.1 p.2 (0 : WO S T) = 0`. Use `GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Rewrite using `[this]`. Rewrite `h0` using `[add_neg_cancel, hz, ea]`.

Rewrite using `[smul_neg]`. Establish `: actO S T p.1 p.2 (-a) = -(a + N • la)` using `(neg_eq_of_add_eq_zero_right h0.symm).symm`. Rewrite using `[this, neg_add] }`. Use `hgen U (fun α hα u hu => ?_) w hw` and prove the remaining obligations. Take `⟨l, hl, e⟩` from `hp u hu`.

Use `⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l, GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩` and prove the remaining obligations. Use `show actO S T p.1 p.2 _ = _`. Rewrite using `[GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]`.
-/
theorem eventually_keep_cong (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1,
      (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T p.1 p.2 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T p.1 p.2 u = u + N • l := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef
  have hfg := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  obtain ⟨G, hG, hGl, hgen⟩ := hfg
  have hev := GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  have hall := (Filter.eventually_all_finite hG).2 fun u hu =>
    hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN
  filter_upwards [hev.1, hall] with p hk hp
  refine ⟨hk, fun w hw => ?_⟩
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l}
      zero_mem' := ⟨0, L.zero_mem, by
        have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
        rw [zero_smul, zero_smul] at this
        rw [this, smul_zero, add_zero]⟩
      add_mem' := by
        rintro a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩
        refine ⟨la + lb, L.add_mem hla hlb, ?_⟩
        rw [GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]
        abel
      neg_mem' := by
        rintro a ⟨la, hla, ea⟩
        refine ⟨-la, L.neg_mem hla, ?_⟩
        have h0 := GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)
        have hz : actO S T p.1 p.2 (0 : WO S T) = 0 := by
          have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
          rw [zero_smul, zero_smul] at this
          rw [this]
        rw [add_neg_cancel, hz, ea] at h0
        rw [smul_neg]
        have : actO S T p.1 p.2 (-a) = -(a + N • la) := (neg_eq_of_add_eq_zero_right h0.symm).symm
        rw [this, neg_add] }
  refine hgen U (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
  show actO S T p.1 p.2 _ = _
  rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]

def KeepMod (S T : HSp D) (L : AddSubgroup (WO S T)) (N : ℕ) (x : GA D S) : Prop :=
  (∀ u ∈ L, actO S T x 1 u ∈ L) ∧ ∀ u ∈ L, ∃ l ∈ L, actO S T x 1 u = u + N • l

/- English proof (translation)
Introduce `D S T ΛS ΛT hS hT N hN`. Use `haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Establish `hev` using `eventually_keep_cong S T ΛS ΛT hS hT N hN`. Establish `t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1)`. Use `((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1` as an intermediate fact.

Conclude with `this`. Establish `t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1)`. Use `((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1` as an intermediate fact. Rewrite `this` using `[inv_one, Prod.mk_one_one]`. Then use the resulting hypothesis. Establish `hx : ∀ᶠ x in 𝓝 (1 : GA D S), KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧ KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹` using `(t1.eventually hev).and (t2.eventually hev)`.

Establish `key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k → KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧ KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) …`. Assume the negation of the conclusion as `hne`. Establish `hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧ ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧ KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D. …` using `fun n => by`. Assume the negation of the conclusion as `h`. Conclude with `hne ⟨n, fun k hk hc => by`.

Assume the negation of the conclusion as `h'`. Conclude with `h ⟨k, hk, hc, h'⟩⟩`. Use `choose k hk hkc hkne using hne'`. Establish `ht` using `GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc`. Take `⟨n, hn⟩` from `(ht.eventually hx).exists`.

Conclude with `hkne n hn`. Take `⟨n, hn⟩` from `key`. Use `⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict, GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩` and prove the remaining obligations. Take `⟨k', hk', e⟩` from `Subgroup.mem_map.1 hJ`. Establish `e' : finHom S k' = finHom S x` using `congrArg Subtype.val e`.

Establish `hc : GlobalTheory.Member.FinCong S n.factorial x`. Use `hk'.2` as an intermediate fact. Unfold `GlobalTheory.Member.FinCong at this ⊢`. Rewrite using `[← e']`. Conclude with `this`.

Take `⟨⟨h1, h2⟩, h3, -⟩` from `hn x hxf hc`. Use `⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩` and prove the remaining obligations. Establish `e2` using `GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u`. Rewrite `e2` using `[inv_one]`. Rewrite using `[← e2]`.

Conclude with `h3 _ hu`.
-/
theorem exists_open_keep_cong : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J →
      (∀ u : WO S T, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
        actO S T x 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T x 1 u = u + N • l := by
  intro D S T ΛS ΛT hS hT N hN
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hev := eventually_keep_cong S T ΛS ΛT hS hT N hN
  have t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1
    exact this
  have t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1
    rwa [inv_one, Prod.mk_one_one] at this
  have hx : ∀ᶠ x in 𝓝 (1 : GA D S),
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹ :=
    (t1.eventually hev).and (t2.eventually hev)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k →
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹ := by
    by_contra hne
    have hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧
        ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
          KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹) :=
      fun n => by
        by_contra h
        exact hne ⟨n, fun k hk hc => by
          by_contra h'
          exact h ⟨k, hk, hc, h'⟩⟩
    choose k hk hkc hkne using hne'
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hx).exists
    exact hkne n hn
  obtain ⟨n, hn⟩ := key
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S x := congrArg Subtype.val e
  have hc : GlobalTheory.Member.FinCong S n.factorial x := by
    have := hk'.2
    unfold GlobalTheory.Member.FinCong at this ⊢
    rw [← e']
    exact this
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hn x hxf hc
  refine ⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩
  have e2 := GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u
  rw [inv_one] at e2
  rw [← e2]
  exact h3 _ hu

end GlobalTheory.LatFixMod
