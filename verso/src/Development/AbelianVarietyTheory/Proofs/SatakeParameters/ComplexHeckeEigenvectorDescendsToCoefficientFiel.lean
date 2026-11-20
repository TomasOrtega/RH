import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

/- English proof (translation)
Introduce `D M B j w μ h1 h2 hμ φ hφ κ y hy hgen`. Substitute `hμ` using the available equality. Use `haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w`. Use `haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)`.

Establish `hjb` using `D.what₂.jMt_basis (D.what₂.muTw w) j b`. Set `bC` to `Module.Basis.mk hjb.1 hjb.2.ge`. Establish `hb` using `B.iV_basis j w b`. Set `bV` to `Module.Basis.mk hb.1 hb.2.ge`. Establish `hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a)` using `fun a => by simp [bC]`.

Establish `hbV : ∀ a, bV a = B.iV j w (b a)` using `fun a => by simp [bV]`. Establish `rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r)` using `fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r`. Establish `rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r)` using `fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r`. Set `A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL` to `fun v k => LinearMap.toMatrix b b (B.hL j w v k)`. Set `G` to `{p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}`.

Set `Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w))` to `fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1`. Establish `hd : (⇑(bC.repr y)) ≠ 0`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Establish `h' : bC.repr y = 0` using `Finsupp.coe_eq_zero.1 h`.

Conclude with `bC.repr.injective (h'.trans (map_zero _).symm)`. Establish `hC : ∀ g : G, Matrix.mulVec ((Mg g).map φ) (⇑(bC.repr y)) = 0`. Introduce and unpack `⟨⟨v, k⟩, hvk⟩`. Take `⟨s, ϖ, hc, hu, hadd, heig⟩` from `hgen v k hvk`. Use `set Mw := M (D.what₂.muTw w) j h1 h2 with hMw`.

Set `tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j)` to `bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))`. Establish `htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0`. Use `hadd 1 0 0` as an intermediate fact. Rewrite `this` using `[one_smul, add_zero, one_smul]`. Simplify using `using this`.

Set `Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W)` to `{ toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y) map_add' := fun y y' => by`. Use `hadd 1 (Mw.real y) (Mw.real y')` as an intermediate fact. Rewrite `this` using `[one_smul, one_smul]`. Simplify using `only [map_add]`. Conclude with `this`.

Use the proof step `map_smul' := fun c y => by`. Use `hadd c (Mw.real y) 0` as an intermediate fact. Rewrite `this` using `[add_zero, htN0, add_zero]`. Simplify using `only [map_smul, RingHom.id_apply]`. Conclude with `this }`.

Establish `hagree : ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x)`. Establish `hLt : Lt = Mw.real.comp tC` using `bC.ext fun a => by`. Establish `e` using `bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a`. Use `show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) = Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))`. Rewrite using `[e, hbC a]`.

Conclude with `(B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm`. Introduce `x`. Conclude with `LinearMap.congr_fun hLt x`. Establish `hty : tC y = φ (κ v k) • y`. Apply `Mw.real_inj` to reduce the goal to its premises.

Rewrite using `[← hagree, heig, map_smul]`. Establish `hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL`. Use extensionality with `r c`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply]`. Establish `e` using `bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c`.

Use `show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _`. Rewrite using `[e, rC]`. Simplify using `only [A, LinearMap.toMatrix_apply]`. Establish `hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1`. Use extensionality with `r c`.

Simplify using `only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp [hφ]`. Rewrite using `[hMg, Matrix.sub_mulVec, ← hmat, LinearMap.toMatrix_mulVec_repr, hty, Matrix.smul_mulVec, Matrix.one_mulVec, map_smul, Finsupp.coe_smul, sub_self]`. Take `⟨c, hc0, hcM⟩` from `GlobalTheory.PtLocalEig.descent φ Mg (⇑(bC.repr y)) hd hC`. Use `⟨bV.equivFun.symm c, ?_, fun v k hvk => ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hc0` to reduce the goal to its premises. Use `congrArg bV.equivFun h` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis. Apply `bV.equivFun.injective` to reduce the goal to its premises.

Establish `hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w)`. Use extensionality with `r c'`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]`. Simplify using `only [A, LinearMap.toMatrix_apply]`. Establish `hM` using `hcM ⟨(v, k), hvk⟩`.

Simplify using `only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hM`. Establish `hr` using `LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)`. Rewrite `hr` using `[hmat]`. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hM]`.
-/
theorem eig_descends : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  intro D M B j w μ h1 h2 hμ φ hφ κ y hy hgen
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  have hd : (⇑(bC.repr y)) ≠ 0 := by
    intro h
    apply hy
    have h' : bC.repr y = 0 := Finsupp.coe_eq_zero.1 h
    exact bC.repr.injective (h'.trans (map_zero _).symm)
  have hC : ∀ g : G, Matrix.mulVec ((Mg g).map φ) (⇑(bC.repr y)) = 0 := by
    rintro ⟨⟨v, k⟩, hvk⟩
    obtain ⟨s, ϖ, hc, hu, hadd, heig⟩ := hgen v k hvk
    set Mw := M (D.what₂.muTw w) j h1 h2 with hMw
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := hadd 1 0 0
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := hadd 1 (Mw.real y) (Mw.real y')
          rw [one_smul, one_smul] at this
          simp only [map_add]
          exact this
        map_smul' := fun c y => by
          have := hadd c (Mw.real y) 0
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hagree : ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hty : tC y = φ (κ v k) • y := by
      apply Mw.real_inj
      rw [← hagree, heig, map_smul]
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    rw [hMg, Matrix.sub_mulVec, ← hmat, LinearMap.toMatrix_mulVec_repr, hty, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_smul, Finsupp.coe_smul, sub_self]
  obtain ⟨c, hc0, hcM⟩ := GlobalTheory.PtLocalEig.descent φ Mg (⇑(bC.repr y)) hd hC
  refine ⟨bV.equivFun.symm c, ?_, fun v k hvk => ?_⟩
  · intro h
    apply hc0
    have := congrArg bV.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · apply bV.equivFun.injective
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hM := hcM ⟨(v, k), hvk⟩
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hM
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    rw [map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply, hM]

end GlobalTheory.PtLocalEig
