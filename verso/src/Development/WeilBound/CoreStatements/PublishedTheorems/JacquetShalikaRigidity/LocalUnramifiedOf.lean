import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

/- English proof (translation)
Introduce `hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc`. Use `⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩` and prove the remaining obligations. Introduce `z φ hφ hsat h hh u`. Establish `hcomm` using `(hG0 E a).2.2.2.2.2.2.2.1 w h hh`. Take `⟨hΛ, hrt, hgood, hreg⟩` from `hG5 E a ψ hψ`.

Break down `hsat with rfl | hsat` into its components or cases. Establish `h0 : ∀ g, Wh ψ (0 : XB E a) g = 0` using `fun g => by`. Take `⟨Λ, hΛ'⟩` from `hΛ g`. Rewrite using `[← hΛ' 0 hφ, map_zero]`. Rewrite using `[h0, h0, zero_mul]`.

Set `v : GL (Fin a) (w.adicCompletion E) → ℂ` to `fun x => Wh ψ φ (h * fl a w x)`. Establish `hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ` using `fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk`. Establish `hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a`. Introduce `n hn x`. Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)`.

Rewrite using `[map_mul, ← mul_assoc, hcomm n, mul_assoc]`. Conclude with `WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _`. Set `vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a` to `⟨v, hv⟩`. Establish `hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h`. Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w 1) = _`.

Rewrite using `[map_one, mul_one]`. Distinguish the cases in `h0 : vs = 0`. Establish `e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0` using `fun x => congrFun (congrArg Subtype.val h0) x`. Establish `e1 : Wh ψ φ (h * fl a w u) = 0` using `e u`. Rewrite using `[e1, ← hv1, e 1, zero_mul]`.

Establish `hK` using `Final.GLintComm E w a`. Establish `hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z)`. Use `⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)`. Rewrite using `[map_mul, ← mul_assoc, ← hrt, hfix k hk]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e` using `map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs`. Rewrite `e` using `[Submodule.subtype_apply, Submodule.subtype_apply]`.

Rewrite using `[e, Submodule.coe_smul]`. Use function extensionality and compare the values at `x`. Take `⟨Λ, hΛ'⟩` from `hΛ (h * fl a w x)`. Establish `hfin` using `finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v`. Establish `hfin2` using `finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ`.

Establish `e1` using `(LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin`. Establish `e2` using `(Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2`. Establish `e3` using `hsat.2.2.2 ϖ hϖ j hj`. Establish `key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a, (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x = Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ)`. Introduce `c`.

Rewrite using `[map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]`. Express the relevant statement in the definitionally equal form `_ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)`. Rewrite using `[hrt, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `_ * Wh ψ φ (h * fl a w (x * c.out)) = _`. Rewrite using `[map_mul, mul_assoc]`.

Establish `LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ)`. Rewrite using `[heckeVec, heckeVec]`. Conclude with `e1.trans ((finsum_congr key).trans e2.symm)`. Use `LHS.trans ?_` and prove the remaining obligations. Rewrite using `[e3, map_smul, hΛ' φ hφ]`.

Both sides reduce to the same expression. Establish `heig` using `(hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv`. Use `hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u` as an intermediate fact. Rewrite `this` using `[WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1]`. Conclude with `this`.
-/
theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a,
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a)
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
