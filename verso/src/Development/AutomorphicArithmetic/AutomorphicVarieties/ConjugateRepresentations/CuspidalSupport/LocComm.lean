import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Establish `h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer → GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = GLint (Fin a) O`. Introduce and unpack `_ rfl`. Both sides reduce to the same expression. Conclude with `h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)`.
-/
private theorem kgl_eq (w : Pl E) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = KGL w a := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = GLint (Fin a) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

/- English proof (translation)
Establish `H : ∀ v, GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) = GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u)` using `fun v => by`. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[hu, mul_one, one_mul]`.

Rewrite using `[pLoc_locGL_of_ne hv, mul_one, one_mul]`. Use extensionality with `i j : 2`. Conclude with `FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)`.
-/
private theorem loc_comm (w : Pl E) (g : GL (Fin a) (w.adicCompletion E)) {u : GL (Fin a) (Af E)}
    (hu : GeneralLinearGroup.map (pLoc E w) u = 1) : u * locGL E a w g = locGL E a w g * u := by
  have H : ∀ v, GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
      GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hu, mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hc E _ _ _ a φ m B h k hk`. Establish `hne : rt E a k φ ≠ 0` using `fun e => h.ne (by`. Use `congrArg (rt E a k⁻¹) e` as an intermediate fact. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)` and apply the resulting hypothesis. Use `⟨hne, (Cm.isAutForm_iff _).2 (((Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk), fun t => ⟨(h.cap t).1, fun u => ?_⟩, h.sat.mono fun w hw => ?_⟩` and prove the remaining obligations.

Establish `e` using `LinearMap.congr_fun ((hc E a t u).1 k).eq φ`. Simplify using `only [Module.End.mul_apply] at e`. Rewrite using `[e, (h.cap t).2 u, map_smul]`. Use `set kf := GeneralLinearGroup.map (pFin E) k with hkf set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw`. Establish `hmem : kw ∈ KGL w a`.

Rewrite using `[← kgl_eq]`. Establish `e : kw = GroundTheory.Automorphic.Reduction.finAt w k`. Use extensionality with `i j : 2`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hk.2 w`. Use `set u := kf * (locGL E a w kw)⁻¹ with hu`. Establish `hu1 : GeneralLinearGroup.map (pLoc E w) u = 1`. Rewrite using `[hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]`. Use `set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'`.

Establish `hdec : k' * finGL E a (locGL E a w kw) = k`. Rewrite using `[hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]`. Establish `hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ` using `GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw hmem`. Establish `e : rt E a k' φ = rt E a k φ` using `by conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]`. Rewrite `hne`, the goal using `[← e]`.

Use `hw.map (rt E a k') (fun g y => ?_) hne` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)`. Establish `hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k'`. Rewrite using `[hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc, infGL_comm _ (locGL E a w g)]`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]`.
-/
theorem UpperTheory.V.Cj.S.rtK :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.RtK := by
  intro hc E _ _ _ a φ m B h k hk
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  refine ⟨hne, (Cm.isAutForm_iff _).2 (((Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    fun t => ⟨(h.cap t).1, fun u => ?_⟩, h.sat.mono fun w hw => ?_⟩
  · have e := LinearMap.congr_fun ((hc E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · set kf := GeneralLinearGroup.map (pFin E) k with hkf
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    have hmem : kw ∈ KGL w a := by
      rw [← kgl_eq]
      have e : kw = GroundTheory.Automorphic.Reduction.finAt w k := by
        ext i j : 2
        rfl
      rw [e]
      exact hk.2 w
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw hmem
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]
