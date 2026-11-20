import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.jumpWindows

namespace WeilJacquetShalikaLaw

section Loc

variable {F : Type} [Field F] {a : ℕ}

def WS (χ : AddChar F ℂ) (a : ℕ) : Submodule ℂ (GL (Fin a) F → ℂ) where
  carrier := {W | ∀ n ∈ GroundTheory.Automorphic.Iwasawa.unipotent F a, ∀ g,
    W (n * g) = GroundTheory.Automorphic.Whittaker.psiN χ n * W g}
  add_mem' {W W'} hW hW' n hn g := by
    simp only [Pi.add_apply, hW n hn g, hW' n hn g, mul_add]
  zero_mem' n hn g := by simp
  smul_mem' c W hW n hn g := by
    simp only [Pi.smul_apply, smul_eq_mul, hW n hn g]
    ring

/- English proof (translation)
Introduce `g v hv n hn x`. Express the relevant statement in the definitionally equal form `v (n * x * g) = _ * v (x * g)`. Rewrite using `[mul_assoc]`. Conclude with `hv n hn _`.
-/
theorem WS_stable (χ : AddChar F ℂ) (a : ℕ) :
    ∀ g, ∀ v ∈ WS χ a, GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ g v ∈ WS χ a := by
  intro g v hv n hn x
  change v (n * x * g) = _ * v (x * g)
  rw [mul_assoc]
  exact hv n hn _

def rhoW (χ : AddChar F ℂ) (a : ℕ) : Representation ℂ (GL (Fin a) F) (WS χ a) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ) (WS χ a) (WS_stable χ a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rhoW_apply (χ : AddChar F ℂ) (g x : GL (Fin a) F) (v : WS χ a) :
    (rhoW χ a g v : GL (Fin a) F → ℂ) x = (v : GL (Fin a) F → ℂ) (x * g) := rfl

def ev (χ : AddChar F ℂ) (a : ℕ) : WS χ a →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) F => ℂ) 1).comp (WS χ a).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_apply (χ : AddChar F ℂ) (v : WS χ a) : ev χ a v = (v : GL (Fin a) F → ℂ) 1 := rfl

/- English proof (translation)
Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem sd_eq (M : Matrix (Fin a) (Fin a) F) :
    GroundTheory.Automorphic.Whittaker.superdiagSum M = ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, M p.1 p.2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rfl

end Loc

/- English proof (translation)
Substitute `hB` using the available equality. Use `⟨fun i => B.toList.get ⟨i, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map]`. Use `conv_lhs => rw [← Multiset.coe_toList B]`. Use `congr 1`.

Use `List.ext_get (by simp) fun n h1 h2 => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_unit_one_add_generator {a : ℕ} (B : Multiset ℂˣ) (hB : B.card = a) : ∃ z : Fin a → ℂˣ, B = Finset.univ.val.map z := by
  subst hB
  refine ⟨fun i => B.toList.get ⟨i, by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  conv_lhs => rw [← Multiset.coe_toList B]
  congr 1
  refine List.ext_get (by simp) fun n h1 h2 => ?_
  simp

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def psiW (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ :=
  ψ.compAddMonoidHom ((sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom)

/- English proof (translation)
Take `⟨h1, ϖ, y, hϖ, hy, hne⟩` from `hc`. Use `⟨fun x hx => h1 x (by rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w]; exact hx), ⟨y, ?_, hne⟩, fun x => hψ.norm _⟩` and prove the remaining obligations. Use `(SetLike.ext_iff.1 (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w) _).2 ?_` and prove the remaining obligations. Establish `hu` using `PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.isUnifV_uniformizer w`. Express the relevant statement in the definitionally equal form `Valued.v (_ * y) ≤ 1`.

Express the relevant statement in the definitionally equal form `Valued.v (ϖ * y) ≤ 1 at hy`. Rewrite `hy`, the goal using `[map_mul]`. Rewrite using `[hu]`. Rewrite `hy` using `[hϖ]`. Conclude with `hy`.
-/
theorem psiOK {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {w : Pl E} (hc : Cond ψ w) :
    PositivityTheory.JacquetShalikaLocal.PsiOK (psiW ψ w) := by
  obtain ⟨h1, ϖ, y, hϖ, hy, hne⟩ := hc
  refine ⟨fun x hx => h1 x (by rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w]; exact hx), ⟨y, ?_, hne⟩, fun x => hψ.norm _⟩
  refine (SetLike.ext_iff.1 (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w) _).2 ?_
  have hu := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.isUnifV_uniformizer w
  change Valued.v (_ * y) ≤ 1
  change Valued.v (ϖ * y) ≤ 1 at hy
  rw [map_mul] at hy ⊢
  rw [hu]
  rw [hϖ] at hy
  exact hy

/- English proof (translation)
Simplify using `only [dot, eLast, lastE]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dot_eLast {k : ℕ} (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Take `⟨t1, t2, t3⟩` from `GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w n (fun i j hij => hn.1 hij) hn.2`. Use `GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ f (fun k hk y g => by rw [dot_eLast]; exact hf k hk y g) _ t1 t2 g` as an intermediate fact. Express the relevant statement in the definitionally equal form `f (finGL E a (locGL E a w n) * g) = _`. Rewrite using `[this, t3, GroundTheory.Automorphic.Whittaker.psiN, sd_eq]`. Both sides reduce to the same expression.
-/
theorem law [IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ} {f : GA E a → ℂ}
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, f (blkU y * g) = ψ (lastE k y) * f g)
    (w : Pl E) (n : GL (Fin a) (w.adicCompletion E)) (hn : n ∈ GroundTheory.Automorphic.Iwasawa.unipotent _ a)
    (g : GA E a) : f (fl a w n * g) = GroundTheory.Automorphic.Whittaker.psiN (psiW ψ w) n * f g := by
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w n (fun i j hij => hn.1 hij) hn.2
  have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ f (fun k hk y g => by rw [dot_eLast]; exact hf k hk y g) _ t1 t2 g
  change f (finGL E a (locGL E a w n) * g) = _
  rw [this, t3, GroundTheory.Automorphic.Whittaker.psiN, sd_eq]
  rfl

/- English proof (translation)
Introduce `g hg u`. Rewrite using `[ev_apply, ev_apply, rhoW_apply, one_mul]`. Use `u.2 g hg 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem whitW (w : Pl E) (χ : AddChar (w.adicCompletion E) ℂ) :
    PositivityTheory.JacquetShalikaLocal.Whit (rhoW χ a) χ (ev χ a) := by
  intro g hg u
  rw [ev_apply, ev_apply, rhoW_apply, one_mul]
  have := u.2 g hg 1
  rwa [mul_one] at this

end WeilJacquetShalikaLaw

/- English proof (translation)
Introduce `hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc B φ hφ hsat h hh hWh u`. Establish `hcomm` using `(hG0 E a).2.2.2.2.2.2.2.1 w h hh`. Take `⟨hΛ, hrt, hgood, hreg⟩` from `hG5 E a ψ hψ`. Break down `hsat with rfl | hsat` into its components or cases. Take `⟨Λ, hΛ'⟩` from `hΛ (h * fl a w u)`.

Rewrite using `[← hΛ' 0 hφ, map_zero]`. Take `⟨z, hz⟩` from `WeilJacquetShalikaLaw.exists_unit_one_add_generator B hsat.2.2.1`. Set `v : GL (Fin a) (w.adicCompletion E) → ℂ` to `fun x => Wh ψ φ (h * fl a w x)`. Establish `hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ` using `fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk`. Establish `hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a`.

Introduce `n hn x`. Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)`. Rewrite using `[map_mul, ← mul_assoc, hcomm n, mul_assoc]`. Conclude with `WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _`. Set `vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a` to `⟨v, hv⟩`.

Establish `hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = 0`. Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w 1) = 0`. Rewrite using `[map_one, mul_one]`. Conclude with `hWh`. Distinguish the cases in `h0 : vs = 0`.

Conclude with `congrFun (congrArg Subtype.val h0) u`. Establish `hK` using `Final.GLintComm E w a`. Establish `hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z)`. Use `⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)`. Rewrite using `[map_mul, ← mul_assoc, ← hrt, hfix k hk]`. Rewrite using `[← hz]`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e` using `map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs`. Rewrite `e` using `[Submodule.subtype_apply, Submodule.subtype_apply]`. Rewrite using `[e, Submodule.coe_smul]`. Use function extensionality and compare the values at `x`. Take `⟨Λ, hΛ'⟩` from `hΛ (h * fl a w x)`.

Establish `hfin` using `finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v`. Establish `hfin2` using `finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ`. Establish `e1` using `(LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin`. Establish `e2` using `(Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2`. Establish `e3` using `hsat.2.2.2 ϖ hϖ j hj`.

Establish `key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a, (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x = Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ)`. Introduce `c`. Rewrite using `[map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]`. Express the relevant statement in the definitionally equal form `_ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)`. Rewrite using `[hrt, smul_eq_mul]`.

Express the relevant statement in the definitionally equal form `_ * Wh ψ φ (h * fl a w (x * c.out)) = _`. Rewrite using `[map_mul, mul_assoc]`. Establish `LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ)`. Rewrite using `[heckeVec, heckeVec]`. Conclude with `e1.trans ((finsum_congr key).trans e2.symm)`.

Use `LHS.trans ?_` and prove the remaining obligations. Rewrite using `[e3, map_smul, hΛ' φ hφ]`. Both sides reduce to the same expression. Establish `heig` using `(hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv`. Use `hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u` as an intermediate fact.

Rewrite `this` using `[WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1, zero_mul]`. Conclude with `this`.
-/
theorem whittaker_uniqueness_local : PositivityTheory.JacquetShalikaLocal.L7 → PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂ → G0 → G5 → G9 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc B φ hφ hsat h hh hWh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w u)
    rw [← hΛ' 0 hφ, map_zero]
  obtain ⟨z, hz⟩ := WeilJacquetShalikaLaw.exists_unit_one_add_generator B hsat.2.2.1
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = 0 := by
    change Wh ψ φ (h * fl a w 1) = 0
    rw [map_one, mul_one]
    exact hWh
  by_cases h0 : vs = 0
  · exact congrFun (congrArg Subtype.val h0) u
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · rw [← hz]
      apply Subtype.ext
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
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1, zero_mul] at this
  exact this

end PositivityTheory.jumpWindows

end
