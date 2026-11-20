import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `D S j hK i b x hx`. Take `⟨n, v, hvK, hliK, hspK, hliL, hspL⟩` from `hK`. Set `bL : Module.Basis (Fin n) D.what₂.LL (S.WL j)` to `Module.Basis.mk hliL (by rw [hspL])`. Set `bK0 : Module.Basis (Fin n) S.Ks (Submodule.span S.Ks (Set.range v))` to `Module.Basis.span hliK`. Set `bK : Module.Basis (Fin n) S.Ks (FmK S j)` to `bK0.map (LinearEquiv.ofEq _ _ hspK)`.

Set `ι : FmK S j →ₗ[S.Ks] S.WL j` to `(S.A j).WK.subtype`. Establish `hbK : ∀ r, ι (bK r) = v r`. Introduce `r`. Use `show ((bK0 r : Submodule.span S.Ks (Set.range v)) : S.WL j) = v r`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hliK r)`.

Establish `hbL : ∀ r, bL r = v r` using `by intro r; simp [bL]`. Set `bF : Module.Basis (Fin n) (KB S i b) (Fm S i j b)` to `Algebra.TensorProduct.basis (KB S i b) bK`. Choose the witnesses or unpack the hypotheses as in `⟨r0, ha⟩ : ∃ r0, bL.repr x r0 ≠ 0 := by`. Assume the negation of the conclusion as `h; push_neg at h; exact hx (bL.ext_elem fun r => by simpa using h r)`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : Module.Dual ↥D.LL0 D.what₂.LL, g (bL.repr x r0) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `ha ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)`. Set `f : D.what₂.LL →ₗ[↥D.LL0] ↥D.LL0` to `(g (bL.repr x r0))⁻¹ • g`. Establish `hfa : f (bL.repr x r0) = 1` using `by simp [f, hg]`.

Establish `hfc : ∀ (c : ↥D.LL0) (y : D.what₂.LL), f ((c : D.what₂.LL) * y) = c * f y`. Introduce `c y`. Rewrite using `[show (c : D.what₂.LL) * y = c • y from (Algebra.smul_def c y).symm, map_smul, smul_eq_mul]`. Set `φ : (Fin n → D.what₂.LL) →+ (Fin n → KB S i b)` to `AddMonoidHom.compLeft ((readLL0 S i b).toAddMonoidHom.comp f.toAddMonoidHom) (Fin n)`. Set `Φ : S.WL j →+ Fm S i j b` to `(bF.equivFun.symm.toLinearMap.toAddMonoidHom).comp (φ.comp bL.equivFun.toLinearMap.toAddMonoidHom)`.

Establish `hΦ : ∀ w, bF.equivFun (Φ w) = fun r => readLL0 S i b (f (bL.repr w r))`. Introduce `w`. Use `show bF.equivFun (bF.equivFun.symm (φ (bL.equivFun w))) = _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Use `⟨Φ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `congrFun (hΦ x) r0` as an intermediate fact. Rewrite `this` using `[h0, map_zero, hfa, map_one]`. Conclude with `zero_ne_one this`.

Introduce `c w`. Apply `bF.equivFun.injective` to reduce the goal to its premises. Rewrite using `[hΦ, bF.equivFun.map_smul, hΦ, bL.repr.map_smul]`. Use function extensionality and compare the values at `r`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_smul, Finsupp.smul_apply]`.

Rewrite using `[hfc, map_mul]`. Introduce `T hT w`. Set `T' : Module.End S.Ks (FmK S j)` to `(T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT`. Set `t` to `LinearMap.toMatrix bK bK T'`. Establish `hTm : LinearMap.toMatrix bL bL T = t.map (algebraMap S.Ks D.what₂.LL)`.

Use extensionality with `r q`. Simplify using `only [t, LinearMap.toMatrix_apply, Matrix.map_apply]`. Establish `e1 : T (bL q) = ι (T' (bK q))`. Rewrite using `[hbL, ← hbK]`. Both sides reduce to the same expression.

Establish `e2 : T (bL q) = ∑ s, (algebraMap S.Ks D.what₂.LL (bK.repr (T' (bK q)) s)) • bL s`. Rewrite using `[e1]`. Use `conv_lhs => rw [← bK.sum_repr (T' (bK q))]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hbK, hbL, algebraMap_smul]`. Rewrite using `[e2, Module.Basis.repr_sum_self]`. Apply `bF.equivFun.injective` to reduce the goal to its premises. Establish `hbc : Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' = LinearMap.baseChange (KB S i b) T'` using `rfl`. Express the relevant statement in the definitionally equal form `bF.equivFun (Φ (T w)) = bF.equivFun (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' (Φ w))`.

Rewrite using `[hbc]`. Establish `hMF : LinearMap.toMatrix bF bF (LinearMap.baseChange (KB S i b) T') = t.map (algebraMap S.Ks (KB S i b))` using `LinearMap.toMatrix_baseChange _ _ _ _`. Establish `hL : ∀ r, bL.repr (T w) r = ∑ q, algebraMap S.Ks D.what₂.LL (t r q) * bL.repr w q`. Introduce `r`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr bL bL T w, hTm]`.

Both sides reduce to the same expression. Establish `hKB : ∀ r, bF.equivFun (LinearMap.baseChange (KB S i b) T' (Φ w)) r = ∑ q, algebraMap S.Ks (KB S i b) (t r q) * bF.equivFun (Φ w) q`. Introduce `r`. Establish `h1` using `congrFun (LinearMap.toMatrix_mulVec_repr bF bF (LinearMap.baseChange (KB S i b) T') (Φ w)) r`. Rewrite `h1` using `[hMF]`.

Conclude with `h1.symm`. Use function extensionality and compare the values at `r`. Rewrite using `[hΦ, hKB, hΦ]`. Simplify using `only []`. Rewrite using `[hL, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← S.kKs_spec, hfc, map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_desc_of_isKsForm : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  intro D S j hK i b x hx
  classical
  obtain ⟨n, v, hvK, hliK, hspK, hliL, hspL⟩ := hK
  let bL : Module.Basis (Fin n) D.what₂.LL (S.WL j) := Module.Basis.mk hliL (by rw [hspL])
  let bK0 : Module.Basis (Fin n) S.Ks (Submodule.span S.Ks (Set.range v)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) S.Ks (FmK S j) := bK0.map (LinearEquiv.ofEq _ _ hspK)
  let ι : FmK S j →ₗ[S.Ks] S.WL j := (S.A j).WK.subtype
  have hbK : ∀ r, ι (bK r) = v r := by
    intro r
    show ((bK0 r : Submodule.span S.Ks (Set.range v)) : S.WL j) = v r
    exact congrArg Subtype.val (Module.Basis.span_apply hliK r)
  have hbL : ∀ r, bL r = v r := by intro r; simp [bL]
  let bF : Module.Basis (Fin n) (KB S i b) (Fm S i j b) := Algebra.TensorProduct.basis (KB S i b) bK
  obtain ⟨r0, ha⟩ : ∃ r0, bL.repr x r0 ≠ 0 := by
    by_contra h; push_neg at h; exact hx (bL.ext_elem fun r => by simpa using h r)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ↥D.LL0 D.what₂.LL, g (bL.repr x r0) ≠ 0 := by
    by_contra h; push_neg at h; exact ha ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)
  let f : D.what₂.LL →ₗ[↥D.LL0] ↥D.LL0 := (g (bL.repr x r0))⁻¹ • g
  have hfa : f (bL.repr x r0) = 1 := by simp [f, hg]
  have hfc : ∀ (c : ↥D.LL0) (y : D.what₂.LL), f ((c : D.what₂.LL) * y) = c * f y := by
    intro c y
    rw [show (c : D.what₂.LL) * y = c • y from (Algebra.smul_def c y).symm, map_smul, smul_eq_mul]
  let φ : (Fin n → D.what₂.LL) →+ (Fin n → KB S i b) :=
    AddMonoidHom.compLeft ((readLL0 S i b).toAddMonoidHom.comp f.toAddMonoidHom) (Fin n)
  let Φ : S.WL j →+ Fm S i j b :=
    (bF.equivFun.symm.toLinearMap.toAddMonoidHom).comp (φ.comp bL.equivFun.toLinearMap.toAddMonoidHom)
  have hΦ : ∀ w, bF.equivFun (Φ w) = fun r => readLL0 S i b (f (bL.repr w r)) := by
    intro w
    show bF.equivFun (bF.equivFun.symm (φ (bL.equivFun w))) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun (hΦ x) r0
    rw [h0, map_zero, hfa, map_one] at this
    exact zero_ne_one this
  · intro c w
    apply bF.equivFun.injective
    rw [hΦ, bF.equivFun.map_smul, hΦ, bL.repr.map_smul]
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, Finsupp.smul_apply]
    rw [hfc, map_mul]
  · intro T hT w
    let T' : Module.End S.Ks (FmK S j) := (T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT
    let t := LinearMap.toMatrix bK bK T'
    have hTm : LinearMap.toMatrix bL bL T = t.map (algebraMap S.Ks D.what₂.LL) := by
      ext r q
      simp only [t, LinearMap.toMatrix_apply, Matrix.map_apply]
      have e1 : T (bL q) = ι (T' (bK q)) := by
        rw [hbL, ← hbK]; rfl
      have e2 : T (bL q) = ∑ s, (algebraMap S.Ks D.what₂.LL (bK.repr (T' (bK q)) s)) • bL s := by
        rw [e1]; conv_lhs => rw [← bK.sum_repr (T' (bK q))]
        rw [map_sum]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul, hbK, hbL, algebraMap_smul]
      rw [e2, Module.Basis.repr_sum_self]
    apply bF.equivFun.injective
    have hbc : Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' = LinearMap.baseChange (KB S i b) T' := rfl
    change bF.equivFun (Φ (T w)) = bF.equivFun (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' (Φ w))
    rw [hbc]
    have hMF : LinearMap.toMatrix bF bF (LinearMap.baseChange (KB S i b) T') = t.map (algebraMap S.Ks (KB S i b)) :=
      LinearMap.toMatrix_baseChange _ _ _ _
    have hL : ∀ r, bL.repr (T w) r = ∑ q, algebraMap S.Ks D.what₂.LL (t r q) * bL.repr w q := by
      intro r
      rw [← LinearMap.toMatrix_mulVec_repr bL bL T w, hTm]; rfl
    have hKB : ∀ r, bF.equivFun (LinearMap.baseChange (KB S i b) T' (Φ w)) r =
        ∑ q, algebraMap S.Ks (KB S i b) (t r q) * bF.equivFun (Φ w) q := by
      intro r
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr bF bF (LinearMap.baseChange (KB S i b) T') (Φ w)) r
      rw [hMF] at h1
      exact h1.symm
    funext r
    rw [hΦ, hKB, hΦ]
    simp only []
    rw [hL, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← S.kKs_spec, hfc, map_mul]; rfl

end GlobalTheory
