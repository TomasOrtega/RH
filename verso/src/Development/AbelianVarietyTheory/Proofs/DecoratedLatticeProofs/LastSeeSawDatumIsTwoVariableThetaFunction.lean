import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastBiTheta

variable {D : D7}

/- English proof (translation)
Simplify using `[symplOH, symplO, hO]`.
-/
theorem sOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

/- English proof (translation)
Simplify using `[symplOH, symplO, hO]`.
-/
theorem sOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

/- English proof (translation)
Rewrite using `[o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`.
-/
theorem sOH_resS_symm {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) (a a' : WO A S) (b b' : WO L S) :
    symplOH V₀ S ((o.resS S).symm (a, b)) ((o.resS S).symm (a', b')) = symplOH A S a a' + symplOH L S b b' := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨γ, rfl⟩` from `hx`. Conclude with `h.quasi γ w`.
-/
theorem quasi_of_mem {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    {x : WO S T} (hx : x ∈ ratMx D T.rank S.rank) (w : WO S T) : f (x + w) = ψ (-(symplOH S T x w)) * f w := by
  obtain ⟨γ, rfl⟩ := hx
  exact h.quasi γ w

/- English proof (translation)
Rewrite using `[OrthDec.resS_symm_apply]`. Conclude with `add_mem (ratMx_mul ha (rat_mem _)) (ratMx_mul hb (rat_mem _))`.
-/
theorem resS_symm_mem {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : a ∈ ratMx D S.rank A.rank) (hb : b ∈ ratMx D S.rank L.rank) :
    (o.resS S).symm (a, b) ∈ ratMx D S.rank V₀.rank := by
  rw [OrthDec.resS_symm_apply]
  exact add_mem (ratMx_mul ha (rat_mem _)) (ratMx_mul hb (rat_mem _))

/- English proof (translation)
Rewrite using `[OrthDec.resS_symm_apply, Matrix.map_add φ (map_add φ), map_mul_eq_zero_left φ ha, map_mul_eq_zero_left φ hb, add_zero]`.
-/
theorem resS_symm_map {B : Type} [CommRing B] (φ : AE D →+* B) {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D)
    {a : WO A S} {b : WO L S} (ha : a.map φ = 0) (hb : b.map φ = 0) : ((o.resS S).symm (a, b)).map φ = 0 := by
  rw [OrthDec.resS_symm_apply, Matrix.map_add φ (map_add φ), map_mul_eq_zero_left φ ha, map_mul_eq_zero_left φ hb,
    add_zero]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ _ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ`. Take `⟨kadd, kcont, krat, -, ksympl, kpart⟩` from `GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)`. Establish `kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w'` using `fun w w' => by`. Unfold `symplOH`. Rewrite using `[ksympl]`.

Simplify using `only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]`. Establish `hC : ∀ u v, lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2))` using `fun _ _ => rfl`. Set `K : WO S L'' →+ WO L S` to `AddMonoidHom.mk' (kap τ S) kadd`. Set `P1 : WO S X →+ WO S T` to `(AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom`. Set `P2 : WO S X →+ WO S L''` to `(AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom`.

Establish `cP1 : Continuous fun b : WO S X => (o''.resT S b).1` using `continuous_fst.comp (o''.continuous_resT S)`. Establish `cP2 : Continuous fun b : WO S X => (o''.resT S b).2` using `continuous_snd.comp (o''.continuous_resT S)`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun p : WO A S × WO S X => Φ₂ (o''.resT S p.2).1 * Ξ ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2))`. Conclude with `(hΦ.cont.comp (cP1.comp continuous_snd)).mul (hΞ.cont.comp ((o.continuous_resS_symm S).comp (continuous_fst.prodMk (kcont.comp (cP2.comp continuous_snd)))))`.

Introduce `n L₁ L₂ hL₁ hL₂ hf₁ hf₂ u v`. Set `M₁ : (Fin n → ℝ) →+ WO S T` to `P1.comp L₂`. Set `M₂ : (Fin n → ℝ) →+ WO V₀ S` to `(o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.prod L₁ (K.comp (P2.comp L₂)))`. Establish `cM₁ : Continuous M₁` using `cP1.comp hL₂`. Establish `cM₂ : Continuous M₂` using `(o.continuous_resS_symm S).comp (hL₁.prodMk (kcont.comp (cP2.comp hL₂)))`.

Establish `fM₁ : ∀ t, (M₁ t).map (finPart D) = 0` using `fun t => map_mul_eq_zero_right (finPart D) _ (hf₂ t)`. Establish `fM₂ : ∀ t, (M₂ t).map (finPart D) = 0` using `fun t => resS_symm_map (finPart D) o S (hf₁ t) ((kpart _).2 (map_mul_eq_zero_right (finPart D) _ (hf₂ t)))`. Establish `e : (fun t => lastBi o o'' τ Ξ Φ₂ (u + L₁ t) (v + L₂ t)) = fun t => Φ₂ ((o''.resT S v).1 + M₁ t) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + M₂ t)`. Use function extensionality and compare the values at `t`. Rewrite using `[hC]`.

Use `show Φ₂ (o''.resT S (v + L₂ t)).1 * Ξ ((o.resS S).symm (u + L₁ t, kap τ S (o''.resT S (v + L₂ t)).2)) = Φ₂ ((o''.resT S v).1 + (o''.resT S (L₂ t)).1) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (L₁ t, kap τ S (o''.resT S (L₂ t)).2))`. Rewrite using `[map_add, Prod.fst_add, Prod.snd_add, kadd, ← map_add, Prod.mk_add_mk]`. Rewrite using `[e]`. Conclude with `(hΦ.smooth n M₁ cM₁ fM₁ _).mul (hΞ.smooth n M₂ cM₂ fM₂ _)`. Introduce `γ u v`.

Rewrite using `[hC, hC]`. Establish `e : (o.resS S).symm (ratW S A γ + u, kap τ S (o''.resT S v).2) = (o.resS S).symm (ratW S A γ, 0) + (o.resS S).symm (u, kap τ S (o''.resT S v).2)`. Rewrite using `[← map_add, Prod.mk_add_mk, zero_add]`. Establish `hγ : ratW S A γ ∈ ratMx D S.rank A.rank` using `rat_mem γ`. Rewrite using `[e, quasi_of_mem hΞ (resS_symm_mem o S hγ (zero_mem _)), sOH_resS_symm, sOH_zero_left, add_zero]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `γ u v`. Rewrite using `[hC, hC]`. Establish `h1 : (o''.resT S (ratW X S γ)).1 ∈ ratMx D T.rank S.rank` using `ratMx_mul (rat_mem _) (rat_mem γ)`. Establish `h2 : (o''.resT S (ratW X S γ)).2 ∈ ratMx D L''.rank S.rank` using `ratMx_mul (rat_mem _) (rat_mem γ)`.

Establish `e : (o.resS S).symm (u, kap τ S ((o''.resT S (ratW X S γ)).2 + (o''.resT S v).2)) = (o.resS S).symm (0, kap τ S (o''.resT S (ratW X S γ)).2) + (o.resS S).symm (u, kap τ S (o''.resT S v).2)`. Rewrite using `[kadd, ← map_add, Prod.mk_add_mk, zero_add]`. Establish `ph : ψ (-symplOH S X (ratW X S γ) v) = ψ (-symplOH S T (o''.resT S (ratW X S γ)).1 (o''.resT S v).1) * ψ (-symplOH S L'' (o''.resT S (ratW X S γ)).2 (o''.resT S v).2)`. Rewrite using `[← AddChar.map_add_eq_mul, o''.symplOH_resT S (ratW X S γ) v]`. Conclude with `congrArg ψ (neg_add _ _)`.

Rewrite using `[map_add, Prod.fst_add, Prod.snd_add, e, quasi_of_mem hΦ h1, quasi_of_mem hΞ (resS_symm_mem o S (zero_mem _) (krat _ h2)), sOH_resS_symm, sOH_zero_left, zero_add, kH, ph]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hUo, hU⟩` from `hΞ.level`. Set `iA : WO A S →+ WO V₀ S` to `(o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)`. Establish `ciA : Continuous fun a : WO A S => (o.resS S).symm (a, 0)` using `(o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)`.

Use `⟨U.comap iA, hUo.preimage ciA, fun a ha hinf v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Establish `h1` using `congrFun (hU (iA a) ha (resS_symm_map (infPart D) o S hinf (by simp))) ((o.resS S).symm (u, kap τ S (o''.resT S v).2))`. Establish `e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) = (o.resS S).symm (u, kap τ S (o''.resT S v).2) + iA a` using `by show _ = _ + (o.resS S).symm (a, 0)`. Rewrite using `[← map_add, Prod.mk_add_mk, add_zero]`.

Establish `ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) (iA a) = symplOH A S u a` using `by show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (a, 0)) = _`. Rewrite using `[sOH_resS_symm, sOH_zero_right, add_zero]`. Simplify using `only [heisO] at h1 ⊢`. Rewrite `h1` using `[ph]`. Rewrite using `[hC, hC, e, ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨UΞ, hUΞo, hUΞ⟩` from `hΞ.level`. Take `⟨UΦ, hUΦo, hUΦ⟩` from `hΦ.level`. Set `jL : WO S X →+ WO V₀ S` to `(o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (K.comp P2))`. Establish `cjL : Continuous fun b : WO S X => (o.resS S).symm (0, kap τ S (o''.resT S b).2)` using `(o.continuous_resS_symm S).comp (continuous_const.prodMk (kcont.comp cP2))`.

Use `⟨UΦ.comap P1 ⊓ UΞ.comap jL, (hUΦo.preimage cP1).inter (hUΞo.preimage cjL), fun b hb hinf u => ?_⟩` and prove the remaining obligations. Establish `hT : (o''.resT S b).1.map (infPart D) = 0` using `map_mul_eq_zero_right (infPart D) _ hinf`. Establish `hJ : (jL b).map (infPart D) = 0` using `resS_symm_map (infPart D) o S (by simp) ((kpart _).1 (map_mul_eq_zero_right (infPart D) _ hinf))`. Use `show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) = o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))`. Rewrite using `[o''.heisO_boxT, hUΦ (o''.resT S b).1 hb.1 hT]`.

Use `congr 1`. Use function extensionality and compare the values at `w`. Establish `h2` using `congrFun (hUΞ (jL b) hb.2 hJ) ((o.resS S).symm (u, kap τ S w))`. Establish `e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) = (o.resS S).symm (u, kap τ S w) + jL b` using `by show _ = _ + (o.resS S).symm (0, kap τ S (o''.resT S b).2)`. Rewrite using `[kadd, ← map_add, Prod.mk_add_mk, add_zero]`.

Establish `ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S w)) (jL b) = symplOH S L'' w (o''.resT S b).2` using `by show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) = _`. Rewrite using `[sOH_resS_symm, sOH_zero_right, zero_add, kH]`. Simplify using `only [heisO] at h2 ⊢`. Rewrite `h2` using `[ph]`. Rewrite using `[e]`.

Conclude with `h2`.
-/
theorem isBiTheta_lastBi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  intro D ψ _ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ
  obtain ⟨kadd, kcont, krat, -, ksympl, kpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  have hC : ∀ u v, lastBi o o'' τ Ξ Φ₂ u v =
      Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := fun _ _ => rfl
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) kadd
  let P1 : WO S X →+ WO S T := (AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom
  let P2 : WO S X →+ WO S L'' := (AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom
  have cP1 : Continuous fun b : WO S X => (o''.resT S b).1 := continuous_fst.comp (o''.continuous_resT S)
  have cP2 : Continuous fun b : WO S X => (o''.resT S b).2 := continuous_snd.comp (o''.continuous_resT S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show Continuous fun p : WO A S × WO S X =>
      Φ₂ (o''.resT S p.2).1 * Ξ ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2))
    exact (hΦ.cont.comp (cP1.comp continuous_snd)).mul
      (hΞ.cont.comp ((o.continuous_resS_symm S).comp (continuous_fst.prodMk (kcont.comp (cP2.comp continuous_snd)))))
  ·
    intro n L₁ L₂ hL₁ hL₂ hf₁ hf₂ u v
    let M₁ : (Fin n → ℝ) →+ WO S T := P1.comp L₂
    let M₂ : (Fin n → ℝ) →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.prod L₁ (K.comp (P2.comp L₂)))
    have cM₁ : Continuous M₁ := cP1.comp hL₂
    have cM₂ : Continuous M₂ := (o.continuous_resS_symm S).comp (hL₁.prodMk (kcont.comp (cP2.comp hL₂)))
    have fM₁ : ∀ t, (M₁ t).map (finPart D) = 0 := fun t => map_mul_eq_zero_right (finPart D) _ (hf₂ t)
    have fM₂ : ∀ t, (M₂ t).map (finPart D) = 0 := fun t =>
      resS_symm_map (finPart D) o S (hf₁ t) ((kpart _).2 (map_mul_eq_zero_right (finPart D) _ (hf₂ t)))
    have e : (fun t => lastBi o o'' τ Ξ Φ₂ (u + L₁ t) (v + L₂ t)) = fun t =>
        Φ₂ ((o''.resT S v).1 + M₁ t) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + M₂ t) := by
      funext t
      rw [hC]
      show Φ₂ (o''.resT S (v + L₂ t)).1 * Ξ ((o.resS S).symm (u + L₁ t, kap τ S (o''.resT S (v + L₂ t)).2)) =
        Φ₂ ((o''.resT S v).1 + (o''.resT S (L₂ t)).1) *
          Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (L₁ t, kap τ S (o''.resT S (L₂ t)).2))
      rw [map_add, Prod.fst_add, Prod.snd_add, kadd, ← map_add, Prod.mk_add_mk]
    rw [e]
    exact (hΦ.smooth n M₁ cM₁ fM₁ _).mul (hΞ.smooth n M₂ cM₂ fM₂ _)
  ·
    intro γ u v
    rw [hC, hC]
    have e : (o.resS S).symm (ratW S A γ + u, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (ratW S A γ, 0) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [← map_add, Prod.mk_add_mk, zero_add]
    have hγ : ratW S A γ ∈ ratMx D S.rank A.rank := rat_mem γ
    rw [e, quasi_of_mem hΞ (resS_symm_mem o S hγ (zero_mem _)), sOH_resS_symm, sOH_zero_left, add_zero]
    ring
  ·
    intro γ u v
    rw [hC, hC]
    have h1 : (o''.resT S (ratW X S γ)).1 ∈ ratMx D T.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have h2 : (o''.resT S (ratW X S γ)).2 ∈ ratMx D L''.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have e : (o.resS S).symm (u, kap τ S ((o''.resT S (ratW X S γ)).2 + (o''.resT S v).2)) =
        (o.resS S).symm (0, kap τ S (o''.resT S (ratW X S γ)).2) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [kadd, ← map_add, Prod.mk_add_mk, zero_add]
    have ph : ψ (-symplOH S X (ratW X S γ) v) = ψ (-symplOH S T (o''.resT S (ratW X S γ)).1 (o''.resT S v).1) *
        ψ (-symplOH S L'' (o''.resT S (ratW X S γ)).2 (o''.resT S v).2) := by
      rw [← AddChar.map_add_eq_mul, o''.symplOH_resT S (ratW X S γ) v]
      exact congrArg ψ (neg_add _ _)
    rw [map_add, Prod.fst_add, Prod.snd_add, e, quasi_of_mem hΦ h1,
      quasi_of_mem hΞ (resS_symm_mem o S (zero_mem _) (krat _ h2)), sOH_resS_symm, sOH_zero_left, zero_add, kH, ph]
    ring
  ·
    obtain ⟨U, hUo, hU⟩ := hΞ.level
    let iA : WO A S →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
    have ciA : Continuous fun a : WO A S => (o.resS S).symm (a, 0) :=
      (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
    refine ⟨U.comap iA, hUo.preimage ciA, fun a ha hinf v => ?_⟩
    funext u
    have h1 := congrFun (hU (iA a) ha (resS_symm_map (infPart D) o S hinf (by simp)))
      ((o.resS S).symm (u, kap τ S (o''.resT S v).2))
    have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (u, kap τ S (o''.resT S v).2) + iA a := by
      show _ = _ + (o.resS S).symm (a, 0)
      rw [← map_add, Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) (iA a) = symplOH A S u a := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (a, 0)) = _
      rw [sOH_resS_symm, sOH_zero_right, add_zero]
    simp only [heisO] at h1 ⊢
    rw [ph] at h1
    rw [hC, hC, e, ← h1]
    ring
  ·
    obtain ⟨UΞ, hUΞo, hUΞ⟩ := hΞ.level
    obtain ⟨UΦ, hUΦo, hUΦ⟩ := hΦ.level
    let jL : WO S X →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (K.comp P2))
    have cjL : Continuous fun b : WO S X => (o.resS S).symm (0, kap τ S (o''.resT S b).2) :=
      (o.continuous_resS_symm S).comp (continuous_const.prodMk (kcont.comp cP2))
    refine ⟨UΦ.comap P1 ⊓ UΞ.comap jL, (hUΦo.preimage cP1).inter (hUΞo.preimage cjL), fun b hb hinf u => ?_⟩
    have hT : (o''.resT S b).1.map (infPart D) = 0 := map_mul_eq_zero_right (infPart D) _ hinf
    have hJ : (jL b).map (infPart D) = 0 :=
      resS_symm_map (infPart D) o S (by simp) ((kpart _).1 (map_mul_eq_zero_right (infPart D) _ hinf))
    show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) =
      o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))
    rw [o''.heisO_boxT, hUΦ (o''.resT S b).1 hb.1 hT]
    congr 1
    funext w
    have h2 := congrFun (hUΞ (jL b) hb.2 hJ) ((o.resS S).symm (u, kap τ S w))
    have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) = (o.resS S).symm (u, kap τ S w) + jL b := by
      show _ = _ + (o.resS S).symm (0, kap τ S (o''.resT S b).2)
      rw [kadd, ← map_add, Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S w)) (jL b) = symplOH S L'' w (o''.resT S b).2 := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) = _
      rw [sOH_resS_symm, sOH_zero_right, zero_add, kH]
    simp only [heisO] at h2 ⊢
    rw [ph] at h2
    rw [e]
    exact h2

end GlobalTheory.LastBiTheta

end
