import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinCond

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `h` using `d.hO_ext T x 0 0 y 0 0`. Simplify using `only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h`. Rewrite using `[symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]`.
-/
theorem symplO_extX_extY_pairS {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

/- English proof (translation)
The claim follows from `GlobalTheory.HandHom.flatAt_smul ψ dV dW _ _ _ _ _ x y a Ψ`.
-/
theorem flatS_smul {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ) (Ψ : WO V W → ℂ) :
    flatS dV dW s x y (a • Ψ) = a • flatS dV dW s x y Ψ :=
  GlobalTheory.HandHom.flatAt_smul ψ dV dW _ _ _ _ _ x y a Ψ

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hF` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Establish `h0 : ∀ u : UX D ρ, GlobalTheory.MixPer.flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y F w u = 0`.

Introduce `u`. Establish `hg : dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) = (0 : ℂ) • dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1)`. Use function extensionality and compare the values at `w₀`. Simplify using `[hne u w₀]`. Simplify using `only [GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt]`.

Rewrite using `[hg, GlobalTheory.HandHom.mixT_smul, zero_smul]`. Simplify using the standard rewrite rules. Simplify using `only [flatS, GlobalTheory.MixPer.flatAt, h0, integral_zero, Pi.zero_apply]`.
-/
theorem exists_mixS_ne {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (F : WO V W → ℂ) (hF : flatS dV dW s x y F ≠ 0) :
    ∃ u : UX D ρ, ∃ w₀, dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) w₀ ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hF
  funext w
  have h0 : ∀ u : UX D ρ, GlobalTheory.MixPer.flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y F w u = 0 := by
    intro u
    have hg : dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) = (0 : ℂ) • dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) := by
      funext w₀; simp [hne u w₀]
    simp only [GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt]
    rw [hg, GlobalTheory.HandHom.mixT_smul, zero_smul]
    simp
  simp only [flatS, GlobalTheory.MixPer.flatAt, h0, integral_zero, Pi.zero_apply]

/- English proof (translation)
Simplify using `only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem actO_one_extX {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extX W a) = d.extX W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem actO_one_extY {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extY W a) = d.extY W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [actO, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem weilAction_one_wittExtZero {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : WO V₀ W) :
    actO V W 1 h (d.ext0 W a) = d.ext0 W (mt W h ⬝ a) := by
  simp only [actO, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨w, hw⟩` from `Function.ne_iff.1 hF`. Establish `e` using `congrFun h w`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e hw`. Establish `: (c - c') * F w = 0` using `by rw [sub_mul, e, sub_self]`. Break down `mul_eq_zero.1 this with h1 | h1` into its components or cases.

Conclude with `sub_eq_zero.1 h1`. Conclude with `absurd h1 hw`.
-/
theorem eq_one_of_smul {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hF
  have e := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e hw
  have : (c - c') * F w = 0 := by rw [sub_mul, e, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hw

/- English proof (translation)
Simplify using `only [pairS, Matrix.mul_sub, Matrix.trace_sub]`.
-/
theorem pairS_sub_left {T : HSp D} {ρ : ℕ} (x x' y : Mx D T.rank ρ) : pairS T (x - x') y = pairS T x y - pairS T x' y := by
  simp only [pairS, Matrix.mul_sub, Matrix.trace_sub]

/- English proof (translation)
Simplify using `only [pairS, adj_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcA]`. Rewrite using `[← mul_assoc, hc]`.
-/
theorem pairS_idem {T : HSp D} {ρ : ℕ} {c : AE D} (hc : c * c = c) (hcA : cA D c = c) (x y : Mx D T.rank ρ) :
    pairS T (c • x) (c • y) = pairS T x (c • y) := by
  simp only [pairS, adj_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcA]
  rw [← mul_assoc, hc]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne`. Take `⟨hΦt, hA1, hA2, hB1, -, -⟩` from `hΦ`. Establish `hf : IsThetaFunO ψ V W (s.om (1, h) Φ)` using `s.weil.om_pres _ _ hΦt`. Establish `laws` using `GlobalTheory.T.flatMap_heisenberg_and_hom_transformation D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli _ hf`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨u, w₀, hM⟩` from `exists_mixS_ne dV dW s (rat x₀) y _ hne`. Take `⟨ε, hε⟩ : ∃ ε, ε = GlobalTheory.FinPlLoc.idem D (fun _ => True)` from `⟨_, rfl⟩`. Establish `hεε : ε * ε = ε` using `by rw [hε]; exact GlobalTheory.FinPlLoc.idem_mul_self _`. Establish `hcA : cA D ε = ε` using `by rw [hε]; exact GlobalTheory.FinPlLoc.cA_idem _`. Take `⟨A, hAdef⟩ : ∃ A : Mx D W.rank ρ, A = mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1)` from `⟨_, rfl⟩`.

Establish `key : ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W A) (dV.extY W a')) = ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a'))`. Introduce `a' ha'`. Establish `e1 : heisO ψ V W (dV.extY W (mt W h ⬝ a')) (s.om (1, h) Φ) = ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) • s.om (1, h) Φ`. Rewrite using `[← actO_one_extY, ← s.weil.om_heis 1 h _ Φ hΦt, hA2 a' ha', map_smul]`. Establish `e2` using `GlobalTheory.MixModel.Check.mixS_heis_extY dV s.vS.covol hf (mt W h ⬝ a') ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀`.

Rewrite `e2` using `[e1, GlobalTheory.HandHom.mixS_smul, Pi.smul_apply, smul_eq_mul]`. Establish `e3 : (ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) - ψ (symplO V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1)) (dV.extY W (mt W h ⬝ a')))) * dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (1, h) Φ) ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀ = 0`. Rewrite using `[sub_mul, e2, sub_self]`. Break down `mul_eq_zero.1 e3 with h1 | h1` into its components or cases. Rewrite using `[hAdef, ← GlobalTheory.StripVanish.symplO_extX_extY_mt]`.

Conclude with `(sub_eq_zero.1 h1).symm`. Conclude with `absurd h1 hM`. Use `⟨u, ε • (A - rat x₀), ?_, ?_⟩` and prove the remaining obligations. Establish `hεb : MxAt (fun _ => True) (ε • (A - rat x₀))` using `fun i j => by`. Rewrite using `[GlobalTheory.FinPlLoc.mem_idAt_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hε, hεε]`.

Use `(hp.dualA _ hεb).2 fun a' ha' => ?_` and prove the remaining obligations. Establish `ha'e : ε • a' = a'` using `Matrix.ext fun i j => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, hε, ← GlobalTheory.FinPlLoc.mem_idAt_iff]`. Conclude with `hp.a₂.fin a' ha' i j`. Establish `hsym : symplO V W (dV.extX W (ε • (A - rat x₀))) (dV.extY W a') = symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a')`.

Rewrite using `[← ha'e, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_idem hεε hcA]`. Establish `hsub : symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') = symplO V W (dV.extX W A) (dV.extY W a') - symplO V W (dV.extX W (rat x₀)) (dV.extY W a')`. Rewrite using `[symplO_extX_extY_pairS, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_sub_left, mul_sub, map_sub]`. Rewrite using `[hsym, hsub, sub_eq_add_neg, AddChar.map_add_eq_mul, key a' ha', ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Rewrite using `[← hAdef]`.

Introduce `i j`. Rewrite using `[GlobalTheory.FinPlLoc.mem_idOff_iff, ← hε]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[mul_sub ε (A i j - (rat x₀ : Mx D W.rank ρ) i j), ← mul_assoc, hεε, sub_self]`. Introduce `N _ hN hA`.

Establish `key : heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) (s.om (1, h) Φ) = s.om (1, h) Φ`. Establish `e : dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N) = actO V W 1 h (dV.extX W (mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ N)))`. Rewrite using `[actO_one_extX, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]`. Rewrite using `[e, ← s.weil.om_heis 1 h _ Φ hΦt, hA1 _ hA]`. Establish `e` using `laws.1 N hN`.

Rewrite `e` using `[key]`. Conclude with `eq_one_of_smul hne (e.symm.trans (one_smul ℂ _).symm)`. Introduce `ξ hξ ξ' _ hξ'`. Establish `key : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ')) (s.om (1, h) Φ) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • s.om (1, h) Φ`. Establish `e : dV.ext0 W (dW.incX V₀ ξ') = actO V W 1 h (dV.ext0 W (dW.incX V₀ ξ))`.

Rewrite using `[weilAction_one_wittExtZero, hξ']`. Rewrite using `[e, ← s.weil.om_heis 1 h _ Φ hΦt, hB1 ξ hξ, map_smul]`. Establish `e` using `laws.2 ξ'`. Rewrite `e` using `[key, flatS_smul]`. Conclude with `(eq_one_of_smul hne e).symm`.
-/
theorem cond_of_flatS_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne
  obtain ⟨hΦt, hA1, hA2, hB1, -, -⟩ := hΦ
  have hf : IsThetaFunO ψ V W (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦt
  have laws := GlobalTheory.T.flatMap_heisenberg_and_hom_transformation D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli _ hf
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨u, w₀, hM⟩ := exists_mixS_ne dV dW s (rat x₀) y _ hne
    obtain ⟨ε, hε⟩ : ∃ ε, ε = GlobalTheory.FinPlLoc.idem D (fun _ => True) := ⟨_, rfl⟩
    have hεε : ε * ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.idem_mul_self _
    have hcA : cA D ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.cA_idem _
    obtain ⟨A, hAdef⟩ : ∃ A : Mx D W.rank ρ, A = mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) := ⟨_, rfl⟩
    have key : ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W A) (dV.extY W a')) =
        ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) := by
      intro a' ha'
      have e1 : heisO ψ V W (dV.extY W (mt W h ⬝ a')) (s.om (1, h) Φ) =
          ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) • s.om (1, h) Φ := by
        rw [← actO_one_extY, ← s.weil.om_heis 1 h _ Φ hΦt, hA2 a' ha', map_smul]
      have e2 := GlobalTheory.MixModel.Check.mixS_heis_extY dV s.vS.covol hf (mt W h ⬝ a') ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀
      rw [e1, GlobalTheory.HandHom.mixS_smul, Pi.smul_apply, smul_eq_mul] at e2
      have e3 : (ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) -
          ψ (symplO V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1)) (dV.extY W (mt W h ⬝ a')))) *
          dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (1, h) Φ) ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀ = 0 := by
        rw [sub_mul, e2, sub_self]
      rcases mul_eq_zero.1 e3 with h1 | h1
      · rw [hAdef, ← GlobalTheory.StripVanish.symplO_extX_extY_mt]; exact (sub_eq_zero.1 h1).symm
      · exact absurd h1 hM
    refine ⟨u, ε • (A - rat x₀), ?_, ?_⟩
    · have hεb : MxAt (fun _ => True) (ε • (A - rat x₀)) := fun i j => by
        rw [GlobalTheory.FinPlLoc.mem_idAt_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hε, hεε]
      refine (hp.dualA _ hεb).2 fun a' ha' => ?_
      have ha'e : ε • a' = a' := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, hε, ← GlobalTheory.FinPlLoc.mem_idAt_iff]; exact hp.a₂.fin a' ha' i j
      have hsym : symplO V W (dV.extX W (ε • (A - rat x₀))) (dV.extY W a') =
          symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') := by
        rw [← ha'e, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_idem hεε hcA]
      have hsub : symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') =
          symplO V W (dV.extX W A) (dV.extY W a') - symplO V W (dV.extX W (rat x₀)) (dV.extY W a') := by
        rw [symplO_extX_extY_pairS, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_sub_left, mul_sub, map_sub]
      rw [hsym, hsub, sub_eq_add_neg, AddChar.map_add_eq_mul, key a' ha', ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · rw [← hAdef]
      intro i j
      rw [GlobalTheory.FinPlLoc.mem_idOff_iff, ← hε]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub ε (A i j - (rat x₀ : Mx D W.rank ρ) i j), ← mul_assoc, hεε, sub_self]
  ·
    intro N _ hN hA
    have key : heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) (s.om (1, h) Φ) = s.om (1, h) Φ := by
      have e : dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N) =
          actO V W 1 h (dV.extX W (mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ N))) := by
        rw [actO_one_extX, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hA1 _ hA]
    have e := laws.1 N hN
    rw [key] at e
    exact eq_one_of_smul hne (e.symm.trans (one_smul ℂ _).symm)
  ·
    intro ξ hξ ξ' _ hξ'
    have key : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ')) (s.om (1, h) Φ) =
        ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • s.om (1, h) Φ := by
      have e : dV.ext0 W (dW.incX V₀ ξ') = actO V W 1 h (dV.ext0 W (dW.incX V₀ ξ)) := by
        rw [weilAction_one_wittExtZero, hξ']
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hB1 ξ hξ, map_smul]
    have e := laws.2 ξ'
    rw [key, flatS_smul] at e
    exact (eq_one_of_smul hne e).symm

end GlobalTheory.AscFinCond
