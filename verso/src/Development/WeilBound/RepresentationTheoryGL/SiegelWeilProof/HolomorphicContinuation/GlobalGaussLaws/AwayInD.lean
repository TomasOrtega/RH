import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

open Classical in
/- English proof (translation)
Take `⟨S, hS⟩` from `hf`. Use `set A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun t => gramAt D V t * s t with hAdef`. Establish `hA : ∀ t, t ≠ τ → (A t).PosDef` using `fun t _ => (hs t).2.2`. Establish `hw : ∀ t, t ≠ τ → 0 < |l t|` using `fun t _ => abs_pos.mpr (hl t)`. Take `⟨G, hG⟩` from `exists_gauss (n := n) τ A hA (fun t => |l t|) hw`.

Use `set poly : Bsp τ V.rank n → ℂ := fun b => MvPolynomial.eval (fun k => vC τ k b) p with hpoly`. Establish `hpolyT : poly.HasTemperateGrowth` using `tg_poly τ p`. Use `set h : 𝓢(Bsp τ V.rank n, ℂ) := SchwartzMap.smulLeftCLM ℂ poly G with hh`. Establish `hhv : ∀ b, h b = poly b * G b` using `fun b => by`. Rewrite using `[hh, SchwartzMap.smulLeftCLM_apply_apply hpolyT, smul_eq_mul]`.

Take `⟨Fp, hFp⟩` from `GlobalTheory.SchwartzHadamard.exists_schwartz_prod S h`. Set `e` to `(eL (n := n) τ fr hfr).toContinuousLinearEquiv`. Set `Fz : 𝓢(D.what₂.Tau → Fin V.rank → Fin n → ℂ, ℂ)` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Fp`. Establish `hFz : ∀ z, Fz z = S (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (poly (fun t => z t.1) * G (fun t => z t.1))`. Introduce `z`.

Simplify using `only [Fz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hFp, hhv]`. Both sides reduce to the same expression. Establish `hpolyz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, poly (fun t => z t.1) = evalPoly p (fun t => Matrix.of (z t))`. Introduce `z`. Rewrite using `[evalPoly_congr p τ hp (fun t => Matrix.of (z t)) (extF τ (fun t => z t.1)) (fun t ht => by simp only [extF, dif_neg ht]; rfl)]`.

Both sides reduce to the same expression. Establish `hGz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, G (fun t => z t.1) = gAway V l s τ (fun t => Matrix.of (z t))`. Introduce `z`. Rewrite using `[hG]`. Unfold `gAway qf`.

Use `congr 1`. Rewrite using `[Finset.sum_subtype _ (p := fun τ' => τ' ≠ τ) (fun x => by simp)]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations.

Rewrite using `[← tr_im_zero (hA t.1 t.2).isHermitian (Matrix.of (z t.1))]`. Simplify using `only [hAdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, Fz z = f (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (evalPoly p (fun t => Matrix.of (z t)) * gAway V l s τ (fun t => Matrix.of (z t)))`. Introduce `z`.

Rewrite using `[hFz, hpolyz, hGz, hS]`. Use `Submodule.subset_span ⟨Fz, g, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Rewrite using `[key]`. Simplify using `only [tens, mul_assoc]`.

Both sides reduce to the same expression.
-/
theorem gen_sch (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hfr : IsUnit fr.det)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hl : ∀ τ', l τ' ≠ 0)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (hp : ∀ v ∈ p.vars, v.1 ≠ τ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    tens θ τ fr f (fun x => evalPoly p (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
  obtain ⟨S, hS⟩ := hf
  set A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun t => gramAt D V t * s t with hAdef
  have hA : ∀ t, t ≠ τ → (A t).PosDef := fun t _ => (hs t).2.2
  have hw : ∀ t, t ≠ τ → 0 < |l t| := fun t _ => abs_pos.mpr (hl t)
  obtain ⟨G, hG⟩ := exists_gauss (n := n) τ A hA (fun t => |l t|) hw
  set poly : Bsp τ V.rank n → ℂ := fun b => MvPolynomial.eval (fun k => vC τ k b) p with hpoly
  have hpolyT : poly.HasTemperateGrowth := tg_poly τ p
  set h : 𝓢(Bsp τ V.rank n, ℂ) := SchwartzMap.smulLeftCLM ℂ poly G with hh
  have hhv : ∀ b, h b = poly b * G b := fun b => by
    rw [hh, SchwartzMap.smulLeftCLM_apply_apply hpolyT, smul_eq_mul]
  obtain ⟨Fp, hFp⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod S h
  let e := (eL (n := n) τ fr hfr).toContinuousLinearEquiv
  let Fz : 𝓢(D.what₂.Tau → Fin V.rank → Fin n → ℂ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Fp
  have hFz : ∀ z, Fz z = S (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (poly (fun t => z t.1) * G (fun t => z t.1)) := by
    intro z
    simp only [Fz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hFp, hhv]
    rfl
  have hpolyz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      poly (fun t => z t.1) = evalPoly p (fun t => Matrix.of (z t)) := by
    intro z
    rw [evalPoly_congr p τ hp (fun t => Matrix.of (z t)) (extF τ (fun t => z t.1)) (fun t ht => by simp only [extF, dif_neg ht]; rfl)]
    rfl
  have hGz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      G (fun t => z t.1) = gAway V l s τ (fun t => Matrix.of (z t)) := by
    intro z
    rw [hG]
    unfold gAway qf
    congr 1
    rw [Finset.sum_subtype _ (p := fun τ' => τ' ≠ τ) (fun x => by simp)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← tr_im_zero (hA t.1 t.2).isHermitian (Matrix.of (z t.1))]
    simp only [hAdef]
    ring
  have key : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, Fz z = f (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) *
      (evalPoly p (fun t => Matrix.of (z t)) * gAway V l s τ (fun t => Matrix.of (z t))) := by
    intro z
    rw [hFz, hpolyz, hGz, hS]
  refine Submodule.subset_span ⟨Fz, g, hg, ?_⟩
  funext x
  rw [key]
  simp only [tens, mul_assoc]
  rfl

end PositivityTheory.Rg.Sw.Glob.AwayPf
