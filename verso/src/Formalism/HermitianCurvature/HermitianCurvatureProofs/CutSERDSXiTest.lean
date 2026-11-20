import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.Kfp

/- English proof (translation)
Use `set N : Finset ℂ := Finset.univ.image f`. Use `set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)`. Establish `hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹`. Introduce `ρ`. Establish `hmem : f ρ ∈ N` using `Finset.mem_image_of_mem _ (Finset.mem_univ ρ)`.

Establish `h` using `Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem`. Simplify `h` using `only [id]`. Establish `he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p`. Use function extensionality and compare the values at `ρ`. Rewrite using `[← hp ρ]`.

Use `Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p` as an intermediate fact. Rewrite `this` using `[Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval]`. Rewrite using `[this]`. Both sides reduce to the same expression. Conclude with `⟨p, by rw [he, ← Polynomial.aeval_algHom_apply]⟩`.
-/
theorem rdsXi_kappa_inv_aeval {T A : Type} [Fintype T] [Ring A] [Algebra ℂ A] (κ : (T → ℂ) →ₐ[ℂ] A) (f : T → ℂ) :
    ∃ p : Polynomial ℂ, κ (fun ρ => (f ρ)⁻¹) = Polynomial.aeval (κ f) p := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  exact ⟨p, by rw [he, ← Polynomial.aeval_algHom_apply]⟩

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y hYr hYi Ψ hΨ`. Take `⟨κ, hx, hxi, -⟩` from `xKappaOfNF normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD`. Establish `hD'` using `hD`. Take `⟨hPl, -, hL, hQQ, -, -, -, hst⟩` from `hD'`. Take `⟨p, hp⟩` from `rdsXi_kappa_inv_aeval κ (fun ρ => M.x0 P l0 ρ Y)`.

Establish `hxiY : st.xi Y = Polynomial.aeval (st.x Y) p` using `by rw [hxi Y hYi, hp, ← hx Y]`. Establish `hx1 : (st.x Y).1 = M.sgn P l0 • (X.fn 5 * X.t Y 1 1)`. Establish `e1 : st.x Y = L.GGi * st.QQ Y 1 1` using `by rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]`. Rewrite using `[e1, hQQ Y, Matrix.smul_apply, hL.2.2.2.2.2.2.2.2.2.2.2.1, mul_smul_comm]`. Rewrite using `[Algebra.smul_def]`.

Use `show algebraMap ℂ (Module.End ℂ _) (M.sgn P l0) * (X.fn 5 * X.t Y 1 1) = _`. Rewrite using `[← Algebra.smul_def]`. Establish `hxi1 : (st.xi Y).1 = Polynomial.aeval (M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) p`. Rewrite using `[hxiY, ← hx1]`. Conclude with `(Polynomial.aeval_algHom_apply (fstAlg _) (st.x Y) p).symm`.

Establish `h1 : RTest ((st.xi Y).1 Ψ)`. Take `⟨K, hK, hKD, hK0⟩` from `hΨ`. Use `⟨K, hK, hKD, fun x hxK => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hxD : x ∈ DomR P.k P.r z z'`. Use `swap`.

Conclude with `((st.xi Y).1 Ψ).2.1 x hxD`. Take `⟨c, g⟩` from `x`. Establish `hxD'` using `hxD`. Take `⟨hc, hg, hG⟩` from `hxD'`. Take `⟨hP, hz, hz', hTz, hTz', -, hπ'⟩` from `hPl`.

Establish `hT : 0 < Tz P.k P.r z` using `by rw [hTz]; exact hP.T_pos`. Establish `hT' : 0 < Tz P.k P.r z'` using `by rw [hTz']; exact hP.T'_pos`. Take `⟨Bs, -, -, hB1, -⟩` from `LieAlgebraWeightVectors.geom_package hz hz' hT hT' hg hG.ne'`. Use `set C : Module.End ℂ Wq := M.sgn P l0 • qdet (EB π' Bs) (Y + ((P.k : ℂ) - 2) / 2) with hCdef`. Establish `hact : ∀ (Φ : RadSp P.k P.r z z' π π') (v : Wq), (((M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v = (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (C v)`.

Introduce `Φ v`. Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, diagonal_transfer_action X hz hz' hπ'.2.1 hπ'.2.2.1 hxD Bs hB1 Y Φ v, hCdef, LinearMap.smul_apply, map_smul]`. Establish `h0 : (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0` using `hK0 (c, g) hxK`. Use extensionality with `v`. Rewrite using `[hxi1]`.

Use `erw [aeval_act _ C hact p Ψ v]`. Rewrite using `[h0]`. Both sides reduce to the same expression. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hstar : star (st.xi Y) = st.xi Y`.

Take `⟨u, -⟩` from `hst.x_xi Y hYi`. Establish `e : star (st.xi Y) * st.x Y = 1`. Use `congrArg star u` as an intermediate fact. Rewrite `this` using `[star_mul, hst.x_star Y hYr, star_one]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : (st.xi Y).2.unop = (st.xi Y).1`. Use `congrArg Prod.fst hstar` as an intermediate fact. Conclude with `this`. Rewrite using `[e2]`. Conclude with `h1`.
-/
theorem spectral_xi_test : RDSXiTest := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y hYr hYi Ψ hΨ
  obtain ⟨κ, hx, hxi, -⟩ := xKappaOfNF normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hPl, -, hL, hQQ, -, -, -, hst⟩ := hD'
  obtain ⟨p, hp⟩ := rdsXi_kappa_inv_aeval κ (fun ρ => M.x0 P l0 ρ Y)
  have hxiY : st.xi Y = Polynomial.aeval (st.x Y) p := by rw [hxi Y hYi, hp, ← hx Y]

  have hx1 : (st.x Y).1 = M.sgn P l0 • (X.fn 5 * X.t Y 1 1) := by
    have e1 : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]
    rw [e1, hQQ Y, Matrix.smul_apply, hL.2.2.2.2.2.2.2.2.2.2.2.1, mul_smul_comm]
    rw [Algebra.smul_def]
    show algebraMap ℂ (Module.End ℂ _) (M.sgn P l0) * (X.fn 5 * X.t Y 1 1) = _
    rw [← Algebra.smul_def]

  have hxi1 : (st.xi Y).1 = Polynomial.aeval (M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) p := by
    rw [hxiY, ← hx1]
    exact (Polynomial.aeval_algHom_apply (fstAlg _) (st.x Y) p).symm

  have h1 : RTest ((st.xi Y).1 Ψ) := by
    obtain ⟨K, hK, hKD, hK0⟩ := hΨ
    refine ⟨K, hK, hKD, fun x hxK => ?_⟩
    by_cases hxD : x ∈ DomR P.k P.r z z'
    swap
    · exact ((st.xi Y).1 Ψ).2.1 x hxD
    obtain ⟨c, g⟩ := x
    have hxD' := hxD
    obtain ⟨hc, hg, hG⟩ := hxD'
    obtain ⟨hP, hz, hz', hTz, hTz', -, hπ'⟩ := hPl
    have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
    have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
    obtain ⟨Bs, -, -, hB1, -⟩ := LieAlgebraWeightVectors.geom_package hz hz' hT hT' hg hG.ne'
    set C : Module.End ℂ Wq := M.sgn P l0 • qdet (EB π' Bs) (Y + ((P.k : ℂ) - 2) / 2) with hCdef
    have hact : ∀ (Φ : RadSp P.k P.r z z' π π') (v : Wq),
        (((M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (C v) := by
      intro Φ v
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply,
        diagonal_transfer_action X hz hz' hπ'.2.1 hπ'.2.2.1 hxD Bs hB1 Y Φ v, hCdef, LinearMap.smul_apply, map_smul]
    have h0 : (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := hK0 (c, g) hxK
    ext v
    rw [hxi1]
    erw [aeval_act _ C hact p Ψ v]
    rw [h0]
    rfl
  refine ⟨h1, ?_⟩

  have hstar : star (st.xi Y) = st.xi Y := by
    obtain ⟨u, -⟩ := hst.x_xi Y hYi
    have e : star (st.xi Y) * st.x Y = 1 := by
      have := congrArg star u
      rwa [star_mul, hst.x_star Y hYr, star_one] at this
    calc star (st.xi Y) = star (st.xi Y) * (st.x Y * st.xi Y) := by rw [u, mul_one]
      _ = st.xi Y := by rw [← mul_assoc, e, one_mul]
  have e2 : (st.xi Y).2.unop = (st.xi Y).1 := by
    have := congrArg Prod.fst hstar
    exact this
  rw [e2]
  exact h1

end Formalism.FourierDecayAlt.P.CutSE
