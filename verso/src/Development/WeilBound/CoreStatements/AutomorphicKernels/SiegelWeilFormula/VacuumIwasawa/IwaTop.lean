import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d L x`. Take `⟨p, k, lam, hk, rfl, hp⟩` from `line_fix' L.i₀ x`. Take `⟨ε, hd, hL⟩` from `eps_eq L`. Take `⟨g, hq⟩` from `q_split' L ε hd hL p lam hp`. Use `set q := p * (L.j g)⁻¹ with hqdef`.

Take `⟨c, hc⟩` from `parabolic_theta_scalar hT L.i₀ hq`. Use `⟨q, g, k, (absE F E lam : ℝ), c, hk, by simp [hqdef, mul_assoc], absE_pos lam, fun g' => ?_, fun Φ hΦ g' X hX => ?_⟩` and prove the remaining obligations. Establish `e : L.j g' * (p * k) = (L.j g' * q * (L.j g')⁻¹) * L.j (g' * g) * k`. Simplify using `only [hqdef, map_mul, mul_assoc, inv_mul_cancel_left]`. Rewrite using `[e, KWhit.a_mul_K d _ k hk, q_ht' L (q_conj' L hq g') (g' * g)]`.

Use `set Ψ := d.om q Φ - c • Φ with hΨ`. Establish `hΨs : Ψ ∈ d.sch` using `sub_mem (KWhit.om_mem_sch d q hΦ) (Submodule.smul_mem _ c hΦ)`. Establish `hTΨ : ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → d.T Ψ X = 0`. Introduce `X hX`. Use `(Tl d).map_sub (d.om q Φ) (c • Φ)` as an intermediate fact.

Establish `hs` using `(Tl d).map_smul c Φ`. Simplify using `only [Tl, LinearMap.coe_mk, AddHom.coe_mk] at this hs`. Rewrite using `[hΨ, this, hs, Pi.sub_apply, Pi.smul_apply, hc Φ hΦ X hX, smul_eq_mul, sub_self]`. Establish `key` using `L.res Ψ hΨs 0 (zero_mem _) (fun X hX => by rw [T_zero, hTΨ X hX]; rfl) g' X hX`. Rewrite `key` using `[map_zero, T_zero]`.

Establish `e1 : d.om (L.j g') Ψ = d.om (L.j g') (d.om q Φ) - c • d.om (L.j g') Φ`. Rewrite using `[hΨ, map_sub, map_smul]`. Establish `e2` using `congrFun ((Tl d).map_sub (d.om (L.j g') (d.om q Φ)) (c • d.om (L.j g') Φ)) X`. Establish `e3` using `congrFun ((Tl d).map_smul c (d.om (L.j g') Φ)) X`. Simplify using `only [Tl, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3`.

Rewrite using `[map_mul, Module.End.mul_apply]`. Establish `: d.T (d.om (L.j g') Ψ) X = 0` using `key.symm`. Rewrite `this` using `[e1, e2, e3]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem iwaQ_of' (hT : TAll) : IwaQ := by
  intro F E _ _ _ _ _ σ d L x
  obtain ⟨p, k, lam, hk, rfl, hp⟩ := line_fix' L.i₀ x
  obtain ⟨ε, hd, hL⟩ := eps_eq L
  obtain ⟨g, hq⟩ := q_split' L ε hd hL p lam hp
  set q := p * (L.j g)⁻¹ with hqdef
  obtain ⟨c, hc⟩ := parabolic_theta_scalar hT L.i₀ hq
  refine ⟨q, g, k, (absE F E lam : ℝ), c, hk, by simp [hqdef, mul_assoc], absE_pos lam, fun g' => ?_, fun Φ hΦ g' X hX => ?_⟩
  · have e : L.j g' * (p * k) = (L.j g' * q * (L.j g')⁻¹) * L.j (g' * g) * k := by
      simp only [hqdef, map_mul, mul_assoc, inv_mul_cancel_left]
    rw [e, KWhit.a_mul_K d _ k hk, q_ht' L (q_conj' L hq g') (g' * g)]
  · set Ψ := d.om q Φ - c • Φ with hΨ
    have hΨs : Ψ ∈ d.sch := sub_mem (KWhit.om_mem_sch d q hΦ) (Submodule.smul_mem _ c hΦ)
    have hTΨ : ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → d.T Ψ X = 0 := by
      intro X hX
      have := (Tl d).map_sub (d.om q Φ) (c • Φ)
      have hs := (Tl d).map_smul c Φ
      simp only [Tl, LinearMap.coe_mk, AddHom.coe_mk] at this hs
      rw [hΨ, this, hs, Pi.sub_apply, Pi.smul_apply, hc Φ hΦ X hX, smul_eq_mul, sub_self]
    have key := L.res Ψ hΨs 0 (zero_mem _) (fun X hX => by rw [T_zero, hTΨ X hX]; rfl) g' X hX
    rw [map_zero, T_zero] at key
    have e1 : d.om (L.j g') Ψ = d.om (L.j g') (d.om q Φ) - c • d.om (L.j g') Φ := by
      rw [hΨ, map_sub, map_smul]
    have e2 := congrFun ((Tl d).map_sub (d.om (L.j g') (d.om q Φ)) (c • d.om (L.j g') Φ)) X
    have e3 := congrFun ((Tl d).map_smul c (d.om (L.j g') Φ)) X
    simp only [Tl, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3
    rw [map_mul, Module.End.mul_apply]
    have : d.T (d.om (L.j g') Ψ) X = 0 := key.symm
    rw [e1, e2, e3] at this
    exact sub_eq_zero.1 this

end PositivityTheory.SiegelWeilFormula.Avac

end
