import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIrred

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, K, hK, hKc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Establish `hμ : v.μ.IsAddHaarMeasure` using `v.covol.1`. Establish `h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ` using `v.covol.2.1`. Take `⟨l1, l2, -, l4, -⟩` from `GlobalTheory.OrientedFormLaws.symplOH_laws D S T`.

Take `⟨hth, hcomp, -⟩` from `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hu` using `hth u g hg`. Establish `key` using `GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S) (fun γ x => ψ (symplO S T x γ)) (fun γ => by`. Establish `: Continuous fun x : WO S T => symplOH S T x (γ : WO S T)` using `GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const`. Simplify using `only [← l4]`.

Conclude with `hψ.1.1.comp (this.add this))`. Use the proof step `(fun γ x y => by`. Simplify using `only [← l4, l1, AddChar.map_add_eq_mul]`. Use the proof step `ring)`. Use the proof step `(fun γ γ' x => by`.

Simplify using `only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]`. Use the proof step `ring)`. Use the proof step `(fun x => by`. Simplify using `only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])`. Use the proof step `(fun γ x => hψ.1.2.1 _)`.

Use the proof step `(fun x => by`. Rewrite using `[← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]`. Conclude with `⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)`. Use the proof step `v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))`. Use the proof step `(hf.cont.mul hu.cont.star)`.

Use the proof step `(fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)`. Use the proof step `(fun γ => by`. Establish `hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T)`. Introduce `x`. Establish `h0` using `l2 x (γ : WO S T) (-(γ : WO S T))`.

Rewrite `h0` using `[add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right]`. Simplify using `only [← l4, AddSubgroup.coe_neg]`. Take the linear combination `(-2 : AF D.host.F) * h0`. Establish `e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x => star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x))`. Use function extensionality and compare the values at `x`.

Establish `E` using `congrFun (hcomp (-(γ : WO S T)) u g) x`. Rewrite `E` using `[GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul]`. Establish `E'` using `congrArg star E`. Rewrite `E'` using `[star_mul', star_mul']`. Establish `hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T))`.

Establish `h1` using `GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))`. Establish `h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`. Take the linear combination `ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2`. Establish `hn` using `hneg x`.

Simplify using `only [AddSubgroup.coe_neg] at hn`. Rewrite `E'` using `[hn]`. Take the linear combination `(f x) * E' - (f x * star (heisO ψ S T u g x)) * hs`. Use `show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0`. Rewrite using `[e, integral_const_mul]`.

Use `horth (-(γ : WO S T) + u)` as an intermediate fact. Unfold `thPair at this`. Rewrite using `[this, mul_zero])`. Conclude with `congrFun key x`.
-/
theorem prod_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (v : VolM D T.rank S.rank)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (horth : ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) (u x : WO S T) :
    f x * star (heisO ψ S T u g x) = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hμ : v.μ.IsAddHaarMeasure := v.covol.1
  have h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hu := hth u g hg
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))
    (hf.cont.mul hu.cont.star)
    (fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)
    (fun γ => by
      have hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T) := by
        intro x
        have h0 := l2 x (γ : WO S T) (-(γ : WO S T))
        rw [add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right] at h0
        simp only [← l4, AddSubgroup.coe_neg]
        linear_combination (-2 : AF D.host.F) * h0
      have e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x =>
          star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x)) := by
        funext x
        have E := congrFun (hcomp (-(γ : WO S T)) u g) x
        rw [GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul] at E
        have E' := congrArg star E
        rw [star_mul', star_mul'] at E'
        have hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T)) := by
          have h1 := GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))
          have h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2
        have hn := hneg x
        simp only [AddSubgroup.coe_neg] at hn
        rw [hn] at E'
        linear_combination (f x) * E' - (f x * star (heisO ψ S T u g x)) * hs
      show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0
      rw [e, integral_const_mul]
      have := horth (-(γ : WO S T) + u)
      unfold thPair at this
      rw [this, mul_zero])
  exact congrFun key x

/- English proof (translation)
Introduce `D ψ hψ S T v f g hf hg hg0 horth`. Take `⟨y, hy⟩` from `Function.ne_iff.1 hg0`. Use function extensionality and compare the values at `x`. Establish `h` using `prod_eq_zero hψ v hf hg horth (y - x) x`. Establish `hz : ψ (symplOH S T x (y - x)) ≠ 0` using `fun h0 => by`.

Use `hψ.1.2.1 (symplOH S T x (y - x))` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Simplify using `only [heisO, add_sub_cancel, star_mul'] at h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd (star_eq_zero.1 h) hz`. Conclude with `absurd (star_eq_zero.1 h) hy`.
-/
theorem eq_zero_of_orth_heis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  intro D ψ hψ S T v f g hf hg hg0 horth
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  funext x
  have h := prod_eq_zero hψ v hf hg horth (y - x) x
  have hz : ψ (symplOH S T x (y - x)) ≠ 0 := fun h0 => by
    have := hψ.1.2.1 (symplOH S T x (y - x))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  simp only [heisO, add_sub_cancel, star_mul'] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (star_eq_zero.1 h) hz
    · exact absurd (star_eq_zero.1 h) hy

end GlobalTheory.ThetaIrred

end
