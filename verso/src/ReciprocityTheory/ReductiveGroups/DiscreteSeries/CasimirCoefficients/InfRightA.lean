import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

/- English proof (translation)
Use `haveI : CompactSpace (KG ε) := compactSpace_KG ε`. Establish `hU : x ∈ Ps1.Uset ε`. Introduce `k`. Establish `hk : toMK k⁻¹ = (toMK k)ᴴ` using `Ps1.toMK_inv_eq k`. Establish `hinv : toMK k⁻¹ * toMK k = 1`.

Unfold `toMK toM`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (toMK k).mulVec`. Introduce `v w hvw`. Use `congrArg (toMK k⁻¹).mulVec hvw` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_mulVec, hinv]`. Establish `hpd : (toMK k⁻¹ * x * toMK k).PosDef`. Rewrite using `[hk]`. Conclude with `hx.conjTranspose_mul_mul_same hinj`. Introduce `i`.

Unfold `lead`. Rewrite using `[dif_pos (by omega)]`. Conclude with `((hpd.submatrix (Fin.castLE_injective _)).det_pos).ne'`. Conclude with `(Ps1.hasFDerivAt_psM T μ hU).differentiableAt.hasFDerivAt`.
-/
lemma infR_hasFDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) x) x := by
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  have hU : x ∈ Ps1.Uset ε := by
    intro k
    have hk : toMK k⁻¹ = (toMK k)ᴴ := Ps1.toMK_inv_eq k
    have hinv : toMK k⁻¹ * toMK k = 1 := by
      unfold toMK toM
      simp
    have hinj : Function.Injective (toMK k).mulVec := by
      intro v w hvw
      have := congrArg (toMK k⁻¹).mulVec hvw
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hpd : (toMK k⁻¹ * x * toMK k).PosDef := by
      rw [hk]
      exact hx.conjTranspose_mul_mul_same hinj
    intro i
    unfold lead
    rw [dif_pos (by omega)]
    exact ((hpd.submatrix (Fin.castLE_injective _)).det_pos).ne'
  exact (Ps1.hasFDerivAt_psM T μ hU).differentiableAt.hasFDerivAt

/- English proof (translation)
Take `⟨γ, -, hγ, hγm⟩` from `exists_oneParam ε hA`. Establish `h0 : γ 0 = 1` using `by simpa using hγm 0 0`. Establish `hinv : ∀ t, (γ (-t))⁻¹ = γ t` using `fun t => inv_eq_of_mul_eq_one_right (by rw [← hγm, neg_add_cancel, h0])`. Establish `heq : ∀ t : ℝ, psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A)) = T.op (γ (-t)) * psM T μ x * T.op (γ t)`. Introduce `t`.

Establish `h1` using `psM_conj T μ (γ (-t)) x`. Rewrite `h1` using `[hinv, hγ, hγ]`. Simplify `h1` using `[Complex.ofReal_neg, neg_smul]`. Establish `hL : HasDerivAt (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0`. Establish `hc` using `dga_path A x`.

Establish `hψ` using `infR_hasFDerivAt T μ hx`. Conclude with `(hψ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)`. Establish `hR1` using `T.hasDeriv A hA γ hγ`. Establish `hR1' : HasDerivAt (fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) (T.dτ A) (-(0 : ℝ))`. Rewrite using `[neg_zero]`.

Conclude with `hR1`. Establish `hR2` using `hR1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))`. Establish `hR` using `(hR2.mul (hasDerivAt_const (0 : ℝ) (psM T μ x))).mul hR1`. Establish `hL' : HasDerivAt (fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0`. Establish `hfun : (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))) = fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)`.

Use function extensionality and compare the values at `t`. Conclude with `heq t`. Rewrite `hL` using `[hfun]`. Conclude with `hL`. Rewrite using `[hL'.unique hR]`.

Simplify using `[h0]`. Normalize the expressions using the abelian group laws.
-/
lemma infR_conj (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A - A * x) = psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
  obtain ⟨γ, -, hγ, hγm⟩ := exists_oneParam ε hA
  have h0 : γ 0 = 1 := by simpa using hγm 0 0
  have hinv : ∀ t, (γ (-t))⁻¹ = γ t := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hγm, neg_add_cancel, h0])

  have heq : ∀ t : ℝ, psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))
      = T.op (γ (-t)) * psM T μ x * T.op (γ t) := by
    intro t
    have h1 := psM_conj T μ (γ (-t)) x
    rw [hinv, hγ, hγ] at h1
    simpa [Complex.ofReal_neg, neg_smul] using h1

  have hL : HasDerivAt (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
      NormedSpace.exp ((t : ℂ) • A))) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hc := dga_path A x
    have hψ := infR_hasFDerivAt T μ hx
    exact (hψ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)

  have hR1 := T.hasDeriv A hA γ hγ
  have hR1' : HasDerivAt (fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (T.dτ A) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hR1
  have hR2 := hR1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hR := (hR2.mul (hasDerivAt_const (0 : ℝ) (psM T μ x))).mul hR1
  have hL' : HasDerivAt (fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) *
      psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hfun : (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
        NormedSpace.exp ((t : ℂ) • A))) = fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) :
          T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext t
      exact heq t
    rw [hfun] at hL
    exact hL
  rw [hL'.unique hR]
  simp [h0]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
