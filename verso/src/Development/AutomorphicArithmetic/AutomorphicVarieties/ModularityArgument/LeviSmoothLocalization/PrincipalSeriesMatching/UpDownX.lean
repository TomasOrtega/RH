import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.CrossG

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

/- English proof (translation)
Introduce `x hx`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, ha x hx, hb x hx, inv_one, one_mul]`.
-/
private theorem unr_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b⁻¹) := by
  intro x hx
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha x hx, hb x hx, inv_one, one_mul]

/- English proof (translation)
Unfold `IsUnram`. Simplify using the standard rewrite rules.
-/
private theorem unr_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsUnram (1 : kˣ →* ℂˣ) := by
  unfold IsUnram
  simp

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Use `ext`. Both sides reduce to the same expression. Consider the case `succ j ih => rw [pow_succ, pow_succ, ← ih]`.

Use `ext`. Both sides reduce to the same expression.
-/
private theorem loc_pow' {K : Type} [Field K] [NumberField K] (η : HChar K) (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    (η ^ j).loc v = η.loc v ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; ext; rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; ext; rfl

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ hp n hn π P hBC v s s' hs hs'`. Take `⟨η, hη, hloc⟩` from `normCnt K L hp`. Establish `hM` using `matchBCX K L hp n hn π P hBC η hη v s s' hs hs'`. Establish `hK` using `(polFacts (v.adicCompletion K)).2.2.2`. Use `⟨fun hT w ζ hζ => ?_, fun ξ hξ => ?_⟩` and prove the remaining obligations.

Take `⟨χ, hχ, hu⟩` from `((upDown K L hp n hn π P hBC v).1 hT w).2 (s' w) (hs' w) ζ hζ.1 hζ.2`. Establish `hL` using `polFacts (w.1.adicCompletion L)`. Establish `hf : 0 < fdeg w` using `(normVal K L v w 1).2.2.1`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq ((((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ)⁻¹) hf`. Establish `hbx : (((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ) * x ^ fdeg w = 1`.

Rewrite using `[hx]`. Conclude with `mul_inv_cancel₀ (Units.ne_zero _)`. Establish `h0` using `congrArg (Polynomial.eval x) (hM χ hχ)`. Rewrite `h0` using `[eval_prod, eval_prod]`. Establish `h1 : eval x ((pol (s' w) (χ.comp (nm w))).comp (X ^ fdeg w)) = 0`.

Rewrite using `[eval_comp, eval_pow, eval_X]`. Conclude with `((hL.2.2.2 (s' w) (χ.comp (nm w))).2.2.1 _).2 ⟨ζ, hζ, hu, hbx⟩`. Rewrite `h0` using `[Finset.prod_eq_zero (Finset.mem_univ w) h1, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj⟩` from `h0`. Take `⟨ξ, hξ, hμ, hax⟩` from `((hK s _).2.2.1 x).1 hj`.

Take `⟨hN, hval⟩` from `(normVal K L v w _).1 hμ`. Establish `hone : ∀ y, (η ^ j).loc v (nm w y) = 1` using `fun y => by`. Use `DFunLike.congr_fun (hloc v w).1 y` as an intermediate fact. Rewrite `this` using `[MonoidHom.comp_apply, MonoidHom.one_apply]`. Rewrite using `[loc_pow', MonoidHom.pow_apply, this, one_pow]`.

Use `⟨ξ, hξ, hL.2.1 _ _ ?_ ?_⟩` and prove the remaining obligations. Use `unr_mul hu hN` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `ext1 y`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hone, mul_one, mul_inv_rev]`.

Rewrite using `[mul_assoc, mul_inv_cancel_left]`. Establish `h2 : (((ξ * (χ * (η ^ j).loc v)) (nm w (unif (w.1.adicCompletion L))) : ℂˣ) : ℂ) * x ^ fdeg w = 1`. Rewrite using `[hval, Units.val_pow_eq_pow_val, ← mul_pow, hax, one_pow]`. Establish `hx0 : x ^ fdeg w ≠ 0` using `right_ne_zero_of_mul_eq_one h2`. Establish `h3` using `Units.ext (mul_right_cancel₀ hx0 (hbx.trans h2.symm))`.

Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, hone, mul_one] at h3`. Conclude with `mul_right_cancel h3`. Establish `h0` using `congrArg (Polynomial.eval 1) (hM ξ⁻¹ (IsSmoothChar.inv hξ.1))`. Rewrite `h0` using `[eval_prod, eval_prod]`. Establish `e : ξ * (ξ⁻¹ * (η ^ 0).loc v) = 1` using `by rw [loc_pow', pow_zero, mul_one, mul_inv_cancel]`.

Establish `h1 : eval 1 (pol s (ξ⁻¹ * (η ^ 0).loc v)) = 0` using `((hK s _).2.2.1 1).2 ⟨ξ, hξ, by rw [e]; exact unr_one, by rw [e]; simp⟩`. Rewrite `h0` using `[Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) h1, eq_comm, Finset.prod_eq_zero_iff]`. Take `⟨w, -, hw⟩` from `h0`. Rewrite `hw` using `[eval_comp, eval_pow, eval_X, one_pow]`. Establish `hL` using `polFacts (w.1.adicCompletion L)`.

Take `⟨ζ, hζ, hu, hval⟩` from `((hL.2.2.2 (s' w) _).2.2.1 1).1 hw`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `: ζ = ξ.comp (nm w)`. Use `hL.2.1 _ _ hu ?_` and prove the remaining obligations. Rewrite `hval` using `[mul_one, Units.val_eq_one]`.

Conclude with `mul_inv_eq_one.1 hval`. Conclude with `this ▸ hζ`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.upDownX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.UpDownX := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hBC v s s' hs hs'
  obtain ⟨η, hη, hloc⟩ := normCnt K L hp
  have hM := matchBCX K L hp n hn π P hBC η hη v s s' hs hs'
  have hK := (polFacts (v.adicCompletion K)).2.2.2
  refine ⟨fun hT w ζ hζ => ?_, fun ξ hξ => ?_⟩
  · obtain ⟨χ, hχ, hu⟩ := ((upDown K L hp n hn π P hBC v).1 hT w).2 (s' w) (hs' w) ζ hζ.1 hζ.2
    have hL := polFacts (w.1.adicCompletion L)
    have hf : 0 < fdeg w := (normVal K L v w 1).2.2.1
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
      ((((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ)⁻¹) hf
    have hbx : (((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ) * x ^ fdeg w = 1 := by
      rw [hx]; exact mul_inv_cancel₀ (Units.ne_zero _)
    have h0 := congrArg (Polynomial.eval x) (hM χ hχ)
    rw [eval_prod, eval_prod] at h0
    have h1 : eval x ((pol (s' w) (χ.comp (nm w))).comp (X ^ fdeg w)) = 0 := by
      rw [eval_comp, eval_pow, eval_X]
      exact ((hL.2.2.2 (s' w) (χ.comp (nm w))).2.2.1 _).2 ⟨ζ, hζ, hu, hbx⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ w) h1, Finset.prod_eq_zero_iff] at h0
    obtain ⟨j, -, hj⟩ := h0
    obtain ⟨ξ, hξ, hμ, hax⟩ := ((hK s _).2.2.1 x).1 hj
    obtain ⟨hN, hval⟩ := (normVal K L v w _).1 hμ
    have hone : ∀ y, (η ^ j).loc v (nm w y) = 1 := fun y => by
      have := DFunLike.congr_fun (hloc v w).1 y
      rw [MonoidHom.comp_apply, MonoidHom.one_apply] at this
      rw [loc_pow', MonoidHom.pow_apply, this, one_pow]
    refine ⟨ξ, hξ, hL.2.1 _ _ ?_ ?_⟩
    · have := unr_mul hu hN
      convert this using 1
      ext1 y
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hone, mul_one, mul_inv_rev]
      rw [mul_assoc, mul_inv_cancel_left]
    · have h2 : (((ξ * (χ * (η ^ j).loc v)) (nm w (unif (w.1.adicCompletion L))) : ℂˣ) : ℂ) * x ^ fdeg w = 1 := by
        rw [hval, Units.val_pow_eq_pow_val, ← mul_pow, hax, one_pow]
      have hx0 : x ^ fdeg w ≠ 0 := right_ne_zero_of_mul_eq_one h2
      have h3 := Units.ext (mul_right_cancel₀ hx0 (hbx.trans h2.symm))
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, hone, mul_one] at h3
      exact mul_right_cancel h3
  · have h0 := congrArg (Polynomial.eval 1) (hM ξ⁻¹ (IsSmoothChar.inv hξ.1))
    rw [eval_prod, eval_prod] at h0
    have e : ξ * (ξ⁻¹ * (η ^ 0).loc v) = 1 := by rw [loc_pow', pow_zero, mul_one, mul_inv_cancel]
    have h1 : eval 1 (pol s (ξ⁻¹ * (η ^ 0).loc v)) = 0 :=
      ((hK s _).2.2.1 1).2 ⟨ξ, hξ, by rw [e]; exact unr_one, by rw [e]; simp⟩
    rw [Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) h1, eq_comm, Finset.prod_eq_zero_iff] at h0
    obtain ⟨w, -, hw⟩ := h0
    rw [eval_comp, eval_pow, eval_X, one_pow] at hw
    have hL := polFacts (w.1.adicCompletion L)
    obtain ⟨ζ, hζ, hu, hval⟩ := ((hL.2.2.2 (s' w) _).2.2.1 1).1 hw
    refine ⟨w, ?_⟩
    have : ζ = ξ.comp (nm w) := by
      refine hL.2.1 _ _ hu ?_
      rw [mul_one, Units.val_eq_one] at hval
      exact mul_inv_eq_one.1 hval
    exact this ▸ hζ
