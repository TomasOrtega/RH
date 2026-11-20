import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAt
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SameSat
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.PowSat
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual
open UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

/- English proof (translation)
Establish `hN` using `(places F E hp).2.2.2.2.1`. Use `filter_upwards [H, H'] with w a b`. Take `⟨B, hB, hB'⟩` from `a _ (hN w)`. Take `⟨C, hC, hC'⟩` from `b _ (hN w)`. Take `rfl` from `hB.unique hC`.

Conclude with `⟨_, hB', hC'⟩`.
-/
private theorem same_sat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyComplex F] [IsGalois F E] {n : ℕ} (hp : (Module.finrank F E).Prime) (π : CuspSub F n)
    {sat sat' : Pl E → Multiset ℂˣ → Prop}
    (H : WeakBC (CG.mk π).HasSat sat) (H' : WeakBC (CG.mk π).HasSat sat') :
    ∀ᶠ w : Pl E in cofinite, ∃ B, sat w B ∧ sat' w B := by
  have hN := (places F E hp).2.2.2.2.1
  filter_upwards [H, H'] with w a b
  obtain ⟨B, hB, hB'⟩ := a _ (hN w)
  obtain ⟨C, hC, hC'⟩ := b _ (hN w)
  obtain rfl := hB.unique hC
  exact ⟨_, hB', hC'⟩

/- English proof (translation)
Establish `a` using `Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot`. Establish `b` using `Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
private theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : Pl K) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have a := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have b := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hW v hv B hB w hw f hf`. Set `μE : Measure (normOneGL E n)` to `Measure.haar`. Set `μF : Measure (normOneGL F n)` to `Measure.haar`. Take `⟨s, χ, χ', V, V', θ, hχ, hχ', hV, -, hθ, -, hW', hOff, -⟩` from `Sph.norm F E σ hσ hp n hn μE μF π P hW`. Take `⟨c1, -, c3, -⟩` from `carryLift F E σ hσ hp n hn μE μF`.

Take `⟨Λ, t, S, hS, hAt⟩` from `c1 V hV.summand`. Establish `hN` using `(places F E hp).2.2.2.2.1`. Establish `hBv : (CG.mk (π.twist χ)).HasSat v (B.map (· * χ.val v))`. Use `satake_twist_holds F n (CG.mk π) χ v B (Sph.powSat F χ s hχ v).1 hB` as an intermediate fact. Rewrite `this` using `[CG.twist_mk]`. Then use the resulting hypothesis.

Establish `hSv : SSat μF V v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ))` using `(Dp.sSatIff F n μF (π.twist χ) V hV v _).2 ⟨_, rfl, hBv⟩`. Set `t₁ : Pl F → Multiset ℂ` to `Function.update t v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ))`. Establish `hAt₁ : At μF (S \ {v}) V Λ t₁`. Use `⟨hAt.1, fun u hu => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : u = v`.

Substitute `e` using the available equality. Simplify `hSv` using `[t₁]`. Establish `hu' : u ∉ S` using `fun h => hu ⟨h, e⟩`. Simplify `hAt.2 u hu'` using `[t₁, Function.update_of_ne e]`. Establish `hfin : (S \ {v}).Finite` using `hS.diff`.

Establish `hAE₁ : AtAE μF V Λ t₁` using `⟨_, hfin, hAt₁⟩`. Take `⟨V'', hV'', hAE'', hup⟩` from `Sph.liftAt ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V Λ t₁ (S \ {v}) hV.summand hfin hAt₁ (hOff Λ t₁ hAE₁) v (by simp) hv`. Take `⟨P', hP', -⟩` from `Dp.exCusp E n μE V'' hV''`. Establish `hl` using `c3 _ P' V V'' Λ t₁ _ _ hV hP' hAE₁ hAE'' rfl (Filter.Eventually.of_forall fun _ => rfl)`. Establish `e : P' = P.twist χ'` using `Sph.smoEq E n hn P' (P.twist χ') (same_sat hp (π.twist χ) hl.1 hW')`.

Rewrite `hP'` using `[e]`. Take `⟨B', hB'e, hB'⟩` from `(Dp.sSatIff E n μE (P.twist χ') V'' hP' w _).1 (hup w hw)`. Establish `h1` using `hN w`. Rewrite `h1` using `[hw]`. Establish `hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f` using `hf`.

Establish `hg : f = resDeg F w` using `Nat.pow_right_injective (two_le_absNorm v) (hf'.symm.trans h1)`. Establish `hB'' : B' = B.map fun b => (b * χ.val v) ^ f`. Use `Multiset.map_injective Units.val_injective ?_` and prove the remaining obligations. Rewrite using `[← hB'e, bcSat, hw, ← hg]`. Simplify using `[t₁, Multiset.map_map]`.

Substitute `hB''` using the available equality. Take `⟨-, hinv, h3⟩` from `(powTwist F E).2 s χ χ' hχ hχ'`. Establish `htt` using `(h3 n hn).2.1 P`. Establish `hval : χ'.val w = χ.val v ^ f`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val, (Sph.powSat F χ s hχ _).2, (Sph.powSat E χ' s hχ' w).2, hf', Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]`. Establish `hfin'` using `satake_twist_holds E n (CG.mk (P.twist χ')) χ'⁻¹ w _ (Sph.powSat E χ'⁻¹ (-s) hinv w).1 hB'`. Rewrite `hfin'` using `[CG.twist_mk, htt]`. Express the relevant statement in the definitionally equal form `(CG.mk P).HasSat w _`. Use `hfin' using 1` and compare the differences between its conclusion and the goal.

Simplify using `[Multiset.map_map, hval, mul_pow, HChar.val_inv]`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.up :
    UpperTheory.ConvolutionTheory.Sph.Up := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hW v hv B hB w hw f hf
  let μE : Measure (normOneGL E n) := Measure.haar
  let μF : Measure (normOneGL F n) := Measure.haar
  obtain ⟨s, χ, χ', V, V', θ, hχ, hχ', hV, -, hθ, -, hW', hOff, -⟩ :=
    Sph.norm F E σ hσ hp n hn μE μF π P hW
  obtain ⟨c1, -, c3, -⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, S, hS, hAt⟩ := c1 V hV.summand
  have hN := (places F E hp).2.2.2.2.1

  have hBv : (CG.mk (π.twist χ)).HasSat v (B.map (· * χ.val v)) := by
    have := satake_twist_holds F n (CG.mk π) χ v B (Sph.powSat F χ s hχ v).1 hB
    rwa [CG.twist_mk] at this
  have hSv : SSat μF V v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ)) :=
    (Dp.sSatIff F n μF (π.twist χ) V hV v _).2 ⟨_, rfl, hBv⟩

  let t₁ : Pl F → Multiset ℂ := Function.update t v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ))
  have hAt₁ : At μF (S \ {v}) V Λ t₁ := by
    refine ⟨hAt.1, fun u hu => ?_⟩
    by_cases e : u = v
    · subst e
      simpa [t₁] using hSv
    · have hu' : u ∉ S := fun h => hu ⟨h, e⟩
      simpa [t₁, Function.update_of_ne e] using hAt.2 u hu'
  have hfin : (S \ {v}).Finite := hS.diff
  have hAE₁ : AtAE μF V Λ t₁ := ⟨_, hfin, hAt₁⟩
  obtain ⟨V'', hV'', hAE'', hup⟩ := Sph.liftAt ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V Λ t₁ (S \ {v})
    hV.summand hfin hAt₁ (hOff Λ t₁ hAE₁) v (by simp) hv

  obtain ⟨P', hP', -⟩ := Dp.exCusp E n μE V'' hV''
  have hl := c3 _ P' V V'' Λ t₁ _ _ hV hP' hAE₁ hAE'' rfl (Filter.Eventually.of_forall fun _ => rfl)
  have e : P' = P.twist χ' := Sph.smoEq E n hn P' (P.twist χ') (same_sat hp (π.twist χ) hl.1 hW')
  rw [e] at hP'

  obtain ⟨B', hB'e, hB'⟩ := (Dp.sSatIff E n μE (P.twist χ') V'' hP' w _).1 (hup w hw)
  have h1 := hN w
  rw [hw] at h1
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hg : f = resDeg F w := Nat.pow_right_injective (two_le_absNorm v) (hf'.symm.trans h1)
  have hB'' : B' = B.map fun b => (b * χ.val v) ^ f := by
    refine Multiset.map_injective Units.val_injective ?_
    rw [← hB'e, bcSat, hw, ← hg]
    simp [t₁, Multiset.map_map]
  subst hB''

  obtain ⟨-, hinv, h3⟩ := (powTwist F E).2 s χ χ' hχ hχ'
  have htt := (h3 n hn).2.1 P
  have hval : χ'.val w = χ.val v ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (Sph.powSat F χ s hχ _).2, (Sph.powSat E χ' s hχ' w).2, hf', Nat.cast_pow,
      ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
  have hfin' := satake_twist_holds E n (CG.mk (P.twist χ')) χ'⁻¹ w _ (Sph.powSat E χ'⁻¹ (-s) hinv w).1 hB'
  rw [CG.twist_mk, htt] at hfin'
  change (CG.mk P).HasSat w _
  convert hfin' using 1
  simp [Multiset.map_map, hval, mul_pow, HChar.val_inv]
