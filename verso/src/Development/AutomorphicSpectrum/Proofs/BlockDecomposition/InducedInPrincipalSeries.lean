import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import GroundTheory.AutomorphicForms.Satake

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp.PsBridge

section SlopeTestRemainingChoices

open ValuativeRel Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_uniformizer_iff.2 (GLnLocal.valuation_uniformizer_lt_one k)`. Take `⟨ϖ, hϖ⟩` from `valuation_surjective (ValuativeRel.uniformizer k)`. Establish `hlt : valuation k ϖ < 1` using `hϖ ▸ uniformizer_lt_one`. Set `y : 𝒪[k]` to `⟨ϖ, hlt.le⟩`.

Establish `hy : y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1`. Rewrite using `[pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]`. Conclude with `hlt.ne`. Establish `h` using `(GLnLocal.mem_maximalIdeal_pow_iff k).1 hy`. Rewrite `h` using `[pow_one]`.

Rewrite using `[← hϖ]`. Conclude with `h`.
-/
theorem valuation_uniformizerUnit :
    valuation k ((uniformizerUnit k : kˣ) : k) = ValuativeRel.uniformizer k := by
  apply le_antisymm
  · exact le_uniformizer_iff.2 (GLnLocal.valuation_uniformizer_lt_one k)
  · obtain ⟨ϖ, hϖ⟩ := valuation_surjective (ValuativeRel.uniformizer k)
    have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
    let y : 𝒪[k] := ⟨ϖ, hlt.le⟩
    have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 := by
      rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact hlt.ne
    have h := (GLnLocal.mem_maximalIdeal_pow_iff k).1 hy
    rw [pow_one] at h
    rw [← hϖ]
    exact h

/- English proof (translation)
Set `o : kˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by`. Rewrite using `[ord_mul, ofAdd_add]`. Establish `h` using `map_zpow o x m`. Establish `h2 : ord k (x ^ m) = m • ord k x` using `congrArg Multiplicative.toAdd h`. Simplify using `using h2`.
-/
theorem ord_zpow' (x : kˣ) (m : ℤ) : ord k (x ^ m) = m * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x m
  have h2 : ord k (x ^ m) = m • ord k x := congrArg Multiplicative.toAdd h
  simpa using h2

variable {n : ℕ}

def diagUnit (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) : kˣ :=
  Units.mk0 (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i)
    (apply_self_ne_zero_of_mem_borel k n p.2 i)

def toParab (p : blockUpper k n (id : Fin n → Fin n)) : parab k (points (Fin n)) :=
  ⟨p.1, fun _ _ h => p.2 h⟩

/- English proof (translation)
Use `ext`. Simplify using `only [GeneralLinearGroup.val_det_apply, Matrix.det_unique]`. Both sides reduce to the same expression.
-/
theorem det_leviProj (p : blockUpper k n (id : Fin n → Fin n)) (i : Fin n) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p) i) = diagUnit p i := by
  ext
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  rfl

/- English proof (translation)
Rewrite using `[val_deltaHalf]`. Express the relevant statement in the definitionally equal form `_ = ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ)`. Use `congr 1`. Rewrite using `[Real.coe_sqrt]`. Use `congr 1`.

Rewrite using `[Measures.modularCharacter_borel, GlobalTheory.SmGL.modulus]`. Use `push_cast`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[det_leviProj, modExp_fin _ (fun _ => by simp)]`. Establish `h` using `Measures.modulus_units (diagUnit p i)`.

Establish `h2 : Measures.modulus (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) = MeasureTheory.distribHaarChar k (diagUnit p i)` using `h`. Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem deltaHalf_eq (p : blockUpper k n (id : Fin n → Fin n)) :
    (deltaHalf k (fun _ : Fin n => Unit) (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) : ℂ) =
      GroundTheory.Automorphic.Parabolic.sqrtModular k n id p := by
  rw [val_deltaHalf]
  change _ = ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ)
  congr 1
  rw [Real.coe_sqrt]
  congr 1
  rw [Measures.modularCharacter_borel, GlobalTheory.SmGL.modulus]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviProj, modExp_fin _ (fun _ => by simp)]
  have h := Measures.modulus_units (diagUnit p i)
  have h2 : Measures.modulus (((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) =
      MeasureTheory.distribHaarChar k (diagUnit p i) := h
  rw [h2]
  rfl

/- English proof (translation)
Use `set l : Fin n → ℤ := fun i => ord k (diagUnit p i) with hl`. Set `e : Fin n → kˣ` to `fun i => diagUnit p i * uniformizerUnit k ^ (-l i)`. Establish `he : ∀ i, valuation k (e i : k) = 1` using `fun i => ord_eq_zero_iff.1 (by`. Establish `h1 : ord k (uniformizerUnit k) = 1` using `ord_eq_one valuation_uniformizerUnit`. Establish `h2 : ord k (e i) = l i + ord k ((uniformizerUnit k) ^ (-l i))` using `ord_mul k _ _`.

Rewrite using `[h2, ord_zpow', h1]`. Use the proof step `ring)`. Set `u : GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n)` to `⟨diagGL k n e, GroundTheory.Automorphic.Parabolic.diagGL_mem_levi e⟩`. Establish `hdec : GroundTheory.Automorphic.Parabolic.leviProj k n id p = torusLevi k n l * u`. Use `Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((GroundTheory.Automorphic.Parabolic.leviProj k n id p : GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n)) : GL (Fin n) k) i j = ((torusPow k n l : Matrix (Fin n) (Fin n) k) * (diagGL k n e : Matrix (Fin n) (Fin n) k)) i j`. Rewrite using `[GroundTheory.Automorphic.Parabolic.leviProj_apply, coe_torusPow, coe_diagGL, diagonal_mul_diagonal, diagonal_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Establish `hϖ : (GLnLocal.uniformizer k : k) ≠ 0` using `(uniformizerUnit k).ne_zero`.

Establish `he' : ((e i : kˣ) : k) = ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i * (GLnLocal.uniformizer k : k) ^ (-l i)`. Simplify using `only [e, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]`. Both sides reduce to the same expression. Rewrite using `[if_pos rfl, if_pos rfl, he', mul_left_comm, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, mul_one]`. Simplify using `[h]`.

Establish `hu : (u : GL (Fin n) k) ∈ GLnLocal.integralGL k n`. Establish `key : ∀ d : Fin n → kˣ, (∀ i, valuation k (d i : k) = 1) → ∀ i j, (diagGL k n d : GL (Fin n) k) i j ∈ 𝒪[k]`. Introduce `d hd i j`. Express the relevant statement in the definitionally equal form `(diagGL k n d : Matrix (Fin n) (Fin n) k) i j ∈ _`. Rewrite using `[coe_diagGL, diagonal_apply]`.

Use `split_ifs`. Conclude with `(hd i).le`. Conclude with `(𝒪[k]).zero_mem`. Rewrite using `[GLnLocal.mem_integralGL_iff]`. Use `⟨key e he, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∀ i j, ((diagGL k n e)⁻¹ : GL (Fin n) k) i j ∈ 𝒪[k]`. Rewrite using `[← map_inv]`. Conclude with `key _ fun i => by simp [he i]`. Rewrite using `[hdec, map_mul, paramChar_torusLevi, isUnramified_paramChar α u hu, mul_one, monomialChar_apply]`.
-/
theorem paramChar_leviProj (α : Fin n → ℂˣ) (p : blockUpper k n (id : Fin n → Fin n)) :
    paramChar k α (GroundTheory.Automorphic.Parabolic.leviProj k n id p) = ∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ) := by
  set l : Fin n → ℤ := fun i => ord k (diagUnit p i) with hl
  let e : Fin n → kˣ := fun i => diagUnit p i * uniformizerUnit k ^ (-l i)
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => ord_eq_zero_iff.1 (by
    have h1 : ord k (uniformizerUnit k) = 1 := ord_eq_one valuation_uniformizerUnit
    have h2 : ord k (e i) = l i + ord k ((uniformizerUnit k) ^ (-l i)) := ord_mul k _ _
    rw [h2, ord_zpow', h1]
    ring)
  let u : GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n) := ⟨diagGL k n e, GroundTheory.Automorphic.Parabolic.diagGL_mem_levi e⟩
  have hdec : GroundTheory.Automorphic.Parabolic.leviProj k n id p = torusLevi k n l * u := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change ((GroundTheory.Automorphic.Parabolic.leviProj k n id p :
        GroundTheory.Automorphic.Parabolic.levi k n (id : Fin n → Fin n)) : GL (Fin n) k) i j =
      ((torusPow k n l : Matrix (Fin n) (Fin n) k) * (diagGL k n e : Matrix (Fin n) (Fin n) k)) i j
    rw [GroundTheory.Automorphic.Parabolic.leviProj_apply, coe_torusPow, coe_diagGL, diagonal_mul_diagonal,
      diagonal_apply]
    by_cases h : i = j
    · subst h
      have hϖ : (GLnLocal.uniformizer k : k) ≠ 0 := (uniformizerUnit k).ne_zero
      have he' : ((e i : kˣ) : k) = ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i *
          (GLnLocal.uniformizer k : k) ^ (-l i) := by
        simp only [e, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit]
        rfl
      rw [if_pos rfl, if_pos rfl, he', mul_left_comm, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero,
        mul_one]
    · simp [h]
  have hu : (u : GL (Fin n) k) ∈ GLnLocal.integralGL k n := by
    have key : ∀ d : Fin n → kˣ, (∀ i, valuation k (d i : k) = 1) →
        ∀ i j, (diagGL k n d : GL (Fin n) k) i j ∈ 𝒪[k] := by
      intro d hd i j
      change (diagGL k n d : Matrix (Fin n) (Fin n) k) i j ∈ _
      rw [coe_diagGL, diagonal_apply]
      split_ifs
      · exact (hd i).le
      · exact (𝒪[k]).zero_mem
    rw [GLnLocal.mem_integralGL_iff]
    refine ⟨key e he, ?_⟩
    change ∀ i j, ((diagGL k n e)⁻¹ : GL (Fin n) k) i j ∈ 𝒪[k]
    rw [← map_inv]
    exact key _ fun i => by simp [he i]
  rw [hdec, map_mul, paramChar_torusLevi, isUnramified_paramChar α u hu, mul_one,
    monomialChar_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨stabilizerOf ρ v, hρ v, fun _ h => mem_stabilizerOf.1 h⟩`.
-/
theorem exists_open_fix {G V : Type} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (v : V) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ x ∈ K, ρ x v = v :=
  ⟨stabilizerOf ρ v, hρ v, fun _ h => mem_stabilizerOf.1 h⟩

end SlopeTestRemainingChoices

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Establish `h1 : ∀ i, ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) i = diagUnit p i` using `det_leviProj p`. Express the relevant statement in the definitionally equal form `GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i)) ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) z = _`. Rewrite using `[GlobalTheory.SmGL.ofChar_apply, torusChar_apply, Units.coe_prod]`. Simplify using `only [h1, unrChar_apply]`.
-/
theorem char_apply (α : Fin n → ℂˣ) (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (z : ℂ) :
    ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)
        (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p)) z =
      (∏ i, ((α i ^ ord k (diagUnit p i) : ℂˣ) : ℂ)) * z := by
  have h1 : ∀ i, ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) i =
      diagUnit p i := det_leviProj p
  change GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))
    ((leviTorus k (Fin n)).symm (GlobalTheory.SmGL.leviProj k (points (Fin n)) (toParab p))) z = _
  rw [GlobalTheory.SmGL.ofChar_apply, torusChar_apply, Units.coe_prod]
  simp only [h1, unrChar_apply]

/- English proof (translation)
Establish `h` using `parInd_law (points (Fin n)) _ f (toParab p) g`. Establish `h2 : f.1.1 ((p : GL (Fin n) k) * g) = _` using `h`. Rewrite using `[h2, borelChar_apply, paramChar_leviProj, ← deltaHalf_eq, smul_eq_mul, char_apply, mul_assoc]`.
-/
theorem addChar_theta_law_rearrangement_identity (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom))
    (p : GroundTheory.Automorphic.Iwasawa.blockUpper k n (id : Fin n → Fin n)) (g : GL (Fin n) k) :
    f.1.1 ((p : GL (Fin n) k) * g) = borelChar (paramChar k α) p * f.1.1 g := by
  have h := parInd_law (points (Fin n)) _ f (toParab p) g
  have h2 : f.1.1 ((p : GL (Fin n) k) * g) = _ := h
  rw [h2, borelChar_apply, paramChar_leviProj, ← deltaHalf_eq, smul_eq_mul, char_apply, mul_assoc]

/- English proof (translation)
Take `⟨K, hK, hKf⟩` from `exists_open_fix _ (isSmooth_parInd (points (Fin n)) ρ) f`. Use `⟨K, hK, fun x hx g => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun v : IndSp (points (Fin n)) ρ => v.1.1 g) (hKf x hx)`. Conclude with `(parInd_apply (points (Fin n)) ρ x g f).symm.trans h`.
-/
theorem induced_vector_smooth_open_subgroup (ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ)
    (f : IndSp (points (Fin n)) ρ) :
    ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧
      ∀ x ∈ K, ∀ g, f.1.1 (g * x) = f.1.1 g := by
  obtain ⟨K, hK, hKf⟩ := exists_open_fix _ (isSmooth_parInd (points (Fin n)) ρ) f
  refine ⟨K, hK, fun x hx g => ?_⟩
  have h := congrArg (fun v : IndSp (points (Fin n)) ρ => v.1.1 g) (hKf x hx)
  exact (parInd_apply (points (Fin n)) ρ x g f).symm.trans h
end

/- English proof (translation)
Introduce `k _ _ _ _ n α f`. Rewrite using `[mem_principalSeriesSpace]`. Conclude with `⟨fun p g => addChar_theta_law_rearrangement_identity α f p g, induced_vector_smooth_open_subgroup _ f⟩`.
-/
theorem indSp_mem_principalSeriesSpace : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  intro k _ _ _ _ n α f
  rw [mem_principalSeriesSpace]
  exact ⟨fun p g => addChar_theta_law_rearrangement_identity α f p g, induced_vector_smooth_open_subgroup _ f⟩

end GlobalTheory.CompanionTheory.SphSupp.PsBridge
