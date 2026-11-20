import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSectionUnramified
import GroundTheory.AutomorphicForms.GL2.GodementSectionLocal
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Matrix Filter
  Topology
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleAt (v : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adeleAt_apply (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K) :
    adeleAt v x = x v := rfl

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval v`.
-/
theorem continuous_adeleAt (v : HeightOneSpectrum (𝓞 K)) : Continuous (adeleAt (K := K) v) :=
  RestrictedProduct.continuous_eval v

def glAt (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (adeleAt v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glAt_apply (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (i j : Fin 2) :
    (glAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j v := rfl

def vecAt (v : HeightOneSpectrum (𝓞 K)) (x : Fin 2 → FiniteAdeleRing (𝓞 K) K) :
    Fin 2 → v.adicCompletion K :=
  fun i ↦ x i v

/- English proof (translation)
The claim follows from `continuous_pi fun i ↦ (continuous_adeleAt v).comp (continuous_apply i)`.
-/
theorem continuous_vecAt (v : HeightOneSpectrum (𝓞 K)) : Continuous (vecAt (K := K) v) :=
  continuous_pi fun i ↦ (continuous_adeleAt v).comp (continuous_apply i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_vecMul (adeleAt v) _ x i`.
-/
theorem vecAt_vecMul (v : HeightOneSpectrum (𝓞 K)) (x : Fin 2 → FiniteAdeleRing (𝓞 K) K)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    vecAt v (x ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) =
      vecAt v x ᵥ* (glAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  funext i
  exact RingHom.map_vecMul (adeleAt v) _ x i

def awayIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) :
    AddSubgroup (FiniteAdeleRing (𝓞 K) K) where
  carrier := {a | ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K}
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_awayIntegral {S : Finset (HeightOneSpectrum (𝓞 K))} {a : FiniteAdeleRing (𝓞 K) K} :
    a ∈ awayIntegral S ↔ ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K := Iff.rfl

/- English proof (translation)
Use `AddSubgroup.isOpen_mono (H₁ := (integralFiniteAdeles (𝓞 K) K).toAddSubgroup) (fun a ha v _ ↦ mem_integralFiniteAdeles.1 ha v) isOpen_integralFiniteAdeles` and prove the remaining obligations.
-/
theorem isOpen_awayIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine AddSubgroup.isOpen_mono (H₁ := (integralFiniteAdeles (𝓞 K) K).toAddSubgroup)
    (fun a ha v _ ↦ mem_integralFiniteAdeles.1 ha v) isOpen_integralFiniteAdeles

def awayBox (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Fin 2 → FiniteAdeleRing (𝓞 K) K) :=
  {x | ∀ i, x i ∈ awayIntegral S}

def restrictedTensor2 (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ψ : ∀ v : S, (Fin 2 → v.1.adicCompletion K) → ℂ) :
    (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ :=
  (awayBox S).indicator fun x ↦ ∏ v : S, Ψ v (vecAt v.1 x)

/- English proof (translation)
Establish `hA : IsClopen (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K))` using `⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_awayIntegral S), isOpen_awayIntegral S⟩`. Establish `h : awayBox (K` using `K) S = (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ x 0) ⁻¹' (awayIntegral S : Set _) ∩ (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ x 1) ⁻¹' (awayIntegral S : Set _) := by`. Use extensionality with `x`. Simplify using `[awayBox, Fin.forall_fin_two]`. Rewrite using `[h]`.

Conclude with `(hA.preimage (continuous_apply 0)).inter (hA.preimage (continuous_apply 1))`.
-/
theorem isClopen_awayBox (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClopen (awayBox (K := K) S) := by
  have hA : IsClopen (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_awayIntegral S), isOpen_awayIntegral S⟩
  have h : awayBox (K := K) S =
      (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ x 0) ⁻¹' (awayIntegral S : Set _) ∩
        (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ x 1) ⁻¹' (awayIntegral S : Set _) := by
    ext x; simp [awayBox, Fin.forall_fin_two]
  rw [h]
  exact (hA.preimage (continuous_apply 0)).inter (hA.preimage (continuous_apply 1))

/- English proof (translation)
Distinguish the cases in `h0 : y = 0`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le`. Establish `hN : (1 : ℝ) < Ideal.absNorm v.asIdeal`. Conclude with `HeightOneSpectrum.one_lt_absNorm v` after adjusting the coercions.

Establish `hv0 : Valued.v y ≠ 0` using `(Valued.v).ne_zero_iff.2 h0`. Establish `h1` using `normalizedAbv_eq_zpow v h0`. Rewrite `h1` using `[normalizedAbv_apply]`. Rewrite `hy` using `[h1, ← zpow_natCast]`. Establish `h2 : WithZero.log (Valued.v y) ≤ n` using `(zpow_le_zpow_iff_right₀ hN).1 hy`.

Conclude with `(WithZero.log_le_iff_le_exp hv0).1 h2`.
-/
theorem valued_le_exp_of_norm_le {v : HeightOneSpectrum (𝓞 K)} {y : v.adicCompletion K} {n : ℕ}
    (hy : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v y ≤ WithZero.exp (n : ℤ) := by
  by_cases h0 : y = 0
  · rw [h0, map_zero]; exact zero_le
  have hN : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hv0 : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.2 h0
  have h1 := normalizedAbv_eq_zpow v h0
  rw [normalizedAbv_apply] at h1
  rw [h1, ← zpow_natCast] at hy
  have h2 : WithZero.log (Valued.v y) ≤ n := (zpow_le_zpow_iff_right₀ hN).1 hy
  exact (WithZero.log_le_iff_le_exp hv0).1 h2

/- English proof (translation)
Use `(mem_finiteSchwartzBruhat2 K).2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `GodementSectionLocal.isLocallyConstant_indicator (isClopen_awayBox S) ?_` and prove the remaining obligations. Establish `hv : ∀ v : S, IsLocallyConstant fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ Ψ v (vecAt v.1 x)` using `fun v ↦ ((GodementSectionLocal.mem_schwartzBruhat2.1 (hΨ v)).1).comp_continuous (continuous_vecAt v.1)`. Establish `heq : (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ ∏ v : S, Ψ v (vecAt v.1 x)) = ∏ v : S, fun x ↦ Ψ v (vecAt v.1 x)`. Use function extensionality and compare the values at `x`.

Simplify using `[Finset.prod_apply]`. Rewrite using `[heq]`. Conclude with `Finset.prod_induction _ IsLocallyConstant (fun a b ha hb ↦ ha.mul hb) (IsLocallyConstant.const 1) fun v _ ↦ hv v`. Establish `hb : ∀ v : S, ∃ n : ℕ, ∀ y, Ψ v y ≠ 0 → ∀ i, ‖y i‖ ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ n`. Introduce `v`.

Take `⟨R, hR⟩` from `((GodementSectionLocal.mem_schwartzBruhat2.1 (hΨ v)).2.isCompact.isBounded ).exists_norm_le`. Establish `hN : (1 : ℝ) < Ideal.absNorm v.1.asIdeal`. Conclude with `HeightOneSpectrum.one_lt_absNorm v.1` after adjusting the coercions. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt R hN`. Use `⟨n, fun y hy i ↦ ?_⟩` and prove the remaining obligations.

Establish `hyR` using `hR y (subset_tsupport _ hy)`. Conclude with `((norm_le_pi_norm y i).trans hyR).trans hn.le`. Use `choose n hn using hb`. Use `set m : HeightOneSpectrum (𝓞 K) → ℤ := fun w ↦ if h : w ∈ S then -(n ⟨w, h⟩ : ℤ) else 0 with hm`. Establish `hmfin : ∀ᶠ w in Filter.cofinite, m w = 0`.

Rewrite using `[Filter.eventually_cofinite]`. Use `S.finite_toSet.subset fun w hw ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hwS`. Conclude with `hw (by simp only [hm, dif_neg (fun h ↦ hwS (Finset.mem_coe.2 h))])`. Use `set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ w, primeIdealUnit w ^ m w with hL`.

Establish `hcount : ∀ w, FractionalIdeal.count K w (L : FractionalIdeal (𝓞 K)⁰ K) = m w` using `count_finprod_primeIdealUnit_zpow m hmfin`. Use `HasCompactSupport.intro (isCompact_idealFiniteAdeles2 L) fun x hx ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, mem_idealFiniteAdeles2]`.

Introduce `i`. Rewrite using `[mem_idealFiniteAdeles]`. Introduce `w`. Rewrite using `[hcount w]`. Establish `hxB : x ∈ awayBox S`.

Assume the negation of the conclusion as `h`. Conclude with `hne (Set.indicator_of_notMem h _)`. Distinguish the cases in `hw : w ∈ S`. Establish `hprod : ∏ v : S, Ψ v (vecAt v.1 x) ≠ 0`. Rewrite `hne` using `[restrictedTensor2, Set.indicator_of_mem hxB]`. Then use the resulting hypothesis.

Establish `hΨw : Ψ ⟨w, hw⟩ (vecAt w x) ≠ 0` using `Finset.prod_ne_zero_iff.1 hprod ⟨w, hw⟩ (Finset.mem_univ _)`. Use `valued_le_exp_of_norm_le (hn ⟨w, hw⟩ (vecAt w x) hΨw i)` as an intermediate fact. Simplify using `only [hm, dif_pos hw, neg_neg]`. Conclude with `this`. Establish `hint : x i w ∈ w.adicCompletionIntegers K` using `hxB i w hw`.

Simplify using `only [hm, dif_neg hw, neg_zero, WithZero.exp_zero]`. Conclude with `(mem_adicCompletionIntegers _ _ _).1 hint`.
-/
theorem restrictedTensor2_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    {Ψ : ∀ v : S, (Fin 2 → v.1.adicCompletion K) → ℂ}
    (hΨ : ∀ v, Ψ v ∈ GodementSectionLocal.schwartzBruhat2 (v.1.adicCompletion K)) :
    restrictedTensor2 S Ψ ∈ finiteSchwartzBruhat2 K := by
  refine (mem_finiteSchwartzBruhat2 K).2 ⟨?_, ?_⟩
  · refine GodementSectionLocal.isLocallyConstant_indicator (isClopen_awayBox S) ?_
    have hv : ∀ v : S, IsLocallyConstant fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦
        Ψ v (vecAt v.1 x) := fun v ↦
      ((GodementSectionLocal.mem_schwartzBruhat2.1 (hΨ v)).1).comp_continuous (continuous_vecAt v.1)
    have heq : (fun x : Fin 2 → FiniteAdeleRing (𝓞 K) K ↦ ∏ v : S, Ψ v (vecAt v.1 x)) =
        ∏ v : S, fun x ↦ Ψ v (vecAt v.1 x) := by
      funext x; simp [Finset.prod_apply]
    rw [heq]
    exact Finset.prod_induction _ IsLocallyConstant (fun a b ha hb ↦ ha.mul hb)
      (IsLocallyConstant.const 1) fun v _ ↦ hv v
  ·
    have hb : ∀ v : S, ∃ n : ℕ, ∀ y, Ψ v y ≠ 0 → ∀ i,
        ‖y i‖ ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ n := by
      intro v
      obtain ⟨R, hR⟩ := ((GodementSectionLocal.mem_schwartzBruhat2.1 (hΨ v)).2.isCompact.isBounded
        ).exists_norm_le
      have hN : (1 : ℝ) < Ideal.absNorm v.1.asIdeal := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.1
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R hN
      refine ⟨n, fun y hy i ↦ ?_⟩
      have hyR := hR y (subset_tsupport _ hy)
      exact ((norm_le_pi_norm y i).trans hyR).trans hn.le
    choose n hn using hb
    set m : HeightOneSpectrum (𝓞 K) → ℤ := fun w ↦ if h : w ∈ S then -(n ⟨w, h⟩ : ℤ) else 0
      with hm
    have hmfin : ∀ᶠ w in Filter.cofinite, m w = 0 := by
      rw [Filter.eventually_cofinite]
      refine S.finite_toSet.subset fun w hw ↦ ?_
      by_contra hwS
      exact hw (by simp only [hm, dif_neg (fun h ↦ hwS (Finset.mem_coe.2 h))])
    set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ w, primeIdealUnit w ^ m w with hL
    have hcount : ∀ w, FractionalIdeal.count K w (L : FractionalIdeal (𝓞 K)⁰ K) = m w :=
      count_finprod_primeIdealUnit_zpow m hmfin
    refine HasCompactSupport.intro (isCompact_idealFiniteAdeles2 L) fun x hx ↦ ?_
    by_contra hne
    apply hx
    rw [SetLike.mem_coe, mem_idealFiniteAdeles2]
    intro i
    rw [mem_idealFiniteAdeles]
    intro w
    rw [hcount w]
    have hxB : x ∈ awayBox S := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    by_cases hw : w ∈ S
    · have hprod : ∏ v : S, Ψ v (vecAt v.1 x) ≠ 0 := by
        rwa [restrictedTensor2, Set.indicator_of_mem hxB] at hne
      have hΨw : Ψ ⟨w, hw⟩ (vecAt w x) ≠ 0 :=
        Finset.prod_ne_zero_iff.1 hprod ⟨w, hw⟩ (Finset.mem_univ _)
      have := valued_le_exp_of_norm_le (hn ⟨w, hw⟩ (vecAt w x) hΨw i)
      simp only [hm, dif_pos hw, neg_neg]
      exact this
    · have hint : x i w ∈ w.adicCompletionIntegers K := hxB i w hw
      simp only [hm, dif_neg hw, neg_zero, WithZero.exp_zero]
      exact (mem_adicCompletionIntegers _ _ _).1 hint

def localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  Circle.toUnits.comp (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : ((localChar χ v a : ℂˣ) : ℂ) = (χ.localComponent v a : ℂ) :=
  rfl

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (χ.localComponent v).continuous`. Establish `h : (fun a ↦ (((localChar χ v a)⁻¹ : ℂˣ) : ℂ)) = fun a ↦ ((χ.localComponent v a⁻¹ : Circle) : ℂ)`. Use function extensionality and compare the values at `a`. Rewrite using `[← map_inv, coe_localChar]`.

Rewrite using `[h]`. Conclude with `continuous_subtype_val.comp ((χ.localComponent v).continuous.comp continuous_inv)`.
-/
theorem continuous_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localChar χ v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_subtype_val.comp (χ.localComponent v).continuous
  · have h : (fun a ↦ (((localChar χ v a)⁻¹ : ℂˣ) : ℂ)) =
        fun a ↦ ((χ.localComponent v a⁻¹ : Circle) : ℂ) := by
      funext a
      rw [← map_inv, coe_localChar]
    rw [h]
    exact continuous_subtype_val.comp ((χ.localComponent v).continuous.comp continuous_inv)

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [coe_localChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]`. Rewrite using `[← coe_localChar, ← coe_localChar]`. Both sides reduce to the same expression.
-/
theorem localChar_mul_inv (χ₁ χ₂ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    localChar (χ₁ * χ₂⁻¹) v = localChar χ₁ v * (localChar χ₂ v)⁻¹ := by
  ext a
  simp only [coe_localChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  rw [← coe_localChar, ← coe_localChar]
  rfl

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx, LocalField.modulus]`. Rewrite using `[LocalField.modulus_of_ne_zero hx, norm_eq_absNorm_zpow_neg_ord v hx, NNReal.coe_zpow]`. Use `congr 1`. Rewrite using `[LocalField.residueCard, natCard_residueField_adicCompletion]`.

Both sides reduce to the same expression.
-/
theorem modulus_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    (LocalField.modulus x : ℝ) = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, LocalField.modulus]
  rw [LocalField.modulus_of_ne_zero hx, norm_eq_absNorm_zpow_neg_ord v hx, NNReal.coe_zpow]
  congr 1
  rw [LocalField.residueCard, natCard_residueField_adicCompletion]
  rfl

def partAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, (finiteUnitsSingle v).comp (finiteComponent v)

/- English proof (translation)
Simplify using `[partAt]`.
-/
theorem partAt_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    partAt S b = ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v b) := by
  simp [partAt]

/- English proof (translation)
Rewrite using `[partAt_apply, map_prod]`. Use `split_ifs with hw`. Rewrite using `[Finset.prod_eq_single w (fun u _ huw ↦ finiteComponent_finiteUnitsSingle_of_ne (Ne.symm huw) _) (fun h ↦ absurd hw h), finiteComponent_finiteUnitsSingle]`. Use `Finset.prod_eq_one fun u hu ↦ finiteComponent_finiteUnitsSingle_of_ne ?_ _` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hw hu`.
-/
theorem finiteComponent_partAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    finiteComponent w (partAt S b) = if w ∈ S then finiteComponent w b else 1 := by
  rw [partAt_apply, map_prod]
  split_ifs with hw
  · rw [Finset.prod_eq_single w (fun u _ huw ↦ finiteComponent_finiteUnitsSingle_of_ne
      (Ne.symm huw) _) (fun h ↦ absurd hw h), finiteComponent_finiteUnitsSingle]
  · refine Finset.prod_eq_one fun u hu ↦ finiteComponent_finiteUnitsSingle_of_ne ?_ _
    rintro rfl
    exact hw hu

def awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  MonoidHom.id _ / partAt S

/- English proof (translation)
Simplify using `[awayPart, div_eq_mul_inv]`.
-/
theorem awayPart_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    awayPart S b = b * (partAt S b)⁻¹ := by
  simp [awayPart, div_eq_mul_inv]

/- English proof (translation)
Rewrite using `[awayPart_apply, map_mul, map_inv, finiteComponent_partAt]`. Use `split_ifs`. Conclude with `mul_inv_cancel _`. Rewrite using `[inv_one, mul_one]`.
-/
theorem finiteComponent_awayPart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    finiteComponent w (awayPart S b) = if w ∈ S then 1 else finiteComponent w b := by
  rw [awayPart_apply, map_mul, map_inv, finiteComponent_partAt]
  split_ifs
  · exact mul_inv_cancel _
  · rw [inv_one, mul_one]

/- English proof (translation)
Rewrite using `[awayPart_apply, mul_comm b, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
theorem partAt_mul_awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    partAt S b * awayPart S b = b := by
  rw [awayPart_apply, mul_comm b, ← mul_assoc, mul_inv_cancel, one_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Conclude with `congrArg Units.val (h w)`.
-/
theorem finiteIdele_ext {b c : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (h : ∀ w, finiteComponent w b = finiteComponent w c) : b = c := by
  apply Units.ext
  apply Subtype.ext
  funext w
  exact congrArg Units.val (h w)

/- English proof (translation)
Use `finiteIdele_ext fun w ↦ ?_` and prove the remaining obligations. Rewrite using `[finiteComponent_awayPart, finiteComponent_awayPart]`. Use `split_ifs with hw`. Both sides reduce to the same expression. Conclude with `h w hw`.
-/
theorem awayPart_eq_of_forall (S : Finset (HeightOneSpectrum (𝓞 K)))
    {b c : (FiniteAdeleRing (𝓞 K) K)ˣ} (h : ∀ w ∉ S, finiteComponent w b = finiteComponent w c) :
    awayPart S b = awayPart S c := by
  refine finiteIdele_ext fun w ↦ ?_
  rw [finiteComponent_awayPart, finiteComponent_awayPart]
  split_ifs with hw
  · rfl
  · exact h w hw

/- English proof (translation)
Establish `h : ⇑(partAt (K` using `K) S) = fun b ↦ ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v b) :=`. Use function extensionality and compare the values at `(partAt_apply S)`. Rewrite using `[h]`. Conclude with `continuous_finsetProd _ fun v _ ↦ (continuous_finiteUnitsSingle v).comp (continuous_finiteComponent v)`.
-/
theorem continuous_partAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (partAt (K := K) S) := by
  have h : ⇑(partAt (K := K) S) = fun b ↦ ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v b) :=
    funext (partAt_apply S)
  rw [h]
  exact continuous_finsetProd _ fun v _ ↦
    (continuous_finiteUnitsSingle v).comp (continuous_finiteComponent v)

/- English proof (translation)
Establish `h : ⇑(awayPart (K` using `K) S) = fun b ↦ b * (partAt S b)⁻¹ := funext (awayPart_apply S)`. Rewrite using `[h]`. Conclude with `continuous_id.mul ((continuous_partAt S).inv)`.
-/
theorem continuous_awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (awayPart (K := K) S) := by
  have h : ⇑(awayPart (K := K) S) = fun b ↦ b * (partAt S b)⁻¹ := funext (awayPart_apply S)
  rw [h]
  exact continuous_id.mul ((continuous_partAt S).inv)

/- English proof (translation)
Rewrite using `[partAt_apply, map_prod, map_prod]`. Conclude with `(map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun v _ ↦ by rw [ofFinite_finiteUnitsSingle]; rfl)`.
-/
theorem toIdele_ofFinite_partAt (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (χ.toIdele (ofFinite (partAt S b)) : ℂ) =
      ∏ v ∈ S, (χ.localComponent v (finiteComponent v b) : ℂ) := by
  rw [partAt_apply, map_prod, map_prod]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun v _ ↦ by rw [ofFinite_finiteUnitsSingle]; rfl)

/- English proof (translation)
Rewrite using `[finiteModule]`. Rewrite using `[finprod_eq_single _ v]`. Simplify using the standard rewrite rules. Introduce `w hw`. Simplify using `[finiteAdeleSingle_apply_of_ne hw]`.
-/
theorem finiteModule_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    finiteModule (finiteEmbedding v a) = ‖(a : v.adicCompletion K)‖ := by
  rw [finiteModule]
  rw [finprod_eq_single _ v]
  · simp
  · intro w hw
    simp [finiteAdeleSingle_apply_of_ne hw]

/- English proof (translation)
Rewrite using `[partAt_apply, map_prod]`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [finiteModule]`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, finiteModule_mul, ih, ofFinite_finiteUnitsSingle, finiteModule_finiteEmbedding]`.
-/
theorem finiteModule_ofFinite_partAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finiteModule (ofFinite (partAt S b)) =
      ∏ v ∈ S, ‖((finiteComponent v b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := by
  rw [partAt_apply, map_prod]
  induction S using Finset.induction_on with
  | empty => simp [finiteModule]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, finiteModule_mul, ih,
      ofFinite_finiteUnitsSingle, finiteModule_finiteEmbedding]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ ↦ hr i), ih]`.
-/
theorem ofReal_prod_cpow {ι : Type*} (T : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (s : ℂ) :
    ((∏ i ∈ T, r i : ℝ) : ℂ) ^ s = ∏ i ∈ T, ((r i : ℝ) : ℂ) ^ s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ ↦ hr i), ih]

def partialLFunction (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), (if ∀ v ∈ S, ¬ v.asIdeal ∣ I then χ.coeff I else 0) *
    (Ideal.absNorm I : ℂ) ^ (-z)

/- English proof (translation)
Use `Summable.hasSum (Summable.of_norm_bounded (χ.summable_norm_coeffTerm hz) fun I ↦ ?_)` and prove the remaining obligations. Rewrite using `[HeckeCharacter.coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]`. Use `split_ifs`. Conclude with `le_rfl`. Simplify using `only [zero_mul, norm_zero, norm_mul, norm_inv]`.

Check the signs of the components of the expression.
-/
theorem hasSum_partialLFunction (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ (if ∀ v ∈ S, ¬ v.asIdeal ∣ I then χ.coeff I else 0) *
      (Ideal.absNorm I : ℂ) ^ (-z)) (partialLFunction χ S z) := by
  refine Summable.hasSum (Summable.of_norm_bounded (χ.summable_norm_coeffTerm hz) fun I ↦ ?_)
  rw [HeckeCharacter.coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]
  split_ifs
  · exact le_rfl
  · simp only [zero_mul, norm_zero, norm_mul, norm_inv]
    positivity

/- English proof (translation)
Use `(hasSum_partialLFunction χ ∅ hz).unique ?_` and prove the remaining obligations. Simplify using `using χ.hasSum_LFunction hz`.
-/
theorem partialLFunction_empty (χ : HeckeCharacter K) {z : ℂ} (hz : 1 < z.re) :
    partialLFunction χ ∅ z = χ.LFunction z := by
  refine (hasSum_partialLFunction χ ∅ hz).unique ?_
  simpa using χ.hasSum_LFunction hz

/- English proof (translation)
Rewrite using `[Submonoid.mem_units_iff]`. Express the relevant statement in the definitionally equal form `(x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _`. Rewrite using `[mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]`. Establish `h0 : Valued.v (x : v.adicCompletion K) ≠ 0` using `(Valued.v).ne_zero_iff.2 x.ne_zero`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)`. Introduce `h`. Rewrite using `[h, inv_one]`. Conclude with `⟨le_rfl, le_rfl⟩`.
-/
theorem mem_units_adicCompletionIntegers_iff {v : HeightOneSpectrum (𝓞 K)}
    (x : (v.adicCompletion K)ˣ) :
    x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ↔
      Valued.v (x : v.adicCompletion K) = 1 := by
  rw [Submonoid.mem_units_iff]
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  have h0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valued.v).ne_zero_iff.2 x.ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

/- English proof (translation)
Rewrite using `[mem_units_adicCompletionIntegers_iff, coe_finiteComponent, HeckeCharacter.valued_eq_exp_ord b v, ← WithZero.exp_zero, WithZero.exp_inj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_units_iff_ord_eq_zero (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ↔
      ord v (ofFinite b) = 0 := by
  rw [mem_units_adicCompletionIntegers_iff, coe_finiteComponent,
    HeckeCharacter.valued_eq_exp_ord b v, ← WithZero.exp_zero, WithZero.exp_inj]
  omega

/- English proof (translation)
Rewrite using `[mem_adicCompletionIntegers, HeckeCharacter.valued_eq_exp_ord b v, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_integers_iff_ord_nonneg (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ↔ 0 ≤ ord v (ofFinite b) := by
  rw [mem_adicCompletionIntegers, HeckeCharacter.valued_eq_exp_ord b v, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

def awayFactor (μ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  (if (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S then 1 else 0) *
    (μ.toIdele (ofFinite (awayPart S b)) : ℂ) *
      ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ z

/- English proof (translation)
Establish `hmem : ((b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S) ↔ ((c : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S)`. Use `forall_congr' fun w ↦ imp_congr_right fun hw ↦ ?_` and prove the remaining obligations. Rewrite using `[← coe_finiteComponent, ← coe_finiteComponent, h w hw]`. Simplify using `only [awayFactor, hmem, awayPart_eq_of_forall S h]`.
-/
theorem awayFactor_eq_of_forall (μ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : ℂ) {b c : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (h : ∀ w ∉ S, finiteComponent w b = finiteComponent w c) :
    awayFactor μ S z b = awayFactor μ S z c := by
  have hmem : ((b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S) ↔
      ((c : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S) := by
    refine forall_congr' fun w ↦ imp_congr_right fun hw ↦ ?_
    rw [← coe_finiteComponent, ← coe_finiteComponent, h w hw]
  simp only [awayFactor, hmem, awayPart_eq_of_forall S h]

def awayOrderTerm (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ)
    (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : ℂ :=
  if (∀ v, 0 ≤ n v) ∧ ∀ v ∈ S, n v = 0 then
    χ.coeff (idealOfExponents n) * (Ideal.absNorm (idealOfExponents n) : ℂ) ^ (-z) else 0

/- English proof (translation)
Rewrite using `[HeckeCharacter.ord_ofFinite, finiteComponent_awayPart]`. Use `split_ifs`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem ord_ofFinite_awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ord v (ofFinite (awayPart S b)) = if v ∈ S then 0 else ord v (ofFinite b) := by
  rw [HeckeCharacter.ord_ofFinite, finiteComponent_awayPart]
  split_ifs
  · simp
  · rfl

/- English proof (translation)
Use `set n := ordFinsupp K (ofFinite b) with hn_def`. Establish `hn : ∀ v, n v = ord v (ofFinite b)` using `fun v ↦ rfl`. Distinguish the cases in `hA : (∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) ∧ (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S`. Establish `hS0 : ∀ v ∈ S, n v = 0` using `fun v hv ↦ by`. Rewrite using `[hn]`.

Conclude with `(mem_units_iff_ord_eq_zero b v).1 (hA.1 v hv)`. Establish `hpos : ∀ v, 0 ≤ n v` using `fun v ↦ by`. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hS0 v hv]`. Rewrite using `[hn]`.

Conclude with `(mem_integers_iff_ord_nonneg b v).1 (hA.2 v hv)`. Rewrite using `[if_pos hA.1, awayFactor, if_pos hA.2, one_mul, one_mul, awayOrderTerm, if_pos ⟨hpos, hS0⟩]`. Use `set b' := awayPart S b with hb'`. Establish `hord : ∀ v, ord v (ofFinite b') = n v`. Introduce `v`.

Rewrite using `[hb', ord_ofFinite_awayPart]`. Use `split_ifs with hv`. Conclude with `(hS0 v hv).symm`. Both sides reduce to the same expression. Establish `hfin : ordFinsupp K (ofFinite b') = n` using `Finsupp.ext hord`.

Establish `hpos' : ∀ v, 0 ≤ ord v (ofFinite b')` using `fun v ↦ by rw [hord]; exact hpos v`. Establish `hI0` using `HeckeCharacter.idealOfExponents_ne_bot hpos`. Establish `hIc : IsCoprime (idealOfExponents n) μ.conductor` using `HeckeCharacter.isCoprime_of_count_eq_zero μ.conductor_ne_bot hI0 fun v hv ↦ by`. Rewrite using `[HeckeCharacter.count_idealOfExponents hpos, hS0 v (hS v hv)]`. Establish `hfrac : toFractionalIdeal (ofFinite b') = idealUnit (idealOfExponents n) hI0`.

Rewrite using `[toFractionalIdeal_eq_iff]`. Introduce `v`. Rewrite using `[hord]`. Conclude with `(HeckeCharacter.count_idealOfExponents hpos v).symm`. Establish `hmem : ofFinite b' ∈ primeToLevel μ.conductor`.

Use `mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← finiteComponent_toFinite, toFinite_ofFinite, hb', finiteComponent_awayPart, if_pos (hS v hv)]`. Conclude with `one_mem _`. Establish `hchar : μ.coeff (idealOfExponents n) = μ.toIdele (ofFinite b')`. Rewrite using `[μ.coeff_of_mem ⟨hI0, hIc⟩]`.

Conclude with `congrArg (fun w : Circle ↦ (w : ℂ)) (μ.idealCharacter_apply hmem _ hfrac)`. Establish `hmod` using `HeckeCharacter.finiteModule_ofFinite_eq hpos'`. Rewrite `hmod` using `[hfin]`. Rewrite using `[hmod, hchar]`. Establish `harg : ((Ideal.absNorm (idealOfExponents n) : ℝ) : ℂ).arg ≠ Real.pi`.

Rewrite using `[Complex.ofReal_natCast, Complex.natCast_arg]`. Conclude with `Real.pi_pos.ne`. Rewrite using `[Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]`. Establish `hT : ¬ ((∀ v, 0 ≤ n v) ∧ ∀ v ∈ S, n v = 0)`. Introduce and unpack `⟨hpos, hS0⟩`.

Use `hA ⟨fun v hv ↦ (mem_units_iff_ord_eq_zero b v).2 (by rw [← hn]; exact hS0 v hv), fun v _ ↦ (mem_integers_iff_ord_nonneg b v).2 (by rw [← hn]; exact hpos v)⟩` and prove the remaining obligations. Rewrite using `[awayOrderTerm, if_neg hT]`. Distinguish the cases in `h1 : ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units`. Establish `h2 : (b : FiniteAdeleRing (𝓞 K) K) ∉ awayIntegral S` using `fun h2 ↦ hA ⟨h1, h2⟩`. Rewrite using `[awayFactor, if_neg h2]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h1, zero_mul]`.
-/
theorem indicator_mul_awayFactor_eq (μ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v, v.asIdeal ∣ μ.conductor → v ∈ S) (z : ℂ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units
      then (1 : ℂ) else 0) * awayFactor μ S z b =
      awayOrderTerm μ S z (ordFinsupp K (ofFinite b)) := by
  set n := ordFinsupp K (ofFinite b) with hn_def
  have hn : ∀ v, n v = ord v (ofFinite b) := fun v ↦ rfl
  by_cases hA : (∀ v ∈ S, finiteComponent v b ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units) ∧
      (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S
  · have hS0 : ∀ v ∈ S, n v = 0 := fun v hv ↦ by
      rw [hn]; exact (mem_units_iff_ord_eq_zero b v).1 (hA.1 v hv)
    have hpos : ∀ v, 0 ≤ n v := fun v ↦ by
      by_cases hv : v ∈ S
      · rw [hS0 v hv]
      · rw [hn]; exact (mem_integers_iff_ord_nonneg b v).1 (hA.2 v hv)
    rw [if_pos hA.1, awayFactor, if_pos hA.2, one_mul, one_mul, awayOrderTerm,
      if_pos ⟨hpos, hS0⟩]
    set b' := awayPart S b with hb'
    have hord : ∀ v, ord v (ofFinite b') = n v := by
      intro v
      rw [hb', ord_ofFinite_awayPart]
      split_ifs with hv
      · exact (hS0 v hv).symm
      · rfl
    have hfin : ordFinsupp K (ofFinite b') = n := Finsupp.ext hord
    have hpos' : ∀ v, 0 ≤ ord v (ofFinite b') := fun v ↦ by rw [hord]; exact hpos v
    have hI0 := HeckeCharacter.idealOfExponents_ne_bot hpos
    have hIc : IsCoprime (idealOfExponents n) μ.conductor :=
      HeckeCharacter.isCoprime_of_count_eq_zero μ.conductor_ne_bot hI0 fun v hv ↦ by
        rw [HeckeCharacter.count_idealOfExponents hpos, hS0 v (hS v hv)]
    have hfrac : toFractionalIdeal (ofFinite b') = idealUnit (idealOfExponents n) hI0 := by
      rw [toFractionalIdeal_eq_iff]
      intro v
      rw [hord]
      exact (HeckeCharacter.count_idealOfExponents hpos v).symm
    have hmem : ofFinite b' ∈ primeToLevel μ.conductor := by
      refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
      rw [← finiteComponent_toFinite, toFinite_ofFinite, hb', finiteComponent_awayPart,
        if_pos (hS v hv)]
      exact one_mem _
    have hchar : μ.coeff (idealOfExponents n) = μ.toIdele (ofFinite b') := by
      rw [μ.coeff_of_mem ⟨hI0, hIc⟩]
      exact congrArg (fun w : Circle ↦ (w : ℂ)) (μ.idealCharacter_apply hmem _ hfrac)
    have hmod := HeckeCharacter.finiteModule_ofFinite_eq hpos'
    rw [hfin] at hmod
    rw [hmod, hchar]
    have harg : ((Ideal.absNorm (idealOfExponents n) : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.ofReal_natCast, Complex.natCast_arg]
      exact Real.pi_pos.ne
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]
  · have hT : ¬ ((∀ v, 0 ≤ n v) ∧ ∀ v ∈ S, n v = 0) := by
      rintro ⟨hpos, hS0⟩
      refine hA ⟨fun v hv ↦ (mem_units_iff_ord_eq_zero b v).2 (by rw [← hn]; exact hS0 v hv),
        fun v _ ↦ (mem_integers_iff_ord_nonneg b v).2 (by rw [← hn]; exact hpos v)⟩
    rw [awayOrderTerm, if_neg hT]
    by_cases h1 : ∀ v ∈ S, finiteComponent v b ∈
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units
    · have h2 : (b : FiniteAdeleRing (𝓞 K) K) ∉ awayIntegral S := fun h2 ↦ hA ⟨h1, h2⟩
      rw [awayFactor, if_neg h2]
      simp
    · rw [if_neg h1, zero_mul]

/- English proof (translation)
Establish `hI0` using `HeckeCharacter.idealOfExponents_ne_bot hn`. Establish `hc` using `count_coeIdeal_eq_multiplicity (K := K) v hI0`. Rewrite `hc` using `[HeckeCharacter.count_idealOfExponents hn]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `multiplicity_pos_of_dvd h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `dvd_of_multiplicity_pos ?_` and prove the remaining obligations. Use `hn v` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem asIdeal_dvd_idealOfExponents_iff {n : HeightOneSpectrum (𝓞 K) →₀ ℤ} (hn : ∀ v, 0 ≤ n v)
    (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal ∣ idealOfExponents n ↔ n v ≠ 0 := by
  have hI0 := HeckeCharacter.idealOfExponents_ne_bot hn
  have hc := count_coeIdeal_eq_multiplicity (K := K) v hI0
  rw [HeckeCharacter.count_idealOfExponents hn] at hc
  constructor
  · intro h
    have := multiplicity_pos_of_dvd h
    omega
  · intro h
    refine dvd_of_multiplicity_pos ?_
    have := hn v
    omega

/- English proof (translation)
Use `set T := {n : HeightOneSpectrum (𝓞 K) →₀ ℤ | ∀ v, 0 ≤ n v}`. Establish `hinj : Function.Injective fun n : T ↦ idealOfExponents (n : HeightOneSpectrum (𝓞 K) →₀ ℤ)` using `fun n m h ↦ Subtype.ext (idealOfExponents_injOn n.2 m.2 h)`. Establish `h1` using `hasSum_partialLFunction χ S hz`. Rewrite `h1` using `[← hinj.hasSum_iff]`. Rewrite using `[← hasSum_subtype_iff_of_support_subset (s := T)]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Establish `hn : ∀ v, 0 ≤ (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v` using `n.2`. Simplify using `only [Function.comp_apply, awayOrderTerm]`. Establish `hiff : (∀ v ∈ S, ¬ v.asIdeal ∣ idealOfExponents (n : HeightOneSpectrum (𝓞 K) →₀ ℤ)) ↔ ∀ v ∈ S, (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v = 0`.

Use `forall₂_congr fun v _ ↦ ?_` and prove the remaining obligations. Rewrite using `[asIdeal_dvd_idealOfExponents_iff hn, not_not]`. Distinguish the cases in `hS : ∀ v ∈ S, (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v = 0`. Rewrite using `[if_pos ⟨hn, hS⟩, if_pos (hiff.2 hS)]`. Rewrite using `[if_neg (fun h ↦ hS h.2), if_neg (fun h ↦ hS (hiff.1 h)), zero_mul]`.

Introduce `n hn`. Assume the negation of the conclusion as `h`. Conclude with `hn (by simp only [awayOrderTerm]; rw [if_neg (fun h' ↦ h h'.1)])`. Introduce `I hI`. Distinguish the cases in `h0 : I = ⊥`.

Rewrite using `[h0, χ.coeff_bot]`. Simplify using the standard rewrite rules. Take `⟨n, hn0, hn⟩` from `HeckeCharacter.exists_idealOfExponents_eq h0`. Conclude with `absurd ⟨⟨n, hn0⟩, hn⟩ hI`.
-/
theorem hasSum_awayOrderTerm (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {z : ℂ} (hz : 1 < z.re) : HasSum (awayOrderTerm χ S z) (partialLFunction χ S z) := by
  set T := {n : HeightOneSpectrum (𝓞 K) →₀ ℤ | ∀ v, 0 ≤ n v}
  have hinj : Function.Injective fun n : T ↦ idealOfExponents (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
    fun n m h ↦ Subtype.ext (idealOfExponents_injOn n.2 m.2 h)
  have h1 := hasSum_partialLFunction χ S hz
  rw [← hinj.hasSum_iff] at h1
  · rw [← hasSum_subtype_iff_of_support_subset (s := T)]
    · convert h1 using 1
      funext n
      have hn : ∀ v, 0 ≤ (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v := n.2
      simp only [Function.comp_apply, awayOrderTerm]
      have hiff : (∀ v ∈ S, ¬ v.asIdeal ∣ idealOfExponents (n : HeightOneSpectrum (𝓞 K) →₀ ℤ)) ↔
          ∀ v ∈ S, (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v = 0 := by
        refine forall₂_congr fun v _ ↦ ?_
        rw [asIdeal_dvd_idealOfExponents_iff hn, not_not]
      by_cases hS : ∀ v ∈ S, (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v = 0
      · rw [if_pos ⟨hn, hS⟩, if_pos (hiff.2 hS)]
      · rw [if_neg (fun h ↦ hS h.2), if_neg (fun h ↦ hS (hiff.1 h)), zero_mul]
    · intro n hn
      by_contra h
      exact hn (by simp only [awayOrderTerm]; rw [if_neg (fun h' ↦ h h'.1)])
  · intro I hI
    by_cases h0 : I = ⊥
    · rw [h0, χ.coeff_bot]
      simp
    · obtain ⟨n, hn0, hn⟩ := HeckeCharacter.exists_idealOfExponents_eq h0
      exact absurd ⟨⟨n, hn0⟩, hn⟩ hI

/- English proof (translation)
Use `set H : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun b ↦ (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units then (1 : ℂ) else 0) * awayFactor μ S z b with hH`. Establish `hHT : ∀ b, H b = awayOrderTerm μ S z (ordFinsupp K (ofFinite b))` using `fun b ↦ indicator_mul_awayFactor_eq μ S hS z b`. Establish `hinv : ∀ x, ∀ w ∈ finiteIntegralUnits K, H (x * w) = H x` using `fun x w hw ↦ by`. Rewrite using `[hHT, hHT, ordFinsupp_ofFinite_mul x hw]`. Establish `hcont : Continuous H` using `continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits K) hinv`.

Establish `hint : Integrable H (finiteIdeleMeasure K)`. Establish `hn` using `integrable_norm_finIntegrand (integralInd2_mem (K := K)) 1 hz`. Use `hn.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun b ↦ ?_)` and prove the remaining obligations. Rewrite using `[hHT, awayOrderTerm]`. Use `split_ifs with hT`.

Take `⟨hpos, -⟩` from `hT`. Establish `hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ integralFiniteAdeles (𝓞 K) K` using `mem_integralFiniteAdeles.2 fun v ↦ (mem_integers_iff_ord_nonneg b v).2 (hpos v)`. Establish `h1 : integralInd2 K (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ* ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _)) = 1`. Rewrite using `[integralInd2_vecMul (one_mem _), integralInd_apply, if_pos hb]`. Rewrite using `[h1, norm_one, one_mul, finMod_eq, HeckeCharacter.finiteModule_ofFinite_eq hpos, norm_mul]`.

Establish `hN : (0 : ℝ) < Ideal.absNorm (idealOfExponents (ordFinsupp K (ofFinite b)))`. Use `HeckeCharacter.idealOfExponents_ne_bot (K := K) hpos` as an intermediate fact. Conclude with `Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ this (Ideal.absNorm_eq_zero_iff.1 h))`. Rewrite using `[Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hN), Complex.neg_re, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_zero]`. Conclude with `mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (finMod_pos b).le _)`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Establish `hsum` using `hasSum_integral_finiteIdeleMeasure_of_invariant hint hinv`. Establish `hL : HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦ H c.out) (partialLFunction μ S z)`.

Repeatedly rewrite using `[hHT]`. Establish `h` using `hasSum_awayOrderTerm μ S hz`. Rewrite `h` using `[← ordFinsupp_ofFinite_out_injective.hasSum_iff]`. Conclude with `h`. Introduce `n hn`.

Take `⟨b, hb⟩` from `HeckeCharacter.exists_ordFinsupp_eq n`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul (finiteIntegralUnits K) b`. Use `absurd ⟨(b : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K), ?_⟩ hn` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ordFinsupp K (ofFinite (QuotientGroup.mk b : _ ⧸ finiteIntegralUnits K).out) = n`. Rewrite using `[hw, ordFinsupp_ofFinite_mul b w.2, hb]`.

Conclude with `hsum.unique hL`.
-/
theorem integral_indicator_mul_awayFactor (μ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, v.asIdeal ∣ μ.conductor → v ∈ S) {z : ℂ}
    (hz : 1 < z.re) :
    Integrable (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units
        then (1 : ℂ) else 0) * awayFactor μ S z b) (finiteIdeleMeasure K) ∧
    ∫ b, (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units
        then (1 : ℂ) else 0) * awayFactor μ S z b ∂finiteIdeleMeasure K =
      partialLFunction μ S z := by
  set H : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun b ↦
    (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units
      then (1 : ℂ) else 0) * awayFactor μ S z b with hH
  have hHT : ∀ b, H b = awayOrderTerm μ S z (ordFinsupp K (ofFinite b)) := fun b ↦
    indicator_mul_awayFactor_eq μ S hS z b
  have hinv : ∀ x, ∀ w ∈ finiteIntegralUnits K, H (x * w) = H x := fun x w hw ↦ by
    rw [hHT, hHT, ordFinsupp_ofFinite_mul x hw]
  have hcont : Continuous H := continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits K) hinv
  have hint : Integrable H (finiteIdeleMeasure K) := by
    have hn := integrable_norm_finIntegrand (integralInd2_mem (K := K)) 1 hz
    refine hn.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun b ↦ ?_)
    rw [hHT, awayOrderTerm]
    split_ifs with hT
    · obtain ⟨hpos, -⟩ := hT
      have hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ integralFiniteAdeles (𝓞 K) K :=
        mem_integralFiniteAdeles.2 fun v ↦ (mem_integers_iff_ord_nonneg b v).2 (hpos v)
      have h1 : integralInd2 K (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
          ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _)) = 1 := by
        rw [integralInd2_vecMul (one_mem _), integralInd_apply, if_pos hb]
      rw [h1, norm_one, one_mul, finMod_eq, HeckeCharacter.finiteModule_ofFinite_eq hpos, norm_mul]
      have hN : (0 : ℝ) < Ideal.absNorm (idealOfExponents (ordFinsupp K (ofFinite b))) := by
        have := HeckeCharacter.idealOfExponents_ne_bot (K := K) hpos
        exact Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ this (Ideal.absNorm_eq_zero_iff.1 h))
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hN), Complex.neg_re,
        Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]
      calc ‖μ.coeff _‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (μ.norm_coeff_le _) (by positivity)
        _ = _ := one_mul _
    · rw [norm_zero]
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (finMod_pos b).le _)
  refine ⟨hint, ?_⟩
  have hsum := hasSum_integral_finiteIdeleMeasure_of_invariant hint hinv
  have hL : HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦ H c.out)
      (partialLFunction μ S z) := by
    simp_rw [hHT]
    have h := hasSum_awayOrderTerm μ S hz
    rw [← ordFinsupp_ofFinite_out_injective.hasSum_iff] at h
    · exact h
    · intro n hn
      obtain ⟨b, hb⟩ := HeckeCharacter.exists_ordFinsupp_eq n
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (finiteIntegralUnits K) b
      refine absurd ⟨(b : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K), ?_⟩ hn
      change ordFinsupp K (ofFinite (QuotientGroup.mk b : _ ⧸ finiteIntegralUnits K).out) = n
      rw [hw, ordFinsupp_ofFinite_mul b w.2, hb]
  exact hsum.unique hL

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem vecAt_zero_cons (v : HeightOneSpectrum (𝓞 K)) (t : FiniteAdeleRing (𝓞 K) K) :
    vecAt v ![0, t] = ![0, t v] := by
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Establish `hv : ∀ (x : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R), (x ᵥ* A) = fun j ↦ x 0 * A 0 j + x 1 * A 1 j` using `fun x A ↦ by`. Use extensionality with `j`. Simplify using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `he : ![0, t] ᵥ* (k : Matrix (Fin 2) (Fin 2) R) ᵥ* ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![0, t]`. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Establish `h1` using `congrFun he 1`. Rewrite `h1` using `[hv]`. Simplify using `only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1`.

Rewrite using `[← h1]`. Conclude with `add_mem (mul_mem (h 0) (hk' 0 1)) (mul_mem (h 1) (hk' 1 1))`. Introduce `ht j`. Rewrite using `[hv]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]`.

Conclude with `mul_mem ht (hk 1 j)`.
-/
theorem vecMul_zero_cons_mem_subring_iff {R : Type*} [CommRing R] (O : Subring R)
    {k : GL (Fin 2) R} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) R) i j ∈ O)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j ∈ O) (t : R) :
    (∀ j, (![0, t] ᵥ* (k : Matrix (Fin 2) (Fin 2) R)) j ∈ O) ↔ t ∈ O := by
  have hv : ∀ (x : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R),
      (x ᵥ* A) = fun j ↦ x 0 * A 0 j + x 1 * A 1 j := fun x A ↦ by
    ext j; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have he : ![0, t] ᵥ* (k : Matrix (Fin 2) (Fin 2) R) ᵥ*
        ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![0, t] := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have h1 := congrFun he 1
    rw [hv] at h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    rw [← h1]
    exact add_mem (mul_mem (h 0) (hk' 0 1)) (mul_mem (h 1) (hk' 1 1))
  · intro ht j
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
    exact mul_mem ht (hk 1 j)

/- English proof (translation)
Establish `hkey : ∀ v ∉ S, (∀ i, (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) i v ∈ v.adicCompletionIntegers K) ↔ b v ∈ v.adicCompletionIntegers K`. Introduce `v hv`. Take `⟨h1, h2⟩` from `(GLnLocal.mem_integralGL_iff _ _).1 (hg v hv)`. Establish `key` using `vecMul_zero_cons_mem_subring_iff (v.adicCompletionIntegers K).toSubring (k := glAt v g) (fun i j ↦ (mem_valuationInteger_iff v _).1 (h1 i j)) (fun i j ↦ (mem_valuationInteger_iff v _).1 (h2 i j)) (b v)`. Establish `he : ∀ i, (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) i v = (![0, b v] ᵥ* (glAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) i` using `fun i ↦ by`.

Rewrite using `[← vecAt_zero_cons, ← vecAt_vecMul]`. Both sides reduce to the same expression. Simplify using `only [he]`. Conclude with `key`. Express the relevant statement in the definitionally equal form `(∀ i, ∀ v ∉ S, _) ↔ ∀ v ∉ S, _`.

Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Conclude with `(hkey v hv).1 fun i ↦ h i v hv`. Introduce `h i v hv`. Conclude with `(hkey v hv).2 (h v hv) i`.
-/
theorem vecMul_mem_awayBox_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : ∀ v ∉ S, glAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) 2)
    (b : FiniteAdeleRing (𝓞 K) K) :
    ![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ awayBox S ↔
      b ∈ awayIntegral S := by
  have hkey : ∀ v ∉ S, (∀ i, (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) i v ∈
      v.adicCompletionIntegers K) ↔ b v ∈ v.adicCompletionIntegers K := by
    intro v hv
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (hg v hv)
    have key := vecMul_zero_cons_mem_subring_iff (v.adicCompletionIntegers K).toSubring
      (k := glAt v g) (fun i j ↦ (mem_valuationInteger_iff v _).1 (h1 i j))
      (fun i j ↦ (mem_valuationInteger_iff v _).1 (h2 i j)) (b v)
    have he : ∀ i, (![0, b] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) i v =
        (![0, b v] ᵥ* (glAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) i := fun i ↦ by
      rw [← vecAt_zero_cons, ← vecAt_vecMul]
      rfl
    simp only [he]
    exact key
  change (∀ i, ∀ v ∉ S, _) ↔ ∀ v ∉ S, _
  constructor
  · intro h v hv
    exact (hkey v hv).1 fun i ↦ h i v hv
  · intro h i v hv
    exact (hkey v hv).2 (h v hv) i

/- English proof (translation)
Use `set μ := χ₁ * χ₂⁻¹ with hμ`. Distinguish the cases in `hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S`. Establish `hx` using `(vecMul_mem_awayBox_iff S hg (b : FiniteAdeleRing (𝓞 K) K)).2 hb`. Rewrite using `[restrictedTensor2, Set.indicator_of_mem hx, awayFactor, if_pos hb, one_mul]`. Establish `hΨ : ∀ v : S, Ψ v (vecAt v.1 (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) = GodementSectionLocal.slice (Ψ v) (glAt v.1 g) ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)` using `fun v ↦ by`.

Rewrite using `[vecAt_vecMul, vecAt_zero_cons]`. Both sides reduce to the same expression. Establish `hchar : (finChar μ b : ℂ) = (∏ v ∈ S, (μ.localComponent v (finiteComponent v b) : ℂ)) * (μ.toIdele (ofFinite (awayPart S b)) : ℂ)`. Express the relevant statement in the definitionally equal form `(μ.toIdele (ofFinite b) : ℂ) = _`. Use `conv_lhs => rw [← partAt_mul_awayPart S b]`.

Rewrite using `[map_mul, map_mul, Circle.coe_mul, toIdele_ofFinite_partAt]`. Establish `hmod : ((finMod b : ℝ) : ℂ) ^ (2 * s) = (∏ v ∈ S, ((‖((finiteComponent v b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) : ℂ) ^ (2 * s)) * ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ (2 * s)`. Rewrite using `[finMod_eq]`. Use `conv_lhs => rw [← partAt_mul_awayPart S b]`. Rewrite using `[map_mul, finiteModule_mul, finiteModule_ofFinite_partAt, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun v _ ↦ norm_nonneg _) (finiteModule_pos _).le, ofReal_prod_cpow S _ (fun v ↦ norm_nonneg _)]`.

Establish `hloc : ∀ v : S, (((localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) (finiteComponent v.1 b) : ℂˣ) : ℂ) = (μ.localComponent v.1 (finiteComponent v.1 b) : ℂ)` using `fun v ↦ by`. Rewrite using `[← localChar_mul_inv, coe_localChar]`. Establish `hnorm : ∀ v : S, ((LocalField.modulus ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) : ℝ) : ℂ) ^ (2 * s) = ((‖((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)‖ : ℝ) : ℂ) ^ (2 * s)` using `fun v ↦ by`. Rewrite using `[modulus_adicCompletion]`. Simplify using `only [hΨ, hloc, hnorm]`.

Rewrite using `[hchar, hmod, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_coe_sort S (fun v ↦ (μ.localComponent v (finiteComponent v b) : ℂ)), Finset.prod_coe_sort S (fun v ↦ ((‖((finiteComponent v b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) : ℂ) ^ (2 * s))]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : ![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∉ awayBox S` using `fun h ↦ hb ((vecMul_mem_awayBox_iff S hg _).1 h)`. Rewrite using `[restrictedTensor2, Set.indicator_of_notMem hx, awayFactor, if_neg hb]`. Simplify using the standard rewrite rules.
-/
theorem finIntegrand_restrictedTensor2 (χ₁ χ₂ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : ∀ v : S, (Fin 2 → v.1.adicCompletion K) → ℂ)
    {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : ∀ v ∉ S, glAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) 2) (s : ℂ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    restrictedTensor2 S Ψ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) *
        (finChar (χ₁ * χ₂⁻¹) b : ℂ) * ((finMod b : ℝ) : ℂ) ^ (2 * s) =
      (∏ v : S, GodementSectionLocal.slice (Ψ v) (glAt v.1 g)
          ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) *
        (((localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) (finiteComponent v.1 b) : ℂˣ) : ℂ) *
        ((LocalField.modulus ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) :
          v.1.adicCompletion K) : ℝ) : ℂ) ^ (2 * s)) *
        awayFactor (χ₁ * χ₂⁻¹) S (2 * s) b := by
  set μ := χ₁ * χ₂⁻¹ with hμ
  by_cases hb : (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S
  · have hx := (vecMul_mem_awayBox_iff S hg (b : FiniteAdeleRing (𝓞 K) K)).2 hb
    rw [restrictedTensor2, Set.indicator_of_mem hx, awayFactor, if_pos hb, one_mul]
    have hΨ : ∀ v : S, Ψ v (vecAt v.1 (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) =
        GodementSectionLocal.slice (Ψ v) (glAt v.1 g)
          ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) := fun v ↦ by
      rw [vecAt_vecMul, vecAt_zero_cons]
      rfl
    have hchar : (finChar μ b : ℂ) =
        (∏ v ∈ S, (μ.localComponent v (finiteComponent v b) : ℂ)) *
          (μ.toIdele (ofFinite (awayPart S b)) : ℂ) := by
      change (μ.toIdele (ofFinite b) : ℂ) = _
      conv_lhs => rw [← partAt_mul_awayPart S b]
      rw [map_mul, map_mul, Circle.coe_mul, toIdele_ofFinite_partAt]
    have hmod : ((finMod b : ℝ) : ℂ) ^ (2 * s) =
        (∏ v ∈ S, ((‖((finiteComponent v b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) :
          ℂ) ^ (2 * s)) * ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ (2 * s) := by
      rw [finMod_eq]
      conv_lhs => rw [← partAt_mul_awayPart S b]
      rw [map_mul, finiteModule_mul, finiteModule_ofFinite_partAt, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun v _ ↦ norm_nonneg _)
          (finiteModule_pos _).le,
        ofReal_prod_cpow S _ (fun v ↦ norm_nonneg _)]
    have hloc : ∀ v : S, (((localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) (finiteComponent v.1 b) : ℂˣ) :
        ℂ) = (μ.localComponent v.1 (finiteComponent v.1 b) : ℂ) := fun v ↦ by
      rw [← localChar_mul_inv, coe_localChar]
    have hnorm : ∀ v : S, ((LocalField.modulus ((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) :
        v.1.adicCompletion K) : ℝ) : ℂ) ^ (2 * s) =
        ((‖((finiteComponent v.1 b : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)‖ : ℝ) : ℂ) ^
          (2 * s) := fun v ↦ by
      rw [modulus_adicCompletion]
    simp only [hΨ, hloc, hnorm]
    rw [hchar, hmod, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_coe_sort S (fun v ↦ (μ.localComponent v (finiteComponent v b) : ℂ)),
      Finset.prod_coe_sort S (fun v ↦ ((‖((finiteComponent v b : (v.adicCompletion K)ˣ) :
        v.adicCompletion K)‖ : ℝ) : ℂ) ^ (2 * s))]
    ring
  · have hx : ![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∉ awayBox S :=
      fun h ↦ hb ((vecMul_mem_awayBox_iff S hg _).1 h)
    rw [restrictedTensor2, Set.indicator_of_notMem hx, awayFactor, if_neg hb]
    simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_finiteComponent, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← adeleAt_apply, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem finiteComponent_det (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    finiteComponent v (Matrix.GeneralLinearGroup.det g) =
      Matrix.GeneralLinearGroup.det (glAt v g) := by
  apply Units.ext
  rw [coe_finiteComponent, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, ← adeleAt_apply, RingHom.map_det]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GLnLocal.mem_integralGL_iff _ _).1 hk`. Establish `h1' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K` using `fun i j ↦ (mem_valuationInteger_iff v _).1 (h1 i j)`. Establish `h2' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) i j ∈ v.adicCompletionIntegers K` using `fun i j ↦ (mem_valuationInteger_iff v _).1 (h2 i j)`. Rewrite using `[Submonoid.mem_units_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Conclude with `sub_mem (mul_mem (h1' 0 0) (h1' 1 1)) (mul_mem (h1' 0 1) (h1' 1 0))`. Express the relevant statement in the definitionally equal form `(((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K`. Rewrite using `[← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`.

Conclude with `sub_mem (mul_mem (h2' 0 0) (h2' 1 1)) (mul_mem (h2' 0 1) (h2' 1 0))`.
-/
theorem det_mem_units_of_mem_integralGL {v : HeightOneSpectrum (𝓞 K)}
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) 2) :
    Matrix.GeneralLinearGroup.det k ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hk
  have h1' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈
      v.adicCompletionIntegers K := fun i j ↦ (mem_valuationInteger_iff v _).1 (h1 i j)
  have h2' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) i j ∈
      v.adicCompletionIntegers K := fun i j ↦ (mem_valuationInteger_iff v _).1 (h2 i j)
  rw [Submonoid.mem_units_iff]
  refine ⟨?_, ?_⟩
  · change ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      v.adicCompletionIntegers K
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1' 0 0) (h1' 1 1)) (mul_mem (h1' 0 1) (h1' 1 0))
  · change (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      v.adicCompletionIntegers K
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2' 0 0) (h2' 1 1)) (mul_mem (h2' 0 1) (h2' 1 0))

/- English proof (translation)
Establish `hc : ∀ v, finiteComponent v (awayPart S (Matrix.GeneralLinearGroup.det g)) ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units`. Introduce `v`. Rewrite using `[finiteComponent_awayPart]`. Use `split_ifs with hv`. Conclude with `one_mem _`.

Rewrite using `[finiteComponent_det]`. Conclude with `det_mem_units_of_mem_integralGL (hg v hv)`. Use `(mem_finiteIntegralUnits K).2 fun v ↦ ?_` and prove the remaining obligations. Establish `h` using `(Submonoid.mem_units_iff _ _).1 (hc v)`. Establish `h2 : ((finiteComponent v (awayPart S (Matrix.GeneralLinearGroup.det g))⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K` using `h.2`.

Conclude with `⟨h.1, h2⟩`.
-/
theorem awayPart_det_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : ∀ v ∉ S, glAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) 2) :
    awayPart S (Matrix.GeneralLinearGroup.det g) ∈ finiteIntegralUnits K := by
  have hc : ∀ v, finiteComponent v (awayPart S (Matrix.GeneralLinearGroup.det g)) ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    intro v
    rw [finiteComponent_awayPart]
    split_ifs with hv
    · exact one_mem _
    · rw [finiteComponent_det]
      exact det_mem_units_of_mem_integralGL (hg v hv)
  refine (mem_finiteIntegralUnits K).2 fun v ↦ ?_
  have h := (Submonoid.mem_units_iff _ _).1 (hc v)
  have h2 : ((finiteComponent v (awayPart S (Matrix.GeneralLinearGroup.det g))⁻¹ :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := h.2
  exact ⟨h.1, h2⟩

/- English proof (translation)
Use `set d := Matrix.GeneralLinearGroup.det g with hd`. Establish `hunit` using `awayPart_det_mem S hg`. Establish `hker : χ₁.toIdele (ofFinite (awayPart S d)) = 1`. Establish `hmem : awayPart S d ∈ idealLevel χ₁.conductor`. Use `mem_finiteLevel.2 fun v ↦ ?_` and prove the remaining obligations.

Rewrite using `[finiteComponent_awayPart]`. Use `split_ifs with hv`. Conclude with `one_mem _`. Establish `hndvd : ¬ v.asIdeal ∣ χ₁.conductor` using `fun h ↦ hv (hχ₁ v h)`. Rewrite using `[multiplicity_eq_zero.2 hndvd, unitsLevel_zero, hd, finiteComponent_det]`.

Conclude with `det_mem_units_of_mem_integralGL (hg v hv)`. Conclude with `χ₁.map_idealLevel_conductor_le_ker ⟨_, hmem, rfl⟩`. Establish `hchar : (finChar χ₁ d : ℂ) = ∏ v ∈ S, (χ₁.localComponent v (finiteComponent v d) : ℂ)`. Express the relevant statement in the definitionally equal form `(χ₁.toIdele (ofFinite d) : ℂ) = _`. Use `conv_lhs => rw [← partAt_mul_awayPart S d]`.

Rewrite using `[map_mul, map_mul, hker, mul_one, toIdele_ofFinite_partAt]`. Establish `hmod : ((finMod d : ℝ) : ℂ) ^ s = ∏ v ∈ S, ((‖((finiteComponent v d : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s`. Rewrite using `[finMod_eq]`. Use `conv_lhs => rw [← partAt_mul_awayPart S d]`. Rewrite using `[map_mul, finiteModule_mul, finiteModule_eq_one_of_mem (show ofFinite (awayPart S d) ∈ standardOpenSubgroup K from hunit), mul_one, finiteModule_ofFinite_partAt, ofReal_prod_cpow S _ (fun v ↦ norm_nonneg _)]`.

Rewrite using `[hchar, hmod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations. Rewrite using `[GodementSectionLocal.modPow, modulus_adicCompletion, coe_localChar, finiteComponent_det]`.
-/
theorem finChar_det_mul_finMod_det (χ₁ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hχ₁ : ∀ v, v.asIdeal ∣ χ₁.conductor → v ∈ S) {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : ∀ v ∉ S, glAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) 2) (s : ℂ) :
    (finChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((finMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      ∏ v ∈ S, ((localChar χ₁ v (Matrix.GeneralLinearGroup.det (glAt v g)) : ℂˣ) : ℂ) *
        GodementSectionLocal.modPow
          ((Matrix.GeneralLinearGroup.det (glAt v g) : (v.adicCompletion K)ˣ) : v.adicCompletion K) s := by
  set d := Matrix.GeneralLinearGroup.det g with hd
  have hunit := awayPart_det_mem S hg
  have hker : χ₁.toIdele (ofFinite (awayPart S d)) = 1 := by
    have hmem : awayPart S d ∈ idealLevel χ₁.conductor := by
      refine mem_finiteLevel.2 fun v ↦ ?_
      rw [finiteComponent_awayPart]
      split_ifs with hv
      · exact one_mem _
      · have hndvd : ¬ v.asIdeal ∣ χ₁.conductor := fun h ↦ hv (hχ₁ v h)
        rw [multiplicity_eq_zero.2 hndvd, unitsLevel_zero, hd, finiteComponent_det]
        exact det_mem_units_of_mem_integralGL (hg v hv)
    exact χ₁.map_idealLevel_conductor_le_ker ⟨_, hmem, rfl⟩
  have hchar : (finChar χ₁ d : ℂ) = ∏ v ∈ S, (χ₁.localComponent v (finiteComponent v d) : ℂ) := by
    change (χ₁.toIdele (ofFinite d) : ℂ) = _
    conv_lhs => rw [← partAt_mul_awayPart S d]
    rw [map_mul, map_mul, hker, mul_one, toIdele_ofFinite_partAt]
  have hmod : ((finMod d : ℝ) : ℂ) ^ s = ∏ v ∈ S,
      ((‖((finiteComponent v d : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
    rw [finMod_eq]
    conv_lhs => rw [← partAt_mul_awayPart S d]
    rw [map_mul, finiteModule_mul,
      finiteModule_eq_one_of_mem (show ofFinite (awayPart S d) ∈ standardOpenSubgroup K from hunit),
      mul_one,
      finiteModule_ofFinite_partAt, ofReal_prod_cpow S _ (fun v ↦ norm_nonneg _)]
  rw [hchar, hmod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [GodementSectionLocal.modPow, modulus_adicCompletion, coe_localChar, finiteComponent_det]

/- English proof (translation)
Assume the negation of the conclusion as `hvS`. Use `((HeckeCharacter.not_dvd_conductor_iff _ v).2 ?_) hv` and prove the remaining obligations. Introduce `a ha`. Establish `h1` using `(χ₁.not_dvd_conductor_iff v).1 (fun h ↦ hvS (hχ₁ v h)) ha`. Establish `h2` using `(χ₂.not_dvd_conductor_iff v).1 (fun h ↦ hvS (hχ₂ v h)) ha`.

Rewrite `h1`, `h2`, the goal using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `χ₁.toIdele (finiteEmbedding v a) * (χ₂.toIdele (finiteEmbedding v a))⁻¹ = 1`. Express the relevant statement in the definitionally equal form `χ₁.toIdele (finiteEmbedding v a) = 1 at h1`. Express the relevant statement in the definitionally equal form `χ₂.toIdele (finiteEmbedding v a) = 1 at h2`. Rewrite using `[h1, h2, inv_one, mul_one]`.
-/
theorem conductor_mul_inv_primes (χ₁ χ₂ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hχ₁ : ∀ v, v.asIdeal ∣ χ₁.conductor → v ∈ S) (hχ₂ : ∀ v, v.asIdeal ∣ χ₂.conductor → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ (χ₁ * χ₂⁻¹).conductor) : v ∈ S := by
  by_contra hvS
  refine ((HeckeCharacter.not_dvd_conductor_iff _ v).2 ?_) hv
  intro a ha
  have h1 := (χ₁.not_dvd_conductor_iff v).1 (fun h ↦ hvS (hχ₁ v h)) ha
  have h2 := (χ₂.not_dvd_conductor_iff v).1 (fun h ↦ hvS (hχ₂ v h)) ha
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  change χ₁.toIdele (finiteEmbedding v a) * (χ₂.toIdele (finiteEmbedding v a))⁻¹ = 1
  change χ₁.toIdele (finiteEmbedding v a) = 1 at h1
  change χ₂.toIdele (finiteEmbedding v a) = 1 at h2
  rw [h1, h2, inv_one, mul_one]

/- English proof (translation)
Rewrite using `[← localChar_mul_inv, LocalField.quasiCharExponent, coe_localChar, Circle.norm_coe, Real.logb_one, neg_zero]`.
-/
theorem quasiCharExponent_localChar_mul_inv (χ₁ χ₂ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    LocalField.quasiCharExponent (localChar χ₁ v * (localChar χ₂ v)⁻¹) = 0 := by
  rw [← localChar_mul_inv, LocalField.quasiCharExponent, coe_localChar, Circle.norm_coe,
    Real.logb_one, neg_zero]

/- English proof (translation)
Establish `hA : MeasurableSet {b : (FiniteAdeleRing (𝓞 K) K)ˣ | (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S}` using `((isOpen_awayIntegral S).preimage Units.continuous_val).measurableSet`. Establish `hc1 : Continuous fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ (μ.toIdele (ofFinite (awayPart S b)) : ℂ)` using `continuous_subtype_val.comp (μ.continuous_toIdele.comp (continuous_ofFinite.comp (continuous_awayPart S)))`. Establish `hc2 : Continuous fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ z`. Establish `h : (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ finiteModule (ofFinite (awayPart S b))) = fun b ↦ finMod (awayPart S b)` using `funext fun b ↦ (finMod_eq _).symm`. Rewrite using `[show (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ z) = fun b ↦ ((finMod (awayPart S b) : ℝ) : ℂ) ^ z from funext fun b ↦ by rw [← finMod_eq]]`.

Conclude with `(Complex.continuous_ofReal.comp (continuous_finMod.comp (continuous_awayPart S))).cpow continuous_const fun b ↦ Complex.ofReal_mem_slitPlane.2 (finMod_pos _)`. Unfold `awayFactor`. Conclude with `((Measurable.ite hA measurable_const measurable_const).mul hc1.measurable).mul hc2.measurable`.
-/
theorem measurable_awayFactor (μ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ) :
    Measurable (awayFactor μ S z) := by
  have hA : MeasurableSet {b : (FiniteAdeleRing (𝓞 K) K)ˣ |
      (b : FiniteAdeleRing (𝓞 K) K) ∈ awayIntegral S} :=
    ((isOpen_awayIntegral S).preimage Units.continuous_val).measurableSet
  have hc1 : Continuous fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      (μ.toIdele (ofFinite (awayPart S b)) : ℂ) :=
    continuous_subtype_val.comp (μ.continuous_toIdele.comp (continuous_ofFinite.comp
      (continuous_awayPart S)))
  have hc2 : Continuous fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ z := by
    have h : (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ finiteModule (ofFinite (awayPart S b))) =
        fun b ↦ finMod (awayPart S b) := funext fun b ↦ (finMod_eq _).symm
    rw [show (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
        ((finiteModule (ofFinite (awayPart S b)) : ℝ) : ℂ) ^ z) =
        fun b ↦ ((finMod (awayPart S b) : ℝ) : ℂ) ^ z from funext fun b ↦ by rw [← finMod_eq]]
    exact (Complex.continuous_ofReal.comp (continuous_finMod.comp (continuous_awayPart S))).cpow
      continuous_const fun b ↦ Complex.ofReal_mem_slitPlane.2 (finMod_pos _)
  unfold awayFactor
  exact ((Measurable.ite hA measurable_const measurable_const).mul hc1.measurable).mul hc2.measurable

/- English proof (translation)
Use `set μ := χ₁ * χ₂⁻¹ with hμ`. Establish `hμS` using `conductor_mul_inv_primes χ₁ χ₂ S hχ₁ hχ₂`. Use `set Fv : ∀ v : S, (v.1.adicCompletion K)ˣ → ℂ := fun v a ↦ GodementSectionLocal.slice (Ψ v) (glAt v.1 g) (a : v.1.adicCompletion K) * (((localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) a : ℂˣ) : ℂ) * ((LocalField.modulus (a : v.1.adicCompletion K) : ℝ) : ℂ) ^ (2 * s) with hFv`. Establish `hFvi : ∀ v, Integrable (Fv v) (LocalField.multHaar (v.1.adicCompletion K))` using `fun v ↦ GodementSectionLocal.integrable_localSectionIntegrand (continuous_localChar χ₁ v.1) (continuous_localChar χ₂ v.1) (by rw [quasiCharExponent_localChar_mul_inv, neg_zero]; linarith) (hΨ v) (glAt v.1 g)`. Take `⟨hint, heq⟩` from `integral_indicator_mul_awayFactor μ S hμS (z := 2 * s) (by simpa using hs)`.

Establish `hind : (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (awayFactor μ S (2 * s)) = fun b ↦ (if ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units then (1 : ℂ) else 0) * awayFactor μ S (2 * s) b`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units`. Establish `hb' : b ∈ finUnitsAt S ⁻¹' intUnitsAtS S` using `fun v _ ↦ hb v.1 v.2`. Rewrite using `[Set.indicator_of_mem hb', if_pos hb, one_mul]`.

Establish `hb' : b ∉ finUnitsAt S ⁻¹' intUnitsAtS S` using `fun h ↦ hb fun v hv ↦ h ⟨v, hv⟩ (Set.mem_univ _)`. Rewrite using `[Set.indicator_of_notMem hb', if_neg hb, zero_mul]`. Take `⟨-, hdec⟩` from `integral_finiteIdele_prod_local_mul S Fv hFvi (measurable_awayFactor μ S (2 * s)) (fun b b' h ↦ awayFactor_eq_of_forall μ S (2 * s) h) (by rw [hind]; exact hint)`. Establish `hintegrand : (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ restrictedTensor2 S Ψ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ* (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) * (finChar μ b : ℂ) * ((finMod b : ℝ) : ℂ) ^ (2 * s)) = fun b ↦ (∏ v : S, Fv v (finUnitAt v.1 b)) * awayFactor …`. Use function extensionality and compare the values at `fun b ↦ finIntegrand_restrictedTensor2 χ₁ χ₂ S Ψ hg s b`.

Establish `hloc : ∀ v : S, ∫ a, Fv v a ∂LocalField.multHaar (v.1.adicCompletion K) = LocalField.localZeta (GodementSectionLocal.slice (Ψ v) (glAt v.1 g)) (localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) (2 * s)` using `fun v ↦ rfl`. Rewrite using `[finSection, hintegrand, hdec, hind, heq, finChar_det_mul_finMod_det χ₁ S hχ₁ hg s, ← Finset.prod_coe_sort S]`. Simplify using `only [hloc, GodementSectionLocal.localSection, GodementSectionLocal.detU, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finSection_restrictedTensor2 (χ₁ χ₂ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {Ψ : ∀ v : S, (Fin 2 → v.1.adicCompletion K) → ℂ}
    (hΨ : ∀ v, Ψ v ∈ GodementSectionLocal.schwartzBruhat2 (v.1.adicCompletion K))
    (hχ₁ : ∀ v, v.asIdeal ∣ χ₁.conductor → v ∈ S) (hχ₂ : ∀ v, v.asIdeal ∣ χ₂.conductor → v ∈ S)
    {s : ℂ} (hs : 1 < 2 * s.re) {g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : ∀ v ∉ S, glAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) 2) :
    finSection χ₁ χ₂ s (restrictedTensor2 S Ψ) g =
      (∏ v : S, GodementSectionLocal.localSection (localChar χ₁ v.1) (localChar χ₂ v.1) s (Ψ v)
        (glAt v.1 g)) * partialLFunction (χ₁ * χ₂⁻¹) S (2 * s) := by
  set μ := χ₁ * χ₂⁻¹ with hμ
  have hμS := conductor_mul_inv_primes χ₁ χ₂ S hχ₁ hχ₂
  set Fv : ∀ v : S, (v.1.adicCompletion K)ˣ → ℂ := fun v a ↦
    GodementSectionLocal.slice (Ψ v) (glAt v.1 g) (a : v.1.adicCompletion K) *
      (((localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) a : ℂˣ) : ℂ) *
      ((LocalField.modulus (a : v.1.adicCompletion K) : ℝ) : ℂ) ^ (2 * s) with hFv
  have hFvi : ∀ v, Integrable (Fv v) (LocalField.multHaar (v.1.adicCompletion K)) := fun v ↦
    GodementSectionLocal.integrable_localSectionIntegrand (continuous_localChar χ₁ v.1)
      (continuous_localChar χ₂ v.1)
      (by rw [quasiCharExponent_localChar_mul_inv, neg_zero]; linarith) (hΨ v) (glAt v.1 g)
  obtain ⟨hint, heq⟩ := integral_indicator_mul_awayFactor μ S hμS (z := 2 * s) (by simpa using hs)
  have hind : (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (awayFactor μ S (2 * s)) =
      fun b ↦ (if ∀ v ∈ S, finiteComponent v b ∈
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units then (1 : ℂ) else 0) *
        awayFactor μ S (2 * s) b := by
    funext b
    by_cases hb : ∀ v ∈ S, finiteComponent v b ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units
    · have hb' : b ∈ finUnitsAt S ⁻¹' intUnitsAtS S := fun v _ ↦ hb v.1 v.2
      rw [Set.indicator_of_mem hb', if_pos hb, one_mul]
    · have hb' : b ∉ finUnitsAt S ⁻¹' intUnitsAtS S := fun h ↦ hb fun v hv ↦ h ⟨v, hv⟩ (Set.mem_univ _)
      rw [Set.indicator_of_notMem hb', if_neg hb, zero_mul]
  obtain ⟨-, hdec⟩ := integral_finiteIdele_prod_local_mul S Fv hFvi (measurable_awayFactor μ S (2 * s))
    (fun b b' h ↦ awayFactor_eq_of_forall μ S (2 * s) h) (by rw [hind]; exact hint)
  have hintegrand : (fun b : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      restrictedTensor2 S Ψ (![0, (b : FiniteAdeleRing (𝓞 K) K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) *
        (finChar μ b : ℂ) * ((finMod b : ℝ) : ℂ) ^ (2 * s)) =
      fun b ↦ (∏ v : S, Fv v (finUnitAt v.1 b)) * awayFactor μ S (2 * s) b :=
    funext fun b ↦ finIntegrand_restrictedTensor2 χ₁ χ₂ S Ψ hg s b
  have hloc : ∀ v : S, ∫ a, Fv v a ∂LocalField.multHaar (v.1.adicCompletion K) =
      LocalField.localZeta (GodementSectionLocal.slice (Ψ v) (glAt v.1 g))
        (localChar χ₁ v.1 * (localChar χ₂ v.1)⁻¹) (2 * s) := fun v ↦ rfl
  rw [finSection, hintegrand, hdec, hind, heq, finChar_det_mul_finMod_det χ₁ S hχ₁ hg s,
    ← Finset.prod_coe_sort S]
  simp only [hloc, GodementSectionLocal.localSection, GodementSectionLocal.detU,
    Finset.prod_mul_distrib]
  ring

end

end GroundTheory.Automorphic.GodementSection
