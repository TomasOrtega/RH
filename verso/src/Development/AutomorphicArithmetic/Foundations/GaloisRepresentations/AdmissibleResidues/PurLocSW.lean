import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.MonodromyFreeOfEigenvalueRatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.GalN.V
open private ex_elt algPow_const flag_cont cyc_cont from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst

/- English proof (translation)
Set `D : Γ →* Multiplicative R` to `MonoidHom.mk' (fun x => Multiplicative.ofAdd (f x)) (by`. Introduce `a b`. Rewrite using `[hf]`. Use the proof step `rfl)`. Establish `h` using `congrArg Multiplicative.toAdd (map_zpow D g m)`.

Simplify using `only [toAdd_zpow] at h`. Rewrite `h` using `[zsmul_eq_mul]`. Conclude with `h`.
-/
private theorem map_zpow_eq_intCast_mul_of_map_mul_eq_add {Γ R : Type} [Group Γ] [Ring R] (f : Γ → R) (hf : ∀ a b, f (a * b) = f a + f b)
    (g : Γ) (m : ℤ) : f (g ^ m) = (m : R) * f g := by
  let D : Γ →* Multiplicative R := MonoidHom.mk' (fun x => Multiplicative.ofAdd (f x)) (by
    intro a b
    rw [hf]
    rfl)
  have h := congrArg Multiplicative.toAdd (map_zpow D g m)
  simp only [toAdd_zpow] at h
  rw [zsmul_eq_mul] at h
  exact h

/- English proof (translation)
Establish `hD` using `map_zpow_eq_intCast_mul_of_map_mul_eq_add d hd`. Establish `hLz` using `map_zpow_eq_intCast_mul_of_map_mul_eq_add L hL`. Establish `key : ∀ m : ℤ, |(m : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ| < c`. Introduce `m`. Establish `h1 : d (s ^ m * φ ^ (1 - m * d s)) = 1`.

Rewrite using `[hd, hD, hD, hφ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hw _ h1`. Rewrite `h2` using `[hL, hLz, hLz, hk]`.

Use `h2 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hδ : k * c - L φ = 0`. Assume the negation of the conclusion as `hne`.

Establish `hpos : 0 < |k * c - L φ|` using `abs_pos.mpr hne`. Take `⟨n, hn⟩` from `exists_nat_gt (2 * c / |k * c - L φ|)`. Establish `h1` using `key n`. Establish `h0` using `key 0`. Simplify using `only [Int.cast_zero, zero_mul, zero_add] at h0`.

Establish `hds : (1 : ℝ) ≤ |(d s : ℝ)|`. Establish `: (1 : ℤ) ≤ |d s|` using `Int.one_le_abs hs`. Conclude with `this` after adjusting the coercions. Establish `h3 : |(n : ℝ) * (d s : ℝ) * (k * c - L φ)| < 2 * c`. Use `abs_sub (((n : ℤ) : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ) (L φ)` as an intermediate fact.

Simplify using `only [add_sub_cancel_right, Int.cast_natCast] at this`. Simplify using `only [Int.cast_natCast] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h3` using `[abs_mul, abs_mul, Nat.abs_cast]`. Rewrite `hn` using `[div_lt_iff₀ hpos]`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hds (mul_nonneg hn0 hpos.le)]`. Establish `hLφ : L φ = k * c` using `by linarith`. Establish `h` using `hw φ hφ`. Rewrite `h` using `[hLφ, abs_mul, abs_of_pos hc]`.

Establish `hk1 : |(k : ℝ)| < 1`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Use the polynomial consequences of the given equalities and inequalities. Establish `: |k| < 1` using `by exact_mod_cast hk1`.

Conclude with `Int.abs_lt_one_iff.mp this`.
-/
private theorem int_zero {Γ : Type} [Group Γ] (d : Γ → ℤ) (L : Γ → ℝ) (hd : ∀ a b, d (a * b) = d a + d b)
    (hL : ∀ a b, L (a * b) = L a + L b) (φ : Γ) (hφ : d φ = 1) {c : ℝ} (hc : 0 < c) (hw : ∀ g, d g = 1 → |L g| < c)
    (s : Γ) (hs : d s ≠ 0) (k : ℤ) (hk : L s = k * d s * c) : k = 0 := by
  have hD := map_zpow_eq_intCast_mul_of_map_mul_eq_add d hd
  have hLz := map_zpow_eq_intCast_mul_of_map_mul_eq_add L hL
  have key : ∀ m : ℤ, |(m : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ| < c := by
    intro m
    have h1 : d (s ^ m * φ ^ (1 - m * d s)) = 1 := by
      rw [hd, hD, hD, hφ]
      push_cast
      ring
    have h2 := hw _ h1
    rw [hL, hLz, hLz, hk] at h2
    convert h2 using 2
    push_cast
    ring
  have hδ : k * c - L φ = 0 := by
    by_contra hne
    have hpos : 0 < |k * c - L φ| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * c / |k * c - L φ|)
    have h1 := key n
    have h0 := key 0
    simp only [Int.cast_zero, zero_mul, zero_add] at h0
    have hds : (1 : ℝ) ≤ |(d s : ℝ)| := by
      have : (1 : ℤ) ≤ |d s| := Int.one_le_abs hs
      exact_mod_cast this
    have h3 : |(n : ℝ) * (d s : ℝ) * (k * c - L φ)| < 2 * c := by
      have := abs_sub (((n : ℤ) : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ) (L φ)
      simp only [add_sub_cancel_right, Int.cast_natCast] at this
      simp only [Int.cast_natCast] at h1
      linarith
    rw [abs_mul, abs_mul, Nat.abs_cast] at h3
    rw [div_lt_iff₀ hpos] at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hds (mul_nonneg hn0 hpos.le)]
  have hLφ : L φ = k * c := by linarith
  have h := hw φ hφ
  rw [hLφ, abs_mul, abs_of_pos hc] at h
  have hk1 : |(k : ℝ)| < 1 := by
    by_contra hh
    push_neg at hh
    nlinarith
  have : |k| < 1 := by exact_mod_cast hk1
  exact Int.abs_lt_one_iff.mp this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨na, a, rfl⟩` from `x.exists_rep`. Rewrite using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Set `b` to `WDRep.ofChars h μ hμ`. Establish `hc : ∀ σ, (a.ρ σ).charpoly = (b.ρ σ).charpoly`. Introduce `σ`.

Rewrite using `[← WD.charPol_mk, hx, WDRep.ofChars_ρ, charpoly_diagEnd]`. Take `⟨e, he⟩` from `GlobalTheory.T.weilRep_equiv_of_charpoly_eq F Ω A w h na n a b hc`. Establish `hes : ∀ σ z, e.symm (b.ρ σ z) = a.ρ σ (e.symm z)`. Introduce `σ z`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Set `N' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `e.toLinearMap ∘ₗ a.N ∘ₗ e.symm.toLinearMap`. Establish `hN' : ∀ σ z, b.ρ σ (N' z) = ((normV w : ℕ) : ℂ) ^ deg σ • N' (b.ρ σ z)`. Introduce `σ z`. Simplify using `only [N', LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[← he, WDRep.comm_apply, hes, LinearEquiv.map_smul]`. Establish `hsingle : ∀ σ j, b.ρ σ (Pi.single j 1) = (μ j σ : ℂ) • Pi.single j 1`. Introduce `σ j`. Use function extensionality and compare the values at `i`. Rewrite using `[WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, smul_eq_mul]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hij]`. Establish `hM : ∀ i j, N' (Pi.single j 1) i = 0`.

Introduce `i j`. Take `⟨σ, hσ⟩` from `hne i j`. Establish `h1` using `congrFun (hN' σ (Pi.single j 1)) i`. Rewrite `h1` using `[hsingle, LinearMap.map_smul, WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `h2 : ((μ i σ : ℂ) - ((normV w : ℕ) : ℂ) ^ deg σ * μ j σ) * N' (Pi.single j 1) i = 0`.

Rewrite using `[sub_mul, h1]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h3) hσ`. Conclude with `h3`.

Establish `hN0 : N' = 0`. Apply `LinearMap.pi_ext'` to reduce the goal to its premises. Introduce `j`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Simplify using `only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_comp, LinearMap.zero_apply, Pi.zero_apply]`. Conclude with `hM i j`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `h4` using `LinearMap.congr_fun hN0 (e v)`.

Simplify using `only [N', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at h4`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `(LinearEquiv.map_eq_zero_iff e).mp h4`.
-/
private theorem mono0_of_charPol_eq_prod_of_ne_normV_pow_mul {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ)))
    (hne : ∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) : x.mono0 := by
  obtain ⟨na, a, rfl⟩ := x.exists_rep
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  let b := WDRep.ofChars h μ hμ
  have hc : ∀ σ, (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
    intro σ
    rw [← WD.charPol_mk, hx, WDRep.ofChars_ρ, charpoly_diagEnd]
  obtain ⟨e, he⟩ := GlobalTheory.T.weilRep_equiv_of_charpoly_eq F Ω A w h na n a b hc
  have hes : ∀ σ z, e.symm (b.ρ σ z) = a.ρ σ (e.symm z) := by
    intro σ z
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let N' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := e.toLinearMap ∘ₗ a.N ∘ₗ e.symm.toLinearMap
  have hN' : ∀ σ z, b.ρ σ (N' z) = ((normV w : ℕ) : ℂ) ^ deg σ • N' (b.ρ σ z) := by
    intro σ z
    simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, WDRep.comm_apply, hes, LinearEquiv.map_smul]
  have hsingle : ∀ σ j, b.ρ σ (Pi.single j 1) = (μ j σ : ℂ) • Pi.single j 1 := by
    intro σ j
    funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij]
  have hM : ∀ i j, N' (Pi.single j 1) i = 0 := by
    intro i j
    obtain ⟨σ, hσ⟩ := hne i j
    have h1 := congrFun (hN' σ (Pi.single j 1)) i
    rw [hsingle, LinearMap.map_smul, WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul] at h1
    have h2 : ((μ i σ : ℂ) - ((normV w : ℕ) : ℂ) ^ deg σ * μ j σ) * N' (Pi.single j 1) i = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hσ
    · exact h3
  have hN0 : N' = 0 := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    funext i
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_comp, LinearMap.zero_apply, Pi.zero_apply]
    exact hM i j
  apply LinearMap.ext
  intro v
  have h4 := LinearMap.congr_fun hN0 (e v)
  simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at h4
  rw [LinearMap.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp h4

/- English proof (translation)
Establish `hm : x.mono0`. Break down `hor with h1 | h1` into its components or cases. Conclude with `mono0_of_charPol_eq_prod_of_ne_normV_pow_mul x μ hμ hx h1`. Conclude with `h1`. Establish `hR` using `ht hm`.

Establish `hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ)` using `by linarith`. Establish `hpos : ∀ l g, 0 < ‖(μ l g : ℂ)‖` using `fun l g => norm_pos_iff.mpr (Units.ne_zero _)`. Establish `hmem : ∀ g l, (μ l g : ℂ) ∈ x.eig g`. Introduce `g l`.

Use `show (μ l g : ℂ) ∈ (x.charPol g).roots`. Rewrite using `[hx]`. Establish `hmon : (∏ k, (X - C (μ k g : ℂ))).Monic` using `monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)`. Rewrite using `[mem_roots hmon.ne_zero, IsRoot, eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ l) (by simp)`.

Use `int_zero (Γ := Weil h) deg (fun g => Real.log ‖(μ i g : ℂ)‖ - Real.log ‖(μ j g : ℂ)‖) deg_mul ?_ (frob h) deg_frob (Real.log_pos hq1) ?_ s hs k ?_` and prove the remaining obligations. Introduce `a b`. Simplify using `only [map_mul, Units.val_mul, norm_mul]`. Rewrite using `[Real.log_mul (hpos i a).ne' (hpos i b).ne', Real.log_mul (hpos j a).ne' (hpos j b).ne']`. Expand and normalize the polynomial expressions, which then agree.

Introduce `g hg`. Establish `h1` using `hR g hg _ (hmem g i) _ (hmem g j)`. Establish `h2` using `hR g hg _ (hmem g j) _ (hmem g i)`. Establish `l1` using `Real.log_lt_log (hpos i g) h1`. Establish `l2` using `Real.log_lt_log (hpos j g) h2`.

Rewrite `l1` using `[Real.log_mul hq0.ne' (hpos j g).ne']`. Rewrite `l2` using `[Real.log_mul hq0.ne' (hpos i g).ne']`. Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;> linarith`. Use `beta_reduce`.

Rewrite using `[hk, Real.log_mul (zpow_pos hq0 _).ne' (hpos j s).ne', Real.log_zpow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ratio_lt {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) (ht : x.mono0 → RatioW x)
    (hor : (∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) ∨ x.mono0) (i j : Fin n) (s : Weil h) (hs : deg s ≠ 0) (k : ℤ)
    (hk : ‖(μ i s : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ (k * deg s) * ‖(μ j s : ℂ)‖) : k = 0 := by
  have hm : x.mono0 := by
    rcases hor with h1 | h1
    · exact mono0_of_charPol_eq_prod_of_ne_normV_pow_mul x μ hμ hx h1
    · exact h1
  have hR := ht hm
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  have hpos : ∀ l g, 0 < ‖(μ l g : ℂ)‖ := fun l g => norm_pos_iff.mpr (Units.ne_zero _)
  have hmem : ∀ g l, (μ l g : ℂ) ∈ x.eig g := by
    intro g l
    show (μ l g : ℂ) ∈ (x.charPol g).roots
    rw [hx]
    have hmon : (∏ k, (X - C (μ k g : ℂ))).Monic := monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
    rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  refine int_zero (Γ := Weil h) deg (fun g => Real.log ‖(μ i g : ℂ)‖ - Real.log ‖(μ j g : ℂ)‖) deg_mul ?_ (frob h)
    deg_frob (Real.log_pos hq1) ?_ s hs k ?_
  · intro a b
    simp only [map_mul, Units.val_mul, norm_mul]
    rw [Real.log_mul (hpos i a).ne' (hpos i b).ne', Real.log_mul (hpos j a).ne' (hpos j b).ne']
    ring
  · intro g hg
    have h1 := hR g hg _ (hmem g i) _ (hmem g j)
    have h2 := hR g hg _ (hmem g j) _ (hmem g i)
    have l1 := Real.log_lt_log (hpos i g) h1
    have l2 := Real.log_lt_log (hpos j g) h2
    rw [Real.log_mul hq0.ne' (hpos j g).ne'] at l1
    rw [Real.log_mul hq0.ne' (hpos i g).ne'] at l2
    rw [abs_lt]
    constructor <;> linarith
  · beta_reduce
    rw [hk, Real.log_mul (zpow_pos hq0 _).ne' (hpos j s).ne', Real.log_zpow]
    push_cast
    ring

end
