import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdelesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSAStep

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `fstA F ε w * fstA F ε w = fstA F ε w`. Distinguish the cases in `hw : w ∈ S₁`.

Rewrite using `[h1 w hw, one_mul]`. Rewrite using `[h2 w hw, zero_mul]`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`. Express the relevant statement in the definitionally equal form `evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)`.

Distinguish the cases in `hv : v ∈ S₂`. Rewrite using `[h3 v hv, one_mul]`. Rewrite using `[h4 v hv, zero_mul]`.
-/
theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

variable {R : Type*} [CommRing R] {a b : R}

/- English proof (translation)
Simplify using `only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]`. Take the linear combination `((x.re - y.re) ^ 2 - a * (x.imI - y.imI) ^ 2 - b * (x.imJ - y.imJ) ^ 2 + a * b * (x.imK - y.imK) ^ 2) * he`.
-/
theorem nrm_split (x y : ℍ[R, a, b]) (e : R) (he : e * e = e) :
    nrm ((1 - e) • x + e • y) = (1 - e) * nrm x + e * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  linear_combination ((x.re - y.re) ^ 2 - a * (x.imI - y.imI) ^ 2 - b * (x.imJ - y.imJ) ^ 2 +
    a * b * (x.imK - y.imK) ^ 2) * he

/- English proof (translation)
Simplify using `[nrm]`.
-/
theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

/- English proof (translation)
Simplify using `[nrm]`.
-/
theorem nrm_one : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

/- English proof (translation)
Unfold `nrm at hn`. Use `⟨by simp [hr], ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [QuaternionAlgebra.algebraMap_eq, hr]`. Take the linear combination `(-1 : R) * hn + (u.re + t) * hr`. Apply the tactic sequence `all_goals ring`.
-/
theorem pure_sq (u : ℍ[R, a, b]) (t : R) (hn : nrm u = 1) (hr : u.re = t) :
    (u - algebraMap R ℍ[R, a, b] t).re = 0 ∧
      (u - algebraMap R ℍ[R, a, b] t) * (u - algebraMap R ℍ[R, a, b] t) = algebraMap R ℍ[R, a, b] (t ^ 2 - 1) := by
  unfold nrm at hn
  refine ⟨by simp [hr], ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hr]
  · linear_combination (-1 : R) * hn + (u.re + t) * hr
  all_goals ring

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

variable {F : Type} [Field F] [NumberField F] {a b : F}

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [rat]`.
-/
theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [rat]`.
-/
theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by
  ext <;> simp [rat]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [rat, QuaternionAlgebra.algebraMap_eq]`.
-/
theorem rat_algebraMap (c : F) :
    rat (algebraMap F ℍ[F, a, b] c) = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) := by
  ext <;> simp [rat, QuaternionAlgebra.algebraMap_eq]

/- English proof (translation)
Apply `continuous_induced_rng.2` to reduce the goal to its premises. Establish `e : (coords ∘ fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b)) = fun x => (1 - ε) • coords x + coords (ε • (1 : DA F a b))`. Use function extensionality and compare the values at `x i`. Apply the tactic sequence `fin_cases i <;> simp [coords]`. Rewrite using `[e]`.

Establish `hc : Continuous (coords : DA F a b → Fin 4 → AF F)` using `continuous_induced_dom`. Conclude with `((continuous_const (y := (1 - ε : AF F))).smul hc).add continuous_const`.
-/
theorem continuous_affine (ε : AF F) :
    Continuous fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b) := by
  apply continuous_induced_rng.2
  have e : (coords ∘ fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b)) =
      fun x => (1 - ε) • coords x + coords (ε • (1 : DA F a b)) := by
    funext x i
    fin_cases i <;> simp [coords]
  rw [e]
  have hc : Continuous (coords : DA F a b → Fin 4 → AF F) := continuous_induced_dom
  exact ((continuous_const (y := (1 - ε : AF F))).smul hc).add continuous_const

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

/- English proof (translation)
Introduce `F _ _ a b ha hb S₁ S₂ ε hε hS hsplit g hg hg1 W hW`. Establish `hee : ε * ε = ε` using `idem_of_isPlacesIdem hε`. Establish `h11 : (1 - ε) * (1 - ε) = 1 - ε` using `by linear_combination hee`. Establish `h10 : (1 - ε) * ε = 0` using `by linear_combination -hee`. Establish `h01 : ε * (1 - ε) = 0` using `by linear_combination -hee`.

Use `set ι := algebraMap F (AF F) with hι`. Use `set φ : DA F a b → DA F a b := fun x => (1 - ε) • x + ε • (1 : DA F a b) with hφ`. Establish `hφg : φ g = g`. Establish `: φ g = g - ε • (g - 1)`. Simplify using `only [hφ, sub_smul, one_smul, smul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, hg1, sub_zero]`. Establish `hW' : φ ⁻¹' W ∈ 𝓝 g` using `(continuous_affine ε).continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (φ g); rw [hφg]; exact hW)`. Take `⟨O, hO, ⟨x, hx⟩, hOu⟩` from `GlobalTheory.T.quaternion_norm_one_trace_open_adeles F a b ha hb g hg _ hW'`. Take `⟨t, htZ, s, hts⟩` from `GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x O (hO.mem_nhds hx) {1, -1}`.

Take `⟨u₀, hu₀W, hu₀n, hu₀r⟩` from `hOu _ hts`. Take `⟨h₁, hh₁n, hh₁r⟩` from `hsplit (ι t)`. Establish `hc : t ^ 2 - 1 ≠ 0`. Establish `h1 : t ≠ 1` using `fun h => htZ (by simp [h])`. Establish `h2 : t ≠ -1` using `fun h => htZ (by simp [h])`.

Establish `: t ^ 2 - 1 = (t - 1) * (t + 1)` using `by ring`. Rewrite using `[this]`. Conclude with `mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))`. Take `⟨u, hu⟩ : ∃ u : DA F a b, u = (1 - ε) • u₀ + ε • h₁` from `⟨_, rfl⟩`. Establish `hun : nrm u = 1`.

Rewrite using `[hu, nrm_split _ _ _ hee, hu₀n, hh₁n]`. Expand and normalize the polynomial expressions, which then agree. Establish `hur : u.re = ι t`. Rewrite using `[hu]`. Simplify using `only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hu₀r]`.

Take the linear combination `hh₁r - s * hee`. Take `⟨hq0, hqq⟩` from `pure_sq u (ι t) hun hur`. Use `set q := u - algebraMap (AF F) (DA F a b) (ι t) with hq`. Establish `hqq' : q * q = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1))`. Rewrite using `[hqq]`.

Simplify using `[hι]`. Take `⟨p, hp0, hpp⟩` from `GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic F a b ha hb _ hc q hq0 hqq'`. Establish `hrp0 : (rat p).re = 0` using `by simp [rat, hp0]`. Establish `hrpp : rat p * rat p = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1))`. Rewrite using `[← rat_mul, hpp, rat_algebraMap]`.

Take `⟨y, hy, hyq⟩` from `GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion F a b ha hb _ hc (rat p) q hrp0 hq0 hrpp hqq'`. Use `set γ : ℍ[F, a, b] := algebraMap F ℍ[F, a, b] t + p with hγ`. Establish `hγn : nrm γ = 1`. Establish `hre` using `congrArg QuaternionAlgebra.re hpp`. Simplify using `[QuaternionAlgebra.algebraMap_eq, hp0] at hre`.

Simplify using `[hγ, nrm, QuaternionAlgebra.algebraMap_eq, hp0]`. Take the linear combination `-hre`. Establish `hyu : y * u = rat γ * y`. Establish `: u = q + algebraMap (AF F) (DA F a b) (ι t)` using `by rw [hq]; abel`. Rewrite using `[this, mul_add, hyq, hγ, rat_add, rat_algebraMap, add_mul, ← Algebra.commutes, add_comm]`.

Use `set h' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • h₁ with hh'`. Use `set h'' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • star h₁ with hh''`. Establish `hwh : φ u₀ * h' = u`. Simplify using `only [hφ, hh', hu, add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul, add_zero, zero_add]`. Establish `hhh : h' * h'' = 1`.

Simplify using `only [hh', hh'', add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul, add_zero, zero_add, mul_star_eq, hh₁n, map_one]`. Rewrite using `[← add_smul, sub_add_cancel, one_smul]`. Use `⟨φ u₀, hu₀W, y, hy, γ, hγn, h'', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hh'', nrm_split _ _ _ hee, nrm_one, nrm_star, hh₁n]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e1 : h'' - 1 = ε • (star h₁ - 1)`. Simplify using `only [hh'', sub_smul, one_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, smul_smul, hee]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem key_step : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  classical
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hsplit g hg hg1 W hW
  have hee : ε * ε = ε := idem_of_isPlacesIdem hε
  have h11 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
  have h10 : (1 - ε) * ε = 0 := by linear_combination -hee
  have h01 : ε * (1 - ε) = 0 := by linear_combination -hee
  set ι := algebraMap F (AF F) with hι
  set φ : DA F a b → DA F a b := fun x => (1 - ε) • x + ε • (1 : DA F a b) with hφ
  have hφg : φ g = g := by
    have : φ g = g - ε • (g - 1) := by
      simp only [hφ, sub_smul, one_smul, smul_sub]; abel
    rw [this, hg1, sub_zero]
  have hW' : φ ⁻¹' W ∈ 𝓝 g :=
    (continuous_affine ε).continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (φ g); rw [hφg]; exact hW)
  obtain ⟨O, hO, ⟨x, hx⟩, hOu⟩ := GlobalTheory.T.quaternion_norm_one_trace_open_adeles F a b ha hb g hg _ hW'
  obtain ⟨t, htZ, s, hts⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x O (hO.mem_nhds hx) {1, -1}
  obtain ⟨u₀, hu₀W, hu₀n, hu₀r⟩ := hOu _ hts
  obtain ⟨h₁, hh₁n, hh₁r⟩ := hsplit (ι t)
  have hc : t ^ 2 - 1 ≠ 0 := by
    have h1 : t ≠ 1 := fun h => htZ (by simp [h])
    have h2 : t ≠ -1 := fun h => htZ (by simp [h])
    have : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  obtain ⟨u, hu⟩ : ∃ u : DA F a b, u = (1 - ε) • u₀ + ε • h₁ := ⟨_, rfl⟩
  have hun : nrm u = 1 := by
    rw [hu, nrm_split _ _ _ hee, hu₀n, hh₁n]; ring
  have hur : u.re = ι t := by
    rw [hu]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hu₀r]
    linear_combination hh₁r - s * hee
  obtain ⟨hq0, hqq⟩ := pure_sq u (ι t) hun hur
  set q := u - algebraMap (AF F) (DA F a b) (ι t) with hq
  have hqq' : q * q = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [hqq]; simp [hι]
  obtain ⟨p, hp0, hpp⟩ := GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic F a b ha hb _ hc q hq0 hqq'
  have hrp0 : (rat p).re = 0 := by simp [rat, hp0]
  have hrpp : rat p * rat p = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [← rat_mul, hpp, rat_algebraMap]
  obtain ⟨y, hy, hyq⟩ := GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion F a b ha hb _ hc (rat p) q hrp0 hq0 hrpp hqq'
  set γ : ℍ[F, a, b] := algebraMap F ℍ[F, a, b] t + p with hγ
  have hγn : nrm γ = 1 := by
    have hre := congrArg QuaternionAlgebra.re hpp
    simp [QuaternionAlgebra.algebraMap_eq, hp0] at hre
    simp [hγ, nrm, QuaternionAlgebra.algebraMap_eq, hp0]
    linear_combination -hre
  have hyu : y * u = rat γ * y := by
    have : u = q + algebraMap (AF F) (DA F a b) (ι t) := by rw [hq]; abel
    rw [this, mul_add, hyq, hγ, rat_add, rat_algebraMap, add_mul, ← Algebra.commutes, add_comm]
  set h' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • h₁ with hh'
  set h'' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • star h₁ with hh''
  have hwh : φ u₀ * h' = u := by
    simp only [hφ, hh', hu, add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add]
  have hhh : h' * h'' = 1 := by
    simp only [hh', hh'', add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add, mul_star_eq, hh₁n, map_one]
    rw [← add_smul, sub_add_cancel, one_smul]
  refine ⟨φ u₀, hu₀W, y, hy, γ, hγn, h'', ?_, ?_, ?_⟩
  · rw [hh'', nrm_split _ _ _ hee, nrm_one, nrm_star, hh₁n]; ring
  · have e1 : h'' - 1 = ε • (star h₁ - 1) := by
      simp only [hh'', sub_smul, one_smul, smul_sub]; abel
    rw [e1, smul_smul, hee]
  · calc y * φ u₀ = y * φ u₀ * (h' * h'') := by rw [hhh, mul_one]
      _ = y * (φ u₀ * h') * h'' := by simp only [mul_assoc]
      _ = rat γ * y * h'' := by rw [hwh, hyu]

end GlobalTheory.QSAStep
