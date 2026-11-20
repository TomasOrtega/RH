import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEqMonomialBoundaryFormStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalOrderBoundaryFormEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBoundaryIdealGeneratedStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.RefineCones

/- English proof (translation)
Rewrite `h` using `[Ideal.span_singleton_eq_span_singleton]`. Conclude with `le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)`.
-/
theorem pow_eq_of_span_eq {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {n n' : ℕ}
    (h : Ideal.span {ϖ ^ n} = Ideal.span {ϖ ^ n'}) : n = n' := by
  rw [Ideal.span_singleton_eq_span_singleton] at h
  exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

/- English proof (translation)
Simplify using `using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)`.
-/
theorem toReal_mem_psdCone' {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms H.bar X)
    (hp : ∀ y, 0 ≤ β y y) : toReal β ∈ psdCone H.bar X := by
  simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp])
    (by simp)

/- English proof (translation)
Establish `h1 : φ.evalZ be = ∑ i, c i * φ.evalZ (γ i)`. Rewrite using `[← evalR_toReal, hbe]`. Conclude with `(linearOn_iff φ γ).1 hγ.linear c hc`. Establish `h2 : (ℓ be : ℝ) = ∑ i, c i * (ℓ (γ i) : ℝ)`. Use `sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id ℓ (β := Fin.cons be γ) (c := Fin.cons (-1) c) (by` as an intermediate fact.

Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[hbe])`. Rewrite `this` using `[Fin.sum_univ_succ]`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[h2, h1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hℓ]; ring`.
-/
theorem ell_eq_of_cone {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {φ : InvFun (𝓞 E)}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone H.bar φ γ) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    {be : LinearMap.BilinForm ℤ X} (hbe : toReal be = ∑ i, c i • toReal (γ i)) {N' : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hℓ : ∀ i, (ℓ (γ i) : ℝ) = N' * φ.evalZ (γ i)) :
    (ℓ be : ℝ) = N' * φ.evalZ be := by
  have h1 : φ.evalZ be = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hbe]; exact (linearOn_iff φ γ).1 hγ.linear c hc
  have h2 : (ℓ be : ℝ) = ∑ i, c i * (ℓ (γ i) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id ℓ
      (β := Fin.cons be γ) (c := Fin.cons (-1) c) (by
        rw [Fin.sum_univ_succ]; simp [hbe])
    rw [Fin.sum_univ_succ] at this
    simp at this
    linarith
  rw [h2, h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hℓ]; ring

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N hg hfan hRef hZ hN hdiv z`. Take `⟨R, i1, i2, i3, ξ, t, hm, P, m, γ, hCN, hz, het, hfu, hti, hcn, hin⟩` from `hZ z`. Establish `hrk` using `GlobalTheory.T.formally_unramified_etale_completion E H D l Xo c Z R ξ t hm P hCN het hfu hti`. Use `haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X`. Establish `hpf : IsPolFanOn H.bar φ P.D.toPre.X` using `hRef.1 P.D.toPre.X hrk`.

Establish `good` using `GlobalTheory.T.local_eq_monomial_boundary_form E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin`. Establish `bal` using `GlobalTheory.T.local_order_boundary_form_eq E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin`. Establish `elt` using `GlobalTheory.T.local_boundary_ideal_generated E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin`. Establish `hsemi : ∀ {W : Type} [CommRing W] {ϖ : W} {f : R →+* W} {be : LinearMap.BilinForm ℤ P.D.toPre.X}, FormAt P.D.toPre f ϖ be → ∀ y, 0 ≤ be y y`. Introduce `W _ ϖ f be hF y`.

Take `⟨r, n, -, h, -⟩` from `hF y`. Rewrite using `[h]`. Check the signs of the components of the expression. Establish `hcov : ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, be ∈ balForms H.bar P.D.toPre.X → (∀ y, 0 ≤ be y y) → ∃ (m' : ℕ) (γ' : Fin m' → LinearMap.BilinForm ℤ P.D.toPre.X) (c' : Fin m' → ℝ), IsCone H.bar φ γ' ∧ (∀ i, 0 ≤ c' i) ∧ toReal be = ∑ i, c' i • toReal (γ' i)` using `fun be hb hp => hpf.cover _ (toReal_mem_psdCone' H hb hp)`. Take `⟨W₀, _, _, _, hW₀, ϖ₀, hϖ₀, f₀, hloc, be₀, hs₀, hF₀, n₀, hn₀, hI₀⟩` from `good`.

Establish `hb₀` using `bal W₀ hW₀ ϖ₀ hϖ₀ f₀ be₀ hs₀ hF₀`. Take `⟨m₀, γ₀, c₀, hγ₀, hc₀, hsum₀⟩` from `hcov be₀ hb₀ (hsemi hF₀)`. Take `⟨N₀, ℓ₀, hN₀, h1, h2, h3⟩` from `hγ₀.strict`. Take `⟨M, u, hM, hu⟩` from `elt N₀ ℓ₀ hN₀ h2`. Establish `hℓ₀` using `ell_eq_of_cone hγ₀ hc₀ hsum₀ h1`.

Establish `hunit : IsUnit u`. Take `⟨n, k, hI, heq, hass⟩` from `hu W₀ hW₀ ϖ₀ hϖ₀ f₀ be₀ hs₀ hF₀`. Take `rfl : n = n₀` from `pow_eq_of_span_eq hϖ₀ (hI.symm.trans hI₀)`. Establish `hk : k = 0`. Establish `e` using `congrArg (Int.cast : ℤ → ℝ) heq`.

Move the coercions through the operations in `at e`. Rewrite `e` using `[hℓ₀, hn₀]`. Establish `: (k : ℝ) = 0` using `by linear_combination -e`. Conclude with `this` after adjusting the coercions. Substitute `hk` using the available equality.

Rewrite `hass` using `[pow_zero, associated_one_iff_isUnit]`. Conclude with `isUnit_of_map_unit f₀ u hass`. Use `⟨R, i1, i2, i3, ξ, t, hm, P, m₀, γ₀, hCN, hz, het, hfu, hti, hγ₀, ?_⟩` and prove the remaining obligations. Introduce `W _ _ _ hW ϖ hϖ f be hs hF`. Take `⟨n, k, hI, heq, hass⟩` from `hu W hW ϖ hϖ f be hs hF`.

Establish `hk : k = 0`. Establish `h0 : IsUnit (ϖ ^ k)` using `hass.isUnit_iff.1 (hunit.map f)`. Assume the negation of the conclusion as `hk`. Conclude with `hϖ.not_isUnit ((isUnit_pow_iff hk).1 h0)`. Substitute `hk` using the available equality.

Establish `hb` using `bal W hW ϖ hϖ f be hs hF`. Establish `hp` using `hsemi hF`. Take `⟨m', γ', c', hγ', hc', hsum'⟩` from `hcov be hb hp`. Take `⟨N', ℓ', hN', h1', h2', -⟩` from `hγ'.strict`. Take `⟨M', u', hM', hu'⟩` from `elt N' ℓ' hN' h2'`.

Take `⟨n', k', hI', heq', -⟩` from `hu' W hW ϖ hϖ f be hs hF`. Take `rfl : n' = n` from `pow_eq_of_span_eq hϖ (hI'.symm.trans hI)`. Establish `hℓ'` using `ell_eq_of_cone hγ' hc' hsum' h1'`. Establish `e1 : (N : ℝ) * ℓ₀ be = N₀ * n'`. Establish `e` using `congrArg (Int.cast : ℤ → ℝ) heq`.

Move the coercions through the operations in `at e`. Establish `hM0 : (M : ℝ) ≠ 0` using `by positivity`. Conclude with `mul_left_cancel₀ hM0 (by linear_combination e)`. Establish `e2 : (N' : ℝ) * n' ≤ N * ℓ' be`. Establish `e` using `congrArg (Int.cast : ℤ → ℝ) heq'`.

Move the coercions through the operations in `at e`. Establish `hk' : (0 : ℝ) ≤ k'` using `by positivity`. Establish `: (M' : ℝ) * (N' * n') ≤ M' * (N * ℓ' be)` using `by linarith`. Conclude with `le_of_mul_le_mul_left this (by positivity)`. Establish `e4 : (n' : ℝ) ≤ N * φ.evalZ be`.

Rewrite `e2` using `[hℓ']`. Establish `hN'0 : (0 : ℝ) < N'` using `by exact_mod_cast hN'`. Establish `: (N' : ℝ) * n' ≤ N' * (N * φ.evalZ be)` using `by linarith [show (N : ℝ) * (N' * φ.evalZ be) = N' * (N * φ.evalZ be) by ring]`. Conclude with `le_of_mul_le_mul_left this hN'0`. Establish `e5 : (N : ℝ) * ℓ₀ be ≤ N * (N₀ * φ.evalZ be)`.

Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Establish `e6 : (ℓ₀ be : ℝ) ≤ N₀ * φ.evalZ be` using `le_of_mul_le_mul_left e5 (by exact_mod_cast hN)`. Establish `heqφ : (N₀ : ℝ) * φ.evalZ be = ℓ₀ be` using `le_antisymm (h2 be hb hp) e6`. Take `⟨kk, cc, hkk, hcc⟩` from `h3 be hb hp heqφ`.

Use `⟨fun i => (cc i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Establish `e` using `LinearMap.congr_fun₂ hcc a b`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e`. Establish `e' : (kk : ℝ) * (be a b : ℝ) = ∑ i, (cc i : ℝ) * (γ₀ i a b : ℝ)` using `by exact_mod_cast e`. Establish `hkk0 : (kk : ℝ) ≠ 0` using `by positivity`.

Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[show ∑ i, (cc i : ℝ) / kk * (γ₀ i a b : ℝ) = (∑ i, (cc i : ℝ) * (γ₀ i a b : ℝ)) / kk by`. Rewrite using `[Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← e']`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasCones_coneO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) Z → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → HasCones (ConeO H φ) Z := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N hg hfan hRef hZ hN hdiv z
  obtain ⟨R, i1, i2, i3, ξ, t, hm, P, m, γ, hCN, hz, het, hfu, hti, hcn, hin⟩ := hZ z
  have hrk := GlobalTheory.T.formally_unramified_etale_completion E H D l Xo c Z R ξ t hm P hCN het hfu hti
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have hpf : IsPolFanOn H.bar φ P.D.toPre.X := hRef.1 P.D.toPre.X hrk
  have good := GlobalTheory.T.local_eq_monomial_boundary_form E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin
  have bal := GlobalTheory.T.local_order_boundary_form_eq E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin
  have elt := GlobalTheory.T.local_boundary_ideal_generated E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hm P m γ hg hfan hRef hN hdiv hCN het hfu hti hcn hin
  have hsemi : ∀ {W : Type} [CommRing W] {ϖ : W} {f : R →+* W} {be : LinearMap.BilinForm ℤ P.D.toPre.X},
      FormAt P.D.toPre f ϖ be → ∀ y, 0 ≤ be y y := by
    intro W _ ϖ f be hF y
    obtain ⟨r, n, -, h, -⟩ := hF y
    rw [h]; positivity
  have hcov : ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, be ∈ balForms H.bar P.D.toPre.X → (∀ y, 0 ≤ be y y) →
      ∃ (m' : ℕ) (γ' : Fin m' → LinearMap.BilinForm ℤ P.D.toPre.X) (c' : Fin m' → ℝ), IsCone H.bar φ γ' ∧
        (∀ i, 0 ≤ c' i) ∧ toReal be = ∑ i, c' i • toReal (γ' i) := fun be hb hp =>
    hpf.cover _ (toReal_mem_psdCone' H hb hp)
  obtain ⟨W₀, _, _, _, hW₀, ϖ₀, hϖ₀, f₀, hloc, be₀, hs₀, hF₀, n₀, hn₀, hI₀⟩ := good
  have hb₀ := bal W₀ hW₀ ϖ₀ hϖ₀ f₀ be₀ hs₀ hF₀
  obtain ⟨m₀, γ₀, c₀, hγ₀, hc₀, hsum₀⟩ := hcov be₀ hb₀ (hsemi hF₀)
  obtain ⟨N₀, ℓ₀, hN₀, h1, h2, h3⟩ := hγ₀.strict
  obtain ⟨M, u, hM, hu⟩ := elt N₀ ℓ₀ hN₀ h2
  have hℓ₀ := ell_eq_of_cone hγ₀ hc₀ hsum₀ h1
  have hunit : IsUnit u := by
    obtain ⟨n, k, hI, heq, hass⟩ := hu W₀ hW₀ ϖ₀ hϖ₀ f₀ be₀ hs₀ hF₀
    obtain rfl : n = n₀ := pow_eq_of_span_eq hϖ₀ (hI.symm.trans hI₀)
    have hk : k = 0 := by
      have e := congrArg (Int.cast : ℤ → ℝ) heq
      push_cast at e
      rw [hℓ₀, hn₀] at e
      have : (k : ℝ) = 0 := by linear_combination -e
      exact_mod_cast this
    subst hk
    rw [pow_zero, associated_one_iff_isUnit] at hass
    exact isUnit_of_map_unit f₀ u hass
  refine ⟨R, i1, i2, i3, ξ, t, hm, P, m₀, γ₀, hCN, hz, het, hfu, hti, hγ₀, ?_⟩
  intro W _ _ _ hW ϖ hϖ f be hs hF
  obtain ⟨n, k, hI, heq, hass⟩ := hu W hW ϖ hϖ f be hs hF
  have hk : k = 0 := by
    have h0 : IsUnit (ϖ ^ k) := hass.isUnit_iff.1 (hunit.map f)
    by_contra hk
    exact hϖ.not_isUnit ((isUnit_pow_iff hk).1 h0)
  subst hk
  have hb := bal W hW ϖ hϖ f be hs hF
  have hp := hsemi hF
  obtain ⟨m', γ', c', hγ', hc', hsum'⟩ := hcov be hb hp
  obtain ⟨N', ℓ', hN', h1', h2', -⟩ := hγ'.strict
  obtain ⟨M', u', hM', hu'⟩ := elt N' ℓ' hN' h2'
  obtain ⟨n', k', hI', heq', -⟩ := hu' W hW ϖ hϖ f be hs hF
  obtain rfl : n' = n := pow_eq_of_span_eq hϖ (hI'.symm.trans hI)
  have hℓ' := ell_eq_of_cone hγ' hc' hsum' h1'
  have e1 : (N : ℝ) * ℓ₀ be = N₀ * n' := by
    have e := congrArg (Int.cast : ℤ → ℝ) heq
    push_cast at e
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hM0 (by linear_combination e)
  have e2 : (N' : ℝ) * n' ≤ N * ℓ' be := by
    have e := congrArg (Int.cast : ℤ → ℝ) heq'
    push_cast at e
    have hk' : (0 : ℝ) ≤ k' := by positivity
    have : (M' : ℝ) * (N' * n') ≤ M' * (N * ℓ' be) := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have e4 : (n' : ℝ) ≤ N * φ.evalZ be := by
    rw [hℓ'] at e2
    have hN'0 : (0 : ℝ) < N' := by exact_mod_cast hN'
    have : (N' : ℝ) * n' ≤ N' * (N * φ.evalZ be) := by linarith [show (N : ℝ) * (N' * φ.evalZ be) = N' * (N * φ.evalZ be) by ring]
    exact le_of_mul_le_mul_left this hN'0
  have e5 : (N : ℝ) * ℓ₀ be ≤ N * (N₀ * φ.evalZ be) := by
    rw [e1]
    calc (N₀ : ℝ) * n' ≤ N₀ * (N * φ.evalZ be) := mul_le_mul_of_nonneg_left e4 (by positivity)
      _ = N * (N₀ * φ.evalZ be) := by ring
  have e6 : (ℓ₀ be : ℝ) ≤ N₀ * φ.evalZ be := le_of_mul_le_mul_left e5 (by exact_mod_cast hN)
  have heqφ : (N₀ : ℝ) * φ.evalZ be = ℓ₀ be := le_antisymm (h2 be hb hp) e6
  obtain ⟨kk, cc, hkk, hcc⟩ := h3 be hb hp heqφ
  refine ⟨fun i => (cc i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have e := LinearMap.congr_fun₂ hcc a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e
  have e' : (kk : ℝ) * (be a b : ℝ) = ∑ i, (cc i : ℝ) * (γ₀ i a b : ℝ) := by exact_mod_cast e
  have hkk0 : (kk : ℝ) ≠ 0 := by positivity
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i, (cc i : ℝ) / kk * (γ₀ i a b : ℝ) = (∑ i, (cc i : ℝ) * (γ₀ i a b : ℝ)) / kk by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← e']
  field_simp

end GlobalTheory.TorRef.RefineCones
