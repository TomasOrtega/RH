import Mathlib
import Formalism.LocalToGlobal.Columns.StandardDeltaIntegralCoeffs
import Formalism.LocalToGlobal.Columns.BrpColLatOneSpan
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds

open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section Loc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `R0.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem (R0.prod_mem fun i _ => h _ _) _`.
-/
theorem det_mem_subring_of_entries_mem (R0 : Subring K) (A : Matrix (Fin n) (Fin n) K) (h : ∀ a b, A a b ∈ R0) : A.det ∈ R0 := by
  rw [Matrix.det_apply]
  refine R0.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (R0.prod_mem fun i _ => h _ _) _

/- English proof (translation)
Break down `e with m | m` into its components or cases. Use `show u ^ ((m : ℕ) : ℤ) ∈ R0`. Rewrite using `[zpow_natCast]`. Conclude with `R0.pow_mem h1 m`. Rewrite using `[zpow_negSucc, ← inv_pow]`.

Conclude with `R0.pow_mem h2 _`.
-/
theorem zpow_mem_subring (R0 : Subring K) {u : K} (h1 : u ∈ R0) (h2 : u⁻¹ ∈ R0) (e : ℤ) : u ^ e ∈ R0 := by
  rcases e with m | m
  · show u ^ ((m : ℕ) : ℤ) ∈ R0
    rw [zpow_natCast]
    exact R0.pow_mem h1 m
  · rw [zpow_negSucc, ← inv_pow]
    exact R0.pow_mem h2 _

/- English proof (translation)
Break down `e with m | m` into its components or cases. Use `show c ^ m * u ^ ((m : ℕ) : ℤ) ∈ R0`. Rewrite using `[zpow_natCast, ← mul_pow]`. Conclude with `R0.pow_mem h1 m`. Use `show c ^ (m + 1) * u ^ (Int.negSucc m) ∈ R0`.

Rewrite using `[zpow_negSucc, ← inv_pow, ← mul_pow]`. Conclude with `R0.pow_mem h2 _`.
-/
theorem scaled_zpow_mem_subring (R0 : Subring K) {c u : K} (h1 : c * u ∈ R0) (h2 : c * u⁻¹ ∈ R0) (e : ℤ) : c ^ e.natAbs * u ^ e ∈ R0 := by
  rcases e with m | m
  · show c ^ m * u ^ ((m : ℕ) : ℤ) ∈ R0
    rw [zpow_natCast, ← mul_pow]
    exact R0.pow_mem h1 m
  · show c ^ (m + 1) * u ^ (Int.negSucc m) ∈ R0
    rw [zpow_negSucc, ← inv_pow, ← mul_pow]
    exact R0.pow_mem h2 _

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_mem _, by rw [one_smul]; exact Submodule.mem_one.2 ⟨r, rfl⟩⟩`.
-/
theorem integer_mem_local_ring (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : algebraMap (𝓞 K) K r ∈ locRing w :=
  ⟨1, one_mem _, by rw [one_smul]; exact Submodule.mem_one.2 ⟨r, rfl⟩⟩

/- English proof (translation)
The claim follows from `det_mem_subring_of_entries_mem _ _ fun a b => (mem_locRing w _).2 (lc_entries_same w hB hB' a b)`.
-/
theorem det_change_of_basis_mem_locRing (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w M B) (hB' : IsBasisAt w M B') :
    ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ∈ locRing w :=
  det_mem_subring_of_entries_mem _ _ fun a b => (mem_locRing w _).2 (lc_entries_same w hB hB' a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem standard_basis_at_place (w : HeightOneSpectrum (𝓞 K)) : IsBasisAt w (colLat (1 : GL (Fin n) K)) 1 := rfl

/- English proof (translation)
Take `⟨hE1, hE2⟩` from `Formalism.L2.DIV.nb_entries w M B hB d h1 h2`. Establish `key : ∀ A : Matrix (Fin n) (Fin n) K, (∀ a b, algebraMap (𝓞 K) K d * A a b ∈ locRing w) → algebraMap (𝓞 K) K (d ^ n) * A.det ∈ locRing w`. Introduce `A hA`. Establish `h3` using `det_mem_subring_of_entries_mem (locRing w) (algebraMap (𝓞 K) K d • A) (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hA a b)`. Rewrite `h3` using `[Matrix.det_smul, Fintype.card_fin, ← map_pow]`. Then use the resulting hypothesis.

Use `⟨key _ (fun a b => hE1 a b), ?_⟩` and prove the remaining obligations. Establish `h4` using `key _ (fun a b => hE2 a b)`. Use `first`. Consider the case `rwa [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h4`. Consider the case `simpa [Matrix.coe_units_inv, Matrix.det_nonsing_inv] using h4`.
-/
theorem det_bound_common_denominator (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)} {B : GL (Fin n) K} (hB : IsBasisAt w M B) (d : 𝓞 K)
    (h1 : ∀ x ∈ M, d • x ∈ colLat (1 : GL (Fin n) K)) (h2 : ∀ x ∈ colLat (1 : GL (Fin n) K), d • x ∈ M) :
    algebraMap (𝓞 K) K (d ^ n) * (B : Matrix (Fin n) (Fin n) K).det ∈ locRing w ∧
    algebraMap (𝓞 K) K (d ^ n) * ((B : Matrix (Fin n) (Fin n) K).det)⁻¹ ∈ locRing w := by
  obtain ⟨hE1, hE2⟩ := Formalism.L2.DIV.nb_entries w M B hB d h1 h2
  have key : ∀ A : Matrix (Fin n) (Fin n) K, (∀ a b, algebraMap (𝓞 K) K d * A a b ∈ locRing w) →
      algebraMap (𝓞 K) K (d ^ n) * A.det ∈ locRing w := by
    intro A hA
    have h3 := det_mem_subring_of_entries_mem (locRing w) (algebraMap (𝓞 K) K d • A)
      (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hA a b)
    rwa [Matrix.det_smul, Fintype.card_fin, ← map_pow] at h3
  refine ⟨key _ (fun a b => hE1 a b), ?_⟩
  have h4 := key _ (fun a b => hE2 a b)
  first
    | rwa [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h4
    | simpa [Matrix.coe_units_inv, Matrix.det_nonsing_inv] using h4

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `only [detTwK, detPow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Units.val_mul, ← mul_zpow, Pi.inv_apply, map_inv, inv_mul_cancel, one_zpow, Units.val_one]`.
-/
theorem det_twist_inv_mul (lam : ι → DomWeight n) (B : ι → GL (Fin n) K) : detTwK lam B⁻¹ * detTwK lam B = 1 := by
  simp only [detTwK, detPow, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [← Units.val_mul, ← mul_zpow, Pi.inv_apply, map_inv, inv_mul_cancel, one_zpow, Units.val_one]

/- English proof (translation)
Introduce `h`. Establish `h1` using `det_twist_inv_mul lam B`. Rewrite `h1` using `[h, mul_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem det_twist_ne_zero (lam : ι → DomWeight n) (B : ι → GL (Fin n) K) : detTwK lam B ≠ 0 := by
  intro h
  have h1 := det_twist_inv_mul lam B
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Simplify using `only [detTwK, detPow, ← Finset.prod_mul_distrib]`. Use `Subring.prod_mem _ fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.inv_apply, ← Units.val_mul, ← mul_zpow, ← map_mul, Units.val_zpow_eq_zpow_val]`. Use `zpow_mem_subring _ ?_ ?_ _` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`.

Conclude with `det_change_of_basis_mem_locRing w (hB τ) (hB' τ)`. Rewrite using `[← Units.val_inv_eq_inv_val, ← map_inv, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `det_change_of_basis_mem_locRing w (hB' τ) (hB τ)`.
-/
theorem det_twist_inv_mul_det_twist_mem_locRing (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) {M : ι → Submodule (𝓞 K) (Fin n → K)}
    {B B' : ι → GL (Fin n) K} (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) (hB' : ∀ τ, IsBasisAt w (M τ) (B' τ)) :
    detTwK lam B'⁻¹ * detTwK lam B ∈ locRing w := by
  simp only [detTwK, detPow, ← Finset.prod_mul_distrib]
  refine Subring.prod_mem _ fun τ _ => ?_
  rw [Pi.inv_apply, ← Units.val_mul, ← mul_zpow, ← map_mul, Units.val_zpow_eq_zpow_val]
  refine zpow_mem_subring _ ?_ ?_ _
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_change_of_basis_mem_locRing w (hB τ) (hB' τ)
  · rw [← Units.val_inv_eq_inv_val, ← map_inv, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_change_of_basis_mem_locRing w (hB' τ) (hB τ)

/- English proof (translation)
Take `⟨d, hd, hdM⟩` from `Formalism.L2.DIV.nb_sandwich_fam M hM`. Use `⟨∏ τ, (d ^ n) ^ (lam τ).detShift.natAbs, ?_, fun w B hB => ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (pow_ne_zero _ hd)`. Establish `hb : ∀ τ, (algebraMap (𝓞 K) K d) ^ n * (B τ : Matrix (Fin n) (Fin n) K).det ∈ locRing w ∧ (algebraMap (𝓞 K) K d) ^ n * ((B τ : Matrix (Fin n) (Fin n) K).det)⁻¹ ∈ locRing w` using `fun τ => by`. Simplify `det_bound_common_denominator w (hB τ) d (hdM τ).1 (hdM τ).2` using `only [map_pow]`.

Simplify using `only [detTwK, detPow, map_prod, map_pow, ← Finset.prod_mul_distrib]`. Prove the components needed by the constructor for the conclusion. Use `Subring.prod_mem _ fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `scaled_zpow_mem_subring _ (hb τ).1 (hb τ).2 _`.

Use `Subring.prod_mem _ fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.inv_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `scaled_zpow_mem_subring _ (hb τ).2 (by rw [inv_inv]; exact (hb τ).1) _`.
-/
theorem det_twist_uniform_bound (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ dd : 𝓞 K, dd ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      algebraMap (𝓞 K) K dd * detTwK lam B ∈ locRing w ∧ algebraMap (𝓞 K) K dd * detTwK lam B⁻¹ ∈ locRing w := by
  obtain ⟨d, hd, hdM⟩ := Formalism.L2.DIV.nb_sandwich_fam M hM
  refine ⟨∏ τ, (d ^ n) ^ (lam τ).detShift.natAbs, ?_, fun w B hB => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (pow_ne_zero _ hd)
  · have hb : ∀ τ, (algebraMap (𝓞 K) K d) ^ n * (B τ : Matrix (Fin n) (Fin n) K).det ∈ locRing w ∧
        (algebraMap (𝓞 K) K d) ^ n * ((B τ : Matrix (Fin n) (Fin n) K).det)⁻¹ ∈ locRing w := fun τ => by
      simpa only [map_pow] using det_bound_common_denominator w (hB τ) d (hdM τ).1 (hdM τ).2
    simp only [detTwK, detPow, map_prod, map_pow, ← Finset.prod_mul_distrib]
    constructor
    · refine Subring.prod_mem _ fun τ _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
      exact scaled_zpow_mem_subring _ (hb τ).1 (hb τ).2 _
    · refine Subring.prod_mem _ fun τ _ => ?_
      rw [Pi.inv_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact scaled_zpow_mem_subring _ (hb τ).2 (by rw [inv_inv]; exact (hb τ).1) _

def twLoc (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) : Submodule (𝓞 K) K :=
  ⨅ (B : ι → GL (Fin n) K) (_ : ∀ τ, IsBasisAt w (M τ) (B τ)),
    (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).comap ((LinearMap.mulLeft K (detTwK lam B⁻¹)).restrictScalars (𝓞 K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twId_eq (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : twId lam M = ⨅ w, twLoc lam M w := rfl

/- English proof (translation)
Simplify using `only [twLoc, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]`. Conclude with `Iff.rfl`.
-/
theorem mem_twLoc (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    a ∈ twLoc lam M w ↔ ∀ B : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (M τ) (B τ)) → detTwK lam B⁻¹ * a ∈ locRing w := by
  simp only [twLoc, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[mem_twLoc]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h B hB`. Introduce `h B' hB'`.

Establish `e : detTwK lam B'⁻¹ * a = (detTwK lam B'⁻¹ * detTwK lam B) * (detTwK lam B⁻¹ * a)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[det_twist_inv_mul, mul_one]`. Use `_ = (detTwK lam B'⁻¹ * detTwK lam B) * (detTwK lam B⁻¹ * a) := by ring`. Rewrite using `[e]`.

Conclude with `(locRing w).mul_mem (det_twist_inv_mul_det_twist_mem_locRing lam w hB hB') h`.
-/
theorem mem_twLoc_iff (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K))
    (B : ι → GL (Fin n) K) (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) (a : K) :
    a ∈ twLoc lam M w ↔ detTwK lam B⁻¹ * a ∈ locRing w := by
  rw [mem_twLoc]
  constructor
  · intro h
    exact h B hB
  · intro h B' hB'
    have e : detTwK lam B'⁻¹ * a = (detTwK lam B'⁻¹ * detTwK lam B) * (detTwK lam B⁻¹ * a) := by
      calc detTwK lam B'⁻¹ * a = detTwK lam B'⁻¹ * a * (detTwK lam B⁻¹ * detTwK lam B) := by
            rw [det_twist_inv_mul, mul_one]
        _ = (detTwK lam B'⁻¹ * detTwK lam B) * (detTwK lam B⁻¹ * a) := by ring
    rw [e]
    exact (locRing w).mul_mem (det_twist_inv_mul_det_twist_mem_locRing lam w hB hB') h

/- English proof (translation)
Take `⟨dd, hdd, hb⟩` from `det_twist_uniform_bound lam M hM`. Use `choose Bw hBw using fun (w : HeightOneSpectrum (𝓞 K)) (τ : ι) => basisAtEx K n (M τ) (hM τ) w`. Rewrite using `[twId_eq]`. Use `localized_iInf (twLoc lam M) (1 : Submodule (𝓞 K) K) dd hdd ?_ ?_ ?_ w` and prove the remaining obligations. Introduce `w`.

Use `le_antisymm ?_ (lc_le_locP w _)` and prove the remaining obligations. Introduce and unpack `x ⟨s, hs, hx⟩`. Rewrite `hx`, the goal using `[mem_twLoc_iff lam M w (Bw w) (hBw w)]`. Rewrite `hx`, the goal using `[mem_locRing]`. Rewrite `hx` using `[Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]`.

Conclude with `(smul_mem_localized_iff w _ hs _).1 hx`. Introduce `w x hx`. Rewrite `hx` using `[mem_twLoc_iff lam M w (Bw w) (hBw w)]`. Rewrite using `[← mem_locRing]`. Establish `e : dd • x = (algebraMap (𝓞 K) K dd * detTwK lam (Bw w)) * (detTwK lam (Bw w)⁻¹ * x)`.

Use `det_twist_inv_mul lam (Bw w)` as an intermediate fact. Rewrite using `[Algebra.smul_def]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `mul_mem (hb w (Bw w) (hBw w)).1 hx`.

Introduce `w x hx`. Rewrite using `[mem_twLoc_iff lam M w (Bw w) (hBw w)]`. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hx`. Establish `e : detTwK lam (Bw w)⁻¹ * dd • algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K dd * detTwK lam (Bw w)⁻¹) * algebraMap (𝓞 K) K r`. Rewrite using `[Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem (hb w (Bw w) (hBw w)).2 (integer_mem_local_ring w r)`.
-/
theorem localisation_twisted_ideal (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (w : HeightOneSpectrum (𝓞 K)) : localization₂ w.asIdeal (twId lam M) = twLoc lam M w := by
  obtain ⟨dd, hdd, hb⟩ := det_twist_uniform_bound lam M hM
  choose Bw hBw using fun (w : HeightOneSpectrum (𝓞 K)) (τ : ι) => basisAtEx K n (M τ) (hM τ) w
  rw [twId_eq]
  refine localized_iInf (twLoc lam M) (1 : Submodule (𝓞 K) K) dd hdd ?_ ?_ ?_ w
  · intro w
    refine le_antisymm ?_ (lc_le_locP w _)
    rintro x ⟨s, hs, hx⟩
    rw [mem_twLoc_iff lam M w (Bw w) (hBw w)] at hx ⊢
    rw [mem_locRing] at hx ⊢
    rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def] at hx
    exact (smul_mem_localized_iff w _ hs _).1 hx
  · intro w x hx
    rw [mem_twLoc_iff lam M w (Bw w) (hBw w)] at hx
    rw [← mem_locRing]
    have e : dd • x = (algebraMap (𝓞 K) K dd * detTwK lam (Bw w)) * (detTwK lam (Bw w)⁻¹ * x) := by
      have := det_twist_inv_mul lam (Bw w)
      rw [Algebra.smul_def]
      calc algebraMap (𝓞 K) K dd * x = algebraMap (𝓞 K) K dd * (detTwK lam (Bw w)⁻¹ * detTwK lam (Bw w)) * x := by rw [this, mul_one]
        _ = _ := by ring
    rw [e]
    exact mul_mem (hb w (Bw w) (hBw w)).1 hx
  · intro w x hx
    rw [mem_twLoc_iff lam M w (Bw w) (hBw w)]
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
    have e : detTwK lam (Bw w)⁻¹ * dd • algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K dd * detTwK lam (Bw w)⁻¹) * algebraMap (𝓞 K) K r := by
      rw [Algebra.smul_def]; ring
    rw [e]
    exact mul_mem (hb w (Bw w) (hBw w)).2 (integer_mem_local_ring w r)

end Loc

section Ideal

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {ι : Type} [Fintype ι]

/- English proof (translation)
Take `⟨dd, hdd, hb⟩` from `det_twist_uniform_bound lam M hM`. Use `⟨dd, hdd, fun w x hx => ?_, fun w x hx => ?_⟩` and prove the remaining obligations. Use `choose B hB using fun τ => Formalism.L2.DIV.basisAtEx K n (M τ) (hM τ) w`. Establish `h1` using `(mem_twLoc_iff lam M w B hB x).1 hx`. Establish `e : dd • x = (algebraMap (𝓞 K) K dd * detTwK lam B) * (detTwK lam B⁻¹ * x)`.

Rewrite using `[Algebra.smul_def]`. Combine the equalities or inequalities in the displayed calculation. Use `show dd • x ∈ locRing w`. Rewrite using `[e]`. Conclude with `(locRing w).mul_mem (hb w B hB).1 h1`.

Use `choose B hB using fun τ => Formalism.L2.DIV.basisAtEx K n (M τ) (hM τ) w`. Rewrite using `[mem_twLoc_iff lam M w B hB]`. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hx`. Establish `e : detTwK lam B⁻¹ * (dd • algebraMap (𝓞 K) K r) = (algebraMap (𝓞 K) K dd * detTwK lam B⁻¹) * algebraMap (𝓞 K) K r`. Rewrite using `[Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(locRing w).mul_mem (hb w B hB).2 (integer_mem_local_ring w r)`.
-/
theorem twisted_localisation_comparable (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ dd : 𝓞 K, dd ≠ 0 ∧ (∀ w, ∀ x ∈ twLoc lam M w, dd • x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ∧
      (∀ w, ∀ x ∈ (1 : Submodule (𝓞 K) K), dd • x ∈ twLoc lam M w) := by
  obtain ⟨dd, hdd, hb⟩ := det_twist_uniform_bound lam M hM
  refine ⟨dd, hdd, fun w x hx => ?_, fun w x hx => ?_⟩
  · choose B hB using fun τ => Formalism.L2.DIV.basisAtEx K n (M τ) (hM τ) w
    have h1 := (mem_twLoc_iff lam M w B hB x).1 hx
    have e : dd • x = (algebraMap (𝓞 K) K dd * detTwK lam B) * (detTwK lam B⁻¹ * x) := by
      rw [Algebra.smul_def]
      calc algebraMap (𝓞 K) K dd * x
          = algebraMap (𝓞 K) K dd * x * (detTwK lam B⁻¹ * detTwK lam B) := by rw [det_twist_inv_mul, mul_one]
        _ = (algebraMap (𝓞 K) K dd * detTwK lam B) * (detTwK lam B⁻¹ * x) := by ring
    show dd • x ∈ locRing w
    rw [e]
    exact (locRing w).mul_mem (hb w B hB).1 h1
  · choose B hB using fun τ => Formalism.L2.DIV.basisAtEx K n (M τ) (hM τ) w
    rw [mem_twLoc_iff lam M w B hB]
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
    have e : detTwK lam B⁻¹ * (dd • algebraMap (𝓞 K) K r) =
        (algebraMap (𝓞 K) K dd * detTwK lam B⁻¹) * algebraMap (𝓞 K) K r := by
      rw [Algebra.smul_def]
      ring
    rw [e]
    exact (locRing w).mul_mem (hb w B hB).2 (integer_mem_local_ring w r)

/- English proof (translation)
Take `⟨dd, hdd, h1, -⟩` from `twisted_localisation_comparable lam M hM`. Use `⟨dd, mem_nonZeroDivisors_of_ne_zero hdd, fun b hb => ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[twId_eq, Submodule.mem_iInf]`. Establish `hw : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K (dd • b) ≤ 1`. Introduce `w`.

Take `⟨s, hs, hx⟩` from `h1 w b (hb w)`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hx`. Establish `hs1 : w.intValuation s = 1` using `le_antisymm (w.intValuation_le_one s) (not_lt.1 fun h => hs ((w.intValuation_lt_one_iff_mem s).1 h))`. Establish `e : w.valuation K (dd • b) = w.valuation K (algebraMap (𝓞 K) K r)`. Rewrite using `[hr, Algebra.smul_def s, map_mul, HeightOneSpectrum.valuation_of_algebraMap, hs1, one_mul]`.

Rewrite using `[e]`. Conclude with `w.valuation_le_one r`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (x := dd • b) hw`. Conclude with `⟨y, hy⟩`.
-/
theorem twisted_ideal_fractional (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    IsFractional (nonZeroDivisors (𝓞 K)) (twId lam M) := by
  obtain ⟨dd, hdd, h1, -⟩ := twisted_localisation_comparable lam M hM
  refine ⟨dd, mem_nonZeroDivisors_of_ne_zero hdd, fun b hb => ?_⟩
  rw [twId_eq, Submodule.mem_iInf] at hb
  have hw : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K (dd • b) ≤ 1 := by
    intro w
    obtain ⟨s, hs, hx⟩ := h1 w b (hb w)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hx
    have hs1 : w.intValuation s = 1 :=
      le_antisymm (w.intValuation_le_one s) (not_lt.1 fun h => hs ((w.intValuation_lt_one_iff_mem s).1 h))
    have e : w.valuation K (dd • b) = w.valuation K (algebraMap (𝓞 K) K r) := by
      rw [hr, Algebra.smul_def s, map_mul, HeightOneSpectrum.valuation_of_algebraMap, hs1, one_mul]
    rw [e]
    exact w.valuation_le_one r
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (x := dd • b) hw
  exact ⟨y, hy⟩

def twIdeal (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨twId lam M, twisted_ideal_fractional lam M hM⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twIdeal_coe (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    (twIdeal lam M hM : Submodule (𝓞 K) K) = twId lam M := rfl

/- English proof (translation)
Introduce `h`. Take `⟨dd, hdd, -, h2⟩` from `twisted_localisation_comparable lam M hM`. Establish `hmem : dd • (1 : K) ∈ (twIdeal lam M hM : Submodule (𝓞 K) K)`. Rewrite using `[twIdeal_coe, twId_eq, Submodule.mem_iInf]`. Conclude with `fun w => h2 w 1 (Submodule.mem_one.2 ⟨1, map_one _⟩)`.

Rewrite `hmem` using `[h]`. Establish `h0 : dd • (1 : K) = 0` using `(FractionalIdeal.mem_zero_iff _).1 hmem`. Rewrite `h0` using `[Algebra.smul_def, mul_one]`. Conclude with `hdd ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h0)`.
-/
theorem twIdeal_ne_zero (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    twIdeal lam M hM ≠ 0 := by
  intro h
  obtain ⟨dd, hdd, -, h2⟩ := twisted_localisation_comparable lam M hM
  have hmem : dd • (1 : K) ∈ (twIdeal lam M hM : Submodule (𝓞 K) K) := by
    rw [twIdeal_coe, twId_eq, Submodule.mem_iInf]
    exact fun w => h2 w 1 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  rw [h] at hmem
  have h0 : dd • (1 : K) = 0 := (FractionalIdeal.mem_zero_iff _).1 hmem
  rw [Algebra.smul_def, mul_one] at h0
  exact hdd ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h0)

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[vAdd]`. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ← ih]`. Establish `h1 : w.valuation K (f a) ≠ 0` using `(Valuation.ne_zero_iff _).2 (hf a)`.

Establish `h2 : w.valuation K (∏ τ ∈ s, f τ) ≠ 0` using `(Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hf τ)`. Simplify using `only [vAdd, map_mul, WithZero.log_mul h1 h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valuation_finset_prod (w : HeightOneSpectrum (𝓞 K)) (f : ι → K) (hf : ∀ τ, f τ ≠ 0) (s : Finset ι) :
    vAdd w (∏ τ ∈ s, f τ) = ∑ τ ∈ s, vAdd w (f τ) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [vAdd]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    have h1 : w.valuation K (f a) ≠ 0 := (Valuation.ne_zero_iff _).2 (hf a)
    have h2 : w.valuation K (∏ τ ∈ s, f τ) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hf τ)
    simp only [vAdd, map_mul, WithZero.log_mul h1 h2]
    ring

variable [StarRing K] [IsTotallyComplex K]

/- English proof (translation)
Unfold `detTwK`. Rewrite using `[valuation_finset_prod w (fun τ => detPow K n (B τ) (lam τ).detShift) (fun τ => Units.ne_zero _)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, vAdd, map_zpow₀, WithZero.log_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valuation_det_twist (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) :
    vAdd w (detTwK lam B) = ∑ τ, (lam τ).detShift * vAdd w (B τ : Matrix (Fin n) (Fin n) K).det := by
  unfold detTwK
  rw [valuation_finset_prod w (fun τ => detPow K n (B τ) (lam τ).detShift) (fun τ => Units.ne_zero _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, vAdd, map_zpow₀,
    WithZero.log_zpow]
  ring

/- English proof (translation)
Establish `hA : Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (1 : K)) = (1 : Submodule (𝓞 K) K)`. Rewrite using `[Set.range_const, Submodule.one_eq_span]`. Establish `hlat : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (1 : K)))` using `brp_span_lattice K _ (by rw [Set.range_const]; exact Ideal.span_singleton_one)`. Rewrite using `[bridge_lidx_det_holds K K w _ (twId lam M) (LinearEquiv.smulOfNeZero K K (detTwK lam B) (det_twist_ne_zero lam B)) hlat ?_]`. Establish `e : ((LinearEquiv.smulOfNeZero K K (detTwK lam B) (det_twist_ne_zero lam B) : K ≃ₗ[K] K) : K →ₗ[K] K) = detTwK lam B • LinearMap.id` using `by ext; simp`.

Rewrite using `[e, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]`. Rewrite using `[localization_map₃, localisation_twisted_ideal lam M hM, hA]`. Use extensionality with `x`. Rewrite using `[mem_twLoc_iff lam M w B hB, mem_locRing]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Establish `e : detTwK lam B⁻¹ * (detTwK lam B • y) = y`. Rewrite using `[smul_eq_mul, ← mul_assoc, det_twist_inv_mul, one_mul]`. Simplify using `only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply]`. Rewrite using `[e]`.

Conclude with `hy`. Introduce `hx`. Use `⟨detTwK lam B⁻¹ * x, hx, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm (detTwK lam B), det_twist_inv_mul, one_mul]`.
-/
theorem local_index_twisted_ideal (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) :
    lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (1 : K))) (twId lam M) = vAdd w (detTwK lam B) := by
  have hA : Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (1 : K)) = (1 : Submodule (𝓞 K) K) := by
    rw [Set.range_const, Submodule.one_eq_span]
  have hlat : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (1 : K))) :=
    brp_span_lattice K _ (by rw [Set.range_const]; exact Ideal.span_singleton_one)
  rw [bridge_lidx_det_holds K K w _ (twId lam M) (LinearEquiv.smulOfNeZero K K (detTwK lam B) (det_twist_ne_zero lam B)) hlat ?_]
  · have e : ((LinearEquiv.smulOfNeZero K K (detTwK lam B) (det_twist_ne_zero lam B) : K ≃ₗ[K] K) : K →ₗ[K] K) =
        detTwK lam B • LinearMap.id := by
      ext; simp
    rw [e, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  · rw [localization_map₃, localisation_twisted_ideal lam M hM, hA]
    ext x
    rw [mem_twLoc_iff lam M w B hB, mem_locRing]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : detTwK lam B⁻¹ * (detTwK lam B • y) = y := by
        rw [smul_eq_mul, ← mul_assoc, det_twist_inv_mul, one_mul]
      simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply]
      rw [e]
      exact hy
    · intro hx
      refine ⟨detTwK lam B⁻¹ * x, hx, ?_⟩
      simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (detTwK lam B), det_twist_inv_mul, one_mul]

end Ideal

section Norm

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ} {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `: Nontrivial (Fin n → K)` using `Pi.nontrivial_at ⟨0, hn⟩`. Use `set es : Fin n → (Fin n → K) := fun i => Pi.single i 1 with hesdef`. Establish `hesb : es = ⇑(Pi.basisFun K (Fin n))` using `by funext i; simp [hesdef]`. Establish `hes : LinearIndependent K es` using `by rw [hesb]; exact (Pi.basisFun K (Fin n)).linearIndependent`. Establish `hspS : Submodule.span K (Set.range es) = ⊤` using `by rw [hesb]; exact (Pi.basisFun K (Fin n)).span_eq`.

Take `⟨hrk2, -, -, hfin2, hmu2⟩` from `Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) (Pi.basisFun K (Fin n)) (fun _ => 1) (fun _ => by simp) n es M hes hM.fg (isLattice_ne_bot hM) (by rw [hM.span_eq_top, hspS])`. Use `⟨hfin2, ?_⟩` and prove the remaining obligations. Rewrite using `[brp_latK_mu K M hM.fg]`. Use `show (n : ℝ) * muDef (Pi.basisFun K (Fin n)) (fun _ => 1) M = _`. Rewrite using `[hmu2, hrk2]`.

Unfold `Formalism.LFunctionChainParameters.LLcv.lcv Formalism.LFunctionChainParameters.LLcv.lcvFin`. Rewrite using `[brp_lcvInf_std]`. Establish `hnpos : (0 : ℝ) < (n : ℝ)` using `by exact_mod_cast hn`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lattice_slope_degree_formula (hn : 0 < n) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
      (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) M)).Finite ∧
    (n : ℝ) * (latK K M).mu = -(2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
        (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) M : ℝ))) := by
  classical
  have : Nontrivial (Fin n → K) := Pi.nontrivial_at ⟨0, hn⟩
  set es : Fin n → (Fin n → K) := fun i => Pi.single i 1 with hesdef
  have hesb : es = ⇑(Pi.basisFun K (Fin n)) := by funext i; simp [hesdef]
  have hes : LinearIndependent K es := by rw [hesb]; exact (Pi.basisFun K (Fin n)).linearIndependent
  have hspS : Submodule.span K (Set.range es) = ⊤ := by rw [hesb]; exact (Pi.basisFun K (Fin n)).span_eq
  obtain ⟨hrk2, -, -, hfin2, hmu2⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) (Pi.basisFun K (Fin n))
    (fun _ => 1) (fun _ => by simp) n es M hes hM.fg (isLattice_ne_bot hM) (by rw [hM.span_eq_top, hspS])
  refine ⟨hfin2, ?_⟩
  rw [brp_latK_mu K M hM.fg]
  show (n : ℝ) * muDef (Pi.basisFun K (Fin n)) (fun _ => 1) M = _
  rw [hmu2, hrk2]
  unfold Formalism.LFunctionChainParameters.LLcv.lcv Formalism.LFunctionChainParameters.LLcv.lcvFin
  rw [brp_lcvInf_std]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp
  ring

/- English proof (translation)
Use `set e1 : Fin 1 → K := fun _ => 1 with he1`. Establish `hli : LinearIndependent K e1` using `LinearIndependent.of_subsingleton (0 : Fin 1) one_ne_zero`. Establish `hId` using `Formalism.LFunctionChainParameters.LLcv.covolume_ideal K K Unit (Basis.singleton Unit K) 1 e1 (twIdeal lam M hM) hli one_pos (twIdeal_ne_zero lam M hM)`. Establish `hsm : idealSmul (twIdeal lam M hM : Submodule (𝓞 K) K) (Submodule.span (𝓞 K) (Set.range e1)) = twId lam M`. Rewrite using `[twIdeal_coe]`.

Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Rewrite `hx` using `[he1, Set.range_const, Submodule.mem_span_singleton]`. Take `⟨r, rfl⟩` from `hx`.

Establish `: a • r • (1 : K) = r • a`. Rewrite using `[smul_eq_mul, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ r ha`.

Introduce `a ha`. Use `Submodule.subset_span ⟨a, ha, 1, Submodule.subset_span ⟨0, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_one]`. Rewrite `hId` using `[hsm]`. Unfold `Formalism.LFunctionChainParameters.LLcv.lcvFin at hId`.

Establish `hterm : ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI` using `p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M)) = ∑ τ, (lam τ).detShift * (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) (M τ)) := by`. Introduce `p`. Use `p.2.isPrime` as an intermediate fact. Set `w : HeightOneSpectrum (𝓞 K)` to `⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩`. Use `choose B hB using fun τ => basisAtEx K n (M τ) (hM τ) w`.

Establish `h1 : lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M) = vAdd w (detTwK lam B)` using `local_index_twisted_ideal lam M hM w B hB`. Establish `h2 : ∀ τ, lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) (M τ) = vAdd w (B τ : Matrix (Fin n) (Fin n) K).det` using `fun τ => by`. Rewrite using `[← brp_colLat_one_span]`. Conclude with `brp_lidx_colLat K (M τ) w (B τ) (hB τ)`. Use `show lidx p.1 _ _ = ∑ τ, _ * lidx p.1 _ _`.

Rewrite using `[h1, valuation_det_twist]`. Conclude with `Finset.sum_congr rfl fun τ _ => by rw [h2 τ]`. Establish `hfin` using `fun τ => (lattice_slope_degree_formula K hn (M τ) (hM τ)).1`. Establish `hdeg` using `fun τ => (lattice_slope_degree_formula K hn (M τ) (hM τ)).2`. Simplify using `only [hdeg]`.

Establish `hsum : ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) * (haveI` using `p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M) : ℝ)) = ∑ τ, ((lam τ).detShift : ℝ) * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) * (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.ran …`. Simplify using `only [mul_finsum]`. Rewrite using `[← finsum_sum_comm]`. Use `finsum_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[hterm p]`.

Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => by ring`. Introduce `τ _`. Use `(hfin τ).subset fun p hp => ?_` and prove the remaining obligations.

Simplify using `only [Function.mem_support] at hp ⊢`. Introduce `h'`. Apply `hp` to reduce the goal to its premises. Rewrite using `[h']`. Simplify using the standard rewrite rules.

Rewrite `hId` using `[hsum]`. Establish `e : 2 * Real.log (FractionalIdeal.absNorm (twIdeal lam M hM) : ℝ) / (Module.finrank ℚ K : ℝ) = 2 * ((1 : ℕ) : ℝ) * Real.log (FractionalIdeal.absNorm (twIdeal lam M hM) : ℝ) / (Module.finrank ℚ K : ℝ)`. Rewrite using `[Nat.cast_one, mul_one]`. Rewrite using `[e, ← hId, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun τ _ => by ring`.
-/
theorem twisted_ideal_norm_formula (hn : 0 < n) (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    -(2 * Real.log (FractionalIdeal.absNorm (twIdeal lam M hM) : ℝ) / (Module.finrank ℚ K : ℝ)) =
      ∑ τ, ((lam τ).detShift : ℝ) * ((n : ℝ) * (latK K (M τ)).mu) := by
  classical
  set e1 : Fin 1 → K := fun _ => 1 with he1
  have hli : LinearIndependent K e1 := LinearIndependent.of_subsingleton (0 : Fin 1) one_ne_zero
  have hId := Formalism.LFunctionChainParameters.LLcv.covolume_ideal K K Unit (Basis.singleton Unit K) 1 e1 (twIdeal lam M hM) hli one_pos
    (twIdeal_ne_zero lam M hM)
  have hsm : idealSmul (twIdeal lam M hM : Submodule (𝓞 K) K) (Submodule.span (𝓞 K) (Set.range e1)) = twId lam M := by
    rw [twIdeal_coe]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, x, hx, rfl⟩
      rw [he1, Set.range_const, Submodule.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      have : a • r • (1 : K) = r • a := by
        rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact Submodule.smul_mem _ r ha
    · intro a ha
      refine Submodule.subset_span ⟨a, ha, 1, Submodule.subset_span ⟨0, rfl⟩, ?_⟩
      rw [smul_eq_mul, mul_one]
  rw [hsm] at hId
  unfold Formalism.LFunctionChainParameters.LLcv.lcvFin at hId
  have hterm : ∀ p : {p : Ideal (𝓞 K) // p.IsMaximal},
      (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M)) =
        ∑ τ, (lam τ).detShift * (haveI := p.2.isPrime;
          lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) (M τ)) := by
    intro p
    have := p.2.isPrime
    let w : HeightOneSpectrum (𝓞 K) :=
      ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
    choose B hB using fun τ => basisAtEx K n (M τ) (hM τ) w
    have h1 : lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M) = vAdd w (detTwK lam B) :=
      local_index_twisted_ideal lam M hM w B hB
    have h2 : ∀ τ, lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) (M τ) =
        vAdd w (B τ : Matrix (Fin n) (Fin n) K).det := fun τ => by
      rw [← brp_colLat_one_span]
      exact brp_lidx_colLat K (M τ) w (B τ) (hB τ)
    show lidx p.1 _ _ = ∑ τ, _ * lidx p.1 _ _
    rw [h1, valuation_det_twist]
    exact Finset.sum_congr rfl fun τ _ => by rw [h2 τ]
  have hfin := fun τ => (lattice_slope_degree_formula K hn (M τ) (hM τ)).1
  have hdeg := fun τ => (lattice_slope_degree_formula K hn (M τ) (hM τ)).2
  simp only [hdeg]
  have hsum : ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
      (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e1)) (twId lam M) : ℝ)) =
      ∑ τ, ((lam τ).detShift : ℝ) * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
        (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) * (haveI := p.2.isPrime;
          (lidx p.1 (Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))) (M τ) : ℝ)) := by
    simp only [mul_finsum]
    rw [← finsum_sum_comm]
    · refine finsum_congr fun p => ?_
      rw [hterm p]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    · intro τ _
      refine (hfin τ).subset fun p hp => ?_
      simp only [Function.mem_support] at hp ⊢
      intro h'
      apply hp
      rw [h']
      simp
  rw [hsum] at hId
  have e : 2 * Real.log (FractionalIdeal.absNorm (twIdeal lam M hM) : ℝ) / (Module.finrank ℚ K : ℝ) =
      2 * ((1 : ℕ) : ℝ) * Real.log (FractionalIdeal.absNorm (twIdeal lam M hM) : ℝ) / (Module.finrank ℚ K : ℝ) := by
    rw [Nat.cast_one, mul_one]
  rw [e, ← hId, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

end Norm

end Formalism.L2.Col
