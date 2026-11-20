import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivRegularFunctionsAffineOpenStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hN`. Take `⟨M, hM, hle⟩` from `(eq_top_or_exists_le_coatom (LinearMap.range (LinearMap.pi fun a => (d a).liftKaehlerDifferential))).resolve_left hN`. Establish `hs : IsSimpleModule B ((J → B) ⧸ M)` using `isSimpleModule_iff_isCoatom.2 hM`. Take `⟨e, he, hw⟩` from `h (Module.annihilator B ((J → B) ⧸ M)) IsSimpleModule.annihilator_isMaximal`.

Set `φ : B →ₗ[K] (J → K)` to `LinearMap.pi fun a => e.toLinearMap ∘ₗ (d a).toLinearMap`. Establish `hφ : LinearMap.range φ = ⊤`. Assume the negation of the conclusion as `hφ`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hφ)`. Establish `hfy : ∀ y : J → K, f y = ∑ a, y a * f (Pi.single a 1)`.

Introduce `y`. Use `conv_lhs => rw [pi_eq_sum_univ' y]`. Simplify using `[map_sum]`. Establish `h0` using `hw (fun a => f (Pi.single a 1)) fun x => by`. Establish `: f (φ x) = 0` using `hf ⟨x, rfl⟩`.

Rewrite `this` using `[hfy]`. Conclude with `this`. Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[hfy]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[congrFun h0 a]`. Simplify using the standard rewrite rules. Apply `hM.1` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Take `⟨x, hx⟩` from `LinearMap.range_eq_top.1 hφ fun a => e (y a)`. Establish `h1 : (fun a => d a x) ∈ M`. Use `hle ⟨KaehlerDifferential.D K B x, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Establish `h2 : y - (fun a => d a x) ∈ M`. Rewrite using `[pi_eq_sum_univ' (y - fun a => d a x)]`. Use `M.sum_mem fun a _ => ?_` and prove the remaining obligations. Establish `hm : (y - fun a => d a x) a ∈ Module.annihilator B ((J → B) ⧸ M)`.

Apply `he` to reduce the goal to its premises. Establish `: e (d a x) = e (y a)` using `congrFun hx a`. Simplify using `[this]`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]`. Conclude with `Module.mem_annihilator.1 hm _`.

Simplify using `using M.add_mem h2 h1`.
-/
theorem surjective_pi_liftKaehler_of_pointwise {K B J : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype J] [DecidableEq J]
    (d : J → Derivation K B B)
    (h : ∀ m : Ideal B, m.IsMaximal → ∃ e : B →ₐ[K] K, (∀ b, e b = 0 → b ∈ m) ∧
      ∀ w : J → K, (∀ x, ∑ a, e (d a x) * w a = 0) → w = 0) :
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  rw [← LinearMap.range_eq_top]
  by_contra hN
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom
    (LinearMap.range (LinearMap.pi fun a => (d a).liftKaehlerDifferential))).resolve_left hN
  have hs : IsSimpleModule B ((J → B) ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨e, he, hw⟩ := h (Module.annihilator B ((J → B) ⧸ M)) IsSimpleModule.annihilator_isMaximal
  let φ : B →ₗ[K] (J → K) := LinearMap.pi fun a => e.toLinearMap ∘ₗ (d a).toLinearMap
  have hφ : LinearMap.range φ = ⊤ := by
    by_contra hφ
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hφ)
    have hfy : ∀ y : J → K, f y = ∑ a, y a * f (Pi.single a 1) := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ' y]
      simp [map_sum]
    have h0 := hw (fun a => f (Pi.single a 1)) fun x => by
      have : f (φ x) = 0 := hf ⟨x, rfl⟩
      rw [hfy] at this
      exact this
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfy]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [congrFun h0 a]
    simp
  apply hM.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hφ fun a => e (y a)
  have h1 : (fun a => d a x) ∈ M := by
    refine hle ⟨KaehlerDifferential.D K B x, ?_⟩
    funext a
    simp
  have h2 : y - (fun a => d a x) ∈ M := by
    rw [pi_eq_sum_univ' (y - fun a => d a x)]
    refine M.sum_mem fun a _ => ?_
    have hm : (y - fun a => d a x) a ∈ Module.annihilator B ((J → B) ⧸ M) := by
      apply he
      have : e (d a x) = e (y a) := congrFun hx a
      simp [this]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hm _
  simpa using M.add_mem h2 h1

/- English proof (translation)
Introduce `A _ g L u hA U d hd`. Use `surjective_pi_liftKaehler_of_pointwise d fun m hm => ?_` and prove the remaining obligations. Take `⟨z, hz, hm'⟩` from `GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA U.1 U.2 m hm`. Take `⟨e, he⟩` from `(GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz`. Use `⟨e, fun b hb => (hm' b).2 ((he b).trans hb), fun w hw => ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen A g L u hA U.1 U.2 z hz w fun b => ?_` and prove the remaining obligations. Rewrite using `[← hw b]`. Use `conv_lhs => rw [pi_eq_sum_univ' w]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Conclude with `congrArg (· * w a) ((hd a b z hz).symm.trans (he _))`.
-/
theorem surjective_pi_liftKaehler_coord : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)),
    (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) →
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  intro A _ g L u hA U d hd
  refine surjective_pi_liftKaehler_of_pointwise d fun m hm => ?_
  obtain ⟨z, hz, hm'⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA U.1 U.2 m hm
  obtain ⟨e, he⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
  refine ⟨e, fun b hb => (hm' b).2 ((he b).trans hb), fun w hw => ?_⟩
  refine GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen A g L u hA U.1 U.2 z hz w fun b => ?_
  rw [← hw b]
  conv_lhs => rw [pi_eq_sum_univ' w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (· * w a) ((hd a b z hz).symm.trans (he _))

end GlobalTheory.CechPer
