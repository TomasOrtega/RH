import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
open NumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM GlobalTheory.CM.IntCoord

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat

/- English proof (translation)
Introduce `E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he`. Take `⟨n, hn, x, hx, f, hf, hfn⟩` from `hc`. Establish `hcA` using `integral_tangent_coordinates K _ FP`. Establish `hcB` using `integral_tangent_coordinates K _ FB`. Take `⟨u, hu, heig⟩` from `(hcA.2.2.2.2.2 _ _ τ e).1 he`.

Use `hf.isMonHom` as an intermediate fact. Establish `ht : IsTangent (u ≫ f)`. Establish `hv` using `hu.1`. Unfold `IsTangent at hv ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]`.

Take `⟨d, hd, -⟩` from `hcB.1 _ ht`. Establish `hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e))`. Introduce `a`. Rewrite using `[← Category.assoc]`. Conclude with `hMP a _ _ (isCoord_smul FP hu (heig (x a)))`.

Establish `hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a)) (∑ a ∈ s, MP a (τ (x a) • e))`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, Finset.sum_empty, comp_one]`.

Conclude with `isCoord_one FB`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]`. Conclude with `isCoord_mul FB (hs a) ih`. Establish `hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_smul]`. Conclude with `isCoord_one FB`.

Consider the case `succ m ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isCoord_mul FB ih hd`. Establish `heq : n • d = ∑ a, MP a (τ (x a) • e)`. Establish `h1` using `hpow n`.

Rewrite `h1` using `[← comp_pow, hfn]`. Conclude with `(hcB.1 _ h1.1).unique h1 (hprod Finset.univ)`. Establish `hdval : d = ∑ a, τE (c a) • MP a e`. Establish `hn0 : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Use `smul_right_injective _ hn0 ?_` and prove the remaining obligations.

Use `show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e`. Rewrite using `[Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]`. Use `congr 1`.

Use `show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)`. Rewrite using `[← hτE, hx a, map_mul, map_natCast]`. Rewrite using `[← hdval]`. Use `(hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s), Category.assoc]`.
-/
theorem sum_smul_diff_mem_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he
  obtain ⟨n, hn, x, hx, f, hf, hfn⟩ := hc
  have hcA := integral_tangent_coordinates K _ FP
  have hcB := integral_tangent_coordinates K _ FB
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have := hf.isMonHom
  have ht : IsTangent (u ≫ f) := by
    have hv := hu.1
    unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨d, hd, -⟩ := hcB.1 _ ht
  have hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FP hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have heq : n • d = ∑ a, MP a (τ (x a) • e) := by
    have h1 := hpow n
    rw [← comp_pow, hfn] at h1
    exact (hcB.1 _ h1.1).unique h1 (hprod Finset.univ)
  have hdval : d = ∑ a, τE (c a) • MP a e := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine smul_right_injective _ hn0 ?_
    show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e
    rw [Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]
    congr 1
    show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)
    rw [← hτE, hx a, map_mul, map_natCast]
  rw [← hdval]
  refine (hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s),
    Category.assoc]

end GlobalTheory.FlatCM.HomLat
