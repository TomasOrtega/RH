import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

/- English proof (translation)
Conclude with `(Sec.res s h).commutes r`.
-/
theorem resG_secMap_lin {U V : Z.Opens} (h : V ≤ U) (r : R) :
    resG Z h ((secMap s U).hom r) = (secMap s V).hom r := by
  exact (Sec.res s h).commutes r

/- English proof (translation)
Rewrite using `[map_sub, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, resG_secMap_lin]`.
-/
theorem resG_sub_sum_lin {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) {N : ℕ} (r : Fin N → R)
    (y : Fin N → Γ(Z, U)) :
    resG Z h (x - ∑ k, (secMap s U).hom (r k) * y k) =
      resG Z h x - ∑ k, (secMap s V).hom (r k) * resG Z h (y k) := by
  rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, resG_secMap_lin]

/- English proof (translation)
Introduce `i i' i''`. Use `beta_reduce`. Rewrite using `[resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]`. Simplify using `only [← hc i i' i'', ← he _ i i' i'', mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isCocycle_sub_sum_lin {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {N : ℕ}
    (r : Fin N → R) {e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')} (he : ∀ k, IsCocycle W (e k)) :
    IsCocycle W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') := by
  intro i i' i''
  beta_reduce
  rw [resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]
  simp only [← hc i i' i'', ← he _ i i' i'', mul_add,
    Finset.sum_add_distrib]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `V V' a`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def]`. Conclude with `resG_sub_sum_lin s _ _ r _`.
-/
theorem fc_sub_sum_lin (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {N : ℕ}
    (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')) :
    fc s W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') =
      fc s W c - ∑ k, r k • fc s W (e k) := by
  funext V V' a
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  exact resG_sub_sum_lin s _ _ r _

/- English proof (translation)
Introduce `R _ Z s J W hW c hc N r e he`. Rewrite using `[cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]`. Simplify using `only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]`. Use `congr 2`. Use `Subtype.ext ?_` and prove the remaining obligations.

Simplify using `only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]`. Conclude with `fc_sub_sum_lin s W c r e`.
-/
theorem cmp_sub_sum_lin : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  intro R _ Z s J W hW c hc N r e he
  rw [cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]
  simp only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]
  congr 2
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  exact fc_sub_sum_lin s W c r e

end GlobalTheory.CechCmp
