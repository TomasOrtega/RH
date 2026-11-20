import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

/- English proof (translation)
Unfold `bideterminant initMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ N ν _`. Establish `hmax : (Ideal.span {ϖ}).IsMaximal`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal O`. Use `letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`.

Establish `hdom : IsDomain (O ⧸ Ideal.span {ϖ})` using `Ideal.Quotient.isDomain _`. Prove the components needed by the constructor for the conclusion. Introduce `f hf`. Rewrite `hf` using `[standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν]`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hsh, rfl⟩` from `hx`. Use `⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩` and prove the remaining obligations. Rewrite using `[← hsh]`. Conclude with `bidetMem O N N K sz hsz I`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, Submodule.add_mem _ ha hb, by simp⟩`.

Consider the case `smul c x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]`.

Introduce `g hg h0`. Establish `hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})))` using `h0`. Rewrite `hk` using `[MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨h, hh⟩` from `hk`. Establish `hgh : g = ϖ • h` using `by rw [smul_eq_C_mul, ← hh, mul_comm]`.

Use `⟨h, ?_, hgh⟩` and prove the remaining obligations. Conclude with `dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)`.
-/
theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
