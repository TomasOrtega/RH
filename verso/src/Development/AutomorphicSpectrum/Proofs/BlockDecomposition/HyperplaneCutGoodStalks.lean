import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

section Alg

open Pointwise

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, hk]`. Simplify using the standard rewrite rules.
-/
theorem smul_top_eq_ker (π : M →ₗ[R] N) (a : R) (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) :
    a • (⊤ : Submodule R M) = LinearMap.ker π := by
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, hk]
  simp

/- English proof (translation)
The claim follows from `(((Submodule.quotEquivOfEq _ _ (smul_top_eq_ker π a hk)).trans (π.quotKerEquivOfSurjective hπ)).isWeaklyRegular_congr l).1 h`.
-/
theorem isWeaklyRegular_of_quotSMulTop (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop a M) l) :
    RingTheory.Sequence.IsWeaklyRegular N l :=
  (((Submodule.quotEquivOfEq _ _ (smul_top_eq_ker π a hk)).trans
    (π.quotKerEquivOfSurjective hπ)).isWeaklyRegular_congr l).1 h

/- English proof (translation)
Establish `hf : Function.Surjective ((J • ⊤ : Submodule R N).mkQ ∘ₗ π)` using `(Submodule.mkQ_surjective _).comp hπ`. Establish `hker : (Ideal.span {a} ⊔ J) • (⊤ : Submodule R M) = LinearMap.ker ((J • ⊤ : Submodule R N).mkQ ∘ₗ π)`. Establish `hmap : (J • ⊤ : Submodule R N) = (J • ⊤ : Submodule R M).map π`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]`. Rewrite using `[LinearMap.ker_comp, Submodule.ker_mkQ, hmap, Submodule.comap_map_eq, Submodule.sup_smul, Submodule.ideal_span_singleton_smul, smul_top_eq_ker π a hk, sup_comm]`.

Conclude with `(((Submodule.quotEquivOfEq _ _ hker).trans (((J • ⊤ : Submodule R N).mkQ ∘ₗ π).quotKerEquivOfSurjective hf)).length_eq).symm`.
-/
theorem length_quot_eq_of_cut (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (J : Ideal R) :
    Module.length R (N ⧸ (J • ⊤ : Submodule R N)) =
      Module.length R (M ⧸ ((Ideal.span {a} ⊔ J) • ⊤ : Submodule R M)) := by
  have hf : Function.Surjective ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  have hker : (Ideal.span {a} ⊔ J) • (⊤ : Submodule R M) =
      LinearMap.ker ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) := by
    have hmap : (J • ⊤ : Submodule R N) = (J • ⊤ : Submodule R M).map π := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hmap, Submodule.comap_map_eq, Submodule.sup_smul,
      Submodule.ideal_span_singleton_smul, smul_top_eq_ker π a hk, sup_comm]
  exact (((Submodule.quotEquivOfEq _ _ hker).trans
    (((J • ⊤ : Submodule R N).mkQ ∘ₗ π).quotKerEquivOfSurjective hf)).length_eq).symm

end Alg

section Cut

variable {X : Scheme.{0}} {L : LB X}

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp`.
-/
theorem germSec_cons {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    (fun j => germSec ((Fin.cons s t : Fin (d + 1) → L.Sec) j) hx) =
      (Fin.cons (germSec s hx) (fun j => germSec (t j) hx) :
        Fin (d + 1) → X.presheaf.stalk x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/- English proof (translation)
Use `(mono_cutHom_iff F hL s).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `GlobalTheory.ThickeningDetermines.exists_mem_chart hL x`. Take `⟨u, hu⟩` from `mem_assPoints_iff_exists.1 hx`. Use `(Cartier.mem_nonzeroLocus_iff s i hi).2 ((X.mem_basicOpen _ x hi).2 ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Establish `hm : germSec s hi ∈ maximalIdeal (X.presheaf.stalk x)` using `hn`. Establish `h0 : u = 0` using `(h x i hi).right_eq_zero_of_smul ((hu _).2 hm)`. Conclude with `(maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 ((hu 1).1 (by simp [h0])))`.
-/
theorem mono_cutHom_of_isSMulRegular [IsLocallyNoetherian X] (hL : L.IsLB) (F : X.Modules)
    [F.IsQuasicoherent] (s : L.Sec)
    (h : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i), IsSMulRegular (F.presheaf.stalk x :) (germSec s hx)) :
    Mono (cutHom F hL s) := by
  refine (mono_cutHom_iff F hL s).2 fun x hx => ?_
  obtain ⟨i, hi⟩ := GlobalTheory.ThickeningDetermines.exists_mem_chart hL x
  obtain ⟨u, hu⟩ := mem_assPoints_iff_exists.1 hx
  refine (Cartier.mem_nonzeroLocus_iff s i hi).2 ((X.mem_basicOpen _ x hi).2 ?_)
  by_contra hn
  have hm : germSec s hi ∈ maximalIdeal (X.presheaf.stalk x) := hn
  have h0 : u = 0 := (h x i hi).right_eq_zero_of_smul ((hu _).2 hm)
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 ((hu 1).1 (by simp [h0])))

end Cut

/- English proof (translation)
Establish `key : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i), IsSMulRegular (F.presheaf.stalk x :) (germSec s hx) ∧ RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop (germSec s hx) (F.presheaf.stalk x :)) (List.ofFn fun j => germSec (t j) hx)` using `fun x i hx => by`. Establish `h₁` using `(h x i hx).1`. Rewrite `h₁` using `[germSec_cons, List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff]`. Conclude with `h₁`. Use `⟨mono_cutHom_of_isSMulRegular hL F s fun x i hx => (key x i hx).1, fun x i hx => ?_⟩` and prove the remaining obligations.

Establish `hπ` using `stalkLinear_surjective (cutπ F hL s) x`. Establish `hk` using `(isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx`. Use `⟨isWeaklyRegular_of_quotSMulTop (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk _ (key x i hx).2, ?_⟩` and prove the remaining obligations. Establish `h₂` using `(h x i hx).2`. Rewrite `h₂` using `[germSec_cons, Fin.range_cons, Ideal.span_insert]`.

Rewrite using `[length_quot_eq_of_cut (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk]`. Conclude with `h₂`.
-/
theorem mono_cutHom_and_goodStalks_cut {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB)
    (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec)
    (h : GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec)) :
    Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  have key : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
      IsSMulRegular (F.presheaf.stalk x :) (germSec s hx) ∧
        RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop (germSec s hx) (F.presheaf.stalk x :))
          (List.ofFn fun j => germSec (t j) hx) := fun x i hx => by
    have h₁ := (h x i hx).1
    rw [germSec_cons, List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff] at h₁
    exact h₁
  refine ⟨mono_cutHom_of_isSMulRegular hL F s fun x i hx => (key x i hx).1, fun x i hx => ?_⟩
  have hπ := stalkLinear_surjective (cutπ F hL s) x
  have hk := (isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx
  refine ⟨isWeaklyRegular_of_quotSMulTop (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk _
    (key x i hx).2, ?_⟩
  have h₂ := (h x i hx).2
  rw [germSec_cons, Fin.range_cons, Ideal.span_insert] at h₂
  rw [length_quot_eq_of_cut (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount
