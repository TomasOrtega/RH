import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

/- English proof (translation)
Take `⟨D, hD, hDe⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E`. Use `set d : E := algebraMap F E (D : F) with hd`. Establish `hd0 : d ≠ 0`. Rewrite using `[hd]`. Introduce `h`.

Conclude with `hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))`. Establish `hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range`. Introduce `k`. Use `hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis.

Set `f : 𝓞 E →ₗ[ℤ] E` to `LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ`. Establish `hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f`. Introduce `x hx`. Rewrite `hx` using `[Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `hx`.

Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]`. Use `Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Take `⟨y, hy⟩` from `hpow k`. Conclude with `⟨y, by simp [f, hy, hd0]⟩`. Establish `: IsNoetherian ℤ (LinearMap.range f)`.

Conclude with `isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)`. Establish `: IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule` using `isNoetherian_of_le hS`. Establish `hint : IsIntegral ℤ e` using `isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e (Algebra.subset_adjoin (Set.mem_singleton e))`. Conclude with `⟨⟨e, hint⟩, rfl⟩`.
-/
theorem bwL_descent (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E)
    (he : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.inclE (F := F) (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AF F) e ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.SS F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨D, hD, hDe⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  set d : E := algebraMap F E (D : F) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; intro h
    exact hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))
  have hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range := by
    intro k
    have := hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)
    rwa [Algebra.smul_def] at this
  let f : 𝓞 E →ₗ[ℤ] E := LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
  have hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    obtain ⟨y, hy⟩ := hpow k
    exact ⟨y, by simp [f, hy, hd0]⟩
  have : IsNoetherian ℤ (LinearMap.range f) := by
    exact isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have : IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule := isNoetherian_of_le hS
  have hint : IsIntegral ℤ e :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e
      (Algebra.subset_adjoin (Set.mem_singleton e))
  exact ⟨⟨e, hint⟩, rfl⟩

variable (D : D7) (u : D.what₂.Word)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `i hi c x hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Introduce `x' hx'`. Establish `hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat ((Tt.cls i hi).y c).1 (Tt.cls i hi).lev.Lb`. Introduce `z hz`.

Conclude with `((Tt.cls i hi).y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)`. Establish `hm : ∀ a ∈ (Tt.cls i hi).lev.Lb, ∀ b ∈ (Tt.cls i hi).lev.Lb, IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b)`. Introduce `a ha b hb`. Take `⟨r, hr⟩` from `(Tt.cls i hi).lev.Lb_int b hb a ha`. Rewrite using `[Int.cast_one, one_mul, ← hr]`.

Conclude with `RingOfIntegers.isIntegral_coe r`. Establish `h` using `Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) (Tt.cls i hi).lev.Lb 1 hm ((Tt.cls i hi).y c).1 ((Tt.cls i hi).y c).2 (hglob x' hx') (hglob x hx)`. Rewrite `h` using `[Int.cast_one, one_mul]`. Conclude with `bwL_descent _ _ _ h`.
-/
theorem bwL_lcInt (Tt : FormsTied D u) : BwLcInt D u := by
  intro i hi c x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat ((Tt.cls i hi).y c).1 (Tt.cls i hi).lev.Lb := by
    intro z hz
    exact ((Tt.cls i hi).y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ (Tt.cls i hi).lev.Lb, ∀ b ∈ (Tt.cls i hi).lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := (Tt.cls i hi).lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) (Tt.cls i hi).lev.Lb 1 hm ((Tt.cls i hi).y c).1
    ((Tt.cls i hi).y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
