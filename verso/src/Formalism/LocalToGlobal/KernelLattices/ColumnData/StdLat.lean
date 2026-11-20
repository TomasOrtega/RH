import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData

noncomputable section

namespace Formalism.L2.Ker.Cd.Inhab

open Formalism.BasicNotions NumberField

variable (D : Car)

/- English proof (translation)
Simplify using `[Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]`.
-/
theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  simp [Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]

/- English proof (translation)
Rewrite using `[mem_stdL]`. Introduce `i`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`.

Conclude with `one_mem _`. Simplify using `only [Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.
-/
theorem single_mem_stdL {N : ℕ} (a : Fin N) : (Pi.single a 1 : Fin N → D.host.E) ∈ Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N := by
  rw [mem_stdL]
  intro i
  by_cases h : i = a
  · subst h
    simp only [Pi.single_eq_same]
    exact one_mem _
  · simp only [Pi.single_eq_of_ne h]
    exact zero_mem _

/- English proof (translation)
Use `letI := D.host.cmStar`. Take `⟨y, rfl⟩` from `RingHom.mem_range.1 h`. Establish `hi : IsIntegral ℤ (star (algebraMap (𝓞 D.host.E) D.host.E y))` using `(NumberField.RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom`. Conclude with `RingHom.mem_range.2 ⟨⟨_, hi⟩, rfl⟩`.
-/
theorem star_mem_range (x : D.host.E) (h : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    (letI := D.host.cmStar; star x) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  letI := D.host.cmStar
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 h
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 D.host.E) D.host.E y)) :=
    (NumberField.RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom
  exact RingHom.mem_range.2 ⟨⟨_, hi⟩, rfl⟩

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hspan : Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N = Submodule.span (𝓞 D.host.E) (Set.range fun i : Fin N => (Pi.single i 1 : Fin N → D.host.E))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`.

Rewrite `hy` using `[mem_stdL]`. Establish `hy' : ∀ i, ∃ z, algebraMap (𝓞 D.host.E) D.host.E z = y i` using `fun i => RingHom.mem_range.1 (hy i)`. Use `choose z hz using hy'`. Establish `hyz : y = ∑ i, z i • (Pi.single i 1 : Fin N → D.host.E)`. Use function extensionality and compare the values at `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply, ← hz j, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[hyz]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `single_mem_stdL D i`. Rewrite using `[hspan]`. Conclude with `Submodule.fg_span (Set.finite_range _)`. Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`.

Rewrite using `[← (Pi.basisFun D.host.E (Fin N)).sum_repr v]`. Use `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply]`. Conclude with `single_mem_stdL D i`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Rewrite `hx`, `hy` using `[mem_stdL]`. Simplify using `only [stdH]`. Use `Subring.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations.

Use `first`. Consider the case `exact Subring.mul_mem _ (star_mem_range D _ (hx i)) (hy i)`. Consider the case `exact Subring.mul_mem _ (hx i) (star_mem_range D _ (hy i))`. Consider the case `exact Subring.mul_mem _ (hy i) (star_mem_range D _ (hx i))`. Consider the case `exact Subring.mul_mem _ (star_mem_range D _ (hy i)) (hx i)`.

Introduce `h`. Rewrite using `[mem_stdL]`. Introduce `i`. Use `h _ (single_mem_stdL D i)` as an intermediate fact. Simplify using `only [stdH] at this`.

Rewrite `this` using `[Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_eq_of_ne hj])]`. Simplify using `only [Pi.single_eq_same, star_one, one_mul, mul_one] at this`. Use `first`. Consider the case `exact this`. Consider the case `simpa using star_mem_range D _ this`.
-/
theorem stdL_isSD (N : ℕ) : (letI := D.host.cmStar; IsSDLat D.host.E N (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N)) := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · have hspan : Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N = Submodule.span (𝓞 D.host.E)
        (Set.range fun i : Fin N => (Pi.single i 1 : Fin N → D.host.E)) := by
      apply le_antisymm
      · intro y hy
        rw [mem_stdL] at hy
        have hy' : ∀ i, ∃ z, algebraMap (𝓞 D.host.E) D.host.E z = y i := fun i => RingHom.mem_range.1 (hy i)
        choose z hz using hy'
        have hyz : y = ∑ i, z i • (Pi.single i 1 : Fin N → D.host.E) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply, ← hz j, Algebra.algebraMap_eq_smul_one]
        rw [hyz]
        exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact single_mem_stdL D i
    rw [hspan]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff]
    rintro v -
    rw [← (Pi.basisFun D.host.E (Fin N)).sum_repr v]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    rw [Pi.basisFun_apply]
    exact single_mem_stdL D i
  · intro y
    constructor
    · intro hy x hx
      rw [mem_stdL] at hx hy
      simp only [stdH]
      refine Subring.sum_mem _ (fun i _ => ?_)
      first
        | exact Subring.mul_mem _ (star_mem_range D _ (hx i)) (hy i)
        | exact Subring.mul_mem _ (hx i) (star_mem_range D _ (hy i))
        | exact Subring.mul_mem _ (hy i) (star_mem_range D _ (hx i))
        | exact Subring.mul_mem _ (star_mem_range D _ (hy i)) (hx i)
    · intro h
      rw [mem_stdL]
      intro i
      have := h _ (single_mem_stdL D i)
      simp only [stdH] at this
      rw [Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_eq_of_ne hj])] at this
      simp only [Pi.single_eq_same, star_one, one_mul, mul_one] at this
      first
        | exact this
        | simpa using star_mem_range D _ this

/- English proof (translation)
Conclude with `⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩`.
-/
theorem Adm_std (N N' : ℕ) (h : Even N) (h' : Even N') :
    Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') := by
  exact ⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩

end Formalism.L2.Ker.Cd.Inhab
