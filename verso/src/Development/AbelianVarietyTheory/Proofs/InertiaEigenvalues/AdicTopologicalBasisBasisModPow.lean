import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
It suffices to establish `h : ∀ r : A, tb.c j (r * y) ∈ I ^ m by simpa using h 1`. Use `Submodule.span_induction (p := fun y _ => ∀ r : A, tb.c j (r * y) ∈ I ^ m) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩ r`. Rewrite using `[mul_comm, tb.c_mul]`. Conclude with `Ideal.mul_mem_right _ _ ha`.

Introduce `r`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy r`. Rewrite using `[mul_add, map_add]`. Conclude with `Ideal.add_mem _ (hx r) (hy r)`.

Introduce `a x _ hx r`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx (r * a)`.
-/
private theorem TopBasis.c_mem_of_mem_map_pow {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (tb : TopBasis s I ι) (m : ℕ) (j : ι) {y : A} (hy : y ∈ (I ^ m).map s) : tb.c j y ∈ I ^ m := by
  suffices h : ∀ r : A, tb.c j (r * y) ∈ I ^ m by simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r : A, tb.c j (r * y) ∈ I ^ m) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ r
    rw [mul_comm, tb.c_mul]
    exact Ideal.mul_mem_right _ _ ha
  · intro r; simp
  · intro x y _ _ hx hy r
    rw [mul_add, map_add]
    exact Ideal.add_mem _ (hx r) (hy r)
  · intro a x _ hx r
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (r * a)

/- English proof (translation)
Introduce `S A _ _ s I ι tb m`. Use `letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra`. Establish `hsmul : ∀ (a : S) (x : A), (Ideal.Quotient.mk (I ^ m) a) • (Ideal.Quotient.mk ((I ^ m).map s) x) = Ideal.Quotient.mk ((I ^ m).map s) (s a * x)`. Introduce `a x`. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]`.

Establish `hli : LinearIndependent (S ⧸ I ^ m) (fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i))`. Rewrite using `[linearIndependent_iff']`. Introduce `F g hg j hj`. Use `choose h hh using fun i => Ideal.Quotient.mk_surjective (I := I ^ m) (g i)`. Establish `hsum : (∑ i ∈ F, s (h i) * tb.b i) ∈ (I ^ m).map s`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hh i, hsmul]`. Establish `hc` using `tb.c_mem_of_mem_map_pow m j hsum`. Rewrite `hc` using `[map_sum, Finset.sum_eq_single j]`.

Rewrite `hc` using `[tb.c_mul, tb.c_self, mul_one]`. Rewrite using `[← hh j]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hc`. Introduce `i _ hij`. Rewrite using `[tb.c_mul, tb.c_ne j i (Ne.symm hij), mul_zero]`.

Introduce `h'`. Conclude with `(h' hj).elim`. Establish `hsp : ⊤ ≤ Submodule.span (S ⧸ I ^ m) (Set.range fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i))`. Introduce and unpack `x -`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Establish `hF : ∀ i, i ∉ (tb.fin y m).toFinset → tb.c i y ∈ I ^ m`. Introduce `i hi`. Simplify using `using hi`. Establish `hx` using `tb.approx y m (tb.fin y m).toFinset hF`. Establish `: Ideal.Quotient.mk ((I ^ m).map s) y = ∑ i ∈ (tb.fin y m).toFinset, (Ideal.Quotient.mk (I ^ m) (tb.c i y)) • Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)`.

Repeatedly rewrite using `[hsmul, ← map_sum]`. Conclude with `Ideal.Quotient.eq.mpr hx`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Conclude with `⟨Module.Basis.mk hli hsp, fun i => by simp⟩`.
-/
theorem TopBasis.basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra;
    ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  intro S A _ _ s I ι tb m
  letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra
  have hsmul : ∀ (a : S) (x : A), (Ideal.Quotient.mk (I ^ m) a) • (Ideal.Quotient.mk ((I ^ m).map s) x)
      = Ideal.Quotient.mk ((I ^ m).map s) (s a * x) := by
    intro a x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]
  have hli : LinearIndependent (S ⧸ I ^ m) (fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rw [linearIndependent_iff']
    intro F g hg j hj
    choose h hh using fun i => Ideal.Quotient.mk_surjective (I := I ^ m) (g i)
    have hsum : (∑ i ∈ F, s (h i) * tb.b i) ∈ (I ^ m).map s := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hh i, hsmul]
    have hc := tb.c_mem_of_mem_map_pow m j hsum
    rw [map_sum, Finset.sum_eq_single j] at hc
    · rw [tb.c_mul, tb.c_self, mul_one] at hc
      rw [← hh j]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    · intro i _ hij
      rw [tb.c_mul, tb.c_ne j i (Ne.symm hij), mul_zero]
    · intro h'; exact (h' hj).elim
  have hsp : ⊤ ≤ Submodule.span (S ⧸ I ^ m) (Set.range fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rintro x -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hF : ∀ i, i ∉ (tb.fin y m).toFinset → tb.c i y ∈ I ^ m := by
      intro i hi
      simpa using hi
    have hx := tb.approx y m (tb.fin y m).toFinset hF
    have : Ideal.Quotient.mk ((I ^ m).map s) y = ∑ i ∈ (tb.fin y m).toFinset,
        (Ideal.Quotient.mk (I ^ m) (tb.c i y)) • Ideal.Quotient.mk ((I ^ m).map s) (tb.b i) := by
      simp_rw [hsmul, ← map_sum]
      exact Ideal.Quotient.eq.mpr hx
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp⟩

end GlobalTheory.BSP
