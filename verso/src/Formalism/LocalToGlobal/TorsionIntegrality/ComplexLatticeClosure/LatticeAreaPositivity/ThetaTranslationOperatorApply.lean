import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

/- English proof (translation)
Simplify using `only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_pair (a b : ℂ) (m n p q : ℤ) :
    ((starRingEnd ℂ) ((m : ℂ) * a + (n : ℂ) * b) * ((p : ℂ) * a + (q : ℂ) * b)).im
      = ((m * q - n * p : ℤ) : ℝ) * ((starRingEnd ℂ) a * b).im := by
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re,
    Complex.intCast_im]
  push_cast
  ring

/- English proof (translation)
Introduce `L`. Establish `hpos : 0 < F.area L` using `F.areaPos L`. Unfold `TaylorLogMetric.area`. Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Use `⟨⟨hpos, L.ω₁, L.ω₁_mem_lattice, L.ω₂, L.ω₂_mem_lattice, rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `a ⟨ha, u, hu, v, hv, rfl⟩`. Take `⟨m, n, rfl⟩` from `PeriodPair.mem_lattice.mp hu`. Take `⟨p, q, rfl⟩` from `PeriodPair.mem_lattice.mp hv`. Rewrite `ha`, the goal using `[im_pair]`. Rewrite `ha`, the goal using `[abs_mul]`.

Establish `h1 : (1 : ℝ) ≤ |((m * q - n * p : ℤ) : ℝ)|`. Establish `h0 : (m * q - n * p : ℤ) ≠ 0`. Introduce `h`. Rewrite `ha` using `[h]`. Simplify using `at ha`.

Use `Int.one_le_abs h0` as an intermediate fact. Conclude with `this` after adjusting the coercions. Unfold `F.area`. Use polynomial arithmetic with `[abs_nonneg ((starRingEnd ℂ) L.ω₁ * L.ω₂).im]`.
-/
theorem area_eq_holds : AreaEq := by
  intro L
  have hpos : 0 < F.area L := F.areaPos L
  unfold TaylorLogMetric.area
  apply IsLeast.csInf_eq
  refine ⟨⟨hpos, L.ω₁, L.ω₁_mem_lattice, L.ω₂, L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hu
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.mp hv
  rw [im_pair] at ha ⊢
  rw [abs_mul] at ha ⊢
  have h1 : (1 : ℝ) ≤ |((m * q - n * p : ℤ) : ℝ)| := by
    have h0 : (m * q - n * p : ℤ) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have := Int.one_le_abs h0
    exact_mod_cast this
  unfold F.area
  nlinarith [abs_nonneg ((starRingEnd ℂ) L.ω₁ * L.ω₂).im]

/- English proof (translation)
Introduce and unpack `Λ ⟨L, rfl⟩`. Rewrite using `[area_eq_holds L]`. Conclude with `F.areaPos L`.
-/
theorem area_pos_lattice_holds : AreaPosLat := by
  rintro Λ ⟨L, rfl⟩
  rw [area_eq_holds L]
  exact F.areaPos L

/- English proof (translation)
Unfold `H1 F.herm`. Rewrite using `[area_eq_holds L]`.
-/
theorem koszul_homology_eq (L : PeriodPair) (z w : ℂ) : H1 L.lattice.toAddSubgroup z w = F.herm L z w := by
  unfold H1 F.herm
  rw [area_eq_holds L]

/- English proof (translation)
Unfold `U1 F.opU`. Simplify using `only [koszul_homology_eq]`.
-/
theorem thetaTranslationOperator_apply (L : PeriodPair) (x : ℂ) (G : ℂ → ℂ) (z : ℂ) : U1 L.lattice.toAddSubgroup x G z = F.opU L x G z := by
  unfold U1 F.opU
  simp only [koszul_homology_eq]

end Formalism.L2.Th1.F2
