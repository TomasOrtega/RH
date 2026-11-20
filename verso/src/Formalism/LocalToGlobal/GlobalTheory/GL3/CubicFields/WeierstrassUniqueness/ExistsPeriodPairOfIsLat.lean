import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

/- English proof (translation)
Take `⟨hd, hs⟩` from `hΛ`. Set `Λ' : Submodule ℤ ℂ` to `Λ.toIntSubmodule`. Use `haveI : DiscreteTopology Λ' := hd`. Use `haveI : IsZLattice ℝ Λ' := ⟨by simpa [Λ'] using hs⟩`. Establish `hr : Module.finrank ℤ Λ' = 2`.

Rewrite using `[ZLattice.rank ℝ (L := Λ'), Complex.finrank_real_complex]`. Set `b : Module.Basis (Fin 2) ℤ Λ'` to `Module.finBasisOfFinrankEq ℤ Λ' hr`. Set `B : Module.Basis (Fin 2) ℝ ℂ` to `Module.Basis.ofZLatticeBasis ℝ Λ' b`. Establish `hB : ∀ i, B i = (b i : ℂ)` using `fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ' b i`. Establish `hfun : (⇑B) = ![(b 0 : ℂ), (b 1 : ℂ)]`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [hB]`. Establish `hind : LinearIndependent ℝ ![(b 0 : ℂ), (b 1 : ℂ)]` using `hfun ▸ B.linearIndependent`. Use `⟨⟨(b 0 : ℂ), (b 1 : ℂ), hind⟩, ?_⟩` and prove the remaining obligations. Establish `hrange : Set.range ⇑B = {(b 0 : ℂ), (b 1 : ℂ)}`.

Rewrite using `[hfun]`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Conclude with `⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩`. Establish `hspan : Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} = Λ'`.

Rewrite using `[← hrange]`. Conclude with `Module.Basis.ofZLatticeBasis_span ℝ Λ' b`. Use `show ((Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} : Submodule ℤ ℂ) : Set ℂ) = Λ`. Rewrite using `[hspan]`. Both sides reduce to the same expression.
-/
theorem exists_periodPair_of_isLat (Λ : AddSubgroup ℂ) (hΛ : IsLat Λ) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = Λ := by
  classical
  obtain ⟨hd, hs⟩ := hΛ
  let Λ' : Submodule ℤ ℂ := Λ.toIntSubmodule
  haveI : DiscreteTopology Λ' := hd
  haveI : IsZLattice ℝ Λ' := ⟨by simpa [Λ'] using hs⟩
  have hr : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ (L := Λ'), Complex.finrank_real_complex]
  let b : Module.Basis (Fin 2) ℤ Λ' := Module.finBasisOfFinrankEq ℤ Λ' hr
  let B : Module.Basis (Fin 2) ℝ ℂ := Module.Basis.ofZLatticeBasis ℝ Λ' b
  have hB : ∀ i, B i = (b i : ℂ) := fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ' b i
  have hfun : (⇑B) = ![(b 0 : ℂ), (b 1 : ℂ)] := by
    funext i
    fin_cases i <;> simp [hB]
  have hind : LinearIndependent ℝ ![(b 0 : ℂ), (b 1 : ℂ)] := hfun ▸ B.linearIndependent
  refine ⟨⟨(b 0 : ℂ), (b 1 : ℂ), hind⟩, ?_⟩
  have hrange : Set.range ⇑B = {(b 0 : ℂ), (b 1 : ℂ)} := by
    rw [hfun]
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  have hspan : Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} = Λ' := by
    rw [← hrange]
    exact Module.Basis.ofZLatticeBasis_span ℝ Λ' b
  show ((Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)} : Submodule ℤ ℂ) : Set ℂ) = Λ
  rw [hspan]
  rfl

/- English proof (translation)
Unfold `Formalism.MainNotions.TaylorLogMetric.eisG PeriodPair.G`. Establish `h1` using `tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0}) (fun w : ℂ => 1 / w ^ (2 * n))`. Establish `h2` using `tsum_subtype ((L.lattice : Set ℂ)) (fun w : ℂ => (w ^ (2 * n))⁻¹)`. Use `h1.trans (Eq.trans ?_ h2.symm)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `h0 : (0 : ℂ) ^ (2 * n) = 0` using `zero_pow (by omega)`. Simplify using `[Set.indicator, h0]`.

Establish `hm : x ∈ L.lattice ↔ x ∈ Λ`. Rewrite using `[← SetLike.mem_coe, hL, SetLike.mem_coe]`. Simplify using `only [Set.indicator, Set.mem_setOf_eq, hx, ne_eq, not_false_eq_true, and_true, SetLike.mem_coe, hm, one_div]`.
-/
theorem eisG_eq_G_of_lattice (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ)
    (n : ℕ) (hn : n ≠ 0) : Formalism.MainNotions.TaylorLogMetric.eisG Λ n = L.G (2 * n) := by
  unfold Formalism.MainNotions.TaylorLogMetric.eisG PeriodPair.G
  have h1 := tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0}) (fun w : ℂ => 1 / w ^ (2 * n))
  have h2 := tsum_subtype ((L.lattice : Set ℂ)) (fun w : ℂ => (w ^ (2 * n))⁻¹)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext x
  by_cases hx : x = 0
  · subst hx
    have h0 : (0 : ℂ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp [Set.indicator, h0]
  · have hm : x ∈ L.lattice ↔ x ∈ Λ := by
      rw [← SetLike.mem_coe, hL, SetLike.mem_coe]
    simp only [Set.indicator, Set.mem_setOf_eq, hx, ne_eq, not_false_eq_true, and_true,
      SetLike.mem_coe, hm, one_div]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.TaylorLogMetric.g2 PeriodPair.g₂`. Rewrite using `[eisG_eq_G_of_lattice Λ L hL 2 (by norm_num)]`. Unfold `Formalism.MainNotions.TaylorLogMetric.g3 PeriodPair.g₃`. Rewrite using `[eisG_eq_G_of_lattice Λ L hL 3 (by norm_num)]`.
-/
theorem g2_g3_eq_periodPair (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ) :
    Formalism.MainNotions.TaylorLogMetric.g2 Λ = L.g₂ ∧ Formalism.MainNotions.TaylorLogMetric.g3 Λ = L.g₃ := by
  refine ⟨?_, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.g2 PeriodPair.g₂
    rw [eisG_eq_G_of_lattice Λ L hL 2 (by norm_num)]
  · unfold Formalism.MainNotions.TaylorLogMetric.g3 PeriodPair.g₃
    rw [eisG_eq_G_of_lattice Λ L hL 3 (by norm_num)]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
