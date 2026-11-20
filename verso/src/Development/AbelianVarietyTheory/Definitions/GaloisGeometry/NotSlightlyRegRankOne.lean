import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OddOrSlightlyRegIffOfEven

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec
open GlobalTheory.CBGal

namespace GlobalTheory.CBGal.Model
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce and unpack `⟨τ, z, -, -, i, j, -, hj, -⟩`. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_slightlyReg_rank_one (π : CuspSub E 1) : ¬ SlightlyReg π := by
  rintro ⟨τ, z, -, -, i, j, -, hj, -⟩
  have := j.2; omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨OddOrSlightlyReg.of_odd _ odd_one, not_slightlyReg_rank_one _⟩`.
-/
theorem triv_oddOr : OddOrSlightlyReg (CuspSub.triv E (le_refl 1)) ∧ ¬ SlightlyReg (CuspSub.triv E (le_refl 1)) :=
  ⟨OddOrSlightlyReg.of_odd _ odd_one, not_slightlyReg_rank_one _⟩

/- English proof (translation)
Introduce and unpack `⟨τ, z, hz, hs, -⟩`. Establish `e : (CG.mk π).infChar τ = Multiset.replicate a 0`. Unfold `CG.infChar; rw [dif_neg (by simpa using h τ)]`. Rewrite `hz` using `[e]`. Establish `h0 : z ⟨0, by omega⟩ ∈ Finset.univ.val.map z` using `Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)`.

Establish `h1 : z ⟨1, by omega⟩ ∈ Finset.univ.val.map z` using `Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)`. Rewrite `h0`, `h1` using `[← hz]`. Use `hs (show (⟨0, by omega⟩ : Fin a) < ⟨1, by omega⟩ from by simp [Fin.lt_def])` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1]`.

Conclude with `lt_irrefl _ this`.
-/
theorem not_slightlyReg_of_not_hasInfChar (π : CuspSub E a) (ha : 2 ≤ a) (h : ∀ τ m, ¬ (CG.mk π).HasInfChar τ m) : ¬ SlightlyReg π := by
  rintro ⟨τ, z, hz, hs, -⟩
  have e : (CG.mk π).infChar τ = Multiset.replicate a 0 := by
    unfold CG.infChar; rw [dif_neg (by simpa using h τ)]
  rw [e] at hz
  have h0 : z ⟨0, by omega⟩ ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
  have h1 : z ⟨1, by omega⟩ ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
  rw [← hz] at h0 h1
  have := hs (show (⟨0, by omega⟩ : Fin a) < ⟨1, by omega⟩ from by simp [Fin.lt_def])
  simp only at this
  rw [Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1] at this
  exact lt_irrefl _ this

/- English proof (translation)
Take `⟨τ, z, hz, hs, i, j, hi, hj, hg⟩` from `h`. Distinguish the cases in `hm : ∃ m, (CG.mk π).HasInfChar τ m`. Take `⟨m, hm⟩` from `hm`. Use `⟨τ, fun k => z k + expo χ τ, ?_, ?_, i, j, hi, hj, ?_⟩` and prove the remaining obligations. Establish `h2` using `(hm.twist χ).infChar_eq`.

Rewrite `h2` using `[CG.twist_mk]`. Rewrite using `[h2, ← hm.infChar_eq, hz, Multiset.map_map]`. Both sides reduce to the same expression. Introduce `x y hxy`. Simplify using `using hs hxy`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Establish `e : (CG.mk π).infChar τ = Multiset.replicate a 0`. Unfold `CG.infChar`.

Rewrite using `[dif_neg hm]`. Rewrite `hz` using `[e]`. Establish `h0 : z i ∈ Finset.univ.val.map z` using `Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)`. Establish `h1 : z j ∈ Finset.univ.val.map z` using `Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)`. Rewrite `h0`, `h1` using `[← hz]`.

Rewrite `hg` using `[Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1]`. Evaluate the numerical expressions using `at hg`.
-/
theorem slightlyReg_twist_of (π : CuspSub E a) (χ : HChar E) (h : SlightlyReg π) : SlightlyReg (π.twist χ) := by
  obtain ⟨τ, z, hz, hs, i, j, hi, hj, hg⟩ := h
  by_cases hm : ∃ m, (CG.mk π).HasInfChar τ m
  · obtain ⟨m, hm⟩ := hm
    refine ⟨τ, fun k => z k + expo χ τ, ?_, ?_, i, j, hi, hj, ?_⟩
    · have h2 := (hm.twist χ).infChar_eq
      rw [CG.twist_mk] at h2
      rw [h2, ← hm.infChar_eq, hz, Multiset.map_map]; rfl
    · intro x y hxy; simpa using hs hxy
    · simp; linarith
  · exfalso
    have e : (CG.mk π).infChar τ = Multiset.replicate a 0 := by
      unfold CG.infChar; rw [dif_neg hm]
    rw [e] at hz
    have h0 : z i ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    have h1 : z j ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [← hz] at h0 h1
    rw [Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1] at hg
    norm_num at hg

/- English proof (translation)
Use `⟨fun h => ?_, slightlyReg_twist_of π χ⟩` and prove the remaining obligations. Establish `e : (π.twist χ).twist χ⁻¹ = π` using `by rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]`. Simplify `slightlyReg_twist_of _ χ⁻¹ h` using `[e]`.
-/
theorem slightlyReg_twist (π : CuspSub E a) (χ : HChar E) : SlightlyReg (π.twist χ) ↔ SlightlyReg π := by
  refine ⟨fun h => ?_, slightlyReg_twist_of π χ⟩
  have e : (π.twist χ).twist χ⁻¹ = π := by rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  simpa [e] using slightlyReg_twist_of _ χ⁻¹ h

/- English proof (translation)
The claim follows from `or_congr Iff.rfl (slightlyReg_twist π χ)`.
-/
theorem oddOrSlightlyReg_twist (π : CuspSub E a) (χ : HChar E) :
    OddOrSlightlyReg (π.twist χ) ↔ OddOrSlightlyReg π := or_congr Iff.rfl (slightlyReg_twist π χ)

end GlobalTheory.CBGal.Model

end
