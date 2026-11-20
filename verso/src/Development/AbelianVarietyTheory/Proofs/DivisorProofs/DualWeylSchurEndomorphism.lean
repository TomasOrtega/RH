import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

/- English proof (translation)
Simplify using `only [eV, dif_pos (And.intro a.isLt b.isLt)]`. Both sides reduce to the same expression.
-/
theorem eV_coe_fin (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N a b (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  simp only [eV, dif_pos (And.intro a.isLt b.isLt)]
  rfl

/- English proof (translation)
Introduce `N ν hν S hS hfix`. Establish `hc : ∀ (a b : Fin N) (x : dualWeyl ℚ N N ν), eV N ν a b (S x) = S (eV N ν a b x)`. Introduce `a b x`. Establish `h` using `LinearMap.congr_fun (hS a a.isLt b b.isLt) x`. Simplify `h` using `only [Module.End.mul_apply]`.

Use `set v : dualWeyl ℚ N N ν := ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ with hv`. Establish `hder : ∀ a b : Fin N, a < b → Formalism.CohomologicalDescent.LR.der N N a b ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0`. Introduce `a b hab`. Establish `h1 : eV N ν a b v = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[eV_coe_fin]`. Conclude with `Formalism.CohomologicalDescent.LR.der_hw_raise ν a b hab`. Rewrite using `[← eV_coe_fin, hc, h1, map_zero]`. Both sides reduce to the same expression. Establish `hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℚ a b k ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0`.

Introduce `a b hab k hk`. Take `⟨k, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Formalism.CohomologicalDescent.LR.der_pow a b (ne_of_lt hab), pow_succ, Module.End.mul_apply]`. Establish `h2` using `hder a b hab`. Express the relevant statement in the definitionally equal form `(Formalism.CohomologicalDescent.LR.der N N a b : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) _ = 0 at h2`.

Rewrite using `[h2, map_zero, smul_zero]`. Take `⟨c, hcv⟩` from `hwLine ℚ N N le_rfl ν hν _ (S v).2 hkill`. Establish `hc1 : c = 1`. Rewrite `hfix` using `[hcv, Formalism.CohomologicalDescent.LR.fock_smul_right]`. Establish `hpos` using `Formalism.CohomologicalDescent.LR.hw_norm_pos ν`.

Establish `h3 : (c - 1) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) = 0` using `by rw [sub_mul, hfix, one_mul, sub_self]`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h (ne_of_gt hpos)`. Establish `hSv : S v = v`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcv, hc1, one_smul]`. Use `set M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) := (LinearMap.ker (S - 1)).map (dualWeyl ℚ N N ν).subtype with hM`. Establish `hmem : ∀ x : dualWeyl ℚ N N ν, S x = x → (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M`. Introduce `x hx`.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]`. Establish `hle : M ≤ dualWeyl ℚ N N ν`. Introduce and unpack `f ⟨x, _, rfl⟩`. Conclude with `x.2`.

Establish `hcl : RowDivClosed M`. Introduce `a b k`. Use `Formalism.CohomologicalDescent.LR.closed_of_der a b M ?_ k` and prove the remaining obligations. Introduce and unpack `f ⟨x, hx, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx`.

Establish `h4` using `hmem (eV N ν a b x) (by rw [← hc, hx])`. Rewrite `h4` using `[eV_coe_fin]`. Conclude with `h4`. Establish `hhw : hw ℚ le_rfl ν ∈ M` using `hmem v hSv`. Establish `heq` using `closedEqNabla N N le_rfl ν hν M hle hcl hhw`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Establish `hx : (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M` using `by rw [heq]; exact x.2`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hyx' : y = x` using `Subtype.ext hyx`.

Substitute `hyx'` using the available equality. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy`. Rewrite using `[Module.End.one_apply]`. Conclude with `hy`.
-/
theorem nablaSchur : NablaSchur := by
  intro N ν hν S hS hfix
  have hc : ∀ (a b : Fin N) (x : dualWeyl ℚ N N ν), eV N ν a b (S x) = S (eV N ν a b x) := by
    intro a b x
    have h := LinearMap.congr_fun (hS a a.isLt b b.isLt) x
    simpa only [Module.End.mul_apply] using h
  set v : dualWeyl ℚ N N ν := ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ with hv

  have hder : ∀ a b : Fin N, a < b →
      Formalism.CohomologicalDescent.LR.der N N a b ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab
    have h1 : eV N ν a b v = 0 := by
      apply Subtype.ext
      rw [eV_coe_fin]
      exact Formalism.CohomologicalDescent.LR.der_hw_raise ν a b hab
    rw [← eV_coe_fin, hc, h1, map_zero]
    rfl
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k →
      rowDiv ℚ a b k ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab k hk
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Formalism.CohomologicalDescent.LR.der_pow a b (ne_of_lt hab), pow_succ, Module.End.mul_apply]
    have h2 := hder a b hab
    change (Formalism.CohomologicalDescent.LR.der N N a b : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) _ = 0 at h2
    rw [h2, map_zero, smul_zero]
  obtain ⟨c, hcv⟩ := hwLine ℚ N N le_rfl ν hν _ (S v).2 hkill
  have hc1 : c = 1 := by
    rw [hcv, Formalism.CohomologicalDescent.LR.fock_smul_right] at hfix
    have hpos := Formalism.CohomologicalDescent.LR.hw_norm_pos ν
    have h3 : (c - 1) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) = 0 := by rw [sub_mul, hfix, one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)
  have hSv : S v = v := by
    apply Subtype.ext
    rw [hcv, hc1, one_smul]

  set M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    (LinearMap.ker (S - 1)).map (dualWeyl ℚ N N ν).subtype with hM
  have hmem : ∀ x : dualWeyl ℚ N N ν, S x = x → (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]
  have hle : M ≤ dualWeyl ℚ N N ν := by
    rintro f ⟨x, _, rfl⟩
    exact x.2
  have hcl : RowDivClosed M := by
    intro a b k
    refine Formalism.CohomologicalDescent.LR.closed_of_der a b M ?_ k
    rintro f ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    have h4 := hmem (eV N ν a b x) (by rw [← hc, hx])
    rw [eV_coe_fin] at h4
    exact h4
  have hhw : hw ℚ le_rfl ν ∈ M := hmem v hSv
  have heq := closedEqNabla N N le_rfl ν hν M hle hcl hhw
  apply LinearMap.ext
  intro x
  have hx : (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy
  rw [Module.End.one_apply]
  exact hy

end GlobalTheory.LeviCut
