import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgLin

/- English proof (translation)
Introduce `H _ u v c g hu hv`. Use `set S : Subgroup H := rStab u ⊓ rStab v with hS`. Establish `hSi : S.index ≠ 0` using `Subgroup.index_inf_ne_zero hu hv`. Use `haveI : S.FiniteIndex := ⟨hSi⟩`. Use `haveI : (rStab u).FiniteIndex := ⟨hu⟩`.

Establish `hSu : S ≤ rStab u` using `inf_le_left`. Establish `hSv : S ≤ rStab v` using `inf_le_right`. Establish `hSuv : S ≤ rStab (u + v)`. Introduce `k hk x`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[hSu hk x, hSv hk x]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser H (u + v) S hSuv hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u S hSu hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H v S hSv hSi, ← mul_add]`. Use `congr 1`. Simplify using `only [Pi.add_apply]`.

Conclude with `finsum_add_distrib (Set.toFinite _) (Set.toFinite _)`. Establish `hc : rStab u ≤ rStab (c • u)`. Introduce `k hk x`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hk x]`.

Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser H (c • u) (rStab u) hc hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_finsum]`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : rStab u ≤ rStab (fun x => u (g * x))`.

Introduce `k hk x`. Simplify using `only`. Rewrite using `[← mul_assoc, hk (g * x)]`. Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ (rStab u) ht hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]`. Use `congr 1`.

Establish `key : ∀ q : H ⧸ rStab u, u (g * q.out) = u (g • q).out`. Introduce `q`. Establish `: g • q = (QuotientGroup.mk (g * q.out) : H ⧸ rStab u)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (rStab u) (g * q.out)`. Rewrite using `[hh, h.2]`. Repeatedly rewrite using `[key]`. Conclude with `finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (H ⧸ rStab u)) (f := fun q => u q.out)`. Establish `htop : (⊤ : Subgroup H) ≤ rStab (fun _ : H => c)`.

Introduce `k _ x`. Both sides reduce to the same expression. Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ ⊤ htop (by simp)]`. Simplify using `only [Subgroup.index_top, Nat.cast_one, inv_one, one_mul]`. Rewrite using `[finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H))]`.

Introduce `x hx`. Conclude with `absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx`.
-/
theorem avg_linear_translate_const : ∀ (H : Type) [Group H] (u v : H → ℂ) (c : ℂ) (g : H), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (u + v) = avg u + avg v ∧ avg (c • u) = c * avg u ∧ avg (fun x => u (g * x)) = avg u ∧ avg (fun _ : H => c) = c := by
  intro H _ u v c g hu hv
  set S : Subgroup H := rStab u ⊓ rStab v with hS
  have hSi : S.index ≠ 0 := Subgroup.index_inf_ne_zero hu hv
  haveI : S.FiniteIndex := ⟨hSi⟩
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  have hSu : S ≤ rStab u := inf_le_left
  have hSv : S ≤ rStab v := inf_le_right
  have hSuv : S ≤ rStab (u + v) := by
    intro k hk x
    simp only [Pi.add_apply]
    rw [hSu hk x, hSv hk x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H (u + v) S hSuv hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u S hSu hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H v S hSv hSi,
      ← mul_add]
    congr 1
    simp only [Pi.add_apply]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  · have hc : rStab u ≤ rStab (c • u) := by
      intro k hk x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hk x]
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H (c • u) (rStab u) hc hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_finsum]
    ring
  · have ht : rStab u ≤ rStab (fun x => u (g * x)) := by
      intro k hk x
      simp only
      rw [← mul_assoc, hk (g * x)]
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ (rStab u) ht hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]
    congr 1
    have key : ∀ q : H ⧸ rStab u, u (g * q.out) = u (g • q).out := by
      intro q
      have : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ rStab u) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (g * q.out)
      rw [hh, h.2]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (H ⧸ rStab u)) (f := fun q => u q.out)
  · have htop : (⊤ : Subgroup H) ≤ rStab (fun _ : H => c) := by
      intro k _ x
      rfl
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ ⊤ htop (by simp)]
    simp only [Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
    rw [finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H))]
    intro x hx
    exact absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx

end GlobalTheory.AvgLin
