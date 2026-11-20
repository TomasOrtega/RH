import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

/- English proof (translation)
Use `haveI : Fact dK.Prime := ⟨hd⟩`. Establish `hd2 : ringChar (ZMod dK) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; omega`. Establish `hζ : IsPrimitiveRoot (ι (Complex.exp (2 * ↑Real.pi * Complex.I / ↑dK))) dK` using `(Complex.isPrimitiveRoot_exp dK hd.ne_zero).map_of_injective ι.injective`. Use `set χ := (quadraticChar (ZMod dK)).ringHomComp (Int.castRingHom ℂ_[l]) with hχ`. Use `set ψ := AddChar.zmodChar dK hζ.pow_eq_one with hψdef`.

Establish `hψ : ψ.IsPrimitive` using `AddChar.zmodChar_primitive_of_primitive_root dK hζ`. Establish `hχ1 : χ ≠ 1`. Take `⟨a, ha⟩` from `MulChar.ne_one_iff.1 (quadraticChar_ne_one hd2)`. Use `MulChar.ne_one_iff.2 ⟨a, fun h => ha ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hχ, MulChar.ringHomComp_apply, eq_intCast]`.

Conclude with `h` after adjusting the coercions. Establish `hG : gaussSum χ ψ ^ 2 = -(dK : ℂ_[l])`. Rewrite using `[gaussSum_sq hχ1 ((quadraticChar_isQuadratic (ZMod dK)).comp _) hψ, ZMod.card, hχ, MulChar.ringHomComp_apply, quadraticChar_neg_one hd2, ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]`. Simplify using the standard rewrite rules. Establish `hx : ι (sq dK) ^ 2 = -(dK : ℂ_[l])`.

Rewrite using `[← map_pow]`. Establish `h2 : sq dK ^ 2 = -(dK : ℂ)`. Unfold `sq`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, map_neg, map_natCast]`. Establish `hmem : gaussSum χ ψ ∈ MaximalUnramifiedExtension l`. Unfold `gaussSum`. Use `Subfield.sum_mem _ (fun a _ => Subfield.mul_mem _ ?_ ?_)` and prove the remaining obligations.

Rewrite using `[hχ, MulChar.ringHomComp_apply, eq_intCast]`. Conclude with `intCast_mem _ _`. Rewrite using `[hψdef, AddChar.zmodChar_apply]`. Unfold `MaximalUnramifiedExtension`. Apply `Subfield.le_topologicalClosure` to reduce the goal to its premises.

Apply `Subfield.subset_closure` to reduce the goal to its premises. Use `⟨dK, hd.pos, hld, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm a.val dK, pow_mul, hζ.pow_eq_one, one_pow]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hG.symm) with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `hmem`. Rewrite using `[h]`. Conclude with `Subfield.neg_mem _ hmem`.
-/
theorem delta_mem (l : ℕ) [Fact l.Prime] (dK : ℕ) (hd : dK.Prime) (hd4 : dK % 4 = 3) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) : ι (sq dK) ∈ MaximalUnramifiedExtension l := by
  haveI : Fact dK.Prime := ⟨hd⟩
  have hd2 : ringChar (ZMod dK) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hζ : IsPrimitiveRoot (ι (Complex.exp (2 * ↑Real.pi * Complex.I / ↑dK))) dK :=
    (Complex.isPrimitiveRoot_exp dK hd.ne_zero).map_of_injective ι.injective
  set χ := (quadraticChar (ZMod dK)).ringHomComp (Int.castRingHom ℂ_[l]) with hχ
  set ψ := AddChar.zmodChar dK hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root dK hζ
  have hχ1 : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := MulChar.ne_one_iff.1 (quadraticChar_ne_one hd2)
    refine MulChar.ne_one_iff.2 ⟨a, fun h => ha ?_⟩
    rw [hχ, MulChar.ringHomComp_apply, eq_intCast] at h
    exact_mod_cast h
  have hG : gaussSum χ ψ ^ 2 = -(dK : ℂ_[l]) := by
    rw [gaussSum_sq hχ1 ((quadraticChar_isQuadratic (ZMod dK)).comp _) hψ, ZMod.card, hχ,
      MulChar.ringHomComp_apply, quadraticChar_neg_one hd2, ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]
    simp
  have hx : ι (sq dK) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow]
    have h2 : sq dK ^ 2 = -(dK : ℂ) := by
      unfold sq
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [h2, map_neg, map_natCast]
  have hmem : gaussSum χ ψ ∈ MaximalUnramifiedExtension l := by
    unfold gaussSum
    refine Subfield.sum_mem _ (fun a _ => Subfield.mul_mem _ ?_ ?_)
    · rw [hχ, MulChar.ringHomComp_apply, eq_intCast]
      exact intCast_mem _ _
    · rw [hψdef, AddChar.zmodChar_apply]
      unfold MaximalUnramifiedExtension
      apply Subfield.le_topologicalClosure
      apply Subfield.subset_closure
      refine ⟨dK, hd.pos, hld, ?_⟩
      rw [← pow_mul, mul_comm a.val dK, pow_mul, hζ.pow_eq_one, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hG.symm) with h | h
  · rw [h]
    exact hmem
  · rw [h]
    exact Subfield.neg_mem _ hmem

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
