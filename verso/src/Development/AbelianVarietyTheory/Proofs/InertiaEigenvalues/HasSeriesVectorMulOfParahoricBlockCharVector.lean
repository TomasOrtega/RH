import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqOfOpposite

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.ParVec

open GlobalTheory.GLq.Opp GlobalTheory.SerSys.Opp MonoidAlgebra

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hj hi`. Take `⟨i', rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨j', rfl⟩` from `finSumFinEquiv.surjective j`. Rewrite using `[par_apply]`.

Break down `i' with i' | i'` into its components or cases. Use `i'.isLt` as an intermediate fact. Simplify using `at hi`. Use linear arithmetic over natural numbers and integers. Break down `j' with j' | j'` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `at hj`. Use extensionality with `i j show entN _ i j = _`. Rewrite using `[(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]`. Simplify using `[entN]`.

Use extensionality with `i j show entN _ (a + i) (a + j) = _`. Rewrite using `[(entN_par (1 : Gn g a) B 1 i j).2.2.1]`. Simplify using `[entN]`.
-/
private theorem inPar_tl_br_par_one {g : ℕ} [Fact g.Prime] {a b : ℕ} (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    InPar a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) ∧
    tl a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 ∧
    br a b ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i' with i' | i'
    · have := i'.isLt
      simp at hi
      omega
    · rcases j' with j' | j'
      · simp
      · simp at hj
  · ext i j
    show entN _ i j = _
    rw [(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]
    simp [entN]
  · ext i j
    show entN _ (a + i) (a + j) = _
    rw [(entN_par (1 : Gn g a) B 1 i j).2.2.1]
    simp [entN]

/- English proof (translation)
Introduce `g _ S n V _ _ π a b χ h f v hn hχ hv hne`. Substitute `hn` using the available equality. Take `⟨hvK, hrad, hy⟩` from `hv`. Set `v' : fixK1 π` to `⟨v, hvK⟩`. Establish `hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x` using `fun x => blk_eq x 1`.

Establish `hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y` using `fun y => blk_eq 1 y`. Set `ρA : Representation ℂ (Gn g a) (fixK1 π)` to `(repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))`. Set `ρB : Representation ℂ (Gn g b) (fixK1 π)` to `(repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))`. Set `u : fixK1 π` to `ρA.asAlgebraHom (S.e a f) v'`. Establish `hu : (u : V) = actTop π a b (S.e a f) v` using `by show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _`.

Rewrite using `[alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hA]`. Both sides reduce to the same expression. Establish `hv1 : ρB.asAlgebraHom (S.e b h) v' = v'`.

Rewrite using `[alg_apply]`. Establish `hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v'`. Introduce `y`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show π (lift g (a + b) (inB finSumFinEquiv y)) v = _`.

Rewrite using `[← hB]`. Conclude with `hy y`. Repeatedly rewrite using `[hyv, smul_smul, ← Finset.sum_smul]`. Establish `hev` using `(Loc.charIn_iff S χ b h).1 hχ`. Simplify using `only [Loc.ev] at hev`.

Rewrite using `[hev, one_smul]`. Establish `key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u`. Apply `S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u` to reduce the goal to its premises. Introduce `u0 h0 h1 h2`. Take `⟨B, rfl⟩` from `eq_par (k := a) (l := b) u0 h0 h1 h2`.

Use `show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'`. Rewrite using `[alg_apply, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `congr 1`.

Establish `hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x = inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1` using `by show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 = par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1`. Rewrite using `[par_mul, par_mul]`. Simplify using `[← Matrix.mul_assoc]`. Use `show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]`.

Use `congr 1`. Take `⟨r0, r1, r2⟩` from `inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)`. Conclude with `Subtype.ext (hrad _ r0 r1 r2)`. Repeatedly rewrite using `[hA]`. Establish `e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u`.

Rewrite using `[alg_apply]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Use `show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'`. Rewrite using `[← Module.End.mul_apply, ← map_mul, S.idem]`.

Repeatedly rewrite using `[hB]`. Establish `e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u`. Rewrite using `[alg_apply]`. Both sides reduce to the same expression. Rewrite using `[e3]`.

Use `show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'`. Establish `hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v')`. Simplify using `only [ρA, ρB, comp_alg]`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]`. Rewrite using `[hc, hv1]`.

Use `⟨(u : V), u.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← repK_alg, key, hu]`. Conclude with `hne`.
-/
theorem has_mul_of_isParVec : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  intro g _ S n V _ _ π a b χ h f v hn hχ hv hne
  subst hn
  obtain ⟨hvK, hrad, hy⟩ := hv
  let v' : fixK1 π := ⟨v, hvK⟩
  have hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x := fun x => blk_eq x 1
  have hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y := fun y => blk_eq 1 y
  let ρA : Representation ℂ (Gn g a) (fixK1 π) := (repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let ρB : Representation ℂ (Gn g b) (fixK1 π) := (repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let u : fixK1 π := ρA.asAlgebraHom (S.e a f) v'
  have hu : (u : V) = actTop π a b (S.e a f) v := by
    show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _
    rw [alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA]
    rfl
  have hv1 : ρB.asAlgebraHom (S.e b h) v' = v' := by
    rw [alg_apply]
    have hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v' := by
      intro y
      apply Subtype.ext
      show π (lift g (a + b) (inB finSumFinEquiv y)) v = _
      rw [← hB]
      exact hy y
    simp_rw [hyv, smul_smul, ← Finset.sum_smul]
    have hev := (Loc.charIn_iff S χ b h).1 hχ
    simp only [Loc.ev] at hev
    rw [hev, one_smul]
  have key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u := by
    apply S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u
    · intro u0 h0 h1 h2
      obtain ⟨B, rfl⟩ := eq_par (k := a) (l := b) u0 h0 h1 h2
      show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [alg_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      congr 1
      have hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x =
          inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1 := by
        show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 =
          par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1
        rw [par_mul, par_mul]
        simp [← Matrix.mul_assoc]
      show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
      congr 1
      obtain ⟨r0, r1, r2⟩ := inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)
      exact Subtype.ext (hrad _ r0 r1 r2)
    · simp_rw [hA]
      have e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u := by
        rw [alg_apply]
        rfl
      rw [e2]
      show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [← Module.End.mul_apply, ← map_mul, S.idem]
    · simp_rw [hB]
      have e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u := by
        rw [alg_apply]
        rfl
      rw [e3]
      show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      have hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') =
          ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v') := by
        simp only [ρA, ρB, comp_alg]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]
      rw [hc, hv1]
  refine ⟨(u : V), u.2, ?_⟩
  rw [← repK_alg, key, hu]
  exact hne

end GlobalTheory.SerSys.ParVec
