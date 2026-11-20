import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `K _ _ n S`. Use `set p := S.charpoly with hp`. Establish `hmon : p.Monic` using `Matrix.charpoly_monic S`. Establish `hprod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree`. Establish `hcard : Multiset.card p.roots = n`.

Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `heval : ∀ x : K, (Matrix.scalar (Fin n) x - S).det = (p.roots.map (fun a => x - a)).prod`. Introduce `x`. Rewrite using `[← Matrix.eval_charpoly, ← hp]`. Use `conv_lhs => rw [← hprod]`.

Rewrite using `[Polynomial.eval_multiset_prod, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a _`. Simplify using the standard rewrite rules.

Establish `hz : ∃ z : Fin n → K, ∀ f : K → K, (p.roots.map f).prod = ∏ i, f (z i)`. Take `⟨L, hL⟩ : ∃ L : List K, (L : Multiset K) = p.roots` from `⟨_, Multiset.coe_toList _⟩`. Establish `hlen : L.length = n` using `by rw [← hcard, ← hL, Multiset.coe_card]`. Use `⟨fun i => L.get (Fin.cast hlen.symm i), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[← hL, Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]`.

Use `congr 1`. Apply the tactic sequence `apply List.ext_get <;> simp [hlen]`. Take `⟨z, hz⟩` from `hz`. Use `⟨z, fun c => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : c = 0`.

Substitute `hc` using the available equality. Simplify using `[Matrix.det_neg]`. Establish `hmat : c • S - 1 = (-c) • (Matrix.scalar (Fin n) c⁻¹ - S)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Matrix.sub_apply, Matrix.one_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.sub_apply, Matrix.one_apply, hij]`.

Rewrite using `[hmat, Matrix.det_smul, heval, hz, Fintype.card_fin, ← Fin.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.PropA.detFactor :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Matrix (Fin n) (Fin n) K),
      ∃ z : Fin n → K, ∀ c : K, (c • S - 1).det = ∏ i, (c * z i - 1) := by
  intro K _ _ n S
  classical
  set p := S.charpoly with hp
  have hmon : p.Monic := Matrix.charpoly_monic S
  have hprod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree
  have hcard : Multiset.card p.roots = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have heval : ∀ x : K, (Matrix.scalar (Fin n) x - S).det = (p.roots.map (fun a => x - a)).prod := by
    intro x
    rw [← Matrix.eval_charpoly, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hz : ∃ z : Fin n → K, ∀ f : K → K, (p.roots.map f).prod = ∏ i, f (z i) := by
    obtain ⟨L, hL⟩ : ∃ L : List K, (L : Multiset K) = p.roots := ⟨_, Multiset.coe_toList _⟩
    have hlen : L.length = n := by rw [← hcard, ← hL, Multiset.coe_card]
    refine ⟨fun i => L.get (Fin.cast hlen.symm i), fun f => ?_⟩
    rw [← hL, Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp [hlen]
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.det_neg]
  · have hmat : c • S - 1 = (-c) • (Matrix.scalar (Fin n) c⁻¹ - S) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.sub_apply, Matrix.one_apply]
        field_simp
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply, hij]
    rw [hmat, Matrix.det_smul, heval, hz, Fintype.card_fin, ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    field_simp
    ring
