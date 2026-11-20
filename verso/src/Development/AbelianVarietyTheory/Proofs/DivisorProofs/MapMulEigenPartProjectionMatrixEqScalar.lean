import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTwoMulRhoSubTr
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open scoped Pointwise

/- English proof (translation)
Establish `hmem : (∏ j, f j) ∈ Ideal.span (∏ j, Set.range (N j))`. Rewrite using `[← Ideal.prod_span]`. Conclude with `Ideal.prod_mem_prod fun j _ => hf j`. Use `Submodule.span_induction (p := fun x _ => x * W = 0) ?_ ?_ ?_ ?_ hmem` and prove the remaining obligations. Introduce `x hx`.

Take `⟨e, he, rfl⟩` from `(Set.mem_finset_prod _ _ _).1 hx`. Establish `: ∀ j, ∃ y, N j y = e j` using `fun j => he (Finset.mem_univ j)`. Use `choose c hc using this`. Simplify `h c` using `[hc]`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[add_mul, hx, hy, add_zero]`. Introduce `a x _ hx`. Rewrite using `[smul_eq_mul, mul_assoc, hx, mul_zero]`.
-/
theorem prod_mul_eq_zero_of_mem_span {S X ι : Type} [CommRing S] [Fintype ι] (N : ι → X → S) (W : S)
    (h : ∀ c : ι → X, (∏ j, N j (c j)) * W = 0) (f : ι → S)
    (hf : ∀ j, f j ∈ Ideal.span (Set.range (N j))) : (∏ j, f j) * W = 0 := by
  classical
  have hmem : (∏ j, f j) ∈ Ideal.span (∏ j, Set.range (N j)) := by
    rw [← Ideal.prod_span]
    exact Ideal.prod_mem_prod fun j _ => hf j
  refine Submodule.span_induction (p := fun x _ => x * W = 0) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (Set.mem_finset_prod _ _ _).1 hx
    have : ∀ j, ∃ y, N j y = e j := fun j => he (Finset.mem_univ j)
    choose c hc using this
    simpa [hc] using h c
  · simp
  · intro x y _ _ hx hy; rw [add_mul, hx, hy, add_zero]
  · intro a x _ hx; rw [smul_eq_mul, mul_assoc, hx, mul_zero]

end GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

/- English proof (translation)
Use extensionality with `k l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mapMatrix_algebraMap_fin {B K : Type} [CommRing B] [CommRing K] (g : B →+* K) {n : ℕ} (x : B) :
    g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap K (Matrix (Fin n) (Fin n) K) (g x) := by
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `hI i c`. Use `set M' : 𝓞 D.F →+* Matrix (Fin n) (Fin n) K := g.mapMatrix.comp M with hM'`. Establish `hcomm : ∀ a ∈ Set.range M', ∀ a' ∈ Set.range M', a * a' = a' * a`. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Set `S` to `Algebra.adjoin K (Set.range M')`. Use `letI : CommRing S := Algebra.adjoinCommRingOfComm K hcomm`. Set `m : 𝓞 D.F → S` to `fun x => ⟨M' x, Algebra.subset_adjoin ⟨x, rfl⟩⟩`. Set `sc : R → S` to `fun r => algebraMap K S (g (βB r))`. Set `N : Fin D.a → 𝓞 D.F → S` to `fun j x => m x - sc (b.t j x)`.

Set `WS : S` to `m D.ω - sc ((D.tr : R) - b.ρ)`. Set `α : Fin D.a → S` to `fun j => (comaxC b i j).sum fun x r => sc r * N j x`. Set `PS : S` to `(List.ofFn fun j => if j = i then 1 else α j).prod * (sc (uInv b) * WS)`. Establish `hsc : ∀ r, S.val (sc r) = g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) (βB r))`. Introduce `r`.

Rewrite using `[AlgHom.commutes, mapMatrix_algebraMap_fin]`. Establish `hm : ∀ x, S.val (m x) = g.mapMatrix (M x)` using `fun _ => rfl`. Establish `hN : ∀ j x, S.val (N j x) = g.mapMatrix (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x)))`. Introduce `j x`. Simplify using `only [N, map_sub, hm, hsc]`.

Establish `hW : S.val WS = g.mapMatrix (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ)))`. Simplify using `only [WS, map_sub, hm, hsc]`. Establish `hα : ∀ j, S.val (α j) = g.mapMatrix (alphaMat b βB M i j)`. Introduce `j`. Simplify using `only [α, alphaMat, Finsupp.sum, map_sum, map_mul, hsc, hN]`.

Establish `hP : S.val PS = g.mapMatrix (projMat b βB M i)`. Simplify using `only [PS, projMat, map_mul, map_list_prod, List.map_ofFn, hsc, hW]`. Use `congr 2`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `only [Function.comp_apply]`. Use `split_ifs`. Rewrite using `[map_one, map_one]`. Conclude with `hα j`. Establish `hlie : ∀ c' : Fin D.a → 𝓞 D.F, (∏ j, N j (c' j)) * WS = 0`.

Introduce `c'`. Establish `h0 : g.mapMatrix (lieMat b βB M c') = 0`. Use extensionality with `k l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]`. Conclude with `hI (Ideal.subset_span ⟨c', k, l, rfl⟩)`.

Rewrite using `[← List.prod_ofFn]`. Use `(map_eq_zero_iff S.val Subtype.val_injective).1 ?_` and prove the remaining obligations. Rewrite using `[← h0, lieMat, map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, hW]`. Use `congr 2`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp_apply, hN]`. Establish `hkey : N i c * PS = 0`. Establish `hf : ∀ j, (if j = i then N i c else α j) ∈ Ideal.span (Set.range (N j))`. Introduce `j`.

Use `split_ifs with hj`. Substitute `hj` using the available equality. Conclude with `Ideal.subset_span ⟨c, rfl⟩`. Conclude with `Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)`. Establish `h1` using `prod_mul_eq_zero_of_mem_span N WS hlie _ hf`.

Establish `h2 : N i c * (∏ j, if j = i then (1 : S) else α j) = ∏ j, if j = i then N i c else α j`. Apply the tactic sequence `rw [show (∏ j, if j = i then N i c else α j) = ∏ j, ((if j = i then N i c else 1) * if j = i then 1 else α j) from Finset.prod_congr rfl fun j _ => by split_ifs <;> simp, Finset.prod_mul_distrib, Finset.prod_ite_eq']`. Simplify using the standard rewrite rules. Simplify using `only [PS, List.prod_ofFn]`. Rewrite using `[← mul_assoc, h2, mul_left_comm, h1, mul_zero]`.

Establish `h3` using `congrArg S.val hkey`. Rewrite `h3` using `[map_mul, map_zero, hN, hP, map_sub, mapMatrix_algebraMap_fin, sub_mul]`. Express the relevant statement in the definitionally equal form `g.mapMatrix (M c) * g.mapMatrix (projMat b βB M i) = _`. Rewrite using `[Algebra.smul_def, ← sub_eq_zero]`. Conclude with `h3`.
-/
theorem map_mul_projMat_eq_smul (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (B : Type) [CommRing B] (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K]
    (g : B →+* K) :
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  intro hI i c
  classical
  set M' : 𝓞 D.F →+* Matrix (Fin n) (Fin n) K := g.mapMatrix.comp M with hM'
  have hcomm : ∀ a ∈ Set.range M', ∀ a' ∈ Set.range M', a * a' = a' * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm]
  let S := Algebra.adjoin K (Set.range M')
  letI : CommRing S := Algebra.adjoinCommRingOfComm K hcomm
  let m : 𝓞 D.F → S := fun x => ⟨M' x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let sc : R → S := fun r => algebraMap K S (g (βB r))
  let N : Fin D.a → 𝓞 D.F → S := fun j x => m x - sc (b.t j x)
  let WS : S := m D.ω - sc ((D.tr : R) - b.ρ)
  let α : Fin D.a → S := fun j => (comaxC b i j).sum fun x r => sc r * N j x
  let PS : S := (List.ofFn fun j => if j = i then 1 else α j).prod * (sc (uInv b) * WS)
  have hsc : ∀ r, S.val (sc r) = g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) (βB r)) := by
    intro r; rw [AlgHom.commutes, mapMatrix_algebraMap_fin]
  have hm : ∀ x, S.val (m x) = g.mapMatrix (M x) := fun _ => rfl
  have hN : ∀ j x, S.val (N j x) =
      g.mapMatrix (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x))) := by
    intro j x; simp only [N, map_sub, hm, hsc]
  have hW : S.val WS = g.mapMatrix (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))) := by
    simp only [WS, map_sub, hm, hsc]
  have hα : ∀ j, S.val (α j) = g.mapMatrix (alphaMat b βB M i j) := by
    intro j; simp only [α, alphaMat, Finsupp.sum, map_sum, map_mul, hsc, hN]
  have hP : S.val PS = g.mapMatrix (projMat b βB M i) := by
    simp only [PS, projMat, map_mul, map_list_prod, List.map_ofFn, hsc, hW]
    congr 2
    congr 1
    funext j
    simp only [Function.comp_apply]
    split_ifs
    · rw [map_one, map_one]
    · exact hα j
  have hlie : ∀ c' : Fin D.a → 𝓞 D.F, (∏ j, N j (c' j)) * WS = 0 := by
    intro c'
    have h0 : g.mapMatrix (lieMat b βB M c') = 0 := by
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact hI (Ideal.subset_span ⟨c', k, l, rfl⟩)
    rw [← List.prod_ofFn]
    refine (map_eq_zero_iff S.val Subtype.val_injective).1 ?_
    rw [← h0, lieMat, map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, hW]
    congr 2
    congr 1
    funext j
    simp only [Function.comp_apply, hN]
  have hkey : N i c * PS = 0 := by
    have hf : ∀ j, (if j = i then N i c else α j) ∈ Ideal.span (Set.range (N j)) := by
      intro j; split_ifs with hj
      · subst hj; exact Ideal.subset_span ⟨c, rfl⟩
      · exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
    have h1 := prod_mul_eq_zero_of_mem_span N WS hlie _ hf
    have h2 : N i c * (∏ j, if j = i then (1 : S) else α j) = ∏ j, if j = i then N i c else α j := by
      rw [show (∏ j, if j = i then N i c else α j) =
          ∏ j, ((if j = i then N i c else 1) * if j = i then 1 else α j) from
          Finset.prod_congr rfl fun j _ => by split_ifs <;> simp, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    simp only [PS, List.prod_ofFn]
    rw [← mul_assoc, h2, mul_left_comm, h1, mul_zero]
  have h3 := congrArg S.val hkey
  rw [map_mul, map_zero, hN, hP, map_sub, mapMatrix_algebraMap_fin, sub_mul] at h3
  change g.mapMatrix (M c) * g.mapMatrix (projMat b βB M i) = _
  rw [Algebra.smul_def, ← sub_eq_zero]
  exact h3

end GlobalTheory.UPel.HT.LieLin.RankIdeal
