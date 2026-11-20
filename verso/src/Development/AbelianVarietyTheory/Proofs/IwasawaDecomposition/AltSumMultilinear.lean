import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PolarMultilinear

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]`.
-/
theorem powerset_map {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

/- English proof (translation)
Simplify using `[Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]`.
-/
theorem powerset_val {α : Type} (s : Finset α) :
    s.val.powerset = s.powerset.val.map Finset.val := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

/- English proof (translation)
Establish `h` using `Finset.prod_add (fun _ : Fin d => (1 : ℝ)) (fun j : Fin d => if j ∈ Set.range r then (0 : ℝ) else -1) Finset.univ`. Rewrite `h` using `[Finset.powerset_univ]`. Establish `h2 : ∀ T : Finset (Fin d), (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) = (∏ _i ∈ T, (1 : ℝ)) * ∏ j ∈ Finset.univ \ T, (if j ∈ Set.range r then (0 : ℝ) else -1)`. Introduce `T`. Rewrite using `[Finset.prod_const_one, one_mul]`.

Use `split_ifs with hT`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)), Finset.prod_const, Finset.card_univ_diff, Fintype.card_fin]`. Introduce `j hj`. Rewrite using `[if_neg]`. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `(Finset.mem_sdiff.1 hj).2 (hT i)`. Take `⟨i, hi⟩` from `not_forall.1 hT`. Conclude with `(Finset.prod_eq_zero (i := r i) (by simp [hi]) (by simp)).symm`. Rewrite using `[Finset.sum_congr rfl fun T _ => h2 T, ← h]`. Use `split_ifs with hs`.

Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos (show j ∈ Set.range r from hs j), add_zero]`. Take `⟨j, hj⟩` from `not_forall.1 hs`. Use `Finset.prod_eq_zero (Finset.mem_univ j) ?_` and prove the remaining obligations. Rewrite using `[if_neg (show ¬ j ∈ Set.range r from hj)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem alt_sum {d : ℕ} (r : Fin d → Fin d) :
    (∑ T : Finset (Fin d), if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      if Function.Surjective r then 1 else 0 := by
  classical
  have h := Finset.prod_add (fun _ : Fin d => (1 : ℝ))
    (fun j : Fin d => if j ∈ Set.range r then (0 : ℝ) else -1) Finset.univ
  rw [Finset.powerset_univ] at h
  have h2 : ∀ T : Finset (Fin d), (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      (∏ _i ∈ T, (1 : ℝ)) * ∏ j ∈ Finset.univ \ T, (if j ∈ Set.range r then (0 : ℝ) else -1) := by
    intro T
    rw [Finset.prod_const_one, one_mul]
    split_ifs with hT
    · rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)), Finset.prod_const, Finset.card_univ_diff,
        Fintype.card_fin]
      intro j hj
      rw [if_neg]
      rintro ⟨i, rfl⟩
      exact (Finset.mem_sdiff.1 hj).2 (hT i)
    · obtain ⟨i, hi⟩ := not_forall.1 hT
      exact (Finset.prod_eq_zero (i := r i) (by simp [hi]) (by simp)).symm
  rw [Finset.sum_congr rfl fun T _ => h2 T, ← h]
  split_ifs with hs
  · refine Finset.prod_eq_one fun j _ => ?_
    rw [if_pos (show j ∈ Set.range r from hs j), add_zero]
  · obtain ⟨j, hj⟩ := not_forall.1 hs
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [if_neg (show ¬ j ∈ Set.range r from hj)]; ring

/- English proof (translation)
Establish `h1 : ∀ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * (M fun _ => ∑ i ∈ T, a i) = ∑ r : Fin d → Fin d, (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) * M (a ∘ r)`. Introduce `T`. Rewrite using `[M.map_sum_finset (fun _ i => a i) (fun _ => T), Finset.mul_sum]`. Repeatedly rewrite using `[ite_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter]`.

Use `Finset.sum_congr ?_ fun r _ => rfl` and prove the remaining obligations. Use extensionality with `r`. Simplify using `[Fintype.mem_piFinset]`. Rewrite using `[Finset.sum_congr rfl fun T _ => h1 T, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, alt_sum, ite_mul, one_mul, zero_mul]`.

Rewrite using `[← Finset.sum_filter]`. Establish `h3 : (∑ r ∈ Finset.univ.filter (fun r : Fin d → Fin d => Function.Surjective r), M (a ∘ r)) = ∑ σ : Equiv.Perm (Fin d), M (a ∘ σ)`. Use `symm`. Use `Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ _`.

Simplify using `using σ.surjective`. Introduce `σ _ τ _ h`. Conclude with `Equiv.ext (congrFun h)`. Introduce `r hr`. Establish `hs : Function.Surjective r` using `by simpa using hr`.

Conclude with `⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩`. Introduce `σ _`. Both sides reduce to the same expression. Rewrite using `[h3]`. Simplify using `[hM, Fintype.card_perm]`.
-/
theorem alt_sum_multilinear {A : Type} [AddCommGroup A] {d : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) (a : Fin d → A) :
    (∑ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * M fun _ => ∑ i ∈ T, a i) =
      (d.factorial : ℝ) * M a := by
  classical
  have h1 : ∀ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * (M fun _ => ∑ i ∈ T, a i) =
      ∑ r : Fin d → Fin d, (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) * M (a ∘ r) := by
    intro T
    rw [M.map_sum_finset (fun _ i => a i) (fun _ => T), Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun r _ => rfl
    ext r
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_congr rfl fun T _ => h1 T, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, alt_sum, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have h3 : (∑ r ∈ Finset.univ.filter (fun r : Fin d → Fin d => Function.Surjective r), M (a ∘ r)) =
      ∑ σ : Equiv.Perm (Fin d), M (a ∘ σ) := by
    symm
    refine Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) ?_ ?_ ?_ ?_
    · intro σ _
      simpa using σ.surjective
    · intro σ _ τ _ h
      exact Equiv.ext (congrFun h)
    · intro r hr
      have hs : Function.Surjective r := by simpa using hr
      exact ⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [h3]
  simp [hM, Fintype.card_perm]

/- English proof (translation)
Introduce `A _ d M hM a`. Establish `hc : Multiset.card (Multiset.map a Finset.univ.val) = d` using `by simp`. Unfold `Pad.polar`. Rewrite using `[hc, powerset_map, powerset_val, Multiset.map_map, Multiset.map_map, Finset.powerset_univ]`. Establish `h` using `alt_sum_multilinear M hM a`.

Establish `h' : (Multiset.map (((fun T : Multiset A => (-1 : ℝ) ^ (d - Multiset.card T) * M fun _ => T.sum) ∘ Multiset.map a) ∘ Finset.val) (Finset.univ : Finset (Finset (Fin d))).val).sum = (d.factorial : ℝ) * M a`. Rewrite using `[← h, Finset.sum_eq_multiset_sum]`. Use `congr 1`. Use `Multiset.map_congr rfl fun T _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, Multiset.card_map, Finset.card_val]`.

Both sides reduce to the same expression. Rewrite using `[h', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]`.
-/
theorem polar_diag : ∀ (A : Type) [AddCommGroup A] (d : ℕ) (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ),
    (∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) →
    ∀ a : Fin d → A, polar (fun b => M fun _ => b) (Multiset.map a Finset.univ.val) = M a := by
  intro A _ d M hM a
  have hc : Multiset.card (Multiset.map a Finset.univ.val) = d := by simp
  unfold Pad.polar
  rw [hc, powerset_map, powerset_val, Multiset.map_map, Multiset.map_map, Finset.powerset_univ]
  have h := alt_sum_multilinear M hM a
  have h' : (Multiset.map (((fun T : Multiset A => (-1 : ℝ) ^ (d - Multiset.card T) * M fun _ => T.sum) ∘
      Multiset.map a) ∘ Finset.val) (Finset.univ : Finset (Finset (Fin d))).val).sum =
      (d.factorial : ℝ) * M a := by
    rw [← h, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun T _ => ?_
    simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rfl
  rw [h', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]

end GlobalTheory.ShFam.PolarMultilinear
