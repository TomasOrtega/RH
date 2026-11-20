import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
private theorem hd_cons' {I M : Type} [AddCommGroup M] (c : List I → M) (i : I) (x : List I) :
    hd c (i :: x) = c x - hd (fun y => c (i :: y)) x := by
  unfold hd
  rw [List.length_cons, Finset.sum_range_succ', sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [pow_succ]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem hd_sub' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I) :
    hd (fun y => c y - c' y) x = hd c x - hd c' x := by
  unfold hd
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem hd_hd' {I M : Type} [AddCommGroup M] (x : List I) :
    ∀ c : List I → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons i x ih =>
    intro c
    rw [hd_cons']
    have h : (fun y => hd c (i :: y)) = fun y => c y - hd (fun z => c (i :: z)) y :=
      funext fun y => hd_cons' c i y
    rw [h, hd_sub', ih]
    simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem hd_map' {I J M : Type} [AddCommGroup M] (f : J → I) (c : List I → M) (x : List J) :
    hd (fun y => c (y.map f)) x = hd c (x.map f) := by
  unfold hd
  rw [List.length_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.eraseIdx_map]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem hd_hom' {I M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (c : List I → M)
    (x : List I) : hd (fun y => f (c y)) x = f (hd c x) := by
  unfold hd
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_zsmul f _ _).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem hd_congr' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I)
    (h : ∀ y : List I, y.length + 1 = x.length → (∀ i ∈ y, i ∈ x) → c y = c' y) : hd c x = hd c' x := by
  unfold hd
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < x.length := Finset.mem_range.1 hj
  rw [h (x.eraseIdx j) (by rw [List.length_eraseIdx_of_lt hj']; omega)
    (fun i hi => List.mem_of_mem_eraseIdx hi)]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.A.hdFacts :
    HdFacts := by
  refine ⟨fun I M _ c x => hd_hd' x c, fun I M _ c i x => hd_cons' c i x,
    fun I J M _ f c x => hd_map' f c x, fun I M N _ _ f c x => hd_hom' f c x,
    fun I M _ c c' x h => hd_congr' c c' x h, ?_⟩
  intro Γ I M _ _ _ _ ρ k c hc γ x hx
  rw [← hd_map']
  refine Eq.trans (hd_congr' _ (fun y => (ρ γ).toAddMonoidHom (c y)) x fun y hy _ => ?_)
    (hd_hom' (ρ γ).toAddMonoidHom c x)
  exact hc γ y (by omega)
