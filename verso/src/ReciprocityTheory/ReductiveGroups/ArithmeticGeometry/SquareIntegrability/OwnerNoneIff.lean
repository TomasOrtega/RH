import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivDeterminantPolyTensor

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Cols
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

def colB (p : Σ j : Fin nb, Fin (bs j).i) : Fin n := (bs p.1).col p.2

variable {bs}

/- English proof (translation)
Introduce and unpack `⟨j, a⟩ ⟨j', a'⟩ h`. Distinguish the cases in `hj : j = j'`. Substitute `hj` using the available equality. Establish `ha : a = a'` using `(bs j).col_inj h`. Substitute `ha` using the available equality.

Both sides reduce to the same expression. Conclude with `absurd h (hD j j' hj a a')`.
-/
theorem colB_inj (hD : Disj bs) : Function.Injective (colB bs) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  by_cases hj : j = j'
  · subst hj
    have ha : a = a' := (bs j).col_inj h
    subst ha
    rfl
  · exact absurd h (hD j j' hj a a')

variable (bs)

open Classical in

def owner (k : Fin n) : Option (Σ j : Fin nb, Fin (bs j).i) :=
  if h : ∃ p, colB bs p = k then some h.choose else none

variable {bs}

/- English proof (translation)
Establish `h' : ∃ q, colB bs q = colB bs p` using `⟨p, rfl⟩`. Rewrite using `[owner, dif_pos h']`. Conclude with `congrArg some (colB_inj hD h'.choose_spec)`.
-/
theorem owner_colB (hD : Disj bs) (p : Σ j : Fin nb, Fin (bs j).i) : owner bs (colB bs p) = some p := by
  have h' : ∃ q, colB bs q = colB bs p := ⟨p, rfl⟩
  rw [owner, dif_pos h']
  exact congrArg some (colB_inj hD h'.choose_spec)

/- English proof (translation)
Distinguish the cases in `h' : ∃ q, colB bs q = k`. Rewrite `h` using `[owner, dif_pos h']`. Take `rfl` from `Option.some_injective _ h`. Conclude with `h'.choose_spec`. Rewrite `h` using `[owner, dif_neg h']`.

Consider the cases of `h`.
-/
theorem colB_of_owner {k : Fin n} {p : Σ j : Fin nb, Fin (bs j).i} (h : owner bs k = some p) :
    colB bs p = k := by
  by_cases h' : ∃ q, colB bs q = k
  · rw [owner, dif_pos h'] at h
    obtain rfl := Option.some_injective _ h
    exact h'.choose_spec
  · rw [owner, dif_neg h'] at h
    cases h

/- English proof (translation)
Rewrite using `[owner, dif_neg (show ¬∃ q, colB bs q = k from fun ⟨q, hq⟩ => h q hq)]`.
-/
theorem owner_eq_none {k : Fin n} (h : ∀ p, colB bs p ≠ k) : owner bs k = none := by
  rw [owner, dif_neg (show ¬∃ q, colB bs q = k from fun ⟨q, hq⟩ => h q hq)]

/- English proof (translation)
Use `⟨fun h p hp => ?_, owner_eq_none⟩` and prove the remaining obligations. Substitute `hp` using the available equality. Rewrite `h` using `[owner_colB hD]`. Consider the cases of `h`.
-/
theorem owner_none_iff (hD : Disj bs) (k : Fin n) : owner bs k = none ↔ ∀ p, colB bs p ≠ k := by
  refine ⟨fun h p hp => ?_, owner_eq_none⟩
  subst hp
  rw [owner_colB hD] at h
  cases h

/- English proof (translation)
Rewrite using `[← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]`. Use `congr 1`. Rewrite using `[← Finset.prod_image (s := Finset.univ) (g := colB bs) (by`. Introduce `a _ b _ h`. Conclude with `colB_inj hD h)]`.

Use `congr 1`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, owner_none_iff hD, not_forall, ne_eq, not_not]`.
-/
theorem prod_cols {M : Type*} [CommMonoid M] (hD : Disj bs) (f : Fin n → M) :
    ∏ k, f k = (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), f k) * ∏ p, f (colB bs p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
  congr 1
  rw [← Finset.prod_image (s := Finset.univ) (g := colB bs) (by
    intro a _ b _ h
    exact colB_inj hD h)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, owner_none_iff hD,
    not_forall, ne_eq, not_not]

end Cols

section Letters
variable (X : PT E) {bs : Fin nb → Block E n X.dim}

/- English proof (translation)
Take `⟨j0, a0⟩` from `p`. Rewrite using `[Multiset.filter_map]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `(Multiset.Nodup.ext (Finset.univ.nodup.filter _) (Finset.univ.nodup.map (fun r r' h => by simpa using h))).2 ?_` and prove the remaining obligations.

Introduce and unpack `⟨j, r, a⟩`. Simplify using `only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp, Multiset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hja : (⟨j, a⟩ : Σ j : Fin nb, Fin (bs j).i) = ⟨j0, a0⟩` using `colB_inj hD h`.

Consider the cases of `hja`. Conclude with `⟨r, rfl⟩`. Introduce and unpack `⟨r', h⟩`. Consider the cases of `h`. Both sides reduce to the same expression.

Use `_ = _ := by rw [Multiset.map_map]; rfl`.
-/
theorem filter_positions (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    (Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = colB bs p) =
      Multiset.map (fun r : Fin (bs p.1).c => letter bs T ⟨p.1, (r, p.2)⟩) Finset.univ.val := by
  obtain ⟨j0, a0⟩ := p
  rw [Multiset.filter_map]
  calc _ = Multiset.map (letter bs T)
        (Multiset.map (fun r : Fin (bs j0).c => (⟨j0, (r, a0)⟩ : Slot bs)) Finset.univ.val) := by
        congr 1
        refine (Multiset.Nodup.ext (Finset.univ.nodup.filter _)
          (Finset.univ.nodup.map (fun r r' h => by simpa using h))).2 ?_
        rintro ⟨j, r, a⟩
        simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp,
          Multiset.mem_map]
        constructor
        · intro h
          have hja : (⟨j, a⟩ : Σ j : Fin nb, Fin (bs j).i) = ⟨j0, a0⟩ := colB_inj hD h
          cases hja
          exact ⟨r, rfl⟩
        · rintro ⟨r', h⟩
          cases h
          rfl
    _ = _ := by rw [Multiset.map_map]; rfl

open Classical in
/- English proof (translation)
Establish `hc : ∀ (L : List (Fin n × Vsp X.dim)) (k : Fin n), ((colL L k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) = Multiset.map Prod.snd (Multiset.filter (fun x => x.1 = k) (L : Multiset _))`. Introduce `L k`. Simplify using `[colL]`. Rewrite using `[hc, lst, ← Multiset.map_coe, Multiset.coe_toList, Multiset.filter_map, Multiset.map_map]`. Establish `h2` using `congrArg (Multiset.map (fun l : Letter n X.dim => EuclideanSpace.single l.2 (1 : ℂ))) (filter_positions X hD T p)`.

Rewrite `h2` using `[Multiset.map_map]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `exact Multiset.filter_congr fun _ _ => Iff.rfl`.
-/
theorem colL_block (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    ((colL (lst X bs T) (colB bs p) : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      Multiset.map (fun r : Fin (bs p.1).c => EuclideanSpace.single
        (⟨(bs p.1).τ, Fin.castLE (bs p.1).hi (T p.1 r p.2)⟩ : Idx X.dim) (1 : ℂ)) Finset.univ.val := by
  have hc : ∀ (L : List (Fin n × Vsp X.dim)) (k : Fin n),
      ((colL L k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
        Multiset.map Prod.snd (Multiset.filter (fun x => x.1 = k) (L : Multiset _)) := by
    intro L k
    simp [colL]
  rw [hc, lst, ← Multiset.map_coe, Multiset.coe_toList, Multiset.filter_map, Multiset.map_map]
  have h2 := congrArg (Multiset.map (fun l : Letter n X.dim => EuclideanSpace.single l.2 (1 : ℂ)))
    (filter_positions X hD T p)
  rw [Multiset.map_map] at h2
  convert h2 using 2
  all_goals first
    | rfl
    | exact Multiset.filter_congr fun _ _ => Iff.rfl

/- English proof (translation)
Rewrite `hk` using `[owner_none_iff hD]`. Unfold `colL`. Rewrite using `[List.map_eq_nil_iff, List.filter_eq_nil_iff]`. Introduce `x hx`. Unfold `lst at hx`.

Take `⟨l, hl, rfl⟩` from `List.mem_map.1 hx`. Take `⟨t, -, rfl⟩` from `Multiset.mem_map.1 (Multiset.mem_toList.1 hl)`. Introduce `h`. Conclude with `hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)`.
-/
theorem colL_empty (hD : Disj bs) (T : Choice bs) {k : Fin n} (hk : owner bs k = none) :
    colL (lst X bs T) k = [] := by
  rw [owner_none_iff hD] at hk
  unfold colL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  unfold lst at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toList.1 hl)
  intro h
  exact hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)

end Letters

end

end ReciprocityTheory.ChartRestriction.G.I2
