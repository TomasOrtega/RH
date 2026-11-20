import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCore

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev TgPlace (X : Loc) := Σ j : Fin (numSeg X.TT), Option (Fin (segS X.TT j))

def tgTop (X : Loc) : TgPlace X → X.TT
  | ⟨j, none⟩ => topEnd X j
  | ⟨j, some i⟩ => topOdd X j i

/- English proof (translation)
Introduce `h`. Establish `e : segNext X.TT j = segPos X.TT j i` using `congrArg Subtype.val h`. Conclude with `(pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j).2)`.
-/
theorem tg_end_ne_odd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topEnd X j ≠ topOdd X j i := by
  intro h
  have e : segNext X.TT j = segPos X.TT j i := congrArg Subtype.val h
  exact (pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j).2)

/- English proof (translation)
Take `⟨j, a⟩` from `pl`. Consider the cases of `a with`. Consider the case `none => exact Or.inl rfl`. Consider the case `some i => exact Or.inr ⟨i, rfl⟩`.
-/
theorem tgTop_mem (X : Loc) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    ((tgTop X pl, b), c) ∈ segVars X pl.1 := by
  obtain ⟨j, a⟩ := pl
  cases a with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩

/- English proof (translation)
Introduce and unpack `⟨j, a⟩ ⟨j', a'⟩ h`. Establish `hj : j = j'`. Assume the negation of the conclusion as `hne`. Establish `h1` using `tgTop_mem X ⟨j, a⟩ true 0`. Establish `h2` using `tgTop_mem X ⟨j', a'⟩ true 0`.

Rewrite `h2` using `[← h]`. Conclude with `Set.disjoint_left.1 (segVars_disj X j j' hne) h1 h2`. Substitute `hj` using the available equality. Consider the cases of `a with`. Consider the case `none`.

Consider the cases of `a' with`. Consider the case `none => rfl`. Consider the case `some i => exact absurd h (tg_end_ne_odd X j i)`. Consider the case `some i`. Consider the cases of `a' with`.

Consider the case `none => exact absurd h.symm (tg_end_ne_odd X j i)`. Consider the case `some i' => rw [topOdd_inj X j h]`.
-/
theorem tgTop_inj (X : Loc) : Function.Injective (tgTop X) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  have hj : j = j' := by
    by_contra hne
    have h1 := tgTop_mem X ⟨j, a⟩ true 0
    have h2 := tgTop_mem X ⟨j', a'⟩ true 0
    rw [← h] at h2
    exact Set.disjoint_left.1 (segVars_disj X j j' hne) h1 h2
  subst hj
  cases a with
  | none =>
    cases a' with
    | none => rfl
    | some i => exact absurd h (tg_end_ne_odd X j i)
  | some i =>
    cases a' with
    | none => exact absurd h.symm (tg_end_ne_odd X j i)
    | some i' => rw [topOdd_inj X j h]

/- English proof (translation)
Introduce and unpack `⟨t, ht⟩`. Distinguish the cases in `he : Even t.val`. Take `⟨j0, hj0⟩` from `List.mem_iff_get.mp ((ev_mem X.TT t).mpr ⟨ht, he⟩)`. Take `⟨j, hj⟩` from `(rot_bij (numSeg X.TT)).2 j0`. Use `⟨⟨j, none⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show segNext X.TT j = t`. Rewrite using `[next_eq, hj]`. Conclude with `hj0`. Take `⟨j, hj⟩` from `odd_covered X.TT h2 t ht he`. Establish `hs` using `Finset.mem_filter.mp hj`.

Take `⟨i, hi⟩` from `List.mem_iff_get.mp (mem_dists.mpr ⟨t, hs, rfl⟩)`. Use `⟨⟨j, some i⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show segPos X.TT j i = t`. Unfold `segPos`. Rewrite using `[hi, posAdd_cdist]`.
-/
theorem tgTop_surj (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Surjective (tgTop X) := by
  rintro ⟨t, ht⟩
  by_cases he : Even t.val
  · obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp ((ev_mem X.TT t).mpr ⟨ht, he⟩)
    obtain ⟨j, hj⟩ := (rot_bij (numSeg X.TT)).2 j0
    refine ⟨⟨j, none⟩, Subtype.ext ?_⟩
    show segNext X.TT j = t
    rw [next_eq, hj]
    exact hj0
  · obtain ⟨j, hj⟩ := odd_covered X.TT h2 t ht he
    have hs := Finset.mem_filter.mp hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem_dists.mpr ⟨t, hs, rfl⟩)
    refine ⟨⟨j, some i⟩, Subtype.ext ?_⟩
    show segPos X.TT j i = t
    unfold segPos
    rw [hi, posAdd_cdist]

/- English proof (translation)
Assemble the required witnesses or components as `⟨tgTop_inj X, tgTop_surj X h2⟩`.
-/
theorem tgTop_bij (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Bijective (tgTop X) :=
  ⟨tgTop_inj X, tgTop_surj X h2⟩

/- English proof (translation)
Rewrite using `[← (tgTop_bij X h2).prod_comp f, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_option]`. Both sides reduce to the same expression.
-/
theorem tg_prod_places {M : Type} [CommMonoid M] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (f : X.TT → M) :
    ∏ t, f t = ∏ j, (f (topEnd X j) * ∏ i, f (topOdd X j i)) := by
  rw [← (tgTop_bij X h2).prod_comp f, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_option]
  rfl

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fintype.prod_prod_type, tg_prod_places X h2]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `segMon`. Simplify using `only [Fintype.prod_bool, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tg_mono_split (O : Type) [CommRing O] [IsDomain O] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (A : MonH X) :
    (monomial A (1 : KK O) : RHH O X) = ∏ j, segMon O X j A := by
  rw [MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fintype.prod_prod_type, tg_prod_places X h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold segMon
  simp only [Fintype.prod_bool, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Rewrite using `[← Finset.prod_filter]`. Use `Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `l _`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩`. Introduce `l _ l' _ h`.

Establish `: S.sigma + l.val = S.sigma + l'.val` using `congrArg Fin.val h`. Conclude with `Fin.ext (by omega)`. Introduce `i hi`. Establish `hi' : S.sigma ≤ i.val` using `(Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2`. Use `⟨⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩` and prove the remaining obligations.

Apply `Fin.ext` to reduce the goal to its premises. Use `show S.sigma + (i.val - S.sigma) = i.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem tg_prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (g : Fin s → M) :
    ∏ l : Fin S.t, g (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then g i else 1 := by
  rw [← Finset.prod_filter]
  refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    have : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  · intro i hi
    have hi' : S.sigma ≤ i.val := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    refine ⟨⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega

end Formalism.MainNotions.ColumnSystems.Pf
