import Mathlib

namespace GroundTheory.LocalField

open Filter Topology Uniformity

section Filtration

variable {G : Type*} [Group G]

@[to_additive AddFiltrationCauchy
]
def FiltrationCauchy (F : ℕ → Subgroup G) (x : ℕ → G) : Prop :=
  ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, x n / x m ∈ F N

@[to_additive AddFiltrationTendsto
]
def FiltrationTendsto (F : ℕ → Subgroup G) (x : ℕ → G) (y : G) : Prop :=
  ∀ N, ∃ M, ∀ n ≥ M, x n / y ∈ F N

@[to_additive AddFiltrationComplete
]
def FiltrationComplete (F : ℕ → Subgroup G) : Prop :=
  ∀ x : ℕ → G, FiltrationCauchy F x → ∃ y, FiltrationTendsto F x y

@[to_additive AddFiltrationSeparated
]
def FiltrationSeparated (F : ℕ → Subgroup G) : Prop :=
  ∀ g : G, (∀ n, g ∈ F n) → g = 1

end Filtration

section Surjectivity

variable {G H : Type*} [Group G] [Group H]

@[to_additive map_eq_of_graded_surjective_add
]
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `hmap k le_rfl g hg`. Introduce `h hh`. Rewrite using `[Subgroup.mem_map]`.

Establish `hs : ∀ (n : ℕ) (a : H), ∃ g : G, k ≤ n → a ∈ E (φ n) → g ∈ F n ∧ a / f g ∈ E (φ (n + 1))`. Introduce `n a`. Distinguish the cases in `hc : k ≤ n ∧ a ∈ E (φ n)`. Take `⟨g, hg1, hg2⟩` from `hgr n hc.1 a hc.2`. Conclude with `⟨g, fun _ _ => ⟨hg1, hg2⟩⟩`.

Conclude with `⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩`. Use `choose s hs using hs`. Take `⟨r, hr0, hrs⟩ : ∃ r : ℕ → H, r 0 = h ∧ ∀ j, r (j + 1) = r j / f (s (k + j) (r j))` from `⟨fun j => Nat.rec h (fun j rj => rj / f (s (k + j) rj)) j, rfl, fun _ => rfl⟩`. Establish `hrE : ∀ j, r j ∈ E (φ (k + j))`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simpa [hr0] using hh`. Consider the case `succ j ih`. Rewrite using `[hrs, ← add_assoc]`. Conclude with `(hs (k + j) (r j) (Nat.le_add_right k j) ih).2`.

Take `⟨D, hD⟩ : ∃ D : ℕ → G, ∀ j, D j = s (k + j) (r j)` from `⟨_, fun _ => rfl⟩`. Establish `hDF : ∀ j, D j ∈ F (k + j)` using `fun j => by`. Rewrite using `[hD]`. Conclude with `(hs (k + j) (r j) (Nat.le_add_right k j) (hrE j)).1`. Establish `hrs' : ∀ j, r (j + 1) = r j / f (D j)` using `fun j => by rw [hrs, hD]`.

Take `⟨x, hx0, hxs⟩ : ∃ x : ℕ → G, x 0 = D 0 ∧ ∀ j, x (j + 1) = D (j + 1) * x j` from `⟨fun j => Nat.rec (D 0) (fun j xj => D (j + 1) * xj) j, rfl, fun _ => rfl⟩`. Establish `hxr : ∀ j, h / f (x j) = r (j + 1)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => rw [hx0, hrs', hr0]`.

Consider the case `succ j ih`. Rewrite using `[hxs, hrs' (j + 1), ← ih, map_mul]`. Simplify using `only [div_eq_mul_inv, mul_inv_rev, mul_assoc]`. Establish `hxF : ∀ m d, x (m + d) / x m ∈ F (k + m + 1)`. Introduce `m d`.

Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Establish `e : x (m + (d + 1)) / x m = D (m + d + 1) * (x (m + d) / x m)`. Rewrite using `[← add_assoc, hxs, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]`.

Rewrite using `[e]`. Conclude with `(F _).mul_mem (hF (by omega) (hDF (m + d + 1))) ih`. Establish `hC : FiltrationCauchy F x`. Introduce `N`. Use `⟨N, fun m hm n hn => ?_⟩` and prove the remaining obligations.

Break down `le_total m n with hmn | hnm` into its components or cases. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `hF (by omega) (hxF m d)`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Establish `e` using `(F _).inv_mem (hxF n d)`.

Rewrite `e` using `[inv_div]`. Conclude with `hF (by omega) e`. Establish `hxk : ∀ j, x j ∈ F k`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => rw [hx0]`. Simplify using `using hDF 0`. Consider the case `succ j ih => rw [hxs]; exact (F k).mul_mem (hF (by omega) (hDF (j + 1))) ih`. Take `⟨y, hy⟩` from `hG x hC`. Take `⟨M0, hM0⟩` from `hy k`.

Establish `hyk : y ∈ F k`. Establish `e : (x M0 / y)⁻¹ * x M0 = y`. Simplify using `only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]`. Rewrite using `[← e]`. Conclude with `(F k).mul_mem ((F k).inv_mem (hM0 M0 le_rfl)) (hxk M0)`.

Use `⟨y, hyk, ?_⟩` and prove the remaining obligations. Establish `h1 : h / f y = 1`. Apply `hH` to reduce the goal to its premises. Introduce `m`. Take `⟨N0, hN0⟩` from `Filter.tendsto_atTop_atTop.mp hφ m`.

Take `⟨M, hM⟩` from `hy (max N0 k)`. Establish `e : h / f y = r (max M N0 + 1) * f (x (max M N0) / y)`. Rewrite using `[← hxr (max M N0), map_div]`. Simplify using `only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]`. Rewrite using `[e]`.

Use `(E m).mul_mem ?_ ?_` and prove the remaining obligations. Conclude with `hE (hN0 _ (by omega)) (hrE (max M N0 + 1))`. Conclude with `hE (hN0 _ (le_max_left _ _)) (hmap _ (le_max_right _ _) _ (hM (max M N0) (le_max_left _ _)))`. Conclude with `(div_eq_one.mp h1).symm`. Use the proof step `@[to_additive surjective_of_graded_surjective_add`.

Use the proof step `]`.
-/
theorem map_eq_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmap k le_rfl g hg
  intro h hh
  rw [Subgroup.mem_map]
  have hs : ∀ (n : ℕ) (a : H), ∃ g : G,
      k ≤ n → a ∈ E (φ n) → g ∈ F n ∧ a / f g ∈ E (φ (n + 1)) := by
    intro n a
    by_cases hc : k ≤ n ∧ a ∈ E (φ n)
    · obtain ⟨g, hg1, hg2⟩ := hgr n hc.1 a hc.2
      exact ⟨g, fun _ _ => ⟨hg1, hg2⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hs

  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → H, r 0 = h ∧ ∀ j, r (j + 1) = r j / f (s (k + j) (r j)) :=
    ⟨fun j => Nat.rec h (fun j rj => rj / f (s (k + j) rj)) j, rfl, fun _ => rfl⟩
  have hrE : ∀ j, r j ∈ E (φ (k + j)) := by
    intro j
    induction j with
    | zero => simpa [hr0] using hh
    | succ j ih =>
      rw [hrs, ← add_assoc]
      exact (hs (k + j) (r j) (Nat.le_add_right k j) ih).2

  obtain ⟨D, hD⟩ : ∃ D : ℕ → G, ∀ j, D j = s (k + j) (r j) := ⟨_, fun _ => rfl⟩
  have hDF : ∀ j, D j ∈ F (k + j) := fun j => by
    rw [hD]
    exact (hs (k + j) (r j) (Nat.le_add_right k j) (hrE j)).1
  have hrs' : ∀ j, r (j + 1) = r j / f (D j) := fun j => by rw [hrs, hD]

  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → G, x 0 = D 0 ∧ ∀ j, x (j + 1) = D (j + 1) * x j :=
    ⟨fun j => Nat.rec (D 0) (fun j xj => D (j + 1) * xj) j, rfl, fun _ => rfl⟩
  have hxr : ∀ j, h / f (x j) = r (j + 1) := by
    intro j
    induction j with
    | zero => rw [hx0, hrs', hr0]
    | succ j ih =>
      rw [hxs, hrs' (j + 1), ← ih, map_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have hxF : ∀ m d, x (m + d) / x m ∈ F (k + m + 1) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : x (m + (d + 1)) / x m = D (m + d + 1) * (x (m + d) / x m) := by
        rw [← add_assoc, hxs, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      rw [e]
      exact (F _).mul_mem (hF (by omega) (hDF (m + d + 1))) ih
  have hC : FiltrationCauchy F x := by
    intro N
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hF (by omega) (hxF m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have e := (F _).inv_mem (hxF n d)
      rw [inv_div] at e
      exact hF (by omega) e
  have hxk : ∀ j, x j ∈ F k := by
    intro j
    induction j with
    | zero => rw [hx0]; simpa using hDF 0
    | succ j ih => rw [hxs]; exact (F k).mul_mem (hF (by omega) (hDF (j + 1))) ih
  obtain ⟨y, hy⟩ := hG x hC
  obtain ⟨M0, hM0⟩ := hy k
  have hyk : y ∈ F k := by
    have e : (x M0 / y)⁻¹ * x M0 = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [← e]
    exact (F k).mul_mem ((F k).inv_mem (hM0 M0 le_rfl)) (hxk M0)
  refine ⟨y, hyk, ?_⟩
  have h1 : h / f y = 1 := by
    apply hH
    intro m
    obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp hφ m
    obtain ⟨M, hM⟩ := hy (max N0 k)
    have e : h / f y = r (max M N0 + 1) * f (x (max M N0) / y) := by
      rw [← hxr (max M N0), map_div]
      simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine (E m).mul_mem ?_ ?_
    · exact hE (hN0 _ (by omega)) (hrE (max M N0 + 1))
    · exact hE (hN0 _ (le_max_left _ _))
        (hmap _ (le_max_right _ _) _ (hM (max M N0) (le_max_left _ _)))
  exact (div_eq_one.mp h1).symm

@[to_additive surjective_of_graded_surjective_add
]
/- English proof (translation)
Introduce `h`. Establish `e` using `map_eq_of_graded_surjective hF hE hG hH f hφ 0 (fun n _ => hmap n) (fun n _ => hgr n)`. Establish `hh : h ∈ E (φ 0)` using `by rw [hE0]; exact Subgroup.mem_top h`. Rewrite `hh` using `[← e, hF0]`. Take `⟨g, -, rfl⟩` from `hh`.

Conclude with `⟨g, rfl⟩`.
-/
theorem surjective_of_graded_surjective {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hF0 : F 0 = ⊤) (hE0 : E (φ 0) = ⊤) (hmap : ∀ n, ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    Function.Surjective f := by
  intro h
  have e := map_eq_of_graded_surjective hF hE hG hH f hφ 0 (fun n _ => hmap n)
    (fun n _ => hgr n)
  have hh : h ∈ E (φ 0) := by rw [hE0]; exact Subgroup.mem_top h
  rw [← e, hF0] at hh
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

end Surjectivity

section Topological

@[to_additive addFiltrationComplete_of_hasBasis
]
/- English proof (translation)
Introduce `x hx`. Establish `hU : (𝓤 G).HasBasis (fun _ : ℕ => True) (fun n => (fun p : G × G => p.2 / p.1) ⁻¹' (F n : Set G))`. Rewrite using `[uniformity_eq_comap_nhds_one G]`. Conclude with `hb.comap _`. Establish `hcs : CauchySeq x`.

Rewrite using `[hU.cauchySeq_iff]`. Introduce `N _`. Take `⟨M, hM⟩` from `hx N`. Conclude with `⟨M, fun m hm n hn => hM m hm n hn⟩`. Take `⟨y, hy⟩` from `cauchySeq_tendsto_of_complete hcs`.

Use `⟨y, fun N => ?_⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun n => x n / y) atTop (𝓝 1)`. Simplify using `using hy.div_const' y`. Conclude with `eventually_atTop.mp ((hb.tendsto_right_iff.mp h1) N trivial)`. Use the proof step `@[to_additive addFiltrationSeparated_of_hasBasis`.

Use the proof step `]`.
-/
theorem filtrationComplete_of_hasBasis {G : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] {F : ℕ → Subgroup G}
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G))) :
    FiltrationComplete F := by
  intro x hx
  have hU : (𝓤 G).HasBasis (fun _ : ℕ => True)
      (fun n => (fun p : G × G => p.2 / p.1) ⁻¹' (F n : Set G)) := by
    rw [uniformity_eq_comap_nhds_one G]
    exact hb.comap _
  have hcs : CauchySeq x := by
    rw [hU.cauchySeq_iff]
    intro N _
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => hM m hm n hn⟩
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨y, fun N => ?_⟩
  have h1 : Tendsto (fun n => x n / y) atTop (𝓝 1) := by
    simpa using hy.div_const' y
  exact eventually_atTop.mp ((hb.tendsto_right_iff.mp h1) N trivial)

@[to_additive addFiltrationSeparated_of_hasBasis
]
/- English proof (translation)
Introduce `g hg`. Assume the negation of the conclusion as `hne`. Take `⟨i, -, hi⟩` from `hb.mem_iff.mp (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hne)))`. Conclude with `hi (hg i) rfl`. Use the proof step `@[to_additive map_eq_of_graded_surjective_of_hasBasis_add`.

Use the proof step `]`.
-/
theorem filtrationSeparated_of_hasBasis {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    {E : ℕ → Subgroup H}
    (hb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H))) :
    FiltrationSeparated E := by
  intro g hg
  by_contra hne
  obtain ⟨i, -, hi⟩ := hb.mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hne)))
  exact hi (hg i) rfl

@[to_additive map_eq_of_graded_surjective_of_hasBasis_add
]
/- English proof (translation)
The claim follows from `map_eq_of_graded_surjective hF hE (filtrationComplete_of_hasBasis hFb) (filtrationSeparated_of_hasBasis hEb) f hφ k hmap hgr`.
-/
theorem map_eq_of_graded_surjective_of_hasBasis {G H : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] [Group H] [TopologicalSpace H] [T1Space H]
    {F : ℕ → Subgroup G} {E : ℕ → Subgroup H} (hF : Antitone F) (hE : Antitone E)
    (hFb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G)))
    (hEb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H)))
    (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) :=
  map_eq_of_graded_surjective hF hE (filtrationComplete_of_hasBasis hFb)
    (filtrationSeparated_of_hasBasis hEb) f hφ k hmap hgr

end Topological

end GroundTheory.LocalField
