import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDMap

variable {B : Type} [CommRing B] {J : Ideal B}

/- English proof (translation)
Use `Ideal.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, h1, h2, rfl⟩`. Conclude with `⟨l, h1, h.trans h2, rfl⟩`.
-/
theorem fil_anti (δ : DividedPowers J) {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m := by
  refine Ideal.span_mono ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact ⟨l, h1, h.trans h2, rfl⟩

/- English proof (translation)
Apply the tactic sequence `refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp`.
-/
theorem fil_zero_top (δ : DividedPowers J) : fil δ 0 = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp

/- English proof (translation)
Apply the tactic sequence `refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]`.
-/
theorem dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n := by
  refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]

/- English proof (translation)
Rewrite using `[fil, fil, Ideal.span_mul_span', Ideal.span_le]`. Introduce and unpack `_ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩`. Use `Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Break down `List.mem_append.1 hp with hp | hp` into its components or cases.

Conclude with `h1 p hp`. Conclude with `h1' p hp`. Simplify using `using Nat.add_le_add h2 h2'`. Simplify using the standard rewrite rules.
-/
theorem fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h1 p hp
    · exact h1' p hp
  · simpa using Nat.add_le_add h2 h2'
  · simp

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap, fil, Ideal.span_le]`. Introduce and unpack `_ ⟨l, h1, h2, rfl⟩`. Establish `hJ : ∀ p ∈ l, f p.2 ∈ J'` using `fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))`. Use `Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`.

Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hq`. Conclude with `hJ p hp`. Simplify `h2` using `[List.map_map, Function.comp_def]`. Rewrite using `[map_list_prod, List.map_map, List.map_map]`. Use `congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Conclude with `(hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm`.
-/
theorem map_fil_le' {C : Type} [CommRing C] {J' : Ideal C} (δ : DividedPowers J) (δ' : DividedPowers J')
    (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) : (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

/- English proof (translation)
Establish `hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f → a * b ∈ (fil δ (m + n)).map f`. Introduce `m n a b ha hb`. Establish `: (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f`. Rewrite using `[← Ideal.map_mul]`. Conclude with `Ideal.map_mono (fil_mul_le δ m n)`.

Conclude with `this (Ideal.mul_mem_mul ha hb)`. Establish `hzero : ∀ c : C, c ∈ (fil δ 0).map f`. Introduce `c`. Rewrite using `[fil_zero_top, Ideal.map_top]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `y ∈ Ideal.span (f '' (J : Set B)) at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, rfl⟩` from `hx`. Introduce `n`. Rewrite using `[hf.dpow_comp a ha]`. Conclude with `Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)`. Consider the case `zero`.

Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `hzero _`. Rewrite using `[δ'.dpow_eval_zero hn.ne']`. Conclude with `Ideal.zero_mem _`.

Consider the case `add x y hx hy ihx ihy`. Introduce `n`. Rewrite using `[δ'.dpow_add hx hy]`. Use `Ideal.sum_mem _ fun k hk ↦ ?_` and prove the remaining obligations. Establish `hk' : k.1 + k.2 = n` using `by simpa using hk`.

Rewrite using `[← hk']`. Conclude with `hmul (ihx k.1) (ihy k.2)`. Consider the case `smul c x hx ih`. Introduce `n`. Rewrite using `[smul_eq_mul, δ'.dpow_mul hx]`.

Conclude with `Ideal.mul_mem_left _ _ (ih n)`. Establish `hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) → (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f`. Introduce `l hl`. Proceed by induction on `l with`. Consider the case `nil => exact hzero _`.

Consider the case `cons p l ih`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons]`. Conclude with `hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, h1, h2, rfl⟩`.

Conclude with `Ideal.map_mono (fil_anti δ h2) (hprod l h1)`.
-/
theorem fil_le_map {C : Type} [CommRing C] (δ : DividedPowers J) (f : B →+* C)
    (δ' : DividedPowers (J.map f)) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    fil δ' N ≤ (fil δ N).map f := by
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (fil_mul_le δ m n)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (fil_anti δ h2) (hprod l h1)

/- English proof (translation)
Introduce `B B' _ _ J δ φ δ' hφ`. Use `⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩` and prove the remaining obligations. Introduce `B'' _ J'' δ'' ψ hψ`. Use `IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)`. Introduce and unpack `n _ ⟨a, ha, rfl⟩`. Establish `h1` using `hφ.dpow_comp (n := n) a ha`. Establish `h2` using `hψ.dpow_comp (n := n) a ha`. Rewrite using `[h1]`.

Conclude with `h2.symm`.
-/
theorem extended_dividedPowers : ∀ {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} (δ : DividedPowers J) (φ : B →+* B') (δ' : DividedPowers (J.map φ)), IsDPMorphism δ δ' φ → (∀ r, fil δ' r = (fil δ r).map φ) ∧ ∀ {B'' : Type} [CommRing B''] {J'' : Ideal B''} (δ'' : DividedPowers J'') (ψ : B' →+* B''), IsDPMorphism δ δ'' (ψ.comp φ) → IsDPMorphism δ' δ'' ψ := by
  intro B B' _ _ J δ φ δ' hφ
  refine ⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩
  intro B'' _ J'' δ'' ψ hψ
  refine IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)
  · rintro n _ ⟨a, ha, rfl⟩
    have h1 := hφ.dpow_comp (n := n) a ha
    have h2 := hψ.dpow_comp (n := n) a ha
    rw [h1]
    exact h2.symm

end GlobalTheory.CompanionTheory.PDMap
