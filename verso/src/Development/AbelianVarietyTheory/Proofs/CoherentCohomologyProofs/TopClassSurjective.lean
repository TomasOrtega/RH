import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory.CubeTop

variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

omit [LinearOrder ι] in

/- English proof (translation)
The claim follows from `(Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge`.
-/
theorem univ_subset {n : ℕ} (hn : Fintype.card ι = n) (s : {s : Finset ι // s.card = n}) :
    (Finset.univ : Finset ι) ⊆ s.1 :=
  (Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge

def topTerm (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    A.obj Finset.univ →ₗ[R] Cube.Term A n :=
  LinearMap.pi fun s => Cube.res A (univ_subset hn s)

omit [LinearOrder ι] in

/- English proof (translation)
Introduce `x`. Use `⟨x ⟨Finset.univ, hn⟩, funext ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨s, hs⟩`. Take `rfl` from `Finset.eq_univ_of_card s (hs.trans hn.symm)`. Conclude with `Cube.res_self A _ _`.
-/
theorem topTerm_surjective (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    Function.Surjective (topTerm A hn) := by
  intro x
  refine ⟨x ⟨Finset.univ, hn⟩, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  exact Cube.res_self A _ _

/- English proof (translation)
Set `y : ∀ s, A.obj s` to `Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)`. Use `⟨fun s => y s.1, funext ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨s, hs⟩`. Take `rfl` from `Finset.eq_univ_of_card s (hs.trans hn.symm)`. Rewrite using `[Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]`.

Simplify using `only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]`. Conclude with `(Cube.res_self A _ _).symm`. Introduce `j _ hji`. Establish `: (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i` using `fun h => by`. Establish `: j ∈ (Finset.univ.erase i : Finset ι)` using `by simp [hji]`.

Rewrite `this` using `[← h]`. Simplify using `at this`. Simplify using `only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem topTerm_res_mem (A : Cube.{0} ι R) {p : ℕ} (hn : Fintype.card ι = p + 1) (i : ι)
    (x : A.obj (Finset.univ.erase i)) :
    ∃ y, Cube.d A p y = topTerm A hn (Cube.res A (Finset.erase_subset i _) x) := by
  let y : ∀ s, A.obj s := Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)
  refine ⟨fun s => y s.1, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  rw [Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]
  · simp only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]
    exact (Cube.res_self A _ _).symm
  · intro j _ hji
    have : (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i := fun h => by
      have : j ∈ (Finset.univ.erase i : Finset ι) := by simp [hji]
      rw [← h] at this
      simp at this
    simp only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]
  · simp

/- English proof (translation)
Rewrite using `[cubeComplex_d]`. Use `Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))` as an intermediate fact. Conclude with `ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)`.
-/
theorem d_top (A : Cube.{0} ι R) :
    (cubeComplex A).d (Fintype.card ι) (Fintype.card ι + 1) = 0 := by
  rw [cubeComplex_d]
  have := Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

def topClass (A : Cube.{0} ι R) :
    A.obj Finset.univ →ₗ[R] (cubeComplex A).homology (Fintype.card ι) :=
  ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv).hom ∘ₗ topTerm A rfl

/- English proof (translation)
The claim follows from `((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫ ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp) (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)`.
-/
theorem topClass_surjective (A : Cube.{0} ι R) : Function.Surjective (topClass A) :=
  ((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)

/- English proof (translation)
Establish `key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0`. Introduce `n hn`. Take `⟨p, rfl⟩ : ∃ p, n = p + 1` from `Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')`. Take `⟨y, hy⟩` from `topTerm_res_mem A hn i x`. Use `(cubeComplex A).d_pOpcycles p (p + 1)` as an intermediate fact.

Rewrite `this` using `[cubeComplex_d]`. Rewrite using `[← hy]`. Conclude with `congr(($this).hom y)`. Use `key _ rfl` as an intermediate fact. Set `g` to `((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp) (d_top A)).inv.hom`.

Conclude with `(congrArg g this).trans (map_zero g)`.
-/
theorem topClass_res (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by
  have key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom
      (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')
    obtain ⟨y, hy⟩ := topTerm_res_mem A hn i x
    have := (cubeComplex A).d_pOpcycles p (p + 1)
    rw [cubeComplex_d] at this
    rw [← hy]
    exact congr(($this).hom y)
  have := key _ rfl
  let g := ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
    (d_top A)).inv.hom
  exact (congrArg g this).trans (map_zero g)

/- English proof (translation)
Rewrite using `[eq_top_iff, ← LinearMap.range_eq_top.2 (topClass_surjective A), LinearMap.range_eq_map, ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, rfl⟩`. Distinguish the cases in `h : T a.1 = Finset.univ`. Conclude with `Submodule.subset_span ⟨a.1, h, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by`.

Simplify `h` using `[Finset.eq_univ_iff_forall]`. Use `topClass_res A i (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩)` as an intermediate fact. Rewrite `this` using `[hb]`. Rewrite using `[this]`. Conclude with `zero_mem _`.
-/
theorem span_topClass {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) :
    Submodule.span R ((fun a : κ => topClass A (b Finset.univ ⟨a, Finset.subset_univ _⟩)) ''
      {a | T a = Finset.univ}) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 (topClass_surjective A), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨a.1, h, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := topClass_res A i (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩)
    rw [hb] at this
    rw [this]
    exact zero_mem _

/- English proof (translation)
Introduce `ι _ _ R _ κ T A b hb`. Establish `h` using `span_topClass T A b hb`. Use `⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩` and prove the remaining obligations. Rewrite `h` using `[Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty, Submodule.span_empty]`. Rewrite using `[HomologicalComplex.exactAt_iff_isZero_homology]`.

Use `(Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)` as an intermediate fact. Conclude with `ModuleCat.isZero_of_subsingleton _`.
-/
theorem main : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R) (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s)), (∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}), Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) → ((∀ a, T a ≠ Finset.univ) → (cubeComplex A).ExactAt (Fintype.card ι)) ∧ ({a | T a = Finset.univ}.Finite → Module.Finite R ((cubeComplex A).homology (Fintype.card ι))) := by
  intro ι _ _ R _ κ T A b hb
  have h := span_topClass T A b hb
  refine ⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty,
      Submodule.span_empty] at h
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := (Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)
    exact ModuleCat.isZero_of_subsingleton _

end GlobalTheory.CubeTop
