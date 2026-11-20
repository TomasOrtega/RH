import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.GeometricLemmaFiltration

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf`. Take `⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j)` from `⟨_, rfl⟩`. Establish `hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l)`. Introduce `l y`. Rewrite using `[hC]`.

Establish `hcov : ∀ y, ∃ l, y ∈ C l` using `fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩`. Establish `hdisj : Pairwise fun i j => Disjoint (C i) (C j)`. Introduce `i j hij`. Rewrite using `[Set.disjoint_left]`. Introduce `y hi hj`.

Conclude with `hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))`. Establish `hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l`. Rewrite using `[hC]`. Conclude with `hcl`. Establish `hsorb : ∀ l y, y ∈ C l → s y ∈ C l`.

Introduce `l y hy`. Rewrite `hy`, the goal using `[hCl]`. Take `⟨g, rfl⟩` from `hy`. Conclude with `⟨τ g, by rw [hcomm, hfix]⟩`. Establish `key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ g hg`. Rewrite `hg` using `[GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero]`.

Establish `hg0 : g = 0`. Use function extensionality and compare the values at `y`. Assume the negation of the conclusion as `hy`. Conclude with `hg.2 hy`. Rewrite using `[hg0, map_zero]`.

Consider the case `succ j ih`. Introduce `hjk g hg`. Establish `hj : j < k` using `by omega`. Establish `hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩` using `GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩`. Use `hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩) (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg` and prove the remaining obligations.

Rewrite using `[Set.inter_comm]`. Establish `h1` using `GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩`. Rewrite using `[h1, hC]`. Introduce `h y hy`. Rewrite `hy`, the goal using `[GroundTheory.Automorphic.Parabolic.mem_cellUnion]`.

Take `⟨l, hl, hyl⟩` from `hy`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Rewrite `hyl`, the goal using `[hCl]`. Take `⟨g', rfl⟩` from `hyl`. Conclude with `⟨h * g', mul_smul _ _ _⟩`.

Introduce `y`. Rewrite using `[GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, hsy⟩`. Take `⟨m, hm⟩` from `hcov y`.

Establish `hlm : l = m` using `(huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))`. Substitute `hlm` using the available equality. Conclude with `⟨l, hl, hm⟩`. Introduce and unpack `⟨l, hl, hy⟩`. Conclude with `⟨l, hl, hsorb l y hy⟩`.

Introduce `g' hg'`. Rewrite `hg'` using `[Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn]`. Take `⟨hg1, hg2⟩` from `hg'`. Apply `ih (by omega)` to reduce the goal to its premises. Rewrite using `[GroundTheory.Automorphic.Whittaker.mem_supportedIn]`.

Use `⟨hg1.1, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hyU` using `hg1.2 hy`. Rewrite `hyU`, the goal using `[GroundTheory.Automorphic.Parabolic.mem_cellUnion]`. Take `⟨l, hl, hyl⟩` from `hyU`.

Use `⟨l, ?_, hyl⟩` and prove the remaining obligations. Break down `Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq` into its components or cases. Conclude with `hlt`. It suffices to derive a contradiction. Apply `hy` to reduce the goal to its premises.

Apply `hg2` to reduce the goal to its premises. Establish `hleq : l = ⟨j, hj⟩` using `Fin.ext heq`. Rewrite `hyl` using `[hleq]`. Conclude with `subset_closure hyl`. Apply `key k le_rfl f` to reduce the goal to its premises.

Rewrite using `[GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]`. Conclude with `⟨hf, Set.subset_univ _⟩`.
-/
theorem UpperTheory.Gal.LocD.distZero :
    CellStep → DistZero := by
  intro hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf
  obtain ⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j) := ⟨_, rfl⟩
  have hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l) := by
    intro l y
    rw [hC]
  have hcov : ∀ y, ∃ l, y ∈ C l := fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    exact hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))
  have hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l := by
    rw [hC]
    exact hcl
  have hsorb : ∀ l y, y ∈ C l → s y ∈ C l := by
    intro l y hy
    rw [hCl] at hy ⊢
    obtain ⟨g, rfl⟩ := hy
    exact ⟨τ g, by rw [hcomm, hfix]⟩
  have key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero] at hg
      have hg0 : g = 0 := by
        funext y
        by_contra hy
        exact hg.2 hy
      rw [hg0, map_zero]
    | succ j ih =>
      intro hjk g hg
      have hj : j < k := by omega
      have hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩ :=
        GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩
      refine hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum
        (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩)
        (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg
      · rw [Set.inter_comm]
        have h1 := GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩
        rw [h1, hC]
      · intro h y hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hy ⊢
        obtain ⟨l, hl, hyl⟩ := hy
        refine ⟨l, hl, ?_⟩
        rw [hCl] at hyl ⊢
        obtain ⟨g', rfl⟩ := hyl
        exact ⟨h * g', mul_smul _ _ _⟩
      · intro y
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]
        constructor
        · rintro ⟨l, hl, hsy⟩
          obtain ⟨m, hm⟩ := hcov y
          have hlm : l = m := (huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))
          subst hlm
          exact ⟨l, hl, hm⟩
        · rintro ⟨l, hl, hy⟩
          exact ⟨l, hl, hsorb l y hy⟩
      · intro g' hg'
        rw [Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn] at hg'
        obtain ⟨hg1, hg2⟩ := hg'
        apply ih (by omega)
        rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn]
        refine ⟨hg1.1, ?_⟩
        intro y hy
        have hyU := hg1.2 hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hyU ⊢
        obtain ⟨l, hl, hyl⟩ := hyU
        refine ⟨l, ?_, hyl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact hlt
        · exfalso
          apply hy
          apply hg2
          have hleq : l = ⟨j, hj⟩ := Fin.ext heq
          rw [hleq] at hyl
          exact subset_closure hyl
  apply key k le_rfl f
  rw [GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]
  exact ⟨hf, Set.subset_univ _⟩
