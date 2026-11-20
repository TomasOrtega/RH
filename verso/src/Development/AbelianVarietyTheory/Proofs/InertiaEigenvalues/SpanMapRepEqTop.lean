import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

namespace GlobalTheory.SpanMapTop

/- English proof (translation)
Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g, rfl⟩`. Consider the case `zero`.

Establish `: (0 : Matrix (Fin r) (Fin r) A).map (algebraMap A B) = 0`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `: (x + y).map (algebraMap A B) = x.map (algebraMap A B) + y.map (algebraMap A B)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: (a • x).map (algebraMap A B) = (algebraMap A B a) • x.map (algebraMap A B)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_span {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (M : Matrix (Fin r) (Fin r) A)
    (hM : M ∈ Submodule.span A (Set.range f)) :
    M.map (algebraMap A B) ∈
      Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin r) (Fin r) A).map (algebraMap A B) = 0 := by
      ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (x + y).map (algebraMap A B) = x.map (algebraMap A B) + y.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (a • x).map (algebraMap A B) = (algebraMap A B a) • x.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `M _`. Rewrite using `[Matrix.matrix_eq_sum_single M]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `map_mem_span (B := B) f (Matrix.single i j 1) (h ▸ Submodule.mem_top)`.

Establish `h2 : Matrix.single i j (M i j) = M i j • (Matrix.single i j (1 : A)).map (algebraMap A B)`. Use extensionality with `a b`. Simplify using `only [Matrix.single, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h2]`.

Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem span_map_eq_top {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (h : Submodule.span A (Set.range f) = ⊤) :
    Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h1 := map_mem_span (B := B) f (Matrix.single i j 1) (h ▸ Submodule.mem_top)
  have h2 : Matrix.single i j (M i j) =
      M i j • (Matrix.single i j (1 : A)).map (algebraMap A B) := by
    ext a b
    simp only [Matrix.single, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [h2]
  exact Submodule.smul_mem _ _ h1

/- English proof (translation)
The claim follows from `span_map_eq_top (B := B) (fun g => GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ g) h`.
-/
theorem span_mapRep_eq_top {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} {B : Type} [CommRing B]
    [Algebra A B] {ρ : Γ →* GL (Fin r) A}
    (h : Submodule.span A (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) = ⊤) :
    Submodule.span B
      (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (algebraMap A B) ρ))) = ⊤ :=
  span_map_eq_top (B := B) (fun g => GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ g) h

end GlobalTheory.SpanMapTop
