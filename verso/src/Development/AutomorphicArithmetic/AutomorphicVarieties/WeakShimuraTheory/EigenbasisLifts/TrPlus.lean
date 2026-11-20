import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Rewrite using `[Matrix.trace_single_mul, one_smul]`.
-/
private theorem entry_eq {A : Type} [CommRing A] {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    X i j = (Matrix.single j i (1 : A) * X).trace := by
  rw [Matrix.trace_single_mul, one_smul]

/- English proof (translation)
Introduce `A G _ _ n ρ hF`. Establish `hs : ∀ h : G, W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single h 1) = W.mat ρ h`. Introduce `h`. Simplify using `[W.GDet.repAlg]`. Establish `hsp : ∀ X : Matrix (Fin n) (Fin n) A, X ∈ Submodule.span A (Set.range (W.mat ρ))`.

Introduce `X`. Unfold `Full at hF`. Rewrite using `[hF]`. Conclude with `Submodule.mem_top`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Use extensionality with `i j`. Conclude with `i.elim0`.

Establish `key : ∀ X, (X * W.GDet.repAlg (W.mat ρ) A z).trace = 0`. Introduce `X`. Proceed by induction on `hsp X using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`.

Rewrite using `[← hs h, ← map_mul, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn]`. Conclude with `hz h`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, Matrix.trace_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]`.

Use extensionality with `i j`. Conclude with `(entry_eq _ i j).trans (key _)`. Introduce `_ _ _ _ hc`. Establish `key : ∀ X, Continuous fun g => (X * W.mat ρ g).trace`. Introduce `X`.

Proceed by induction on `hsp X using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Repeatedly rewrite using `[← map_mul]`. Conclude with `hc.comp (continuous_mul_left h)`.

Consider the case `zero => simpa using continuous_const`. Consider the case `add x y _ _ hx hy`. Repeatedly rewrite using `[add_mul, Matrix.trace_add]`. Conclude with `hx.add hy`. Consider the case `smul a x _ hx`.

Repeatedly rewrite using `[Matrix.smul_mul, Matrix.trace_smul]`. Conclude with `hx.const_smul a`. Establish `hm : Continuous fun g => W.mat ρ g`. Apply `continuous_matrix` to reduce the goal to its premises. Introduce `i j`.

Conclude with `(key (Matrix.single j i 1)).congr (fun g => (entry_eq _ i j).symm)`. Rewrite using `[Units.continuous_iff]`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `(hm.comp continuous_inv).congr fun x => ?_` and prove the remaining obligations. Use `show ((ρ x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = _`.

Rewrite using `[map_inv]`.
-/
theorem UpperTheory.V.Ws.Eb.trPlus :
    ∀ {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A), Full ρ →
        (∀ z : MonoidAlgebra A G, (∀ h : G, (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1 * z) = 0) → W.GDet.repAlg (W.mat ρ) A z = 0) ∧
        ∀ [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] [IsTopologicalGroup G], (Continuous fun g => (W.mat ρ g).trace) → Continuous ρ := by
  intro A G _ _ n ρ hF
  have hs : ∀ h : G, W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single h 1) = W.mat ρ h := by
    intro h
    simp [W.GDet.repAlg]
  have hsp : ∀ X : Matrix (Fin n) (Fin n) A, X ∈ Submodule.span A (Set.range (W.mat ρ)) := by
    intro X
    unfold Full at hF
    rw [hF]
    exact Submodule.mem_top
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      ext i j
      exact i.elim0
    have key : ∀ X, (X * W.GDet.repAlg (W.mat ρ) A z).trace = 0 := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hs h, ← map_mul, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn]
        exact hz h
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    ext i j
    exact (entry_eq _ i j).trans (key _)
  · intro _ _ _ _ hc
    have key : ∀ X, Continuous fun g => (X * W.mat ρ g).trace := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simp_rw [← map_mul]
        exact hc.comp (continuous_mul_left h)
      | zero => simpa using continuous_const
      | add x y _ _ hx hy =>
        simp_rw [add_mul, Matrix.trace_add]
        exact hx.add hy
      | smul a x _ hx =>
        simp_rw [Matrix.smul_mul, Matrix.trace_smul]
        exact hx.const_smul a
    have hm : Continuous fun g => W.mat ρ g := by
      apply continuous_matrix
      intro i j
      exact (key (Matrix.single j i 1)).congr (fun g => (entry_eq _ i j).symm)
    rw [Units.continuous_iff]
    refine ⟨hm, ?_⟩
    refine (hm.comp continuous_inv).congr fun x => ?_
    show ((ρ x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = _
    rw [map_inv]
