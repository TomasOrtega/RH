import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

open GroundTheory.Automorphic.CuspidalSpectrum in
/- English proof (translation)
Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace K`. Set `P : UPos (r + s) r → AdeleRing (𝓞 K) K` to `fun p => if p.1 = (Fin.castAdd s i, Fin.natAdd r j) then ((e.symm x, 0) : AdeleRing (𝓞 K) K) else 0`. Use `⟨P, ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ p, (P p).2 = 0`. Introduce `p`.

Distinguish the cases in `hp : p.1 = (Fin.castAdd s i, Fin.natAdd r j)`. Simplify using `[P, hp]`. Simplify using `only [P, hp, if_false]`. Both sides reduce to the same expression. Establish `hc` using `conj_unipGL_eq_archExp (1 : AdelicGLn.AdelicGL K (r + s)) P h0`.

Simplify using `only [inv_one, one_mul, mul_one] at hc`. Rewrite using `[hc]`. Use `congr 1`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Simplify using `[conjArch, archMat, archMatrixEquiv, Matrix.single_apply]`.

Apply the tactic sequence `show _ = e ((blockEntry P a b).1)`. Rewrite using `[blockEntry_apply]`. Distinguish the cases in `hab : Fin.castAdd s i = a ∧ Fin.natAdd r j = b`. Take `⟨rfl, rfl⟩` from `hab`. Establish `hh : ((Fin.castAdd s i : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r j : Fin (r + s)) : ℕ)` using `⟨by simp, by simp⟩`.

Rewrite using `[dif_pos hh, if_pos ⟨rfl, rfl⟩]`. Simplify using `[P, e]`. Rewrite using `[if_neg hab] split_ifs with hh`. Establish `hne : ¬ ((a, b) : Fin (r + s) × Fin (r + s)) = (Fin.castAdd s i, Fin.natAdd r j)`. Introduce `heq`.

Apply `hab` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq] at heq`. Conclude with `⟨heq.1.symm, heq.2.symm⟩`. Simplify using `only [P, hne, if_false]`. Conclude with `(map_zero e).symm`.

Conclude with `(map_zero e).symm`.
-/
private theorem archExp_single (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s)
    (x : mixedSpace K) :
    ∃ P : UPos (r + s) r → AdeleRing (𝓞 K) K,
      archExp (K := K) (n := r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) = unipGL P := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let P : UPos (r + s) r → AdeleRing (𝓞 K) K := fun p =>
    if p.1 = (Fin.castAdd s i, Fin.natAdd r j) then ((e.symm x, 0) : AdeleRing (𝓞 K) K) else 0
  refine ⟨P, ?_⟩
  have h0 : ∀ p, (P p).2 = 0 := by
    intro p
    by_cases hp : p.1 = (Fin.castAdd s i, Fin.natAdd r j)
    · simp [P, hp]
    · simp only [P, hp, if_false]
      rfl
  have hc := conj_unipGL_eq_archExp (1 : AdelicGLn.AdelicGL K (r + s)) P h0
  simp only [inv_one, one_mul, mul_one] at hc
  rw [hc]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp [conjArch, archMat, archMatrixEquiv, Matrix.single_apply]
  show _ = e ((blockEntry P a b).1)
  rw [blockEntry_apply]
  by_cases hab : Fin.castAdd s i = a ∧ Fin.natAdd r j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have hh : ((Fin.castAdd s i : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r j : Fin (r + s)) : ℕ) :=
      ⟨by simp, by simp⟩
    rw [dif_pos hh, if_pos ⟨rfl, rfl⟩]
    simp [P, e]
  · rw [if_neg hab]
    split_ifs with hh
    · have hne : ¬ ((a, b) : Fin (r + s) × Fin (r + s)) = (Fin.castAdd s i, Fin.natAdd r j) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.symm⟩
      simp only [P, hne, if_false]
      exact (map_zero e).symm
    · exact (map_zero e).symm

open GroundTheory.Automorphic.CuspidalSpectrum in
/- English proof (translation)
Introduce `K _ _ r s i j x ψ hψ`. Establish `hψ' : ∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K (r + s)), ψ.1 (unipGL X * g) = ψ.1 g` using `hψ`. Use `show ∀ (m₁ : GL (Fin r) (AdeleRing (𝓞 K) K)) (m₂ : GL (Fin s) (AdeleRing (𝓞 K) K)), (lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ).1 (blk m₁ m₂) = 0`. Introduce `m₁ m₂`. Set `Y : ArchMatrix K (r + s)` to `Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x`.

Set `g : AdelicGLn.AdelicGL K (r + s)` to `blk m₁ m₂`. Establish `hd` using `CuspidalSpectrum.hasDerivAt_archExp ψ g Y 0`. Simplify using `only [zero_smul, CuspidalSpectrum.archExp_zero, mul_one] at hd`. Take `⟨c, hc⟩` from `UpperTheory.blockDiag_conj_unipotent_linear (AdeleRing (𝓞 K) K) r s m₁ m₂`. Establish `hmap : Matrix.GeneralLinearGroup.map (RingHom.id (AdeleRing (𝓞 K) K)) (blk m₁ m₂) = blk m₁ m₂`.

Use `ext`. Both sides reduce to the same expression. Establish `hconst : (fun t : ℝ => ψ.1 (g * CuspidalSpectrum.archExp (t • Y))) = fun _ => ψ.1 g`. Use function extensionality and compare the values at `t`. Establish `hsY : t • Y = Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) (t • x)` using `Matrix.smul_single _ _ _ _`.

Take `⟨P, hP⟩` from `archExp_single K r s i j (t • x)`. Rewrite using `[hsY, hP]`. Establish `h1` using `hc (AdeleRing (𝓞 K) K) (RingHom.id _) P`. Rewrite `h1` using `[hmap]`. Use `show ψ.1 (blk m₁ m₂ * unipGL P) = ψ.1 (blk m₁ m₂)`.

Rewrite using `[h1, hψ']`. Rewrite `hd` using `[hconst]`. Establish `h2` using `hd.unique (hasDerivAt_const (0 : ℝ) (ψ.1 g))`. Conclude with `h2`.
-/
theorem UpperTheory.archExp_single_unipotent_embedding :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s) (x : mixedSpace K), ∀ ψ ∈ NInv K (r + s) r, lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ ∈ Van K r s := by
  intro K _ _ r s i j x ψ hψ
  classical
  have hψ' : ∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K (r + s)),
      ψ.1 (unipGL X * g) = ψ.1 g := hψ
  show ∀ (m₁ : GL (Fin r) (AdeleRing (𝓞 K) K)) (m₂ : GL (Fin s) (AdeleRing (𝓞 K) K)),
    (lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ).1 (blk m₁ m₂) = 0
  intro m₁ m₂
  let Y : ArchMatrix K (r + s) := Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x
  let g : AdelicGLn.AdelicGL K (r + s) := blk m₁ m₂
  have hd := CuspidalSpectrum.hasDerivAt_archExp ψ g Y 0
  simp only [zero_smul, CuspidalSpectrum.archExp_zero, mul_one] at hd
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (AdeleRing (𝓞 K) K) r s m₁ m₂
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id (AdeleRing (𝓞 K) K)) (blk m₁ m₂) = blk m₁ m₂ := by
    ext
    rfl
  have hconst : (fun t : ℝ => ψ.1 (g * CuspidalSpectrum.archExp (t • Y))) = fun _ => ψ.1 g := by
    funext t
    have hsY : t • Y = Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) (t • x) :=
      Matrix.smul_single _ _ _ _
    obtain ⟨P, hP⟩ := archExp_single K r s i j (t • x)
    rw [hsY, hP]
    have h1 := hc (AdeleRing (𝓞 K) K) (RingHom.id _) P
    rw [hmap] at h1
    show ψ.1 (blk m₁ m₂ * unipGL P) = ψ.1 (blk m₁ m₂)
    rw [h1, hψ']
  rw [hconst] at hd
  have h2 := hd.unique (hasDerivAt_const (0 : ℝ) (ψ.1 g))
  exact h2
