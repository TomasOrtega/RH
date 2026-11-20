import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCuspSplit
import GroundTheory.AutomorphicForms.UnitaryAdmissible
import GroundTheory.AutomorphicForms.GL2Classical.Irreducible

noncomputable section

namespace GroundTheory.Automorphic

namespace AutomorphicForm

open NumberField MeasureTheory CuspidalSpectrum Polynomial UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Take `⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩` from `exists_archCartanData (K := K) (n := n)`. Take `⟨μ, hμ⟩ : ∃ μ : Measure (Reduction.normOneGL K n), μ.IsHaarMeasure` from `⟨Measure.haar, inferInstance⟩`. Conclude with `exists_isCompl_of_finite (cuspToL2 μ) (fun a ha h0 => injOn_cuspToL2 μ ha (fun _ _ => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm)) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun X …`.
-/
theorem exists_compl_centralCuspForms (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hUρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U)
    (hUσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hUτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) :
    ∃ C : Submodule ℂ (cuspForms K n), C ≤ centralCuspForms K n ∧
      (∀ X, ∀ φ ∈ C, (gkModuleCusp K n).ρ X φ ∈ C) ∧ (∀ k, ∀ φ ∈ C, (gkModuleCusp K n).σ k φ ∈ C) ∧
      (∀ g, ∀ φ ∈ C, finRepCusp K n g φ ∈ C) ∧ U ⊓ C = ⊥ ∧ U ⊔ C = centralCuspForms K n := by
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData (K := K) (n := n)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (Reduction.normOneGL K n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  exact exists_isCompl_of_finite (cuspToL2 μ)
    (fun a ha h0 => injOn_cuspToL2 μ ha (fun _ _ => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm))
    (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc)
    (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc) b
    (fun φ => exists_aeval_uActionCusp_laplacianU_eq_zero φ b ε B hε horth hsymm hinv hK)
    (fun U₀ _ P hP hPd S hS => finiteDimensional_of_eigen b P hP hPd 0
      ((U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)).comap (AdelicGLn.integralFiniteGL K n).subtype)
      (U₀.isOpen.preimage continuous_subtype_val) S fun φ hφ =>
        ⟨(hS φ hφ).1, by rw [zero_smul]; exact (hS φ hφ).2.1, fun u hu => (hS φ hφ).2.2 _ hu⟩)
    U hU hUρ hUσ hUτ

/- English proof (translation)
Use `set Mx := cuspSubmodule K n U hρ hσ hτ with hMx`. Take `⟨u, huU, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hne' : (⊥ : Subrepresentation Mx.fullRep) ≠ ⊤`. Introduce `h`. Establish `hmem : (⟨u, huU⟩ : U) ∈ (⊤ : Subrepresentation Mx.fullRep).toSubmodule` using `trivial`.

Rewrite `hmem` using `[← h]`. Conclude with `hu0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hmem))`. Use `{ toNontrivial := ⟨⟨⊥, ⊤, hne'⟩⟩, eq_bot_or_eq_top := fun Y => ?_ }` and prove the remaining obligations. Establish `hY : ∀ p, ∀ y ∈ Y.toSubmodule, Mx.fullRep p y ∈ Y.toSubmodule` using `fun p y hy => Y.apply_mem_toSubmodule p hy`. Use `set W := Y.toSubmodule.map U.subtype with hW`.

Establish `hWρ : ∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W`. Introduce and unpack `X _ ⟨y, hy, rfl⟩`. Use `⟨_, hY (FreeMonoid.of (Sum.inl X), 1) y hy, ?_⟩` and prove the remaining obligations. Use `show (((Mx.gk.rep (FreeMonoid.of (Sum.inl X))) (Mx.τ 1 y) : U) : cuspForms K n) = _`. Rewrite using `[map_one, Module.End.one_apply, IsExpLieAlgebra.GKModule.rep_of_inl]`.

Both sides reduce to the same expression. Establish `hWσ : ∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W`. Introduce and unpack `k _ ⟨y, hy, rfl⟩`. Use `⟨_, hY (FreeMonoid.of (Sum.inr k), 1) y hy, ?_⟩` and prove the remaining obligations. Use `show (((Mx.gk.rep (FreeMonoid.of (Sum.inr k))) (Mx.τ 1 y) : U) : cuspForms K n) = _`.

Rewrite using `[map_one, Module.End.one_apply, IsExpLieAlgebra.GKModule.rep_of_inr]`. Both sides reduce to the same expression. Establish `hWτ : ∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W`. Introduce and unpack `g _ ⟨y, hy, rfl⟩`. Use `⟨_, hY (1, g) y hy, ?_⟩` and prove the remaining obligations.

Use `show (((Mx.gk.rep 1) (Mx.τ g y) : U) : cuspForms K n) = _`. Rewrite using `[map_one, Module.End.one_apply]`. Both sides reduce to the same expression. Break down `hmin W (Submodule.map_subtype_le _ _) hWρ hWσ hWτ with h | h` into its components or cases. Use `left`.

Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show Y.toSubmodule = (⊥ : Submodule ℂ U)`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Establish `: (y : cuspForms K n) ∈ W` using `⟨y, hy, rfl⟩`.

Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 this))`. Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show Y.toSubmodule = (⊤ : Submodule ℂ U)`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `: (y : cuspForms K n) ∈ W` using `by rw [h]; exact y.2`. Take `⟨y', hy', e⟩` from `this`. Rewrite using `[← Subtype.ext e]` and apply the resulting hypothesis.
-/
theorem isIrreducible_cuspSubmodule_of (U : Submodule ℂ (cuspForms K n))
    (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) (hne : U ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ (cuspForms K n), W ≤ U → (∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W) →
      (∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W) → (∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W) →
      W = ⊥ ∨ W = U) :
    (cuspSubmodule K n U hρ hσ hτ).IsIrreducible := by
  set Mx := cuspSubmodule K n U hρ hσ hτ with hMx
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hne' : (⊥ : Subrepresentation Mx.fullRep) ≠ ⊤ := by
    intro h
    have hmem : (⟨u, huU⟩ : U) ∈ (⊤ : Subrepresentation Mx.fullRep).toSubmodule := trivial
    rw [← h] at hmem
    exact hu0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hmem))
  refine { toNontrivial := ⟨⟨⊥, ⊤, hne'⟩⟩, eq_bot_or_eq_top := fun Y => ?_ }
  have hY : ∀ p, ∀ y ∈ Y.toSubmodule, Mx.fullRep p y ∈ Y.toSubmodule := fun p y hy =>
    Y.apply_mem_toSubmodule p hy
  set W := Y.toSubmodule.map U.subtype with hW
  have hWρ : ∀ X, ∀ φ ∈ W, (gkModuleCusp K n).ρ X φ ∈ W := by
    rintro X _ ⟨y, hy, rfl⟩
    refine ⟨_, hY (FreeMonoid.of (Sum.inl X), 1) y hy, ?_⟩
    show (((Mx.gk.rep (FreeMonoid.of (Sum.inl X))) (Mx.τ 1 y) : U) : cuspForms K n) = _
    rw [map_one, Module.End.one_apply, IsExpLieAlgebra.GKModule.rep_of_inl]
    rfl
  have hWσ : ∀ k, ∀ φ ∈ W, (gkModuleCusp K n).σ k φ ∈ W := by
    rintro k _ ⟨y, hy, rfl⟩
    refine ⟨_, hY (FreeMonoid.of (Sum.inr k), 1) y hy, ?_⟩
    show (((Mx.gk.rep (FreeMonoid.of (Sum.inr k))) (Mx.τ 1 y) : U) : cuspForms K n) = _
    rw [map_one, Module.End.one_apply, IsExpLieAlgebra.GKModule.rep_of_inr]
    rfl
  have hWτ : ∀ g, ∀ φ ∈ W, finRepCusp K n g φ ∈ W := by
    rintro g _ ⟨y, hy, rfl⟩
    refine ⟨_, hY (1, g) y hy, ?_⟩
    show (((Mx.gk.rep 1) (Mx.τ g y) : U) : cuspForms K n) = _
    rw [map_one, Module.End.one_apply]
    rfl
  rcases hmin W (Submodule.map_subtype_le _ _) hWρ hWσ hWτ with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    show Y.toSubmodule = (⊥ : Submodule ℂ U)
    rw [eq_bot_iff]
    intro y hy
    have : (y : cuspForms K n) ∈ W := ⟨y, hy, rfl⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 this))
  · right
    apply Subrepresentation.toSubmodule_injective
    show Y.toSubmodule = (⊤ : Submodule ℂ U)
    rw [eq_top_iff]
    intro y _
    have : (y : cuspForms K n) ∈ W := by rw [h]; exact y.2
    obtain ⟨y', hy', e⟩ := this
    rwa [← Subtype.ext e]

variable (K n) in

structure CuspidalAutomorphicRepresentation where

  carrier : Submodule ℂ (cuspForms K n)
  le_central : carrier ≤ centralCuspForms K n
  stable_ρ : ∀ X, ∀ φ ∈ carrier, (gkModuleCusp K n).ρ X φ ∈ carrier
  stable_σ : ∀ k, ∀ φ ∈ carrier, (gkModuleCusp K n).σ k φ ∈ carrier
  stable_τ : ∀ g, ∀ φ ∈ carrier, finRepCusp K n g φ ∈ carrier
  isIrreducible : (cuspSubmodule K n carrier stable_ρ stable_σ stable_τ).IsIrreducible
  exists_compl : ∃ C : Submodule ℂ (cuspForms K n), C ≤ centralCuspForms K n ∧
    (∀ X, ∀ φ ∈ C, (gkModuleCusp K n).ρ X φ ∈ C) ∧ (∀ k, ∀ φ ∈ C, (gkModuleCusp K n).σ k φ ∈ C) ∧
    (∀ g, ∀ φ ∈ C, finRepCusp K n g φ ∈ C) ∧ carrier ⊓ C = ⊥ ∧ carrier ⊔ C = centralCuspForms K n

namespace CuspidalAutomorphicRepresentation

def ofIrreducible (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) :
    CuspidalAutomorphicRepresentation K n where
  carrier := U
  le_central := hU
  stable_ρ := hρ
  stable_σ := hσ
  stable_τ := hτ
  isIrreducible := hirr
  exists_compl := exists_compl_centralCuspForms U hU hρ hσ hτ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem carrier_ofIrreducible (U : Submodule ℂ (cuspForms K n)) (hU hρ hσ hτ hirr) :
    (ofIrreducible (K := K) (n := n) U hU hρ hσ hτ hirr).carrier = U := rfl

abbrev toModule (π : CuspidalAutomorphicRepresentation K n) : AdelicGKModule K n π.carrier :=
  cuspSubmodule K n π.carrier π.stable_ρ π.stable_σ π.stable_τ

/- English proof (translation)
The claim follows from `isAdmissible_cuspSubmodule π.carrier π.stable_ρ π.stable_σ π.stable_τ π.isIrreducible`.
-/
theorem isAdmissible (π : CuspidalAutomorphicRepresentation K n) : π.toModule.IsAdmissible :=
  isAdmissible_cuspSubmodule π.carrier π.stable_ρ π.stable_σ π.stable_τ π.isIrreducible

/- English proof (translation)
The claim follows from `AutomorphicForm.nonempty_adelicDecomposition π.toModule π.isIrreducible π.isAdmissible`.
-/
theorem nonempty_adelicDecomposition (π : CuspidalAutomorphicRepresentation K n) :
    Nonempty (AdelicDecomposition π.toModule) :=
  AutomorphicForm.nonempty_adelicDecomposition π.toModule π.isIrreducible π.isAdmissible

end CuspidalAutomorphicRepresentation

open GL2Classical ModularForm CongruenceSubgroup in

def CuspidalAutomorphicRepresentation.ofEigenform {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeCusp N p k f = c • f)
    (hf1 : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) : CuspidalAutomorphicRepresentation ℚ 2 :=
  have hst := isGKFStable_gkfSpan (liftCusp f)
  have hle : gkfSpan (liftCusp f) ≤ centralCuspForms ℚ 2 :=
    gkfSpan_le ⟨fun X _ hv => ρ_mem_centralCuspForms X hv, fun x _ hv => σ_mem_centralCuspForms x hv,
      fun g _ hv => finRepCusp_mem_centralCuspForms g hv⟩
      (fun s x => centralSection_of_mem_translateSpanCusp f (liftCusp_mem_translateSpanCusp f) s x)
  have hirr := gkfSpan_liftCusp_irreducible f hf hf1
  CuspidalAutomorphicRepresentation.ofIrreducible (gkfSpan (liftCusp f)) hle hst.1 hst.2.1 hst.2.2
    (isIrreducible_cuspSubmodule_of _ hst.1 hst.2.1 hst.2.2 hirr.1
      fun W hW hWρ hWσ hWτ => hirr.2 W ⟨hWρ, hWσ, hWτ⟩ hW)

open GL2Classical ModularForm CongruenceSubgroup in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem CuspidalAutomorphicRepresentation.carrier_ofEigenform {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeCusp N p k f = c • f)
    (hf1 : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1) :
    (CuspidalAutomorphicRepresentation.ofEigenform f hf hf1).carrier = gkfSpan (liftCusp f) := rfl

end AutomorphicForm

end GroundTheory.Automorphic
