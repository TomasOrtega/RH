import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenLat

/- English proof (translation)
Unfold `GlobalTheory.EtaJoin.lat at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← D.nd.prMt_lat i]`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Take `⟨b, hb⟩` from `hO a`. Establish `h1 : a • x = (a : D.what₂.LL) • x` using `rfl`. Rewrite using `[h1, LinearMap.map_smulₛₗ, ← hb, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem prMt_mem_range (D : D7) (i : D.nd.Loc)
    (hO : ∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range)
    (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) (hy : y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i)) :
    D.nd.prMt i y ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := by
  unfold GlobalTheory.EtaJoin.lat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rw [← D.nd.prMt_lat i]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hO a
    have h1 : a • x = (a : D.what₂.LL) • x := rfl
    rw [h1, LinearMap.map_smulₛₗ, ← hb, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `D i S hO hΦ hC c hc m`. Establish `hm : (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m ∈ LinearMap.range (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1)` using `⟨m, rfl⟩`. Rewrite `hm` using `[← D.nd.prMt_lat i]`. Generalize the expression as in `(1 : KK D.nd i) ⊗ₜ[D.nd.O i] m = v at hm`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨x, hx, rfl⟩` from `hv`. Take `⟨y, hy, hxy⟩` from `hC i c hc x hx`. Take `⟨m', hm'⟩` from `prMt_mem_range D i hO y hy`. Use `⟨m', ?_⟩` and prove the remaining obligations.

Rewrite using `[← hΦ _ x y hxy, ← hm']`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [TensorProduct.tmul_add, map_add, map_add, map_add, ha, hb]⟩`. Consider the case `smul a x _ hx`. Take `⟨b, hb⟩` from `hx`. Use `⟨a • b, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul (KK D.nd i) a, ← algebraMap_smul (KK D.nd i) a x, S.semi, S.semi, map_smul, hb]`.
-/
theorem cenInt_lat : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), (∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range) → (∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x))) → CenInt D → ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m') = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)) := by
  intro D i S hO hΦ hC c hc m
  have hm : (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := ⟨m, rfl⟩
  rw [← D.nd.prMt_lat i] at hm
  generalize (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m = v at hm
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, hxy⟩ := hC i c hc x hx
    obtain ⟨m', hm'⟩ := prMt_mem_range D i hO y hy
    refine ⟨m', ?_⟩
    rw [← hΦ _ x y hxy, ← hm']
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.tmul_add, map_add, map_add, map_add, ha, hb]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a • b, ?_⟩
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (KK D.nd i) a, ← algebraMap_smul (KK D.nd i) a x,
      S.semi, S.semi, map_smul, hb]

end GlobalTheory.PendOf.CenLat
