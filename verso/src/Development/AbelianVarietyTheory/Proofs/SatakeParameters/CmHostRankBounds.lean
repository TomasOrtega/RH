import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W1

/- English proof (translation)
Introduce `k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv`. Use `letI := φ.toAlgebra`. Use `haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap k L c = ((φ (algebraMap k B c) : B') : L)`.

Rewrite using `[hφ, IsScalarTower.algebraMap_apply k K L]`. Both sides reduce to the same expression. Use `haveI : Algebra.FormallyUnramified B B' := hU`. Establish `hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `x -`. Take `⟨y, rfl⟩` from `(KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add _ _ h1 h2 => rw [map_add]`.

Conclude with `add_mem h1 h2`. Consider the case `tmul b m`. Rewrite using `[KaehlerDifferential.mapBaseChange_tmul]`. Use `Submodule.smul_mem _ b ?_` and prove the remaining obligations. Establish `hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B))`.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Rewrite using `[KaehlerDifferential.map_D]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`.

Consider the case `smul a x _ hx`. Rewrite using `[map_smul, ← algebraMap_smul B' a]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈ Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a))` using `hspan ▸ Submodule.mem_top`. Take `⟨n, f, g, hsum⟩` from `Submodule.mem_span_set'.mp hmem`.

Use `choose w hw using fun j => (g j).2`. Use `⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩` and prove the remaining obligations. Establish `key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j))`. Establish `h` using `congrArg (KaehlerDifferential.map k k B' L) hsum`. Rewrite `h` using `[map_sum, KaehlerDifferential.map_D]`.

Use `h.symm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]`. Apply the tactic sequence `first | rfl | simp [Subalgebra.smul_def]`. Establish `hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a))`.

Introduce `a`. Rewrite using `[mapDR, ExteriorAlgebra.lift_ι_apply]`. Simplify using `[map1]`. Repeatedly rewrite using `[hpull, key, map_sum, map_smul]`.
-/
theorem dv_mem_span_of_formallyUnramified : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv
  letI := φ.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap k L c = ((φ (algebraMap k B c) : B') : L)
    rw [hφ, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : Algebra.FormallyUnramified B B' := hU
  have hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)
    induction y with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B' a]
        exact Submodule.smul_mem _ _ hx
  have hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈
      Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) := hspan ▸ Submodule.mem_top
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose w hw using fun j => (g j).2
  refine ⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩
  have key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j)) := by
    have h := congrArg (KaehlerDifferential.map k k B' L) hsum
    rw [map_sum, KaehlerDifferential.map_D] at h
    refine h.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]
    first | rfl | simp [Subalgebra.smul_def]
  have hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a)) := by
    intro a
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1]
  simp_rw [hpull, key, map_sum, map_smul]

end GlobalTheory.W1
