import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIndepEigAtOfAnyFamily

open Formalism.L2.Col

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ (i : I) (k : ℕ) (v : V), ((T i - σ (y i) • (1 : Module.End ℂ W)) ^ k) (j v) = j (((op i - y i • (1 : Module.End K V)) ^ k) v)`. Introduce `i k`. Proceed by induction on `k with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `v`. Rewrite using `[pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]`. Use `congr 1`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smulₛₗ, hT]`.

Rewrite using `[eigAt, Submodule.mem_iInf]`. Introduce `i`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 (eigAt_le op y i hv)`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Conclude with `⟨k, by rw [key, hk, map_zero]⟩`.
-/
theorem map_mem_eigAt_of_semilinear {K V W I : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V)
    (T : I → Module.End ℂ W) (hT : ∀ i v, T i (j v) = j (op i v)) (y : I → K) (v : V)
    (hv : v ∈ eigAt op y) : j v ∈ eigAt T (fun i => σ (y i)) := by
  have key : ∀ (i : I) (k : ℕ) (v : V),
      ((T i - σ (y i) • (1 : Module.End ℂ W)) ^ k) (j v)
        = j (((op i - y i • (1 : Module.End K V)) ^ k) v) := by
    intro i k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hT]
  rw [eigAt, Submodule.mem_iInf]
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (eigAt_le op y i hv)
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨k, by rw [key, hk, map_zero]⟩

/- English proof (translation)
Introduce `K V W I _ _ _ _ _ _ σ j op T e x w hT hc hs he hw hw0 hx`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `hall : ∀ v : V, j (e v) ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z`. Introduce `v`.

Establish `hv : v ∈ ⨆ y, eigAt op y`. Rewrite using `[iSup_eigAt_eq_top hc hs]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.iSup_induction' with`. Consider the case `mem y v hv`.

Establish `hev : e v ∈ eigAt op y` using `eigAt_le_comap he y hv`. Distinguish the cases in `hy : ∀ i, σ (y i) = x i`. Establish `h0 : e v ∈ eigAt op y ⊓ LinearMap.range e` using `⟨hev, ⟨v, rfl⟩⟩`. Rewrite `h0` using `[hno y hy, Submodule.mem_bot]`. Rewrite using `[h0, map_zero]`.

Conclude with `Submodule.zero_mem _`. Establish `hne : (fun i => σ (y i)) ≠ x` using `fun h => hy fun i => congrFun h i`. Conclude with `le_iSup₂_of_le (f := fun (z : I → ℂ) (_ : z ≠ x) => eigAt T z) _ hne le_rfl (map_mem_eigAt_of_semilinear σ j op T hT y _ hev)`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Establish `hw' : w ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z`. Use `Submodule.span_le.2 ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨v, rfl⟩, rfl⟩`.

Conclude with `hall v`. Establish `hd` using `iSupIndep_eigAt_of_any_family ℂ W I T x`. Conclude with `hw0 ((Submodule.mem_bot ℂ).1 (hd.le_bot ⟨mem_eigAt_of_forall_apply hx, hw'⟩))`.
-/
theorem exists_eigAt_inf_range_ne_bot_of_mem_span :
    ∀ {K V W I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V) (T : I → Module.End ℂ W) (e : Module.End K V) (x : I → ℂ) (w : W), (∀ i v, T i (j v) = j (op i v)) → PairComm op → SplitOver op → (∀ i, Commute (op i) e) → w ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) → w ≠ 0 → (∀ i, T i w = x i • w) → ∃ y : I → K, (∀ i, σ (y i) = x i) ∧ eigAt op y ⊓ LinearMap.range e ≠ ⊥ := by
  intro K V W I _ _ _ _ _ _ σ j op T e x w hT hc hs he hw hw0 hx
  by_contra hno
  push Not at hno
  have hall : ∀ v : V, j (e v) ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    intro v
    have hv : v ∈ ⨆ y, eigAt op y := by
      rw [iSup_eigAt_eq_top hc hs]; exact Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem y v hv =>
      have hev : e v ∈ eigAt op y := eigAt_le_comap he y hv
      by_cases hy : ∀ i, σ (y i) = x i
      · have h0 : e v ∈ eigAt op y ⊓ LinearMap.range e := ⟨hev, ⟨v, rfl⟩⟩
        rw [hno y hy, Submodule.mem_bot] at h0
        rw [h0, map_zero]
        exact Submodule.zero_mem _
      · have hne : (fun i => σ (y i)) ≠ x := fun h => hy fun i => congrFun h i
        exact le_iSup₂_of_le (f := fun (z : I → ℂ) (_ : z ≠ x) => eigAt T z) _ hne le_rfl
          (map_mem_eigAt_of_semilinear σ j op T hT y _ hev)
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  have hw' : w ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    refine Submodule.span_le.2 ?_ hw
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact hall v
  have hd := iSupIndep_eigAt_of_any_family ℂ W I T x
  exact hw0 ((Submodule.mem_bot ℂ).1 (hd.le_bot ⟨mem_eigAt_of_forall_apply hx, hw'⟩))

end GlobalTheory
