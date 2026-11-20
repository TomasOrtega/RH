import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.LocallyProfinite

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `H _ _ _ _ _ _ τ p hp hτ hper L hL`. Take `⟨K, hKc, hKL⟩` from `GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hL.mem_nhds L.one_mem)`. Set `L₀ : Subgroup H` to `{ carrier := {l | ∀ i < p, τ^[i] l ∈ K} one_mem' := fun i _ => by rw [iterate_map_one]; exact K.one_mem mul_mem' := fun ha hb i hi => by`. Rewrite using `[iterate_map_mul]`. Conclude with `K.mul_mem (ha i hi) (hb i hi)`.

Use the proof step `inv_mem' := fun ha i hi => by`. Rewrite using `[iterate_map_inv]`. Conclude with `K.inv_mem (ha i hi) }`. Establish `hset : (L₀ : Set H) = ⋂ i ∈ {i : ℕ | i < p}, τ^[i] ⁻¹' (K : Set H)`. Use extensionality with `l`.

Simplify using `[L₀]`. Establish `hopen : IsOpen (L₀ : Set H)`. Rewrite using `[hset]`. Conclude with `(Set.finite_lt_nat p).isOpen_biInter (fun i _ => K.isOpen.preimage (hτ.iterate i))`. Establish `hsub : (L₀ : Set H) ⊆ K` using `fun l hl => by`.

Use `hl 0 hp` as an intermediate fact. Simplify using `using this`. Use `⟨L₀, hKc.of_isClosed_subset (L₀.isClosed_of_isOpen hopen) hsub, hopen, fun l hl => hKL (hsub hl), fun l => ?_⟩` and prove the remaining obligations. Use `show (∀ i < p, τ^[i] (τ l) ∈ K) ↔ ∀ i < p, τ^[i] l ∈ K`. Prove the components needed by the constructor for the conclusion.

Introduce `h i hi`. Break down `i with _ | j` into its components or cases. Establish `h1` using `h (p - 1) (by omega)`. Rewrite `h1` using `[← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp, hper]`. Simplify using `using h1`.

Rewrite using `[Function.iterate_succ_apply]`. Conclude with `h j (by omega)`. Introduce `h i hi`. Rewrite using `[← Function.iterate_succ_apply]`. Distinguish the cases in `hlt : i + 1 < p`.

Conclude with `h (i + 1) hlt`. Establish `hip : i + 1 = p` using `by omega`. Rewrite using `[Nat.succ_eq_add_one, hip, hper]`. Simplify using `using h 0 hp`.
-/
theorem UpperTheory.Gal.LocD.stabSub :
    StabSub := by
  intro H _ _ _ _ _ _ τ p hp hτ hper L hL
  obtain ⟨K, hKc, hKL⟩ := GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
    (hL.mem_nhds L.one_mem)
  let L₀ : Subgroup H :=
    { carrier := {l | ∀ i < p, τ^[i] l ∈ K}
      one_mem' := fun i _ => by rw [iterate_map_one]; exact K.one_mem
      mul_mem' := fun ha hb i hi => by
        rw [iterate_map_mul]; exact K.mul_mem (ha i hi) (hb i hi)
      inv_mem' := fun ha i hi => by
        rw [iterate_map_inv]; exact K.inv_mem (ha i hi) }
  have hset : (L₀ : Set H) = ⋂ i ∈ {i : ℕ | i < p}, τ^[i] ⁻¹' (K : Set H) := by
    ext l; simp [L₀]
  have hopen : IsOpen (L₀ : Set H) := by
    rw [hset]
    exact (Set.finite_lt_nat p).isOpen_biInter
      (fun i _ => K.isOpen.preimage (hτ.iterate i))
  have hsub : (L₀ : Set H) ⊆ K := fun l hl => by
    have := hl 0 hp
    simpa using this
  refine ⟨L₀, hKc.of_isClosed_subset (L₀.isClosed_of_isOpen hopen) hsub, hopen,
    fun l hl => hKL (hsub hl), fun l => ?_⟩
  show (∀ i < p, τ^[i] (τ l) ∈ K) ↔ ∀ i < p, τ^[i] l ∈ K
  constructor
  · intro h i hi
    rcases i with _ | j
    · have h1 := h (p - 1) (by omega)
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper] at h1
      simpa using h1
    · rw [Function.iterate_succ_apply]
      exact h j (by omega)
  · intro h i hi
    rw [← Function.iterate_succ_apply]
    by_cases hlt : i + 1 < p
    · exact h (i + 1) hlt
    · have hip : i + 1 = p := by omega
      rw [Nat.succ_eq_add_one, hip, hper]
      simpa using h 0 hp
