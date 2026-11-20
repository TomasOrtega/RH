import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

/- English proof (translation)
Introduce `O K _ _ _ n M hM c hc`. Use `haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1`. Set `f : Module.End O M` to `{ toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩ map_add' := fun x y => by ext1; simp [Matrix.mulVec_add] map_smul' := fun a x => by ext1`. Simplify using `only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]`. Rewrite using `[Matrix.mulVec_smul] }`.

Establish `hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `v`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]`. Establish `h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K)` using `rfl`. Rewrite using `[← h1, ih]`.

Establish `key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K)`. Introduce `q`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => intro v`. Simplify using `[Matrix.add_mulVec, hp, hq]`.

Consider the case `monomial k a`. Introduce `v`. Rewrite using `[aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]`. Take `⟨p, hp, hpf⟩` from `LinearMap.exists_monic_and_aeval_eq_zero O f`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.aeval_def]`. Use `set A := aeval c p`. Establish `hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A)`. Rewrite using `[Submodule.span_le]`. Introduce `v hv`.

Use `key p ⟨v, hv⟩` as an intermediate fact. Rewrite `this` using `[hpf]`. Simplify using `using this`. Rewrite `hker` using `[hM.2, top_le_iff, LinearMap.ker_eq_top]`. Establish `: Matrix.toLin' A = 0` using `by rw [Matrix.toLin'_apply']; exact hker`.

Simplify using `using this`.
-/
theorem isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this

end GlobalTheory.LatOrb
