import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNegStatement
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.CapelliAdj

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasAdj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (T S : Module.End ℂ V) : Prop :=
  ∀ φ ψ : V, B (T φ) ψ = B φ (S ψ)

/- English proof (translation)
Introduce `φ ψ`. Use `show B (T (T' φ)) ψ = B φ (S' (S ψ))`. Rewrite using `[h (T' φ) ψ, h' φ (S ψ)]`.
-/
theorem HasAdj.mul {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by
  intro φ ψ
  show B (T (T' φ)) ψ = B φ (S' (S ψ))
  rw [h (T' φ) ψ, h' φ (S ψ)]

/- English proof (translation)
Introduce `φ ψ`. Both sides reduce to the same expression.
-/
theorem HasAdj.one (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 1 1 := by
  intro φ ψ
  rfl

/- English proof (translation)
Introduce `φ ψ`. Simplify using `only [LinearMap.add_apply, map_add, h φ ψ, h' φ ψ]`.
-/
theorem HasAdj.add {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T + T') (S + S') := by
  intro φ ψ
  simp only [LinearMap.add_apply, map_add, h φ ψ, h' φ ψ]

/- English proof (translation)
Introduce `φ ψ`. Simplify using the standard rewrite rules.
-/
theorem HasAdj.zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 0 0 := by
  intro φ ψ
  simp

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `f g _`. Simplify using `using HasAdj.one B`.

Consider the case `succ t ih`. Introduce `f g hk`. Rewrite using `[List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]`. Conclude with `(hk 0).mul (ih _ _ fun k => hk k.succ)`.
-/
theorem HasAdj.ofFn {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ V) (g : Fin t → (Module.End ℂ V)ᵐᵒᵖ),
      (∀ k, HasAdj B (f k) (MulOpposite.unop (g k))) →
      HasAdj B (List.ofFn f).prod (MulOpposite.unop (List.ofFn g).prod) := by
  intro t
  induction t with
  | zero =>
    intro f g _
    simpa using HasAdj.one B
  | succ t ih =>
    intro f g hk
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    exact (hk 0).mul (ih _ _ fun k => hk k.succ)

/- English proof (translation)
Introduce `φ ψ`. Simplify using `[Module.algebraMap_end_apply]`.
-/
private theorem hasAdj_algebraMap_lemma (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (u : ℂ) :
    HasAdj B (algebraMap ℂ (Module.End ℂ V) u) (algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u)) := by
  intro φ ψ
  simp [Module.algebraMap_end_apply]

/- English proof (translation)
Establish `h1 : HasAdj B (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0)` using `by split_ifs`. Conclude with `hasAdj_algebraMap_lemma B u`. Conclude with `HasAdj.zero B`. Establish `h2 : HasAdj B (X i j) (-Y i j)`. Introduce `φ ψ`.

Rewrite using `[h i j φ ψ, LinearMap.neg_apply, map_neg]`. Establish `e1 : Tm X u i j = (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) + X i j` using `rfl`. Establish `e2 : MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j) = (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) + -Y i j`. Unfold `Tm`. Apply the tactic sequence `split_ifs <;> simp [MulOpposite.algebraMap_apply]`.

Rewrite using `[e1, e2]`. Conclude with `h1.add h2`.
-/
theorem HasAdj.tm {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (u : ℂ) (i j : Fin n) :
    HasAdj B (Tm X u i j)
      (MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)) := by
  have h1 : HasAdj B (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0)
      (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) := by
    split_ifs
    · exact hasAdj_algebraMap_lemma B u
    · exact HasAdj.zero B
  have h2 : HasAdj B (X i j) (-Y i j) := by
    intro φ ψ
    rw [h i j φ ψ, LinearMap.neg_apply, map_neg]
  have e1 : Tm X u i j = (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) + X i j := rfl
  have e2 : MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)
      = (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) + -Y i j := by
    unfold Tm
    split_ifs <;> simp [MulOpposite.algebraMap_apply]
  rw [e1, e2]
  exact h1.add h2

/- English proof (translation)
Introduce `φ ψ`. Simplify using `[Module.End.intCast_apply]`.
-/
theorem HasAdj.intCast (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (z : ℤ) :
    HasAdj B (z : Module.End ℂ V) (z : Module.End ℂ V) := by
  intro φ ψ
  simp [Module.End.intCast_apply]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using HasAdj.zero B`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem HasAdj.sum {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAdj.zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Unfold `qdet qminor`. Establish `e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ), MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ)` using `fun F => map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ`. Rewrite using `[e]`. Use `HasAdj.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[MulOpposite.unop_mul, MulOpposite.unop_intCast]`.

Use `(HasAdj.intCast B _).mul ?_` and prove the remaining obligations. Apply `HasAdj.ofFn` to reduce the goal to its premises. Introduce `k`. Establish `hk` using `HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k`. Simplify `hk` using `[map_sub, map_natCast]`.
-/
theorem hasAdj_qdet {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by
  unfold qdet qminor
  have e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ),
      MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ) := fun F =>
    map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ
  rw [e]
  refine HasAdj.sum _ _ _ fun σ _ => ?_
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast]
  refine (HasAdj.intCast B _).mul ?_
  apply HasAdj.ofFn
  intro k
  have hk := HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k
  simpa [map_sub, map_natCast] using hk

/- English proof (translation)
Rewrite using `[hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]`.
-/
theorem adj_qdet (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (X Y : Fin n → Fin n → Module.End ℂ V) (hY : GlRel Y)
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) (φ ψ : V) :
    B (qdet X v φ) ψ =
      B φ ((((-1 : ℂ) ^ n) • qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  rw [hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]

end GlobalTheory.CompanionTheory.CapelliAdj
