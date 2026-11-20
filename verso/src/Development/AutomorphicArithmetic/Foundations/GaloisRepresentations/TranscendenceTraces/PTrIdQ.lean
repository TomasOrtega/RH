import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `hw : IsWt (𝟙 S) (Wt.const S d)` using `hW.2.2 (𝟙 S) d`. Use `Subtype.ext (funext fun k => ?_)` and prove the remaining obligations. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤))`. Rewrite using `[Nat.cast_pow]`.

Conclude with `hu.pow k`. Use `(hHl l n i (𝟙 S) _ hw hu x k).trans ?_` and prove the remaining obligations. Conclude with `(hL (l ^ k) n i).2.2 S d hq (x.1 k)`.
-/
private theorem trHl_id_apply (hHl : TrHl) (hL : TrLin) (hW : WtLin) (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0})
    (d : ℤ) (hu : IsUnit (l : Γ(S, ⊤))) (x : Hl l (sch.obj S) n i) :
    trHl l (𝟙 S) (Wt.const S d) n i x = d • x := by
  have hw : IsWt (𝟙 S) (Wt.const S d) := hW.2.2 (𝟙 S) d
  refine Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hu.pow k
  refine (hHl l n i (𝟙 S) _ hw hu x k).trans ?_
  exact (hL (l ^ k) n i).2.2 S d hq (x.1 k)

/- English proof (translation)
Introduce `hHl hL hW l _ n i S d hu`. Unfold `trHQ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a m`. Rewrite using `[LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]`. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trIdQ_of :
    TrHl → TrLin → WtLin → TrIdQ := by
  intro hHl hL hW l _ n i S d hu
  unfold trHQ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]
    rw [Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
