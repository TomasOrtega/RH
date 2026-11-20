import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `e : (fun g => (((r g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = (fun g => (r g : Matrix (Fin n) (Fin n) k)) ∘ fun g => g⁻¹`. Use function extensionality and compare the values at `g`. Simplify using `[map_inv]`.

Rewrite using `[e]`. Conclude with `h.comp continuous_inv`.
-/
private theorem cont_of_val {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (h : Continuous fun g => (r g : Matrix (Fin n) (Fin n) k)) : Continuous r := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((r g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun g => (r g : Matrix (Fin n) (Fin n) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  rw [e]
  exact h.comp continuous_inv

/- English proof (translation)
The claim follows from `Units.continuous_val`.
-/
private theorem val_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k) := Units.continuous_val

/- English proof (translation)
Establish `hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i` using `finSumFinEquiv_symm_apply_castAdd i`. Establish `hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j` using `finSumFinEquiv_symm_apply_castAdd j`. Simplify using `[sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]`. Both sides reduce to the same expression.
-/
private theorem sumRep_entry {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k)
    (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  have hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
  have hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j := finSumFinEquiv_symm_apply_castAdd j
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  rfl

/- English proof (translation)
Introduce `Γ k _ _ _ _ _ _ a b`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r s hc`. Apply `cont_of_val r` to reduce the goal to its premises. Establish `hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k)` using `val_cont.comp hc`.

Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j)` using `(continuous_apply _).comp ((continuous_apply _).comp hm)`. Use `he.congr fun g => ?_` and prove the remaining obligations. Apply the tactic sequence `exact sumRep_entry r s g i j`. Introduce and unpack `r r' ⟨u, hu⟩ hr`.

Establish `hf : (⇑r') = fun x => u * r x * u⁻¹` using `funext hu`. Rewrite using `[hf]`. Conclude with `(continuous_const.mul hr).mul continuous_const`. Introduce `r c hr hc`. Apply `cont_of_val` to reduce the goal to its premises.

Establish `hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) = fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k)`. Use function extensionality and compare the values at `g`. Conclude with `UpperTheory.V.Af.tw_val r c g`. Rewrite using `[hv]`. Conclude with `(Units.continuous_val.comp hc).smul (val_cont.comp hr)`.

Introduce `c hc`. Apply `cont_of_val` to reduce the goal to its premises. Establish `hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) = fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k)`. Use function extensionality and compare the values at `g`. Simplify using `[rk1, Matrix.scalar_apply]`.

Rewrite using `[hv]`. Conclude with `Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)`.
-/
theorem UpperTheory.Gal.TP.Sub.contLeft_holds :
    ContLeft := by
  intro Γ k _ _ _ _ _ _ a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hc
    apply cont_of_val r
    have hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) := val_cont.comp hc
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) :=
      (continuous_apply _).comp ((continuous_apply _).comp hm)
    refine he.congr fun g => ?_
    exact sumRep_entry r s g i j
  · rintro r r' ⟨u, hu⟩ hr
    have hf : (⇑r') = fun x => u * r x * u⁻¹ := funext hu
    rw [hf]
    exact (continuous_const.mul hr).mul continuous_const
  · intro r c hr hc
    apply cont_of_val
    have hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) = fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k) := by
      funext g
      exact UpperTheory.V.Af.tw_val r c g
    rw [hv]
    exact (Units.continuous_val.comp hc).smul (val_cont.comp hr)
  · intro c hc
    apply cont_of_val
    have hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) = fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k) := by
      funext g
      simp [rk1, Matrix.scalar_apply]
    rw [hv]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)
