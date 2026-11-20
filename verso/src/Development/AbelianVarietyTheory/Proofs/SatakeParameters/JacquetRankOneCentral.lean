import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacGL1

open GlobalTheory.SmGL GlobalTheory.PRep Matrix in

/- English proof (translation)
Introduce `k _ _ _ _ d V _ _ σ ω s' b f j hd hj hω z x`. Establish `hsum : ∑ i, b i = 1`. Use `Fintype.card_congr f` as an intermediate fact. Simplify `this` using `[Fintype.card_sigma, hd]`. Establish `hsplit` using `Finset.add_sum_erase Finset.univ b (Finset.mem_univ j)`.

Establish `ha : ∀ i, i ≠ j → IsEmpty (Fin (b i))` using `fun i hi => by`. Establish `h0 : ∑ i ∈ Finset.univ.erase j, b i = 0` using `by omega`. Rewrite using `[Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]`. Use `infer_instance`. Establish `h1 : leviEmb k f (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = GeneralLinearGroup.scalar (Fin d) z`.

Use extensionality with `i i'`. Take `⟨⟨a, y⟩, rfl⟩` from `f.surjective i`. Take `⟨⟨a', y'⟩, rfl⟩` from `f.surjective i'`. Take `rfl : a = j` from `by_contra fun h => (ha a h).elim y`. Take `rfl : a' = a` from `by_contra fun h => (ha a' h).elim y'`.

Rewrite using `[leviEmb_apply_same]`. Simplify using `[GeneralLinearGroup.scalar, diagonal_apply]`. Establish `h2 : modExp (fun i => Fin (b i)) j = 0`. Unfold `modExp`. Rewrite using `[Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]`.

Introduce `a hb`. Use `ha a (Finset.mem_filter.1 hb).2.ne` as an intermediate fact. Conclude with `Nat.cast_eq_zero.2 Fintype.card_eq_zero`. Introduce `a hb`. Use `ha a (Finset.mem_filter.1 hb).2.ne'` as an intermediate fact.

Conclude with `Nat.cast_eq_zero.2 Fintype.card_eq_zero`. Establish `h3 : deltaHalf k (fun i => Fin (b i)) (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = 1`. Rewrite using `[deltaHalf_apply]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : a = j`.

Substitute `hb` using the available equality. Simplify using `[h2]`. Rewrite using `[Pi.mulSingle_eq_of_ne hb, map_one, map_one]`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `(jac_mk f σ _ v).trans ?_` and prove the remaining obligations.

Rewrite using `[h3, h1, hω z v, inv_one, Units.val_one, one_smul]`. Both sides reduce to the same expression.
-/
theorem jac_mulSingle_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  intro k _ _ _ _ d V _ _ σ ω s' b f j hd hj hω z x
  have hsum : ∑ i, b i = 1 := by
    have := Fintype.card_congr f
    simpa [Fintype.card_sigma, hd] using this
  have hsplit := Finset.add_sum_erase Finset.univ b (Finset.mem_univ j)
  have ha : ∀ i, i ≠ j → IsEmpty (Fin (b i)) := fun i hi => by
    have h0 : ∑ i ∈ Finset.univ.erase j, b i = 0 := by omega
    rw [Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]
    infer_instance
  have h1 : leviEmb k f (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) =
      GeneralLinearGroup.scalar (Fin d) z := by
    ext i i'
    obtain ⟨⟨a, y⟩, rfl⟩ := f.surjective i
    obtain ⟨⟨a', y'⟩, rfl⟩ := f.surjective i'
    obtain rfl : a = j := by_contra fun h => (ha a h).elim y
    obtain rfl : a' = a := by_contra fun h => (ha a' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp (fun i => Fin (b i)) j = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne'
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
  have h3 : deltaHalf k (fun i => Fin (b i))
      (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => ?_
    by_cases hb : a = j
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (jac_mk f σ _ v).trans ?_
  rw [h3, h1, hω z v, inv_one, Units.val_one, one_smul]
  rfl

end GlobalTheory.JacGL1
