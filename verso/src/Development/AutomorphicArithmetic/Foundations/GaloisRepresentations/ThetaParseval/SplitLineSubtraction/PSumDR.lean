import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAddStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

section Alg

variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k']

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k) (finSumFinEquiv.symm (Fin.castAdd b i)) (finSumFinEquiv.symm (Fin.castAdd b j)) = _`. Simplify using the standard rewrite rules.
-/
private theorem sumRep_ll {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.castAdd b i)) (finSumFinEquiv.symm (Fin.castAdd b j)) = _
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k) (finSumFinEquiv.symm (Fin.natAdd a i)) (finSumFinEquiv.symm (Fin.natAdd a j)) = _`. Simplify using the standard rewrite rules.
-/
private theorem sumRep_rr {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin b) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.natAdd a i) (Fin.natAdd a j) =
      (s g : Matrix (Fin b) (Fin b) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.natAdd a i)) (finSumFinEquiv.symm (Fin.natAdd a j)) = _
  simp

/- English proof (translation)
Use extensionality with `g i j`. Express the relevant statement in the definitionally equal form `f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) = Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k') (finSumFinEquiv.symm i) (f …`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]`.
-/
private theorem map_sum' {a b : ℕ} (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (sumRep r₁ r₂) = sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

/- English proof (translation)
Set `M : Γ →* Matrix (Fin n) (Fin n) k` to `{ toFun := A map_one' := by`. Use extensionality with `i j`. Apply `hf` to reduce the goal to its premises. Rewrite using `[hA]`. Simplify using `[Matrix.one_apply, apply_ite f]`.

Use the proof step `map_mul' := fun g h => by`. Use extensionality with `i j`. Apply `hf` to reduce the goal to its premises. Rewrite using `[hA, Matrix.mul_apply, map_sum]`. Simplify using `only [map_mul, hA, Units.val_mul, Matrix.mul_apply] }`.

Use `⟨M.toHomUnits, ?_⟩` and prove the remaining obligations. Use extensionality with `g i j`. Simplify `hA g i j` using `[mapRep, M]`.
-/
private theorem descend {n : ℕ} (f : k →+* k') (hf : Function.Injective f) (r : Γ →* GL (Fin n) k')
    (A : Γ → Matrix (Fin n) (Fin n) k) (hA : ∀ g i j, f (A g i j) = (r g : Matrix (Fin n) (Fin n) k') i j) :
    ∃ r₁ : Γ →* GL (Fin n) k, mapRep f r₁ = r := by
  let M : Γ →* Matrix (Fin n) (Fin n) k :=
    { toFun := A
      map_one' := by
        ext i j
        apply hf
        rw [hA]
        simp [Matrix.one_apply, apply_ite f]
      map_mul' := fun g h => by
        ext i j
        apply hf
        rw [hA, Matrix.mul_apply, map_sum]
        simp only [map_mul, hA, Units.val_mul, Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_⟩
  ext g i j
  simpa [mapRep, M] using hA g i j

end Alg

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {s : ↥Gw →* GL (Fin b) (Om l)}

/- English proof (translation)
Establish `hf : Function.Injective (algebraMap ↥L.1 (Om l))` using `(algebraMap ↥L.1 (Om l)).injective`. Establish `e : ∀ g i j, algebraMap ↥L.1 (Om l) ((ρ g : Matrix _ _ ↥L.1) i j) = (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) (Om l)) i j` using `fun g i j => by`. Rewrite using `[← h.2]`. Simplify using `[mapRep]`. Take `⟨r₁, hr⟩` from `descend (algebraMap ↥L.1 (Om l)) hf r (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.castAdd b i) (Fin.castAdd b j)) (fun g i j => by rw [e, sumRep_ll])`.

Take `⟨s₁, hs⟩` from `descend (algebraMap ↥L.1 (Om l)) hf s (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.natAdd a i) (Fin.natAdd a j)) (fun g i j => by rw [e, sumRep_rr])`. Conclude with `⟨r₁, s₁, ⟨h.1, hr⟩, ⟨h.1, hs⟩, ⟨h.1, by rw [map_sum', hr, hs]⟩⟩`.
-/
private theorem model_split {L : FinExt l} {ρ : ↥Gw →* GL (Fin (a + b)) ↥L.1}
    (h : IsModel Bw (sumRep r s) L ρ) :
    ∃ (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (s₁ : ↥Gw →* GL (Fin b) ↥L.1),
      IsModel Bw r L r₁ ∧ IsModel Bw s L s₁ ∧ IsModel Bw (sumRep r s) L (sumRep r₁ s₁) := by
  have hf : Function.Injective (algebraMap ↥L.1 (Om l)) := (algebraMap ↥L.1 (Om l)).injective
  have e : ∀ g i j, algebraMap ↥L.1 (Om l) ((ρ g : Matrix _ _ ↥L.1) i j) =
      (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) (Om l)) i j := fun g i j => by
    rw [← h.2]
    simp [mapRep]
  obtain ⟨r₁, hr⟩ := descend (algebraMap ↥L.1 (Om l)) hf r
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.castAdd b i) (Fin.castAdd b j))
    (fun g i j => by rw [e, sumRep_ll])
  obtain ⟨s₁, hs⟩ := descend (algebraMap ↥L.1 (Om l)) hf s
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.natAdd a i) (Fin.natAdd a j))
    (fun g i j => by rw [e, sumRep_rr])
  exact ⟨r₁, s₁, ⟨h.1, hr⟩, ⟨h.1, hs⟩, ⟨h.1, by rw [map_sum', hr, hs]⟩⟩

/- English proof (translation)
Introduce `l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s hd`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨L, ρ, hm, -⟩` from `id hd`. Take `⟨r₁, s₁, m₁, m₂, m⟩` from `model_split hm`. Establish `S` using `GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁`.

Conclude with `⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1⟩`. Take `⟨L, ρ, hm, -⟩` from `id hd`. Take `⟨r₁, s₁, m₁, m₂, m⟩` from `model_split hm`. Establish `S` using `GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁`. Conclude with `⟨L, s₁, m₂, (S.1.1 ((m.isdRAt_iff P).1 hd)).2⟩`.

Introduce `τ J J' hJ hJ'`. Take `⟨L, ρ, hm, -, τ', t, -⟩` from `id hJ`. Take `⟨r₁, s₁, m₁, m₂, m⟩` from `model_split hm`. Establish `S` using `GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁`. Use `⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1, τ', t, fun n => ?_⟩` and prove the remaining obligations.

Establish `c₁` using `hJ.count_eq P m t n`. Establish `c₂` using `hJ'.count_eq P m₂ t n`. Rewrite `c₁` using `[S.2, Multiset.count_add, Nat.cast_add, c₂]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sumDR_holds : SumDR := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s hd
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, s₁, m₂, (S.1.1 ((m.isdRAt_iff P).1 hd)).2⟩
  · intro τ J J' hJ hJ'
    obtain ⟨L, ρ, hm, -, τ', t, -⟩ := id hJ
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    refine ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1, τ', t, fun n => ?_⟩
    have c₁ := hJ.count_eq P m t n
    have c₂ := hJ'.count_eq P m₂ t n
    rw [S.2, Multiset.count_add, Nat.cast_add, c₂] at c₁
    linarith

end UpperTheory.Gal.TP.Sub

end
