import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.PadicSubsetSums.StableGradedCounts.PropositionOneCentralCount
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbSum
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
import Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaLWeight
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec
import Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaP
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemSelfAdjoint
import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
import Formalism.PadicSubsetSums.StableGradedCounts.IRRSquarefreeCount
import Formalism.PadicSubsetSums.StableGradedCounts.IRRTypeCountExact
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleTypeProb

namespace Bl.CyclicComponents

/- English proof (translation)
Introduce `v`. Establish `hU : Submodule.span ℂ (Set.range fun g => ρ g w) = ⊤`. Establish `hinv : ∀ g : G, ∀ x ∈ Submodule.span ℂ (Set.range fun g => ρ g w), ρ g x ∈ Submodule.span ℂ (Set.range fun g => ρ g w)`. Introduce `g x hx`. Establish `hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤ (Submodule.span ℂ (Set.range fun g => ρ g w)).comap (ρ g)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g', rfl⟩`. Conclude with `Submodule.subset_span ⟨g * g', by simp [map_mul]⟩`. Conclude with `hle hx`. Break down `hirr _ hinv with h | h` into its components or cases.

It suffices to derive a contradiction. Apply `hw` to reduce the goal to its premises. Establish `hmem : w ∈ Submodule.span ℂ (Set.range fun g => ρ g w)` using `Submodule.subset_span ⟨1, by simp⟩`. Rewrite `hmem` using `[h]`. Simplify using `using hmem`.

Conclude with `h`. Establish `hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤ S.comap f`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `hf g`.

Rewrite `hle` using `[hU]`. Conclude with `hle Submodule.mem_top`.
-/
private lemma cyc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (w : V) (hw : w ≠ 0) (S : Submodule ℂ V) (f : Module.End ℂ V)
    (hf : ∀ g : G, f (ρ g w) ∈ S) : ∀ v, f v ∈ S := by
  intro v
  have hU : Submodule.span ℂ (Set.range fun g => ρ g w) = ⊤ := by
    have hinv : ∀ g : G, ∀ x ∈ Submodule.span ℂ (Set.range fun g => ρ g w),
        ρ g x ∈ Submodule.span ℂ (Set.range fun g => ρ g w) := by
      intro g x hx
      have hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤
          (Submodule.span ℂ (Set.range fun g => ρ g w)).comap (ρ g) := by
        rw [Submodule.span_le]
        rintro _ ⟨g', rfl⟩
        exact Submodule.subset_span ⟨g * g', by simp [map_mul]⟩
      exact hle hx
    rcases hirr _ hinv with h | h
    · exfalso
      apply hw
      have hmem : w ∈ Submodule.span ℂ (Set.range fun g => ρ g w) :=
        Submodule.subset_span ⟨1, by simp⟩
      rw [h] at hmem
      simpa using hmem
    · exact h
  have hle : Submodule.span ℂ (Set.range fun g => ρ g w) ≤ S.comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hf g
  rw [hU] at hle
  exact hle Submodule.mem_top

/- English proof (translation)
Distinguish the cases in `hW : W = ⊥`. Rewrite using `[hW]`. Simplify using the standard rewrite rules. Establish `hB : ∀ g : G, ∀ w ∈ W, P (ρ g w) = (P * ρ g * P) w`. Introduce `g w hw`.

Simplify using `[hPfix w hw]`. Establish `hscal : ∀ h : G, ∃ μ : ℂ, ∀ x ∈ W, (P * ρ h * P) x = μ • x`. Introduce `h`. Establish `hBW : ∀ x ∈ W, (P * ρ h * P) x ∈ W` using `fun x _ => by`. Simplify using `only [Module.End.mul_apply]`.

Conclude with `hPW _`. Establish `: Nontrivial W` using `Submodule.nontrivial_iff_ne_bot.mpr hW`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue ((P * ρ h * P).restrict hBW)`. Take `⟨w, hwv⟩` from `hμ.exists_hasEigenvector`. Establish `hw1` using `hwv.apply_eq_smul`.

Establish `hw2 : (P * ρ h * P) (w : V) = μ • (w : V)`. Use `congrArg Subtype.val hw1` as an intermediate fact. Simplify `this` using `[LinearMap.restrict_apply]`. Establish `hw0 : (w : V) ≠ 0`. Introduce `h0`.

Apply `hwv.2` to reduce the goal to its premises. Conclude with `Subtype.ext h0`. Establish `key` using `cyc ρ hirr (w : V) hw0 ((P * ρ h * P).eigenspace μ) P (by`. Introduce `g`. Rewrite using `[Module.End.mem_eigenspace_iff, hB g w w.2]`.

Rewrite using `[← Module.End.mul_apply, hcomm h g, Module.End.mul_apply, hw2, map_smul])`. Use `⟨μ, fun x hx => ?_⟩` and prove the remaining obligations. Use `Module.End.mem_eigenspace_iff.mp (key x)` as an intermediate fact. Rewrite `this` using `[hPfix x hx]`. Then use the resulting hypothesis. Take `⟨w0, hw0W, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`.

Establish `key` using `cyc ρ hirr w0 hw0 (ℂ ∙ w0) P (by`. Introduce `g`. Take `⟨μ, hμ⟩` from `hscal g`. Rewrite using `[hB g w0 hw0W, hμ w0 hw0W]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))`.

Establish `hle : W ≤ ℂ ∙ w0`. Introduce `x hx`. Rewrite using `[← hPfix x hx]`. Conclude with `key x`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma core {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (P : Module.End ℂ V)
    (hPW : ∀ v, P v ∈ W) (hPfix : ∀ w ∈ W, P w = w)
    (hcomm : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P))
    (hirr : ∀ U : Submodule ℂ V, (∀ g : G, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank ℂ W ≤ 1 := by
  by_cases hW : W = ⊥
  · rw [hW]
    simp
  have hB : ∀ g : G, ∀ w ∈ W, P (ρ g w) = (P * ρ g * P) w := by
    intro g w hw
    simp [hPfix w hw]
  have hscal : ∀ h : G, ∃ μ : ℂ, ∀ x ∈ W, (P * ρ h * P) x = μ • x := by
    intro h
    have hBW : ∀ x ∈ W, (P * ρ h * P) x ∈ W := fun x _ => by
      simp only [Module.End.mul_apply]
      exact hPW _
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((P * ρ h * P).restrict hBW)
    obtain ⟨w, hwv⟩ := hμ.exists_hasEigenvector
    have hw1 := hwv.apply_eq_smul
    have hw2 : (P * ρ h * P) (w : V) = μ • (w : V) := by
      have := congrArg Subtype.val hw1
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := by
      intro h0
      apply hwv.2
      exact Subtype.ext h0
    have key := cyc ρ hirr (w : V) hw0 ((P * ρ h * P).eigenspace μ) P (by
      intro g
      rw [Module.End.mem_eigenspace_iff, hB g w w.2]
      rw [← Module.End.mul_apply, hcomm h g, Module.End.mul_apply, hw2, map_smul])
    refine ⟨μ, fun x hx => ?_⟩
    have := Module.End.mem_eigenspace_iff.mp (key x)
    rwa [hPfix x hx] at this
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have key := cyc ρ hirr w0 hw0 (ℂ ∙ w0) P (by
    intro g
    obtain ⟨μ, hμ⟩ := hscal g
    rw [hB g w0 hw0W, hμ w0 hw0W]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hle : W ≤ ℂ ∙ w0 := by
    intro x hx
    rw [← hPfix x hx]
    exact key x
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (ℂ ∙ w0) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw0

/- English proof (translation)
Introduce `G inst inst_1 V inst_2 inst_3 inst_4 ρ J χ hcomm hirr`. Establish `hirr2` using `hirr`. Rewrite `hirr2` using `[Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr.eq_def]`. Take `⟨P, hPdef⟩ : ∃ P : Module.End ℂ V, P = ρ.asAlgebraHom (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)` from `⟨_, rfl⟩`. Establish `hP : ∀ v, P v = ∑ u : J, ((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹) • ρ ↑u v`.

Introduce `v`. Rewrite using `[hPdef, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem.eq_def, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, Representation.asAlgebraHom_of]`. Establish `hPW : ∀ v, P v ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val)`.

Introduce `v`. Rewrite using `[Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def]`. Use `show ∀ u : J, ρ ↑u (P v) = (χ u : ℂ) • P v`. Introduce `u0`. Rewrite using `[hP, map_sum, Finset.smul_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, mul_inv_rev, Units.val_mul]`. Use `congr 1`. Take the linear combination `(-((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹)) * Units.inv_mul (χ u0)`. Establish `hPfix : ∀ w ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val), P w = w`.

Introduce `w hw`. Rewrite `hw` using `[Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def]`. Establish `hw' : ∀ u : J, ρ ↑u w = (χ u : ℂ) • w` using `hw`. Rewrite using `[hP]`. Simplify using `only [hw', smul_smul, mul_assoc, Units.inv_mul, mul_one]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]`. Conclude with `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hcomm2 : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P)`. Introduce `g g'`. Use `congrArg ρ.asAlgebraHom (hcomm g g')` as an intermediate fact.

Simplify `this` using `[map_mul, Representation.asAlgebraHom_of, hPdef]`. Conclude with `core ρ _ P hPW hPfix hcomm2 hirr2.2`.
-/
theorem goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : Fintype.{0} G] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} Complex V] [FiniteDimensional.{0, 0} Complex V] (ρ : Representation.{0, 0, 0} Complex G V)
  (J : Subgroup.{0} G) (χ : MonoidHom.{0, 0} (Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) (Units.{0} Complex)),
  (∀ (g g' : G),
      Eq.{1}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))) →
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr ρ →
      LE.le.{0}
        (Module.finrank.{0, 0} Complex
          (Subtype.{1} fun (x : V) ↦
            Membership.mem.{0, 0}
              (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ
                (fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦ Subtype.val.{1} u)
                fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦
                Units.val.{0} (DFunLike.coe.{1, 1, 1} χ u))
              x))
        1 := by
  intro G inst inst_1 V inst_2 inst_3 inst_4 ρ J χ hcomm hirr
  classical
  have hirr2 := hirr
  rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr.eq_def] at hirr2
  obtain ⟨P, hPdef⟩ : ∃ P : Module.End ℂ V, P = ρ.asAlgebraHom (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ) :=
    ⟨_, rfl⟩
  have hP : ∀ v, P v = ∑ u : J, ((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹) • ρ ↑u v := by
    intro v
    rw [hPdef, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem.eq_def, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Representation.asAlgebraHom_of]
  have hPW : ∀ v, P v ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val) := by
    intro v
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def]
    show ∀ u : J, ρ ↑u (P v) = (χ u : ℂ) • P v
    intro u0
    rw [hP, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulLeft, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul,
      mul_inv_rev, Units.val_mul]
    congr 1
    linear_combination (-((↑(Nat.card J) : ℂ)⁻¹ * ↑(χ u)⁻¹)) * Units.inv_mul (χ u0)
  have hPfix : ∀ w ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ (fun u : J => u.val) (fun u => (χ u).val), P w = w := by
    intro w hw
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace.eq_def] at hw
    have hw' : ∀ u : J, ρ ↑u w = (χ u : ℂ) • w := hw
    rw [hP]
    simp only [hw', smul_smul, mul_assoc, Units.inv_mul, mul_one]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, mul_inv_cancel₀, one_smul]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcomm2 : ∀ g g' : G, P * ρ g * P * (P * ρ g' * P) = P * ρ g' * P * (P * ρ g * P) := by
    intro g g'
    have := congrArg ρ.asAlgebraHom (hcomm g g')
    simpa [map_mul, Representation.asAlgebraHom_of, hPdef] using this
  exact core ρ _ P hPW hPfix hcomm2 hirr2.2

end Bl.CyclicComponents
