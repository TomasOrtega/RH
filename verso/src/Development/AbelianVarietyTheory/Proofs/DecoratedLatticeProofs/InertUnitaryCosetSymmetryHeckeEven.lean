import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertSym

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨k * a, mul_mem hk ha, ?_⟩` and prove the remaining obligations. Rewrite using `[e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]`. Introduce and unpack `⟨k, hk, rfl⟩`.

Use `⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩` and prove the remaining obligations. Rewrite using `[e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]`.
-/
theorem cosets_eq {G : Type} [Group G] (K : Subgroup G) {g g' : G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : g' = a * g * b) (c : G ⧸ K) :
    (∃ k ∈ K, c = ((k * g' : G) : G ⧸ K)) ↔ (∃ k ∈ K, c = ((k * g : G) : G ⧸ K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, mul_mem hk ha, ?_⟩
    rw [e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]

/- English proof (translation)
Introduce `g`. Take `⟨a, ha, b, hb, e⟩` from `h g`. Conclude with `(Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm`.
-/
theorem cosetSym_of_inv {G : Type} [Group G] (K : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, g⁻¹ = a * g * b) : CosetSym K := by
  intro g
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm

/- English proof (translation)
Establish `hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L`. Introduce `i j`. Unfold `Formalism.UG.antiJ`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Take `⟨J, hJ, hJe⟩` from `Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint`. Take `⟨k₁, hk₁, k₂, hk₂, e⟩` from `(GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by`. Introduce `i j`. Rewrite using `[hJe]`.

Simplify using `only [Formalism.UG.antiJ, add_comm i.val j.val]`. Apply the tactic sequence `split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)`. Rewrite `hk₁`, `hk₂` using `[hJe]`. Conclude with `⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩`.
-/
theorem inv_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) (g : GU σ n) :
    ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g⁻¹ = a * g * b := by
  have hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := (GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by
    intro i j
    rw [hJe]
    simp only [Formalism.UG.antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

end GlobalTheory.ChainOnto.InertSym

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q hU n`. Use `⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩` and prove the remaining obligations. Introduce `φ hφ g`. Take `⟨a, ha, b, hb, e⟩` from `InertSym.inv_mem_KU hU n g`. Rewrite using `[e]`.

Conclude with `hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g`.
-/
theorem inert_cosetSym_heckeEven : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  intro L _ _ _ ϖ σ q hU n
  refine ⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩
  intro φ hφ g
  obtain ⟨a, ha, b, hb, e⟩ := InertSym.inv_mem_KU hU n g
  rw [e]
  exact hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g

end GlobalTheory.ChainOnto

end
