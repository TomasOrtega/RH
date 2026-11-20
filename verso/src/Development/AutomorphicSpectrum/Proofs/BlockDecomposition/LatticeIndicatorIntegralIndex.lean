import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintInd

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Proceed by induction. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finsum_out_indicator {A : Type} [AddCommGroup A] (S Λ : AddSubgroup A) (hSΛ : S ≤ Λ)
    (K : Subgroup (Multiplicative A)) (hK : ∀ X, X ∈ K ↔ Multiplicative.toAdd X ∈ S) :
    ∑ᶠ q : Multiplicative A ⧸ K, (if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      ((S.relIndex Λ : ℕ) : ℂ) := by
  have hrep : ∀ x : Multiplicative A,
      Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) ∈ Λ ↔ Multiplicative.toAdd x ∈ Λ := by
    intro x
    have h1 : ((x : Multiplicative A ⧸ K).out)⁻¹ * x ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : Multiplicative A ⧸ K))
    have h2 : -Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) + Multiplicative.toAdd x ∈ Λ :=
      hSΛ ((hK _).1 h1)
    constructor
    · intro h
      have := Λ.add_mem h h2
      simpa using this
    · intro h
      have := Λ.add_mem h (Λ.neg_mem h2)
      simpa using this
  let T : Set (Multiplicative A ⧸ K) := {q | Multiplicative.toAdd q.out ∈ Λ}
  have hsame : ∀ x y : Multiplicative A, (x : Multiplicative A ⧸ K) = y ↔
      -Multiplicative.toAdd x + Multiplicative.toAdd y ∈ S := by
    intro x y
    rw [QuotientGroup.eq, hK]
    rfl
  let f : Λ → T := fun x => ⟨((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K),
    (hrep _).2 x.2⟩
  let g : Λ ⧸ S.addSubgroupOf Λ → T := fun y => Quotient.liftOn' y f (by
    intro x y hxy
    have h : -(x : A) + (y : A) ∈ S := by
      have := QuotientAddGroup.leftRel_apply.1 hxy
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hsame _ _).2 h))
  have hg : Function.Bijective g := by
    constructor
    · intro y₁ y₂
      induction y₁ using QuotientAddGroup.induction_on with | H x =>
      induction y₂ using QuotientAddGroup.induction_on with | H y =>
      intro h
      have h' : ((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K) =
          ((Multiplicative.ofAdd (y : A) : Multiplicative A) : Multiplicative A ⧸ K) :=
        congrArg Subtype.val h
      refine QuotientAddGroup.eq.2 ?_
      rw [AddSubgroup.mem_addSubgroupOf]
      simpa using (hsame _ _).1 h'
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨((⟨Multiplicative.toAdd x, (hrep x).1 hq⟩ : Λ) : Λ ⧸ S.addSubgroupOf Λ), rfl⟩
  have hcard : Nat.card T = S.relIndex Λ := (Nat.card_congr (Equiv.ofBijective g hg)).symm
  have hfun : (fun q : Multiplicative A ⧸ K => if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      T.indicator 1 := by
    funext q
    by_cases h : q ∈ T
    · rw [Set.indicator_of_mem h]; exact if_pos h
    · rw [Set.indicator_of_notMem h]; exact if_neg h
  rw [hfun, ← hcard]
  by_cases hT : T.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hT, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card T hT]
    simp
  · rw [finsum_of_infinite_support (by simpa using hT)]
    haveI : Infinite T := Set.Infinite.to_subtype hT
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mem_intMat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ Multiplicative.toAdd X ∈ intSub a b w := by
  constructor
  · intro hX
    induction hX using Subgroup.closure_induction with
    | mem x hx => exact fun i j => hx i j
    | one => exact isInt_zero w _ _
    | mul x y _ _ hx hy => exact IsInt.add hx hy
    | inv x _ hx => exact IsInt.neg hx
  · intro hX
    exact Subgroup.subset_closure fun i j => hX i j

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem hint_indicator_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  intro E _ _ _ a b w Λ h
  have hstab : intMat a b w ≤
      rStab (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) := by
    intro k hk x
    have hkΛ : Multiplicative.toAdd k ∈ Λ := h ((mem_intMat_iff a b w k).1 hk)
    have e : (Multiplicative.toAdd (x * k) ∈ Λ) ↔ Multiplicative.toAdd x ∈ Λ := by
      rw [toAdd_mul]
      exact Λ.add_mem_cancel_right hkΛ
    simp only [e]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) (intMat a b w) _ le_rfl hstab
    (by simp [Subgroup.relIndex_self])]
  rw [Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_mul]
  exact finsum_out_indicator (intSub a b w) Λ h (intMat a b w) (mem_intMat_iff a b w)

end GlobalTheory.CompanionTheory.HintInd
