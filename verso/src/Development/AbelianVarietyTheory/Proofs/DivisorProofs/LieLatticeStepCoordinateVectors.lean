import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.LieRead

namespace GlobalTheory.LieRead.StepLetters

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem idx_uniq {α : Type} {L : List α} (hL : L.Nodup) {k k' : ℕ} {x : α} (h : L[k]? = some x)
    (h' : L[k']? = some x) : k = k' := by
  rw [List.getElem?_eq_some_iff] at h h'
  obtain ⟨hk, rfl⟩ := h
  obtain ⟨hk', e⟩ := h'
  exact ((hL.getElem_inj_iff).1 e).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify by unfolding definitions. Substitute using the available equality.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Supply the required witnesses or components.
-/
theorem letter_iff {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} (x : Letter Dw) (τ : E →+* ℂ) (j : ℕ) (hj : j < Dw.mult τ) :
    (x.1 = τ ∧ (x.2 : ℕ) = j) ↔ x = ⟨τ, ⟨j, hj⟩⟩ := by
  obtain ⟨τ', m⟩ := x
  constructor
  · rintro ⟨h1, h2⟩
    dsimp only at h1 h2
    subst h1 h2
    rfl
  · intro h
    cases h
    exact ⟨rfl, rfl⟩

end GlobalTheory.LieRead.StepLetters

open GlobalTheory.LieRead.StepLetters in
open Classical in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem GlobalTheory.LieRead.stepVec_letters : ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = (letters O.S.Dw).length → ∀ (τ : D.host.E →+* ℂ) (i : ℕ), i < O.S.Dw.mult τ → ∃ p : Fin (i + 1) → Fin F.P₀.g, Function.Injective p ∧ (∀ j : Fin (i + 1), stepVec O F τ j = Pi.single (p j) 1) ∧ (∀ v, stepCoef O F τ i v = v (p (Fin.last i))) ∧ stepLat O F τ (i + 1) = F.lieLat ⊓ (Submodule.span K (Set.range fun j => (Pi.single (p j) 1 : Fin F.P₀.g → K))).restrictScalars (𝓞 K) ∧ stepLat O F τ i = F.lieLat ⊓ (Submodule.span K (Set.range fun j : Fin i => (Pi.single (p j.castSucc) 1 : Fin F.P₀.g → K))).restrictScalars (𝓞 K) := by
  intro D O K _ _ F hg τ i hi
  set L := letters O.S.Dw with hLdef
  have hnd : L.Nodup := GlobalTheory.Proof.LetterConjugation.nodup_letters _

  let pos : ∀ m : ℕ, m < O.S.Dw.mult τ → Fin F.P₀.g := fun m hm =>
    ⟨L.idxOf (⟨τ, ⟨m, hm⟩⟩ : Letter O.S.Dw), by
      rw [hg]; exact List.idxOf_lt_length_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters _ _)⟩
  have hpos : ∀ m (hm : m < O.S.Dw.mult τ), L[((pos m hm : Fin F.P₀.g) : ℕ)]? = some ⟨τ, ⟨m, hm⟩⟩ :=
    fun m hm => List.getElem?_idxOf (GlobalTheory.Proof.LetterConjugation.mem_letters _ _)

  have hcond : ∀ (p' : Fin F.P₀.g) (m : ℕ) (hm : m < O.S.Dw.mult τ),
      (∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) = m ∧ L[(p' : ℕ)]? = some x) ↔ p' = pos m hm := by
    intro p' m hm
    constructor
    · rintro ⟨x, h1, h2, h3⟩
      rw [(letter_iff x τ m hm).1 ⟨h1, h2⟩] at h3
      exact Fin.ext (idx_uniq hnd h3 (hpos m hm))
    · rintro rfl
      exact ⟨_, rfl, rfl, hpos m hm⟩
  have hlt : ∀ j : Fin (i + 1), (j : ℕ) < O.S.Dw.mult τ := fun j => lt_of_lt_of_le j.2 hi
  let p : Fin (i + 1) → Fin F.P₀.g := fun j => pos j (hlt j)
  have hvec : ∀ j : Fin (i + 1), stepVec O F τ j = Pi.single (p j) 1 := by
    intro j
    funext p'
    rw [stepVec, Pi.single_apply]
    exact if_congr (hcond p' j (hlt j)) rfl rfl

  have hset : ∀ k (hk : k ≤ i + 1),
      {v : Fin F.P₀.g → K | ∃ (i' : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < k ∧
        L[(i' : ℕ)]? = some x ∧ v = Pi.single i' 1} =
      Set.range fun j : Fin k => (Pi.single (p (Fin.castLE hk j)) 1 : Fin F.P₀.g → K) := by
    intro k hk
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨i', x, h1, h2, h3, rfl⟩
      refine ⟨⟨x.2, h2⟩, ?_⟩
      have : i' = p (Fin.castLE hk ⟨x.2, h2⟩) := (hcond i' x.2 _).1 ⟨x, h1, rfl, h3⟩
      rw [this]
    · rintro ⟨j, rfl⟩
      exact ⟨_, _, rfl, j.2, hpos _ _, rfl⟩
  refine ⟨p, ?_, hvec, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := hpos a (hlt a)
    have h2 := hpos b (hlt b)
    change (pos a (hlt a)) = pos b (hlt b) at hab
    rw [hab] at h1
    rw [h1] at h2
    have := Option.some_injective _ h2
    exact Fin.ext (congrArg (fun x : Letter O.S.Dw => (x.2 : ℕ)) this)
  · intro v
    rw [stepCoef, LinearMap.sum_apply]
    have := hvec (Fin.last i)
    simp only [Fin.val_last] at this
    simp only [LinearMap.smul_apply, LinearMap.proj_apply, this, smul_eq_mul, Pi.single_apply]
    simp
  · rw [stepLat, hset (i + 1) le_rfl]
    rfl
  · rw [stepLat, hset i (Nat.le_succ i)]
    rfl

end
