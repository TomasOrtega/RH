import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.LatDiag

variable {E : Type} [Field E] [NumberField E] {w : Pl E}

/- English proof (translation)
Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem unif_ne_zero {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  rintro rfl
  unfold IsUnifV at h
  rw [map_zero] at h
  exact WithZero.zero_ne_coe h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unif_lt_one {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem le_one_of_unif_mul {ϖ x : w.adicCompletion E} (h : IsUnifV E w ϖ)
    (hx : Valued.v (ϖ * x) < 1) : Valued.v x ≤ 1 := by
  unfold IsUnifV at h
  rw [map_mul, h] at hx
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h0
  rw [← hm] at hx ⊢
  have h1 : Multiplicative.ofAdd (-1 : ℤ) * m < 1 := by exact_mod_cast hx
  have h2 : (-1 : ℤ) + Multiplicative.toAdd m < 0 := h1
  have h3 : m ≤ 1 := by
    show Multiplicative.toAdd m ≤ 0
    omega
  exact_mod_cast h3

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔
      Valued.v (x : w.adicCompletion E) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : w.adicCompletion E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E := by
      show Valued.v (x : w.adicCompletion E)⁻¹ ≤ 1
      rw [map_inv₀, h1, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
  · intro hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : Valued.v (x : w.adicCompletion E) * Valued.v (y : w.adicCompletion E) = 1 := by
      rw [← map_mul]
      have : (x : w.adicCompletion E) * (y : w.adicCompletion E) = 1 := congrArg Subtype.val hy
      rw [this, map_one]
    have h2 : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
    have h3 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hx
    exact absurd h1 (ne_of_lt h3)

def posR {a i : ℕ} (hi : i ≤ a) (r : Fin i) : Fin a := Fin.castLE hi r

def posS {b j : ℕ} (s : Fin (b - j)) : Fin b := ⟨j + s, by have := s.2; omega⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem corner_mem {ϖ : w.adicCompletion E} {a b i j : ℕ} (hi : i ≤ a)
    (W : latD ϖ a b i j) (p : Fin i × Fin (b - j)) :
    ϖ * W.1 (posR hi p.1) (posS p.2) ∈ w.adicCompletionIntegers E := by
  have h := W.2 (posR hi p.1) (posS p.2)
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  rw [if_pos hc] at h
  exact h

def cornerMap (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) :
    latD ϖ a b i j →+
      (Fin i × Fin (b - j) → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun W p := IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩
  map_zero' := by
    funext p
    have : (⟨_, corner_mem hi (0 : latD ϖ a b i j) p⟩ : w.adicCompletionIntegers E) = 0 :=
      Subtype.ext (by simp)
    simp only [this, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext p
    have : (⟨_, corner_mem hi (X + Y) p⟩ : w.adicCompletionIntegers E) =
        ⟨_, corner_mem hi X p⟩ + ⟨_, corner_mem hi Y p⟩ :=
      Subtype.ext (by simp [mul_add])
    simp only [this, map_add, Pi.add_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cornerMap_apply (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) (W : latD ϖ a b i j)
    (p : Fin i × Fin (b - j)) :
    cornerMap ϖ a b i j hi W p = IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩ := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ker_cornerMap {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ) (hi : i ≤ a)
    (hj : j ≤ b) :
    (cornerMap ϖ a b i j hi).ker = (intSub a b w).addSubgroupOf (latD ϖ a b i j) := by
  ext W
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro hW r s
    have hWp : ∀ p : Fin i × Fin (b - j), Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1 := by
      intro p
      have := congrFun hW p
      rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff] at this
      exact this
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · have := hWp (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩)
      have hr : posR hi ⟨(r : ℕ), hc.1⟩ = r := Fin.ext rfl
      have hs : posS (j := j) (⟨(s : ℕ) - j, by have := s.2; omega⟩ : Fin (b - j)) = s :=
        Fin.ext (by simp [posS]; omega)
      simp only [hr, hs] at this
      exact le_one_of_unif_mul h this
    · have := W.2 r s
      rw [if_neg hc] at this
      exact this
  · intro hW
    funext p
    rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
    show Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hW _ _)) (unif_lt_one h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cornerMap_surjective {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ)
    (hi : i ≤ a) (hj : j ≤ b) : Function.Surjective (cornerMap ϖ a b i j hi) := by
  intro c
  choose x hx using fun p => IsLocalRing.residue_surjective (c p)
  have h0 := unif_ne_zero h
  let M : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun r s =>
    if hc : (r : ℕ) < i ∧ j ≤ (s : ℕ) then
      ϖ⁻¹ * (x (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩) : w.adicCompletion E) else 0
  have hM : M ∈ latD ϖ a b i j := by
    intro r s
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · rw [if_pos hc]
      simp only [M, dif_pos hc]
      rw [mul_inv_cancel_left₀ h0]
      exact (x _).2
    · rw [if_neg hc]
      simp only [M, dif_neg hc]
      exact (Ov E w).zero_mem
  refine ⟨⟨M, hM⟩, ?_⟩
  funext p
  rw [cornerMap_apply, ← hx p]
  congr 1
  apply Subtype.ext
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  show ϖ * M (posR hi p.1) (posS p.2) = _
  simp only [M, dif_pos hc]
  rw [mul_inv_cancel_left₀ h0]
  congr 2
  refine Prod.ext (Fin.ext rfl) (Fin.ext ?_)
  simp [posS]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem relIndex_intSub_latD (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E) (h : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  have hcard : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = qV E w := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue w]
    rfl
  rw [AddSubgroup.relIndex, ← ker_cornerMap h a b i j hi hj, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (cornerMap_surjective h a b i j hi hj), AddSubgroup.card_top,
    Nat.card_fun, hcard, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end GlobalTheory.CompanionTheory.CtS.LatDiag
