import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

namespace Formalism.L2.SG.GramJoint

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def pairVec (F : FlagG S r T) (F' : FlagG S r T') : Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
  Sum.elim F.fvec F'.fvec

def gramFF (F : FlagG S r T) (F' : FlagG S r T') :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  fun i j => brS S (pairVec F F' j) (pairVec F F' i)

end Defs

def TF {E : Type} [CommRing E] (r : ℕ) (T : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.diagonal fun i => if i = Fin.last r then -T else 0

def Gmat {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gflag_eq_gmat {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') : Gflag F F' = Gmat (Zhat F F') T T' := rfl

def GramBlocks : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (F : FlagG S r T) (F' : FlagG S r T'),
    gramFF F F' = Matrix.fromBlocks (TF r T) (Zhat F F') (Zhat F F')ᴴ (TF r T')

def GramDetFlag : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (F : FlagG S r T) (F' : FlagG S r T'),
    (gramFF F F').det = (-1) ^ (r + 1) * Gflag F F'

def GramIndep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (F : FlagG S r T) (F' : FlagG S r T'), Gflag F F' ≠ 0 →
    LinearIndependent E (pairVec F F') ∧ F.Xplus ⊓ F'.Xplus = ⊥

def GNonnegAt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) → S.SigOK →
    ∀ (r T T' : ℕ), (S.sig τ).2 = r + 1 → 0 < T → 0 < T' →
    ∀ (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)), ∃ c : ℝ, 0 ≤ c ∧ τ (Gflag F F') = c

def DNeZeroAt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) → S.SigOK →
    ∀ (r T T' : ℕ), (S.sig τ).2 = r + 1 → 0 < T → 0 < T' →
    ∀ (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)), Gflag F F' ≠ 0 → Dl F F' (r + 1) ≠ 0

def GmatScale : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (c c' : Fin (r + 1) → E), c (Fin.last r) = 1 → c' (Fin.last r) = 1 →
    Gmat (Matrix.diagonal (fun a => star (c a)) * Z * Matrix.diagonal c') T T' =
      (∏ a : Fin r, star (c a.castSucc) * c' a.castSucc) *
        star (∏ a : Fin r, star (c a.castSucc) * c' a.castSucc) * Gmat Z T T'

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Lat

def GtermGram (D : D7) : Prop :=
  ∀ (X : TermTie D) (u u' : D.what₂.Word) (t : D.s.Term u u'),
    algebraMap D.host.F D.host.E (D.s.Gterm t) =
      (-1) ^ (D.R.rS + 1) * (gramFF (X.fl t).fl (X.fl' t).fl).det

def GtermJoint (D : D7) : Prop :=
  ∀ (X : TermTie D) (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dr1 (X.fl t) (X.fl' t) ≠ 0 ∧ Xplus (X.fl t) ⊓ Xplus (X.fl' t) = ⊥

def GtermNonneg (D : D7) : Prop :=
  Nonempty (TermTie D) → ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (τ : D.host.E →+* ℂ),
    ∃ c : ℝ, 0 ≤ c ∧ τ (algebraMap D.host.F D.host.E (D.s.Gterm t)) = c

end Record

section Lemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem leadMinorE_self {K : Type} [Field K] [StarRing K] {N : ℕ}
    (Z : Matrix (Fin N) (Fin N) K) : leadMinorE Z N = Z.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  exact congrArg Matrix.det (Matrix.ext fun i j => rfl)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem leadMinorE_castSucc {K : Type} [Field K] [StarRing K] {N : ℕ}
    (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) K) :
    leadMinorE Z N = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ N)]
  exact congrArg Matrix.det (Matrix.ext fun i j => rfl)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hT_fvec (F : FlagG S r T) (i j : Fin (r + 1)) : S.hT (F.fvec i) (F.fvec j) = TF r T i j := by
  have hne : ∀ k : Fin r, Fin.castSucc k ≠ Fin.last r := fun k => (Fin.castSucc_lt_last k).ne
  have hne' : ∀ k : Fin r, Fin.last r ≠ Fin.castSucc k := fun k => (hne k).symm
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [FlagG.fvec, TF, F.z_norm]
    | cast j =>
      have h1 : S.hT F.z (F.e j) = 0 := by
        first
          | rw [← S.herm (F.e j) F.z, F.z_orth j, map_zero]
          | rw [← S.herm.eq (F.e j) F.z, F.z_orth j, map_zero]
      simp [FlagG.fvec, TF, h1, Matrix.diagonal_apply_ne _ (hne j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [FlagG.fvec, TF, F.z_orth i, Matrix.diagonal_apply_ne _ (hne i)]
    | cast j =>
      simp only [FlagG.fvec, Fin.snoc_castSucc, F.e_iso i j, TF, Matrix.diagonal_apply]
      split_ifs <;> simp_all

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.
-/
theorem xplus_eq_span (F : FlagG S r T) : F.Xplus = Submodule.span E (Set.range F.fvec) := by
  rw [FlagG.Xplus, FlagG.X, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, FlagG.fvec]
  constructor
  · rintro (⟨a, rfl⟩ | rfl)
    · exact ⟨a.castSucc, by simp⟩
    · exact ⟨Fin.last r, by simp⟩
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => right; simp
    | cast a => left; exact ⟨a, by simp⟩

end Lemmas

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem gramBlocks : GramBlocks := by
  intro E _ _ _ S r T T' F F'
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp [gramFF, pairVec, brS, hT_fvec]
  · simp [gramFF, pairVec, brS, Zhat]
  · simp only [gramFF, pairVec, brS, Zhat, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Sum.elim_inl,
      Sum.elim_inr]
    first
      | exact (S.herm _ _).symm
      | exact (S.herm.eq _ _).symm
  · simp [gramFF, pairVec, brS, hT_fvec]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramDetFlag : GramDetFlag := by
  intro E _ _ _ S r T T' F F'
  rw [gramBlocks E S r T T' F F']
  have h := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramDetGen E r (Zhat F F')ᴴ (Zhat F F') T T'
  unfold TF
  rw [h, Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    gflag_eq_gmat]
  unfold Gmat
  rw [leadMinorE_self, leadMinorE_castSucc]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gramIndep : GramIndep := by
  intro E _ _ _ S r T T' F F' hG
  have hdet : (gramFF F F').det ≠ 0 := by
    rw [gramDetFlag E S r T T' F F']
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hG
  have hB : (Matrix.of fun i j => S.hT.flip (pairVec F F' i) (pairVec F F' j)).det ≠ 0 := by
    have : (Matrix.of fun i j => S.hT.flip (pairVec F F' i) (pairVec F F' j)) = (gramFF F F')ᵀ := by
      ext i j; rfl
    rw [this, Matrix.det_transpose]
    exact hdet
  have h := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.gramNondeg E S.V (Fin (r + 1) ⊕ Fin (r + 1)) (starRingEnd E) S.hT.flip
    (pairVec F F') hB
  refine ⟨h.1, ?_⟩
  have hl : LinearIndependent E (Sum.elim F.fvec F'.fvec) := h.1
  rw [linearIndependent_sum] at hl
  rw [xplus_eq_span, xplus_eq_span]
  exact disjoint_iff.mp (by simpa using hl.2.2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem dNeZeroAt_of (h : GNonnegAt) : DNeZeroAt := by
  intro E _ _ _ S τ hτ hsig r T T' hr hT hT' F F' hG hD
  obtain ⟨c, hc, hτG⟩ := h E S τ hτ hsig r T T' hr hT hT' F F'
  have hG' : Gflag F F' = -((T : E) * (T' : E) * (Dl F F' r * star (Dl F F' r))) := by
    unfold Gflag
    rw [hD]
    simp
  have hval : τ (-((T : E) * (T' : E) * (Dl F F' r * star (Dl F F' r)))) =
      -(((T : ℝ) * (T' : ℝ) * Complex.normSq (τ (Dl F F' r)) : ℝ) : ℂ) := by
    rw [map_neg, map_mul, map_mul, map_mul, hτ, map_natCast, map_natCast, Complex.mul_conj]
    simp
  rw [hG', hval] at hτG
  have hre := congrArg Complex.re hτG
  simp only [Complex.neg_re, Complex.ofReal_re] at hre
  have hTT : (0 : ℝ) < (T : ℝ) * (T' : ℝ) := by
    have h1 : (0 : ℝ) < T := by exact_mod_cast hT
    have h2 : (0 : ℝ) < T' := by exact_mod_cast hT'
    exact mul_pos h1 h2
  have hN0 := Complex.normSq_nonneg (τ (Dl F F' r))
  have hN : Complex.normSq (τ (Dl F F' r)) = 0 := by nlinarith
  have hD0 : Dl F F' r = 0 := by
    rw [Complex.normSq_eq_zero] at hN
    exact (map_eq_zero_iff τ τ.injective).1 hN
  exact hG (by rw [hG', hD0]; simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gmatScale : GmatScale := by
  intro E _ _ r Z T T' c c' hc hc'
  have hminor : ∀ (l : ℕ) (hl : l ≤ r + 1),
      leadMinorE (Matrix.diagonal (fun a => star (c a)) * Z * Matrix.diagonal c') l =
        (∏ a : Fin l, star (c (Fin.castLE hl a)) * c' (Fin.castLE hl a)) * leadMinorE Z l := by
    intro l hl
    unfold leadMinorE
    rw [dif_pos hl, dif_pos hl]
    have hsub : (Matrix.diagonal (fun a => star (c a)) * Z * Matrix.diagonal c').submatrix (Fin.castLE hl)
        (Fin.castLE hl) = Matrix.diagonal (fun a : Fin l => star (c (Fin.castLE hl a))) *
          Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * Matrix.diagonal (fun a : Fin l => c' (Fin.castLE hl a)) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
    ring
  have h1 := hminor (r + 1) (le_refl (r + 1))
  have h0 := hminor r (Nat.le_succ r)
  have e1 : (∏ a : Fin (r + 1), star (c (Fin.castLE (le_refl (r + 1)) a)) * c' (Fin.castLE (le_refl (r + 1)) a)) =
      ∏ a : Fin r, star (c a.castSucc) * c' a.castSucc := by
    rw [Fin.prod_univ_castSucc]
    have hlast : star (c (Fin.castLE (le_refl (r + 1)) (Fin.last r))) *
        c' (Fin.castLE (le_refl (r + 1)) (Fin.last r)) = 1 := by
      show star (c (Fin.last r)) * c' (Fin.last r) = 1
      rw [hc, hc', star_one, one_mul]
    rw [hlast, mul_one]
    rfl
  have e0 : (∏ a : Fin r, star (c (Fin.castLE (Nat.le_succ r) a)) * c' (Fin.castLE (Nat.le_succ r) a)) =
      ∏ a : Fin r, star (c a.castSucc) * c' a.castSucc := rfl
  rw [e1] at h1
  rw [e0] at h0
  unfold Gmat
  rw [h1, h0, star_mul, star_mul]
  ring

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Lat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem gtermGram (D : D7) : GtermGram D := by
  intro X u u' t
  rw [X.G_eq t, gramDetFlag D.host.E (hS D) D.R.rS _ _ (X.fl t).fl (X.fl' t).fl, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sig_hS (D : D7) (τ : D.host.E →+* ℂ) : ((hS D).sig τ).2 = D.R.rS + 1 := by
  show ((D.sp.Y 0).sig τ).2 = D.R.rS + 1
  rw [D.sp.baseSpace_signature_eq τ]
  rfl

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem Tu_pos (D : D7) (u : D.what₂.Word) : 0 < Tu D u := by
  show 0 < (D.mem u).A.T
  by_contra hneg
  have h0 : (D.mem u).A.T = 0 := by omega
  have hc := D.host.level_coprimeS _ (D.T_level u)
  rw [h0] at hc
  have hQ : D.host.QS = 1 := (Nat.coprime_zero_left _).1 hc
  have hdvd := D.host.tower_dvd
  rw [hQ] at hdvd
  have h1 := Nat.dvd_one.1 hdvd
  rw [Nat.pow_eq_one] at h1
  rcases h1 with h1 | h1 <;> omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem gval_ne_zero (D : D7) (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) : Gval (X.fl t) (X.fl' t) ≠ 0 := by
  intro h
  apply hG
  have e := X.G_eq t
  rw [h] at e
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem gtermJoint_of (h : GNonnegAt) (D : D7) : GtermJoint D := by
  intro X u u' t hG
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hG' := gval_ne_zero D X t hG
  have hτ : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) := by
    intro a
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj D.host.φ₀ a
      | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) D.host.φ₀ a)
  refine ⟨?_, ?_⟩
  · exact dNeZeroAt_of h D.host.E (hS D) D.host.φ₀ hτ (D.sp.Y_sig 0) D.R.rS (Tu D u) (Tu D u') (sig_hS D _)
      (Tu_pos D u) (Tu_pos D u') (X.fl t).fl (X.fl' t).fl hG'
  · exact (gramIndep D.host.E (hS D) D.R.rS _ _ (X.fl t).fl (X.fl' t).fl hG').2

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gtermNonneg_of (h : GNonnegAt) (D : D7) : GtermNonneg D := by
  rintro ⟨X⟩ u u' t τ
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hτ : ∀ a : D.host.E, τ (star a) = starRingEnd ℂ (τ a) := by
    intro a
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj τ a
      | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) τ a)
      | simp [Formalism.BasicNotions.Host.cmStar]
  obtain ⟨c, hc, e⟩ := h D.host.E (hS D) τ hτ (D.sp.Y_sig 0) D.R.rS (Tu D u) (Tu D u') (sig_hS D τ)
    (Tu_pos D u) (Tu_pos D u') (X.fl t).fl (X.fl' t).fl
  refine ⟨c, hc, ?_⟩
  rw [X.G_eq t]
  exact e

end Record

end Formalism.L2.SG.GramJoint
