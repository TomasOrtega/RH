import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockWithThresholds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

def tieW {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i, by have := hT.lt i; omega⟩

def tieE {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i + 1, hT.lt i⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lettersAt_update {D : BlockData N} (hT : TieOK D) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i) :
    D.lettersAt (Function.update j i (j i - l)) jp =
      ⟨D.LL.vec, fun a => (D.lettersAt j jp).deg a + if a = tieW hT i ∨ a = tieE hT i then l else 0⟩ := by
  classical
  unfold BlockData.lettersAt
  simp only [ChainLetters.mk.injEq, true_and]
  funext a
  have hW : a = tieW hT i ↔ (a : ℕ) = D.T.pos i := by unfold tieW; rw [Fin.ext_iff]
  have hE : a = tieE hT i ↔ (a : ℕ) = D.T.pos i + 1 := by unfold tieE; rw [Fin.ext_iff]
  simp only [hW, hE]
  by_cases ha : (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1
  · have hoth : ∀ i', i' ≠ i → ¬ ((a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1) := by
      intro i' hi' h
      rcases ha with ha | ha <;> rcases h with h | h
      · exact hi' (hT.inj _ _ (h.symm.trans ha))
      · exact hT.sep i' i (h.symm.trans ha)
      · exact hT.sep i i' (ha.symm.trans h)
      · exact hi' (hT.inj _ _ (by omega))
    have s1 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then
        Function.update j i (j i - l) i' else 0) = j i - l := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha, Function.update_self]
    have s2 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha]
    have hu : a ≠ D.uPos := by
      intro h
      rcases ha with ha | ha
      · exact (hT.uW i).1 (by rw [← ha, h])
      · exact (hT.uW i).2 (by rw [← ha, h])
    have hdeg : j i ≤ D.LL.deg a := by
      have hN := hT.lt i
      rcases ha with ha | ha
      · have : D.letterAt (D.T.pos i) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).1
      · have : D.letterAt (D.T.pos i + 1) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).2
    rw [s1, s2, if_neg hu, if_pos ha]
    omega
  · rw [if_neg ha, add_zero]
    congr 2
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases hi' : i' = i
    · subst hi'
      rw [if_neg ha, if_neg ha]
    · rw [Function.update_of_ne hi']

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem levelOK_update {D : BlockData N} {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) :
    D.LevelOK (Function.update j i (j i - l)) jp := by
  classical
  refine ⟨fun i' => ?_, hL.2⟩
  have : Function.update j i (j i - l) i' ≤ j i' := by
    by_cases h : i' = i
    · subst h; rw [Function.update_self]; omega
    · rw [Function.update_of_ne h]
  exact ⟨this.trans (hL.1 i').1, this.trans (hL.1 i').2⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tailP_mul (D : BlockData N) (jp : ℕ) (q y : MvPolynomial (Fin N × Fin r) (KK O))
    (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    tailP O r D jp (q * y) g = rename (chainEmb N r D.T.t) q * tailP O r D jp y g := by
  unfold tailP
  rw [map_mul]
  ring

open Classical in

def otherE (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  ∏ i' ∈ Finset.univ.erase i, D.Ehat O (r := r) i' ^ j i'

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem prodE_split (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    (∏ i', D.Ehat O (r := r) i' ^ j i') = D.Ehat O (r := r) i ^ j i * otherE O r D j i := by
  classical
  unfold otherE
  exact (Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ j i') (Finset.mem_univ i)).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem prodE_update (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (e : ℕ) :
    (∏ i', D.Ehat O (r := r) i' ^ Function.update j i e i') = D.Ehat O (r := r) i ^ e * otherE O r D j i := by
  classical
  unfold otherE
  rw [← Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ Function.update j i e i')
    (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i' hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shift_mem {D : BlockData N} (hT : TieOK D) {thr0 thr' : Fin D.T.q → WithTop ℤ} {j : Fin D.T.t → ℕ} {jp : ℕ}
    (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i)
    (hthr : ∀ k, thr0 k + ((l : ℤ) : WithTop ℤ) ≤ thr' k)
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr0)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    D.Ehat O (r := r) i ^ (j i - l) * rename (chainEmb N r D.T.t) q0 ^ l * otherE O r D j i * tailP O r D jp y g ∈
      SSt O r D thr' := by
  have h1 := hq0.pow l (D.lettersAt j jp).deg thr0 y hy
  rw [← lettersAt_update hT hL i l hl] at h1
  have h2 := gen_mem D (fun k => thr0 k + ((l : ℤ) : WithTop ℤ)) (levelOK_update hL i l) h1 hg
  rw [prodE_update, tailP_mul, map_pow] at h2
  have h3 := SSt_mono (O := O) (r := r) D hthr h2
  convert h3 using 1
  ring

def FreeV {K σ : Type} [CommSemiring K] (v : σ) (F : MvPolynomial σ K) : Prop := ∀ μ ∈ F.support, μ v = 0

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem freeV_of_vars {K σ : Type} [CommSemiring K] {v : σ} {F : MvPolynomial σ K} (h : v ∉ F.vars) : FreeV v F := by
  classical
  intro μ hμ
  by_contra h0
  exact h ((mem_vars_iff_mem_support v).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 h0⟩)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cth_lin {K σ : Type} [Field K] {v : σ} {E m' E' : MvPolynomial σ K} (hE : E = X v * m' + E')
    (hm' : FreeV v m') (hE' : FreeV v E') : cth v 1 E = X v * m' ∧ ∀ a, 2 ≤ a → cth v a E = 0 := by
  have hX : ∀ a, cth v a (X v * m') = m' * cth v a (X v : MvPolynomial σ K) := by
    intro a
    rw [mul_comm, cth_mul_free v a hm']
  have hXa : ∀ a, cth v a (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) (((Nat.choose 1 a : ℕ) : K)) := by
    intro a
    show cth v a (monomial (Finsupp.single v 1) (1 : K)) = _
    rw [cth_monomial, Finsupp.single_eq_same, one_mul]
  constructor
  · rw [hE, cth_add, cth_free v hE' one_ne_zero, add_zero, hX, hXa]
    simp only [Nat.choose_self, Nat.cast_one]
    rw [mul_comm]
    rfl
  · intro a ha
    rw [hE, cth_add, cth_free v hE' (by omega), add_zero, hX, hXa, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tie_mem {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (v : BVar N r D.T.t) {m' E' : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hE : D.Ehat O (r := r) i = X v * m' + E') (hm' : FreeV v m') (hE' : FreeV v E')
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    (δ : Bool) (hq : X v * m' = (if δ then D.Ehat O (r := r) i else 0) + rename (chainEmb N r D.T.t) q0)
    (hPE : FreeV v (otherE O r D j i))
    {y : MvPolynomial (Fin N × Fin r) (KK O)} {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp))
    (H : ∀ b, b ≤ n → ∃ (cb : ℕ) (yb : MvPolynomial (Fin N × Fin r) (KK O)),
      yb ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J (fun k => thr k + ((b : ℤ) : WithTop ℤ)) ∧
      cth v b (tailP O r D jp y g) = cb • tailP O r D jp yb g) :
    cth v n ((∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g) ∈ SSt O r D thr' := by
  classical
  obtain ⟨h1, h2⟩ := cth_lin hE hm' hE'
  rw [prodE_split D j i, mul_comm (D.Ehat O (r := r) i ^ j i), mul_assoc, cth_mul_free v n hPE, cth_mul, Finset.mul_sum]
  refine Submodule.sum_mem _ ?_
  rintro ⟨l, b⟩ hlb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hlb
  simp only at hlb ⊢
  obtain ⟨cb, yb, hyb, hcb⟩ := H b (by omega)
  rw [cth_pow v h1 h2, hcb, Nat.cast_smul_eq_nsmul]
  by_cases hl : l ≤ j i
  · have key : D.Ehat O (r := r) i ^ (j i - l) * (X v * m') ^ l * otherE O r D j i * tailP O r D jp yb g ∈
        SSt O r D thr' := by
      cases δ with
      | false =>
        simp only [Bool.false_eq_true, if_false, zero_add] at hq
        rw [hq]
        refine shift_mem hT hL i l hl (fun k => ?_) hq0 hyb hg
        refine le_trans (le_of_eq ?_) (hthr k)
        rw [add_assoc, ← hlb]
        push_cast
        rw [add_comm (l : WithTop ℤ)]
      | true =>
        simp only [if_true] at hq
        rw [hq, add_pow, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        refine Submodule.sum_mem _ fun a ha => ?_
        have ha' : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
        have h3 := shift_mem (thr' := thr') hT hL i (l - a) (by omega) (fun k => ?_) hq0 hyb hg
        · have h4 := (SSt O r D thr').smul_of_tower_mem (l.choose a) h3
          convert h4 using 1
          have e : j i - (l - a) = (j i - l) + a := by omega
          rw [e, pow_add, nsmul_eq_mul]
          ring
        · refine le_trans ?_ (hthr k)
          rw [add_assoc]
          gcongr
          have : ((b : ℤ) + ((l - a : ℕ) : ℤ)) ≤ (n : ℤ) := by omega
          exact_mod_cast this
    have h5 := (SSt O r D thr').smul_of_tower_mem ((j i).choose l) ((SSt O r D thr').smul_of_tower_mem cb key)
    convert h5 using 1
    simp only [nsmul_eq_mul]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
