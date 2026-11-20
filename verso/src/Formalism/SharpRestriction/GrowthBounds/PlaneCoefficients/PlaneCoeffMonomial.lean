import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Comm

variable {σ τ Kf : Type} [Field Kf]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem oneT_monomial (e : Module.End Kf (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) (q : MvPolynomial τ Kf) :
    oneT e (monomial mo q) = monomial mo (e q) := by
  unfold oneT
  by_cases hq : q = 0
  · simp [hq]
  · rw [support_monomial, if_neg hq, Finset.sum_singleton, coeff_monomial, if_pos rfl]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem planeCoeff_monomial (nu : τ →₀ ℕ) (mo : σ →₀ ℕ) (q : MvPolynomial τ Kf) :
    planeCoeff nu (monomial mo q) = monomial mo (q.coeff nu) := by
  unfold planeCoeff
  by_cases hq : q = 0
  · simp [hq]
  · rw [support_monomial, if_neg hq, Finset.sum_singleton, coeff_monomial, if_pos rfl]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem X_mul_monomial' {R : Type} [CommSemiring R] (v : σ) (u : σ →₀ ℕ) (a : R) :
    (X v : MvPolynomial σ R) * monomial u a = monomial (Finsupp.single v 1 + u) a := by
  rw [X, monomial_mul, one_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem oneT_pderiv (e : Module.End Kf (MvPolynomial τ Kf)) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (pderiv v G) = pderiv v (oneT e G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, oneT_monomial, oneT_monomial, pderiv_monomial, ← nsmul_eq_mul', ← nsmul_eq_mul', map_nsmul]
  | add p q hp hq => simp only [map_add, oneT_add, hp, hq]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem oneT_X_mul (e : Module.End Kf (MvPolynomial τ Kf)) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (X v * G) = X v * oneT e G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [X_mul_monomial', oneT_monomial, oneT_monomial, X_mul_monomial']
  | add p q hp hq => simp only [mul_add, oneT_add, hp, hq]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem planeCoeff_pderiv (nu : τ →₀ ℕ) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (pderiv v G) = pderiv v (planeCoeff nu G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, planeCoeff_monomial, planeCoeff_monomial, pderiv_monomial, ← nsmul_eq_mul', ← nsmul_eq_mul',
      coeff_smul]
  | add p q hp hq => simp only [map_add, planeCoeff_add, hp, hq]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem planeCoeff_X_mul (nu : τ →₀ ℕ) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (X v * G) = X v * planeCoeff nu G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [X_mul_monomial', planeCoeff_monomial, planeCoeff_monomial, X_mul_monomial']
  | add p q hp hq => simp only [mul_add, planeCoeff_add, hp, hq]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem oneT_oneT (e T : Module.End Kf (MvPolynomial τ Kf)) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (oneT T G) = oneT (e * T) G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [oneT_monomial, oneT_monomial, oneT_monomial, Module.End.mul_apply]
  | add p q hp hq => simp only [oneT_add, hp, hq]

end Comm

section XXgLin

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J) {d : TL J Dt.nL r → ℕ} {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem XXg_add {F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) (hG : XXg Dt d th thL G) :
    XXg Dt d th thL (F + G) := by
  refine ⟨Submodule.add_mem _ hF.1 hG.1, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_add]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF.2.1 rho j i) (hG.2.1 rho j i))
  · exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF.2.2 j mm hm) (hG.2.2 j mm hm))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem XXg_smul (c : KK O) {F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) :
    XXg Dt d th thL (c • F) := by
  refine ⟨Submodule.smul_mem _ c hF.1, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_smul]
    exact geZ_mono (valS_smul_ge _ _ _ _) (hF.2.1 rho j i)
  · exact geZ_mono (valS_smul_ge _ _ _ _) (hF.2.2 j mm hm)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem XXg_zero : XXg Dt d th thL (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]; exact geZ_top _
  · rw [valS_zero_eq_top]; exact geZ_top _

end XXgLin

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem max_three_le_add {a b c a' b' c' t : ℝ} (ha : a ≤ a' + t) (hb : b ≤ b' + t) (hc : c ≤ c' + t) :
    max a (max b c) ≤ max a' (max b' c') + t := by
  refine max_le (le_trans ha ?_) (max_le (le_trans hb ?_) (le_trans hc ?_))
  · exact add_le_add_left (le_max_left _ _) _
  · exact add_le_add_left (le_trans (le_max_left _ _) (le_max_right _ _)) _
  · exact add_le_add_left (le_trans (le_max_right _ _) (le_max_right _ _)) _

section Th

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {J : ℕ} (nL : ZMod J → ℕ) (K : ℕ) [NeZero K]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Combine the linear equalities and inequalities to obtain the conclusion. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem thStar_le (ka ka1 : ZMod J → ℕ → Fin K → ℤ) (j : ZMod J) (u : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (h1 : (ka j (u + 1) 0 : ℝ) ≤ ka1 j (u + 1) 0 + t) (h2 : (ka j (u - 1) 0 : ℝ) ≤ ka1 j (u - 1) 0 + t) :
    thStar Fr p deg Y k mS nL K ka j u ≤ thStar Fr p deg Y k mS nL K ka1 j u + t := by
  unfold thStar
  simp only []
  apply max_three_le_add
  · linarith
  · split_ifs <;> linarith
  · split_ifs <;> linarith

end Th

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem touch_cost_nonneg {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (s : Fin n') (jz : ℤ) (u : ℕ) : 0 ≤ cost1 Fr s jz u := by
  unfold cost1
  split_ifs <;> norm_num

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem touch_cost_eq_one {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (s : Fin n') (jz : ℤ) (u : ℕ) (h : touchT Fr jz u s) :
    cost1 Fr s jz u = 1 := by
  unfold cost1
  rw [if_pos h]

def thUp {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) (s : Fin n') (th : ∀ j, Fin (Dt.nch j) → ℝ) :
    ∀ j, Fin (Dt.nch j) → ℝ :=
  fun j i => th j i + cost1 Fr s (segZ j) i.val

def thLUp {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) (s : Fin n') (thL : ZMod J → Fin r → ℝ) :
    ZMod J → Fin r → ℝ :=
  fun j mm => thL j mm + cost1 Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))

section Glue

variable {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} [NeZero J] (K : ℕ) [NeZero K]
  (Dt : SignedChainData p O r J)

variable {Fr p deg Y k mS K Dt}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thLe_up {sc sL : ℝ} {loss : ℤ → ℕ → ℝ} {s : Fin n'} {ka : ZMod J → ℕ → Fin K → ℤ}
    {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr s jz u) Dt ka th thL) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka (thUp Fr Dt s th) (thLUp Fr Dt s thL) := by
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have := hT.1 j i
    unfold thUp
    linarith
  · have := hT.2 j mm hm
    unfold thLUp
    linarith

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thLe_weak {sc sL : ℝ} {loss : ℤ → ℕ → ℝ} {s : Fin n'} {ka : ZMod J → ℕ → Fin K → ℤ}
    {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr s jz u) Dt ka th thL) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka th thL := by
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have := hT.1 j i
    have := touch_cost_nonneg Fr s (segZ j) i.val
    linarith
  · have := hT.2 j mm hm
    have := touch_cost_nonneg Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))
    linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thLUp_pos {s : Fin n'} {thL : ZMod J → Fin r → ℝ} (h : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm) :
    ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thLUp Fr Dt s thL j mm := by
  intro j mm hm
  have := h j mm hm
  have := touch_cost_nonneg Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))
  unfold thLUp
  linarith

def TouchAt (Fr : Frames n' r) (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) : Prop :=
  ∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
      (x0 ∈ NSet Dt.nL j (u + 1) ∨ ∃ m : Fin r, x0 = ⟨j - 1, Sum.inr m⟩) →
      touchT Fr (segZ j) u (posOf n' (posTL Fr x0))

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Substitute using the available equality. Prove the first alternative. Prove the second alternative. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem thDrop_of (hB : Base Fr p Dt) {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) :
    ThDrop Dt x0 th (thUp Fr Dt (posOf n' (posTL Fr x0)) th) thL (thLUp Fr Dt (posOf n' (posTL Fr x0)) thL) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
  have hr : 0 < r := NeZero.pos r
  refine ⟨fun j i => ?_, fun j i hc => ?_, fun j mm => ?_, fun j mm hx => ?_⟩
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) i.val
    unfold thUp
    linarith
  · have hi : i.val < Dt.nL j + r := by
      have := i.isLt
      have := b5 j
      omega
    have ht : touchT Fr (segZ j) i.val (posOf n' (posTL Fr x0)) := by
      apply hG j i.val hi
      rcases hc with ⟨l, hl, hmem⟩ | hw
      · left
        rw [b6 j i] at hmem
        rcases hmem with hmem | ⟨l', hl', hlt⟩
        · exact absurd hmem (by simp)
        · have : l = l' := Sum.inl.inj hl'
          subst this
          exact Or.inl ⟨l, hl, by omega⟩
      · exact Or.inr hw
    unfold thUp
    rw [touch_cost_eq_one Fr _ _ _ ht]
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) (Dt.nL j + (r - 1 - mm.val))
    unfold thLUp
    linarith
  · have hi : Dt.nL j + (r - 1 - mm.val) < Dt.nL j + r := by omega
    have ht : touchT Fr (segZ j) (Dt.nL j + (r - 1 - mm.val)) (posOf n' (posTL Fr x0)) := by
      apply hG j _ hi
      left
      rcases hx with ⟨l, hl⟩ | ⟨m', hlt, hm'⟩
      · exact Or.inl ⟨l, hl, by have := l.isLt; omega⟩
      · refine Or.inr ⟨m', hm', ?_⟩
        have h1 : mm.val < m'.val := hlt
        have h2 := m'.isLt
        omega
    unfold thLUp
    rw [touch_cost_eq_one Fr _ _ _ ht]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem inN_le_cost {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0) (j : ZMod J) (u u' : ℕ) (hu : u < Dt.nL j + r)
    (hu' : u' ≤ u + 1) : (inN Dt.nL x0 j u' : ℝ) ≤ cost1 Fr (posOf n' (posTL Fr x0)) (segZ j) u := by
  unfold inN
  split_ifs with h
  · rw [touch_cost_eq_one Fr _ _ _ (hG j u hu (Or.inl (NSet_mono Dt.nL j hu' h)))]
    norm_num
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) u
    simpa using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thLe_ka (hB : Base Fr p Dt) {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0) {sc sL : ℝ} {loss : ℤ → ℕ → ℝ}
    {ka ka1 : ZMod J → ℕ → Fin K → ℤ} {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr (posOf n' (posTL Fr x0)) jz u) Dt ka th thL)
    (hka : ∀ j u, ka j u 0 ≤ ka1 j u 0 + inN Dt.nL x0 j u) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka1 th thL := by
  have hr : 0 < r := NeZero.pos r
  have key : ∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
      thStar Fr p deg Y k mS Dt.nL K ka j u ≤
        thStar Fr p deg Y k mS Dt.nL K ka1 j u + cost1 Fr (posOf n' (posTL Fr x0)) (segZ j) u := by
    intro j u hu
    apply thStar_le _ _ _ _ _ _ _ _ _ _ _ _ _ (touch_cost_nonneg _ _ _ _)
    · have h1 : ((ka j (u + 1) 0 : ℤ) : ℝ) ≤ ((ka1 j (u + 1) 0 + inN Dt.nL x0 j (u + 1) : ℤ) : ℝ) := by
        exact_mod_cast hka j (u + 1)
      have h2 := inN_le_cost hG j u (u + 1) hu le_rfl
      push_cast at h1
      linarith
    · have h1 : ((ka j (u - 1) 0 : ℤ) : ℝ) ≤ ((ka1 j (u - 1) 0 + inN Dt.nL x0 j (u - 1) : ℤ) : ℝ) := by
        exact_mod_cast hka j (u - 1)
      have h2 := inN_le_cost hG j u (u - 1) hu (by omega)
      push_cast at h1
      linarith
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have hi : i.val < Dt.nL j + r := by
      have := i.isLt
      have := hB.2.2.2.2.1 j
      omega
    have := hT.1 j i
    have := key j i.val hi
    linarith
  · have := hT.2 j mm hm
    have := key j (Dt.nL j + (r - 1 - mm.val)) (by omega)
    linarith

end Glue

end Formalism.MainNotions.PairMembershipBlocks
