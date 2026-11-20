import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DigOKAddInl

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Pof_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) : Pof Dt (⟨j0, Sum.inl l⟩, a0) = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Pof_inr (j0 : ZMod J) (m0 a0 : Fin r) : Pof Dt (⟨j0, Sum.inr m0⟩, a0) = Dt.P j0 m0 := rfl

/- English proof (translation)
Rewrite using `[monomial_single_add, pow_one]`.
-/
private theorem X_mul_monomialPlaneCoefficients {σ R : Type} [CommSemiring R] (w : σ) (mo : σ →₀ ℕ) (c : R) :
    (X w : MvPolynomial σ R) * monomial mo c = monomial (Finsupp.single w 1 + mo) c := by
  rw [monomial_single_add, pow_one]

/- English proof (translation)
Unfold `liftMon`. Rewrite using `[Finsupp.mapDomain_apply (liftVar_inj Dt)]`. Simplify using `[liftE, Finsupp.onFinset_apply]`.
-/
private theorem liftMon_apply_liftVar (mo : TL J Dt.nL r × Fin r →₀ ℕ) (w : TL J Dt.nL r × Fin r) :
    liftMon Dt mo (Dt.liftVar w) = mo w / Pof Dt w := by
  unfold liftMon
  rw [Finsupp.mapDomain_apply (liftVar_inj Dt)]
  simp [liftE, Finsupp.onFinset_apply]

/- English proof (translation)
Unfold `liftMon`. Rewrite using `[← Finsupp.mapDomain_single, ← Finsupp.mapDomain_add]`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [liftE, Finsupp.onFinset_apply, Finsupp.add_apply, Finsupp.single_apply]`.

Use `split_ifs with hw`. Substitute `hw` using the available equality. Conclude with `h2`. Rewrite using `[h1 w (Ne.symm hw), add_zero]`.
-/
private theorem liftMon_eq_add_single_of_eq_off (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) (d : ℕ)
    (h1 : ∀ w, w ≠ v → mo' w = mo w) (h2 : mo' v / Pof Dt v = mo v / Pof Dt v + d) :
    liftMon Dt mo' = liftMon Dt mo + Finsupp.single (Dt.liftVar v) d := by
  unfold liftMon
  rw [← Finsupp.mapDomain_single, ← Finsupp.mapDomain_add]
  congr 1
  ext w
  simp only [liftE, Finsupp.onFinset_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with hw
  · subst hw
    exact h2
  · rw [h1 w (Ne.symm hw), add_zero]

/- English proof (translation)
Unfold `SignedChainData.digOK`. Use `forall_congr' fun j => forall_congr' fun m => forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[h1]`. Introduce `h`. Simplify using `only [Prod.mk.injEq, Sigma.mk.inj_iff] at h`.

Take `⟨⟨rfl, h⟩, -⟩` from `h`. Simplify using `at h`.
-/
private theorem digOK_iff_of_eq_off_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r)
    (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ)
    (h1 : ∀ w, w ≠ (⟨j0, Sum.inl l⟩, a0) → mo' w = mo w) :
    Dt.digOK rho mo' ↔ Dt.digOK rho mo := by
  unfold SignedChainData.digOK
  refine forall_congr' fun j => forall_congr' fun m => forall_congr' fun a => ?_
  rw [h1]
  intro h
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨⟨rfl, h⟩, -⟩ := h
  simp at h

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) → (Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Rewrite using `[X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]`.

Distinguish the cases in `hd : Dt.digOK rho mo`. Rewrite using `[if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, X_mul_monomialPlaneCoefficients, liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by simp [Pof_inl, add_comm]), add_comm]`. Rewrite using `[if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, mul_zero]`. Rewrite using `[mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]`.
-/
theorem Fdig_mul_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inl l⟩, a0) * H) = X (Dt.liftVar (⟨j0, Sum.inl l⟩, a0)) * Dt.Fdig rho H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w
          = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    by_cases hd : Dt.digOK rho mo
    · rw [if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, X_mul_monomialPlaneCoefficients,
        liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by simp [Pof_inl, add_comm]), add_comm]
    · rw [if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, mul_zero]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]

/- English proof (translation)
Introduce `he`. Apply `hk` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq, Sigma.mk.inj_iff] at he`. Take `⟨⟨rfl, he⟩, rfl⟩` from `he`. Simplify using `at he`.

Substitute `he` using the available equality. Both sides reduce to the same expression.
-/
private theorem inr_pair_ne_of_ne {j j0 : ZMod J} {m m0 a a0 : Fin r} (hk : ((j, m), a) ≠ ((j0, m0), a0)) :
    ((⟨j, Sum.inr m⟩, a) : TL J Dt.nL r × Fin r) ≠ (⟨j0, Sum.inr m0⟩, a0) := by
  intro he
  apply hk
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at he
  obtain ⟨⟨rfl, he⟩, rfl⟩ := he
  simp at he
  subst he
  rfl

/- English proof (translation)
Unfold `SignedChainData.digOK`. Prove the components needed by the constructor for the conclusion. Introduce `h j m a`. Distinguish the cases in `hk : ((j, m), a) = ((j0, m0), a0)`. Simplify using `only [Prod.mk.injEq] at hk`.

Take `⟨⟨rfl, rfl⟩, rfl⟩` from `hk`. Rewrite using `[Function.update_self]`. Conclude with `h2.1 (h _ _ _)`. Rewrite using `[Function.update_of_ne hk, ← h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]`. Conclude with `h j m a`.

Introduce `h j m a`. Distinguish the cases in `hk : ((j, m), a) = ((j0, m0), a0)`. Simplify using `only [Prod.mk.injEq] at hk`. Take `⟨⟨rfl, rfl⟩, rfl⟩` from `hk`. Establish `h3` using `h j m a`.

Rewrite `h3` using `[Function.update_self]`. Conclude with `h2.2 h3`. Establish `h3` using `h j m a`. Rewrite `h3` using `[Function.update_of_ne hk]`. Rewrite using `[h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]`.

Conclude with `h3`.
-/
private theorem digOK_iff_update_of_eq_off_inr (j0 : ZMod J) (m0 a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) (x : ℕ)
    (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ)
    (h1 : ∀ w, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → mo' w = mo w)
    (h2 : mo' (⟨j0, Sum.inr m0⟩, a0) % Dt.P j0 m0 = rho ((j0, m0), a0) ↔
      mo (⟨j0, Sum.inr m0⟩, a0) % Dt.P j0 m0 = x) :
    Dt.digOK rho mo' ↔ Dt.digOK (Function.update rho ((j0, m0), a0) x) mo := by
  unfold SignedChainData.digOK
  constructor
  · intro h j m a
    by_cases hk : ((j, m), a) = ((j0, m0), a0)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
      rw [Function.update_self]
      exact h2.1 (h _ _ _)
    · rw [Function.update_of_ne hk, ← h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]
      exact h j m a
  · intro h j m a
    by_cases hk : ((j, m), a) = ((j0, m0), a0)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
      have h3 := h j m a
      rw [Function.update_self] at h3
      exact h2.2 h3
    · have h3 := h j m a
      rw [Function.update_of_ne hk] at h3
      rw [h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]
      exact h3

/- English proof (translation)
Establish `ha` using `Nat.mod_add_div a P`. Establish `hs` using `Nat.mod_lt a hP`. Break down `Nat.lt_or_ge (a % P + 1) P with h | h` into its components or cases. Use `left`. Establish `e : 1 + a = (a % P + 1) + P * (a / P)` using `by omega`.

Rewrite using `[e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h, zero_add]`. Conclude with `⟨h, rfl, rfl⟩`. Use `right`. Establish `e : 1 + a = 0 + P * (a / P + 1)` using `by rw [Nat.mul_add]; omega`. Rewrite using `[e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hP]`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
private theorem one_add_mod_div_cases (a P : ℕ) (hP : 0 < P) :
    (a % P + 1 < P ∧ (1 + a) % P = a % P + 1 ∧ (1 + a) / P = a / P) ∨
    (a % P + 1 = P ∧ (1 + a) % P = 0 ∧ (1 + a) / P = a / P + 1) := by
  have ha := Nat.mod_add_div a P
  have hs := Nat.mod_lt a hP
  rcases Nat.lt_or_ge (a % P + 1) P with h | h
  · left
    have e : 1 + a = (a % P + 1) + P * (a / P) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h,
      zero_add]
    exact ⟨h, rfl, rfl⟩
  · right
    have e : 1 + a = 0 + P * (a / P + 1) := by rw [Nat.mul_add]; omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hP]
    simp
    omega

/- English proof (translation)
Use `one_add_mod_div_cases (a - 1) P hP` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' ha]`. Then use the resulting hypothesis.
-/
private theorem mod_div_cases_of_sub_one (a P : ℕ) (hP : 0 < P) (ha : 1 ≤ a) :
    ((a - 1) % P + 1 < P ∧ a % P = (a - 1) % P + 1 ∧ a / P = (a - 1) / P) ∨
    ((a - 1) % P + 1 = P ∧ a % P = 0 ∧ a / P = (a - 1) / P + 1) := by
  have := one_add_mod_div_cases (a - 1) P hP
  rwa [Nat.add_sub_cancel' ha] at this

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) → (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Rewrite using `[pderiv_monomial, Fdig_mono, Fdig_mono]`.

Distinguish the cases in `hd : Dt.digOK rho mo`. Rewrite using `[if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, pderiv_monomial, liftMon_apply_liftVar, Pof_inl, Nat.div_one]`. Break down `Nat.eq_zero_or_pos (mo (⟨j0, Sum.inl l⟩, a0)) with h0 | h0` into its components or cases. Simplify using `[h0]`. Use `congr 1`.

Establish `e2` using `liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1) mo (⟨j0, Sum.inl l⟩, a0) 1 (fun w hw => (e1 w hw).symm) (by simp only [Pof_inl, Nat.div_one, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega)`. Rewrite using `[e2, add_tsub_cancel_right]`. Rewrite using `[if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, map_zero]`. Rewrite using `[map_add, Fdig_add, Fdig_add, hp, hq, map_add]`.
-/
theorem Fdig_der_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inl l⟩, a0) H) = pderiv (Dt.liftVar (⟨j0, Sum.inl l⟩, a0)) (Dt.Fdig rho H) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w
          = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    by_cases hd : Dt.digOK rho mo
    · rw [if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, pderiv_monomial,
        liftMon_apply_liftVar, Pof_inl, Nat.div_one]
      rcases Nat.eq_zero_or_pos (mo (⟨j0, Sum.inl l⟩, a0)) with h0 | h0
      · simp [h0]
      · congr 1
        have e2 := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1) mo
          (⟨j0, Sum.inl l⟩, a0) 1 (fun w hw => (e1 w hw).symm)
          (by simp only [Pof_inl, Nat.div_one, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega)
        rw [e2, add_tsub_cancel_right]
    · rw [if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, map_zero]
  · rw [map_add, Fdig_add, Fdig_add, hp, hq, map_add]

section Tau

variable (j0 : ZMod J) (m0 a0 : Fin r) (hP : 0 < Dt.P j0 m0) (rho : (ZMod J × Fin r) × Fin r → ℕ)

include hP

/- English proof (translation)
Unfold `SignedChainData.Fdig`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `mo hmo`. Establish `h3` using `(Finset.mem_filter.1 hmo).2 j0 m0 a0`. Establish `h4` using `Nat.mod_lt (mo (⟨j0, Sum.inr m0⟩, a0)) hP`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Fdig_big (h : Dt.P j0 m0 ≤ rho ((j0, m0), a0)) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho H = 0 := by
  unfold SignedChainData.Fdig
  apply Finset.sum_eq_zero
  intro mo hmo
  have h3 := (Finset.mem_filter.1 hmo).2 j0 m0 a0
  have h4 := Nat.mod_lt (mo (⟨j0, Sum.inr m0⟩, a0)) hP
  omega

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Establish `hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)` using `by simp`.

Rewrite using `[X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]`. Break down `one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩` into its components or cases. Establish `hn : ¬ Dt.digOK rho (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo)`. Introduce `hd`. Use `hd j0 m0 a0` as an intermediate fact.

Rewrite `this` using `[hv1, h2, h]`. Use linear arithmetic over natural numbers and integers. Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by`. Rewrite using `[hv1, h2, h]`. Apply the tactic sequence `constructor <;> intro <;> omega)`.

Rewrite using `[if_neg hn, if_neg (fun h' => hn (hd.2 h')), mul_zero]`. Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by`. Rewrite using `[hv1, h2, h]`. Apply the tactic sequence `constructor <;> intro <;> omega)`. Distinguish the cases in `hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (Dt.P j0 m0 - 1)) mo`.

Rewrite using `[if_pos (hd.2 hd'), if_pos hd', X_mul_monomialPlaneCoefficients, liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by rw [hv1, Pof_inr, h3]), add_comm]`. Rewrite using `[if_neg (fun h' => hd' (hd.1 h')), if_neg hd', mul_zero]`. Rewrite using `[mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]`.
-/
theorem Fdig_mul_zero (h : rho ((j0, m0), a0) = 0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inr m0⟩, a0) * H) =
      X (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0)) * Dt.Fdig (Function.update rho ((j0, m0), a0) (Dt.P j0 m0 - 1)) H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) := by simp
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    rcases one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hn : ¬ Dt.digOK rho (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo) := by
        intro hd
        have := hd j0 m0 a0
        rw [hv1, h2, h] at this
        omega
      have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by
        rw [hv1, h2, h]
        constructor <;> intro <;> omega)
      rw [if_neg hn, if_neg (fun h' => hn (hd.2 h')), mul_zero]
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by
        rw [hv1, h2, h]
        constructor <;> intro <;> omega)
      by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (Dt.P j0 m0 - 1)) mo
      · rw [if_pos (hd.2 hd'), if_pos hd', X_mul_monomialPlaneCoefficients,
          liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by rw [hv1, Pof_inr, h3]), add_comm]
      · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd', mul_zero]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Establish `hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)` using `by simp`.

Rewrite using `[X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]`. Break down `one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩` into its components or cases. Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by`. Rewrite using `[hv1, k2]`. Apply the tactic sequence `constructor <;> intro <;> omega)`.

Distinguish the cases in `hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo`. Rewrite using `[if_pos (hd.2 hd'), if_pos hd', liftMon_eq_add_single_of_eq_off Dt mo _ _ 0 e1 (by rw [hv1, Pof_inr, k3, add_zero]), Finsupp.single_zero, add_zero]`. Rewrite using `[if_neg (fun h' => hd' (hd.1 h')), if_neg hd']`. Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by`. Rewrite using `[hv1, k2]`.

Apply the tactic sequence `constructor <;> intro <;> omega)`. Establish `hn : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo`. Introduce `hd'`. Use `hd' j0 m0 a0` as an intermediate fact. Rewrite `this` using `[Function.update_self]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h' => hn (hd.1 h')), if_neg hn]`. Rewrite using `[mul_add, Fdig_add, Fdig_add, hp, hq]`.
-/
theorem Fdig_mul_pos (h1 : 0 < rho ((j0, m0), a0)) (h2 : rho ((j0, m0), a0) < Dt.P j0 m0)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inr m0⟩, a0) * H) =
      Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) := by simp
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    rcases one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by
        rw [hv1, k2]
        constructor <;> intro <;> omega)
      by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo
      · rw [if_pos (hd.2 hd'), if_pos hd',
          liftMon_eq_add_single_of_eq_off Dt mo _ _ 0 e1 (by rw [hv1, Pof_inr, k3, add_zero]), Finsupp.single_zero, add_zero]
      · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by
        rw [hv1, k2]
        constructor <;> intro <;> omega)
      have hn : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo := by
        intro hd'
        have := hd' j0 m0 a0
        rw [Function.update_self] at this
        omega
      rw [if_neg (fun h' => hn (hd.1 h')), if_neg hn]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq]

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Establish `hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1` using `by simp`.

Rewrite using `[pderiv_monomial, Fdig_mono, Fdig_mono]`. Break down `Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha` into its components or cases. Establish `hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo`. Introduce `hd`. Use `hd j0 m0 a0` as an intermediate fact.

Rewrite `this` using `[Function.update_self, ha, Nat.zero_mod]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hn', ha]`. Simplify using the standard rewrite rules. Break down `mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩` into its components or cases.

Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) + 1) mo _ e1 (by`. Rewrite using `[hv1, k2]`. Apply the tactic sequence `constructor <;> intro <;> omega)`. Distinguish the cases in `hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo`. Establish `hk : mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) % Dt.P j0 m0 = rho ((j0, m0), a0) + 1`.

Use `hd' j0 m0 a0` as an intermediate fact. Rewrite `this` using `[Function.update_self]`. Then use the resulting hypothesis. Establish `hL` using `liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 0 (fun w hw => (e1 w hw).symm) (by rw [hv1, Pof_inr, k3, add_zero])`. Rewrite `hL` using `[Finsupp.single_zero, add_zero]`. Rewrite using `[if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ← hL, X_mul_monomialPlaneCoefficients]`.

Establish `hc : ((rho ((j0, m0), a0) + 1 : ℕ) : KK O) + ((Dt.P j0 m0 : ℕ) : KK O) * ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O)`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_add, ← hk, Nat.mod_add_div]`. Break down `Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0) with hq | hq` into its components or cases. Rewrite `hc`, the goal using `[hq]`. Simplify using `only [Nat.cast_zero, mul_zero, map_zero, smul_zero, add_zero, smul_monomial] at hc ⊢`.

Rewrite using `[smul_eq_mul, ← hc, mul_comm]`. Establish `hLv : liftMon Dt mo (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0` using `by rw [liftMon_apply_liftVar, Pof_inr]`. Establish `hs : Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1 + (liftMon Dt mo - Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1) = liftMon Dt mo`. Use extensionality with `w`. Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`.

Use `split_ifs with hw`. Substitute `hw` using the available equality. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite using `[hs, smul_monomial, smul_monomial, ← map_add, smul_eq_mul, smul_eq_mul, ← hc]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => hd' (hd.1 h')), if_neg hd']`. Simplify using the standard rewrite rules. Establish `hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo`.

Introduce `hd`. Use `hd j0 m0 a0` as an intermediate fact. Rewrite `this` using `[Function.update_self, k2]`. Use linear arithmetic over natural numbers and integers. Establish `hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1)`.

Introduce `hd`. Use `hd j0 m0 a0` as an intermediate fact. Rewrite `this` using `[hv1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hn, if_neg hn']`.

Simplify using the standard rewrite rules. Simplify using `only [map_add, Fdig_add, hp, hq, smul_add, mul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem Fdig_der_lt (h : rho ((j0, m0), a0) + 1 < Dt.P j0 m0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inr m0⟩, a0) H) =
      ((rho ((j0, m0), a0) + 1 : ℕ) : KK O) • Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) H +
      ((Dt.P j0 m0 : ℕ) : KK O) • (X (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0)) * pderiv (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0))
        (Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) H)) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1 := by simp
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha
    · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo := by
        intro hd
        have := hd j0 m0 a0
        rw [Function.update_self, ha, Nat.zero_mod] at this
        omega
      rw [if_neg hn', ha]
      simp
    · rcases mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) + 1) mo _ e1 (by
          rw [hv1, k2]
          constructor <;> intro <;> omega)
        by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo
        · have hk : mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) % Dt.P j0 m0 = rho ((j0, m0), a0) + 1 := by
            have := hd' j0 m0 a0
            rwa [Function.update_self] at this
          have hL := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 0 (fun w hw => (e1 w hw).symm)
            (by rw [hv1, Pof_inr, k3, add_zero])
          rw [Finsupp.single_zero, add_zero] at hL
          rw [if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ← hL, X_mul_monomialPlaneCoefficients]
          have hc : ((rho ((j0, m0), a0) + 1 : ℕ) : KK O) + ((Dt.P j0 m0 : ℕ) : KK O) *
              ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O) := by
            rw [← Nat.cast_mul, ← Nat.cast_add, ← hk, Nat.mod_add_div]
          rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0) with hq | hq
          · rw [hq] at hc ⊢
            simp only [Nat.cast_zero, mul_zero, map_zero, smul_zero, add_zero, smul_monomial] at hc ⊢
            rw [smul_eq_mul, ← hc, mul_comm]
          · have hLv : liftMon Dt mo (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 := by rw [liftMon_apply_liftVar, Pof_inr]
            have hs : Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1 + (liftMon Dt mo - Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1) = liftMon Dt mo := by
              ext w
              simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
              split_ifs with hw
              · subst hw
                omega
              · simp
            rw [hs, smul_monomial, smul_monomial, ← map_add, smul_eq_mul, smul_eq_mul, ← hc]
            congr 1
            ring
        · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
          simp
      · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo := by
          intro hd
          have := hd j0 m0 a0
          rw [Function.update_self, k2] at this
          omega
        have hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) := by
          intro hd
          have := hd j0 m0 a0
          rw [hv1] at this
          omega
        rw [if_neg hn, if_neg hn']
        simp
  · simp only [map_add, Fdig_add, hp, hq, smul_add, mul_add]
    abel

/- English proof (translation)
Use `MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)` and prove the remaining obligations. Establish `e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w`. Introduce `w hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Establish `hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1` using `by simp`.

Rewrite using `[pderiv_monomial, Fdig_mono, Fdig_mono]`. Break down `Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha` into its components or cases. Distinguish the cases in `hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo`. Rewrite using `[if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ha]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hd', ha]`. Simplify using the standard rewrite rules. Break down `mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩` into its components or cases. Establish `hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo`. Introduce `hd`.

Use `hd j0 m0 a0` as an intermediate fact. Rewrite `this` using `[Function.update_self, k2]`. Use linear arithmetic over natural numbers and integers. Establish `hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1)`. Introduce `hd`.

Use `hd j0 m0 a0` as an intermediate fact. Rewrite `this` using `[hv1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hn, if_neg hn']`. Simplify using the standard rewrite rules.

Establish `hd` using `digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho 0 mo _ e1 (by`. Rewrite using `[hv1, k2]`. Apply the tactic sequence `constructor <;> intro <;> omega)`. Distinguish the cases in `hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo`. Establish `hL` using `liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 (fun w hw => (e1 w hw).symm) (by rw [hv1, Pof_inr, k3])`.

Establish `hc : ((Dt.P j0 m0 : ℕ) : KK O) * ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O)`. Rewrite using `[← Nat.cast_mul]`. Use `congr 1`. Use `Nat.mod_add_div (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0)` as an intermediate fact. Rewrite `this` using `[k2, zero_add]`.

Conclude with `this`. Rewrite using `[if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, hL, add_tsub_cancel_right, smul_monomial, smul_eq_mul, ← hc]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => hd' (hd.1 h')), if_neg hd']`.

Simplify using the standard rewrite rules. Simplify using `only [map_add, Fdig_add, hp, hq, smul_add]`.
-/
theorem Fdig_der_eq (h : rho ((j0, m0), a0) + 1 = Dt.P j0 m0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inr m0⟩, a0) H) =
      ((Dt.P j0 m0 : ℕ) : KK O) • pderiv (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0))
        (Dt.Fdig (Function.update rho ((j0, m0), a0) 0) H) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1 := by simp
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha
    · by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo
      · rw [if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ha]
        simp
      · rw [if_neg hd', ha]
        simp
    · rcases mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo := by
          intro hd
          have := hd j0 m0 a0
          rw [Function.update_self, k2] at this
          omega
        have hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) := by
          intro hd
          have := hd j0 m0 a0
          rw [hv1] at this
          omega
        rw [if_neg hn, if_neg hn']
        simp
      · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho 0 mo _ e1 (by
          rw [hv1, k2]
          constructor <;> intro <;> omega)
        by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo
        · have hL := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 (fun w hw => (e1 w hw).symm)
            (by rw [hv1, Pof_inr, k3])
          have hc : ((Dt.P j0 m0 : ℕ) : KK O) * ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O) := by
            rw [← Nat.cast_mul]
            congr 1
            have := Nat.mod_add_div (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0)
            rw [k2, zero_add] at this
            exact this
          rw [if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, hL, add_tsub_cancel_right,
            smul_monomial, smul_eq_mul, ← hc]
          congr 1
          ring
        · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
          simp
  · simp only [map_add, Fdig_add, hp, hq, smul_add]

end Tau

/- English proof (translation)
Break down `v0 with ⟨⟨j, l | m⟩, a⟩` into its components or cases. Use `⟨0, 0, 1, rho, rho, fun h => absurd rfl h, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_der_inl]`. Simplify using the standard rewrite rules. Establish `hPm` using `hP j m`.

Break down `lt_trichotomy (rho ((j, m), a) + 1) (Dt.P j m) with h | h | h` into its components or cases. Use `⟨((rho ((j, m), a) + 1 : ℕ) : KK O), ((Dt.P j m : ℕ) : KK O), 0, Function.update rho ((j, m), a) (rho ((j, m), a) + 1), rho, fun _ => rfl, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_der_lt Dt j m a hPm rho h H]`. Simplify using the standard rewrite rules. Use `⟨0, 0, ((Dt.P j m : ℕ) : KK O), rho, Function.update rho ((j, m), a) 0, fun h => absurd rfl h, fun H => ?_⟩` and prove the remaining obligations.

Rewrite using `[Fdig_der_eq Dt j m a hPm rho h H]`. Simplify using the standard rewrite rules. Use `⟨0, 0, 0, rho, rho, fun h => absurd rfl h, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_big Dt j m a hPm rho (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem Fdig_der_ex (hP : ∀ j m, 0 < Dt.P j m) (v0 : TL J Dt.nL r × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) :
    ∃ (c1 c2 c3 : KK O) (rho1 rho2 : (ZMod J × Fin r) × Fin r → ℕ), (c2 ≠ 0 → Dt.trueLet.vec v0.1 = true) ∧
      ∀ H, Dt.Fdig rho (pderiv v0 H) = c1 • Dt.Fdig rho1 H +
        c2 • (X (Dt.liftVar v0) * pderiv (Dt.liftVar v0) (Dt.Fdig rho1 H)) +
        c3 • pderiv (Dt.liftVar v0) (Dt.Fdig rho2 H) := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩
  · refine ⟨0, 0, 1, rho, rho, fun h => absurd rfl h, fun H => ?_⟩
    rw [Fdig_der_inl]
    simp
  · have hPm := hP j m
    rcases lt_trichotomy (rho ((j, m), a) + 1) (Dt.P j m) with h | h | h
    · refine ⟨((rho ((j, m), a) + 1 : ℕ) : KK O), ((Dt.P j m : ℕ) : KK O), 0,
        Function.update rho ((j, m), a) (rho ((j, m), a) + 1), rho, fun _ => rfl, fun H => ?_⟩
      rw [Fdig_der_lt Dt j m a hPm rho h H]
      simp
    · refine ⟨0, 0, ((Dt.P j m : ℕ) : KK O), rho, Function.update rho ((j, m), a) 0,
        fun h => absurd rfl h, fun H => ?_⟩
      rw [Fdig_der_eq Dt j m a hPm rho h H]
      simp
    · refine ⟨0, 0, 0, rho, rho, fun h => absurd rfl h, fun H => ?_⟩
      rw [Fdig_big Dt j m a hPm rho (by omega)]
      simp

/- English proof (translation)
Break down `v0 with ⟨⟨j, l | m⟩, a⟩` into its components or cases. Use `⟨0, 1, rho, rho, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_mul_inl]`. Simplify using the standard rewrite rules. Establish `hPm` using `hP j m`.

Distinguish the cases in `h0 : rho ((j, m), a) = 0`. Use `⟨0, 1, rho, Function.update rho ((j, m), a) (Dt.P j m - 1), fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_mul_zero Dt j m a hPm rho h0 H]`. Simplify using the standard rewrite rules. Distinguish the cases in `h1 : rho ((j, m), a) < Dt.P j m`.

Use `⟨1, 0, Function.update rho ((j, m), a) (rho ((j, m), a) - 1), rho, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_mul_pos Dt j m a hPm rho (Nat.pos_of_ne_zero h0) h1 H]`. Simplify using the standard rewrite rules. Use `⟨0, 0, rho, rho, fun H => ?_⟩` and prove the remaining obligations. Rewrite using `[Fdig_big Dt j m a hPm rho (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem Fdig_mul_ex (hP : ∀ j m, 0 < Dt.P j m) (v0 : TL J Dt.nL r × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) :
    ∃ (c1 c2 : KK O) (rho1 rho2 : (ZMod J × Fin r) × Fin r → ℕ),
      ∀ H, Dt.Fdig rho (X v0 * H) = c1 • Dt.Fdig rho1 H + c2 • (X (Dt.liftVar v0) * Dt.Fdig rho2 H) := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩
  · refine ⟨0, 1, rho, rho, fun H => ?_⟩
    rw [Fdig_mul_inl]
    simp
  · have hPm := hP j m
    by_cases h0 : rho ((j, m), a) = 0
    · refine ⟨0, 1, rho, Function.update rho ((j, m), a) (Dt.P j m - 1), fun H => ?_⟩
      rw [Fdig_mul_zero Dt j m a hPm rho h0 H]
      simp
    · by_cases h1 : rho ((j, m), a) < Dt.P j m
      · refine ⟨1, 0, Function.update rho ((j, m), a) (rho ((j, m), a) - 1), rho, fun H => ?_⟩
        rw [Fdig_mul_pos Dt j m a hPm rho (Nat.pos_of_ne_zero h0) h1 H]
        simp
      · refine ⟨0, 0, rho, rho, fun H => ?_⟩
        rw [Fdig_big Dt j m a hPm rho (by omega)]
        simp

/- English proof (translation)
Apply the tactic sequence `rcases v0 with ⟨⟨j, l | m⟩, a⟩ <;> rfl`.
-/
theorem modelLet_vec (v0 : TL J Dt.nL r × Fin r) : Dt.modelLet.vec (Dt.liftVar v0).1 = Dt.trueLet.vec v0.1 := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩ <;> rfl

end Formalism.MainNotions.PairMembershipBlocks
