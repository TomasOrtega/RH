import Formalism.SharpRestriction.GrowthBounds.AevalValuation.PlDefs

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.LetterSubstitution

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks Formalism.MainNotions.TraceSpectra

section Ph

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

def phV : ML J Dt.nL r × Fin r → TL J Dt.nL r × Fin r
  | (ML.ll j l, a) => (⟨j, Sum.inl l⟩, a)
  | (ML.lab j m, a) => (⟨j, Sum.inr m⟩, a)
  | (ML.wc j m, a) => (⟨j, Sum.inr m⟩, a)
  | (ML.tp j m _, a) => (⟨j, Sum.inr m⟩, a)

def phW : ML J Dt.nL r × Fin r → ℕ
  | (ML.wc j m, _) => Dt.P j m
  | _ => 1

/- English proof (translation)
Take `⟨w, a⟩` from `v`. Apply the tactic sequence `cases w <;> simp [SignedChainData.ph, phV, phW]`.
-/
theorem ph_X (v : ML J Dt.nL r × Fin r) : Dt.ph (X v) = X (phV Dt v) ^ phW Dt v := by
  obtain ⟨w, a⟩ := v
  cases w <;> simp [SignedChainData.ph, phV, phW]

/- English proof (translation)
Use extensionality with `⟨⟨j, x⟩, a⟩`. Break down `x with l | m` into its components or cases. Simplify using `[phExp]`. Simplify using `[phExp]`.
-/
theorem phExp_zero : phExp Dt 0 = 0 := by
  ext ⟨⟨j, x⟩, a⟩
  rcases x with l | m
  · simp [phExp]
  · simp [phExp]

/- English proof (translation)
Use extensionality with `⟨⟨j, l | m⟩, a⟩`. Simplify using `[phExp]`. Apply the tactic sequence `simp only [phExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_add, Pi.add_apply] split_ifs <;> ring`.
-/
theorem phExp_add (M N : ML J Dt.nL r × Fin r →₀ ℕ) : phExp Dt (M + N) = phExp Dt M + phExp Dt N := by
  ext ⟨⟨j, l | m⟩, a⟩
  · simp [phExp]
  · simp only [phExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_add, Pi.add_apply]
    split_ifs <;> ring

/- English proof (translation)
Apply the tactic sequence `ext ⟨⟨j, l | m⟩, a⟩ <;> rcases v with ⟨⟨j', l'⟩ | ⟨j', m'⟩ | ⟨j', m'⟩ | ⟨j', m', h'⟩, b⟩ <;>`. Simplify using `[phExp, phV, phW, Finsupp.single_apply]`. Apply the tactic sequence `all_goals by_cases hj : j' = j`. Apply the tactic sequence `all_goals first | (subst hj; simp_all) | simp_all`. Apply the tactic sequence `all_goals (rintro h1 rfl rfl; omega)`.
-/
theorem phExp_single (v : ML J Dt.nL r × Fin r) (k : ℕ) :
    phExp Dt (Finsupp.single v k) = Finsupp.single (phV Dt v) (phW Dt v * k) := by
  ext ⟨⟨j, l | m⟩, a⟩ <;> rcases v with ⟨⟨j', l'⟩ | ⟨j', m'⟩ | ⟨j', m'⟩ | ⟨j', m', h'⟩, b⟩ <;>
    simp [phExp, phV, phW, Finsupp.single_apply]
  all_goals by_cases hj : j' = j
  all_goals first | (subst hj; simp_all) | simp_all
  all_goals (rintro h1 rfl rfl; omega)

end Ph

/- English proof (translation)
Introduce `p O _ _ _ r J _ Dt M c`. Use `Finsupp.induction M ?_ ?_` and prove the remaining obligations. Simplify using `[phExp_zero, SignedChainData.ph]`. Introduce `v k N _ _ ih`. Rewrite using `[monomial_single_add, map_mul, map_pow, ih, ph_X, phExp_add, phExp_single, monomial_single_add, pow_mul]`.
-/
theorem phMon : PhMon := by
  intro p O _ _ _ r J _ Dt M c
  refine Finsupp.induction M ?_ ?_
  · simp [phExp_zero, SignedChainData.ph]
  · intro v k N _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, ph_X, phExp_add, phExp_single, monomial_single_add, pow_mul]

section Alg2

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

/- English proof (translation)
Establish `h` using `phMon p O r J Dt M a`. Rewrite using `[h, monomial_mul]`.
-/
theorem ph_monomial_mul (β : TL J Dt.nL r × Fin r →₀ ℕ) (c : KK O) (M : ML J Dt.nL r × Fin r →₀ ℕ) (a : KK O) :
    monomial β c * Dt.ph (monomial M a) = monomial (β + phExp Dt M) (c * a) := by
  have h := phMon p O r J Dt M a
  rw [h, monomial_mul]

/- English proof (translation)
Unfold `multideg`. Simplify using `[Finset.sum_add_distrib]`.
-/
theorem multideg_add' {ι : Type} {n : ℕ} (a b : ι × Fin n →₀ ℕ) (x : ι) :
    multideg (a + b) x = multideg a x + multideg b x := by
  unfold multideg
  simp [Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[phExp]`.
-/
theorem phExp_inl (M : ML J Dt.nL r × Fin r →₀ ℕ) (j : ZMod J) (l : Fin (Dt.nL j)) (a : Fin r) :
    phExp Dt M (⟨j, Sum.inl l⟩, a) = M (ML.ll j l, a) := by
  simp [phExp]

/- English proof (translation)
Simplify using `[phExp]`.
-/
theorem phExp_inr (M : ML J Dt.nL r × Fin r →₀ ℕ) (j : ZMod J) (m : Fin r) (a : Fin r) :
    phExp Dt M (⟨j, Sum.inr m⟩, a) = M (ML.lab j m, a) + Dt.P j m * M (ML.wc j m, a) +
      (if h : 1 ≤ m.val then M (ML.tp j m h, a) else 0) := by
  simp [phExp]

/- English proof (translation)
Break down `x with ⟨j, l | m⟩` into its components or cases. Simplify using `only [multideg, phDeg, phExp_inl]`. Simplify using `only [multideg, phDeg, phExp_inr, Finset.sum_add_distrib, Finset.mul_sum]`. Apply the tactic sequence `by_cases h : 1 ≤ (m : ℕ) <;> simp [h]`.
-/
theorem multideg_phExp (M : ML J Dt.nL r × Fin r →₀ ℕ) (x : TL J Dt.nL r) :
    multideg (phExp Dt M) x = phDeg Dt (fun y => multideg M y) x := by
  rcases x with ⟨j, l | m⟩
  · simp only [multideg, phDeg, phExp_inl]
  · simp only [multideg, phDeg, phExp_inr, Finset.sum_add_distrib, Finset.mul_sum]
    by_cases h : 1 ≤ (m : ℕ) <;> simp [h]

end Alg2

/- English proof (translation)
Unfold `compD`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_filter, mem_support_iff]`.

Distinguish the cases in `h : ∀ x, multideg m x = d x`. Apply the tactic sequence `by_cases h0 : coeff m H = 0 <;> simp [h, h0]`. Simplify using `[h]`.
-/
private theorem coeff_compD {Kf : Type} [Field Kf] {ι : Type} {s : ℕ} (d : ι → ℕ)
    (H : MvPolynomial (ι × Fin s) Kf) (m : ι × Fin s →₀ ℕ) :
    coeff m (compD d H) = if (∀ x, multideg m x = d x) then coeff m H else 0 := by
  unfold compD
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : ∀ x, multideg m x = d x
  · by_cases h0 : coeff m H = 0 <;> simp [h, h0]
  · simp [h]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_compD, coeff_monomial]`. Distinguish the cases in `h : m = n`. Substitute `h` using the available equality. Apply the tactic sequence `by_cases h' : ∀ x, multideg m x = d x <;> simp [h']`.

Apply the tactic sequence `by_cases h' : ∀ x, multideg m x = d x <;> simp [h, h']`.
-/
private theorem compD_monomial' {Kf : Type} [Field Kf] {ι : Type} {s : ℕ} (d : ι → ℕ)
    (m : ι × Fin s →₀ ℕ) (b : Kf) :
    compD d (monomial m b) = if (∀ x, multideg m x = d x) then monomial m b else 0 := by
  ext n
  rw [coeff_compD, coeff_monomial]
  by_cases h : m = n
  · subst h
    by_cases h' : ∀ x, multideg m x = d x <;> simp [h']
  · by_cases h' : ∀ x, multideg m x = d x <;> simp [h, h']

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [coeff_compD, coeff_sum]`. Apply the tactic sequence `by_cases h : ∀ x, multideg m x = d x <;> simp [h]`.
-/
theorem compD_sum {Kf : Type} [Field Kf] {ι : Type} {s : ℕ} (d : ι → ℕ) {κ : Type*} (S : Finset κ)
    (f : κ → MvPolynomial (ι × Fin s) Kf) : compD d (∑ k ∈ S, f k) = ∑ k ∈ S, compD d (f k) := by
  ext m
  simp only [coeff_compD, coeff_sum]
  by_cases h : ∀ x, multideg m x = d x <;> simp [h]

/- English proof (translation)
Introduce `p O _ _ _ r J _ Dt d β c F`. Establish `key : ∀ mo : ML J Dt.nL r × Fin r →₀ ℕ, ((∀ x, multideg (β + phExp Dt mo) x = d x) ↔ ∀ x, multideg β x + phDeg Dt (fun y => multideg mo y) x = d x)`. Introduce `mo`. Simplify using `only [multideg_add', multideg_phExp]`. Unfold `filtQ`.

Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, Finset.mul_sum, compD_sum, map_sum, Finset.mul_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun mo _ => ?_)` and prove the remaining obligations. Rewrite using `[ph_monomial_mul, compD_monomial']`. Simplify using `only [key]`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem compPh : CompPh := by
  intro p O _ _ _ r J _ Dt d β c F
  have key : ∀ mo : ML J Dt.nL r × Fin r →₀ ℕ, ((∀ x, multideg (β + phExp Dt mo) x = d x) ↔
      ∀ x, multideg β x + phDeg Dt (fun y => multideg mo y) x = d x) := by
    intro mo
    simp only [multideg_add', multideg_phExp]
  unfold filtQ
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum, compD_sum, map_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [ph_monomial_mul, compD_monomial']
  simp only [key]
  split_ifs <;> rfl

/- English proof (translation)
Unfold `SignedChainData.Fdig`. Use `Finset.sum_subset (Finset.filter_subset_filter _ hS) ?_` and prove the remaining obligations. Introduce `mo h1 h2`. Establish `h0 : coeff mo F = 0`. Assume the negation of the conclusion as `h`.

Conclude with `h2 (Finset.mem_filter.2 ⟨mem_support_iff.2 h, (Finset.mem_filter.1 h1).2⟩)`. Simplify using `[h0]`.
-/
private theorem fdig_eq_sum_C_coeff_mul_prod_of_support_subset {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
    (Dt : SignedChainData p O r J) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (S : Finset (TL J Dt.nL r × Fin r →₀ ℕ))
    (hS : F.support ⊆ S) :
    Dt.Fdig rho F = ∑ mo ∈ S with Dt.digOK rho mo,
      C (coeff mo F) * ∏ v ∈ mo.support, X (Dt.liftVar v) ^ Dt.liftExp mo v := by
  unfold SignedChainData.Fdig
  refine Finset.sum_subset (Finset.filter_subset_filter _ hS) ?_
  intro mo h1 h2
  have h0 : coeff mo F = 0 := by
    by_contra h
    exact h2 (Finset.mem_filter.2 ⟨mem_support_iff.2 h, (Finset.mem_filter.1 h1).2⟩)
  simp [h0]

/- English proof (translation)
Rewrite using `[fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho (F + G) (F.support ∪ G.support) support_add, fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho F (F.support ∪ G.support) Finset.subset_union_left, fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho G (F.support ∪ G.sup …`. Use `Finset.sum_congr rfl (fun mo _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_add, map_add, add_mul]`.
-/
private theorem signedChainData_fdig_add {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
    (Dt : SignedChainData p O r J) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (F + G) = Dt.Fdig rho F + Dt.Fdig rho G := by
  rw [fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho (F + G) (F.support ∪ G.support) support_add,
    fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho F (F.support ∪ G.support) Finset.subset_union_left,
    fdig_eq_sum_C_coeff_mul_prod_of_support_subset Dt rho G (F.support ∪ G.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [coeff_add, map_add, add_mul]

/- English proof (translation)
Introduce `p O _ _ _ r J Dt rho α s f`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[SignedChainData.Fdig]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, signedChainData_fdig_add, ih]`.
-/
theorem fdigSum : FdigSum := by
  intro p O _ _ _ r J Dt rho α s f
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [SignedChainData.Fdig]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, signedChainData_fdig_add, ih]

section Dig

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

/- English proof (translation)
Use `⟨fun j m a => ?_, fun j m h a => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hM _ (Finsupp.mem_support_iff.2 hne)`. Assume the negation of the conclusion as `hne`. Conclude with `hM _ (Finsupp.mem_support_iff.2 hne)`.
-/
theorem lw_zero (M : ML J Dt.nL r × Fin r →₀ ℕ) (hM : ∀ v ∈ M.support, IsLW v.1) :
    (∀ j m a, M (ML.lab j m, a) = 0) ∧ (∀ j m h a, M (ML.tp j m h, a) = 0) := by
  refine ⟨fun j m a => ?_, fun j m h a => ?_⟩
  · by_contra hne
    exact hM _ (Finsupp.mem_support_iff.2 hne)
  · by_contra hne
    exact hM _ (Finsupp.mem_support_iff.2 hne)

/- English proof (translation)
Take `⟨h1, h2⟩` from `lw_zero Dt M hM`. Unfold `SignedChainData.digOK`. Use `forall_congr' (fun j => forall_congr' (fun m => forall_congr' (fun a => ?_)))` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, phExp_inr, h1, zero_add]`. Use `split_ifs with h`.

Rewrite using `[h2, add_zero, Nat.add_mul_mod_self_left]`. Rewrite using `[add_zero, Nat.add_mul_mod_self_left]`.
-/
theorem digOK_phExp (hP : ∀ j m, 0 < Dt.P j m) (rho : (ZMod J × Fin r) × Fin r → ℕ) (β : TL J Dt.nL r × Fin r →₀ ℕ)
    (M : ML J Dt.nL r × Fin r →₀ ℕ) (hM : ∀ v ∈ M.support, IsLW v.1) :
    Dt.digOK rho (β + phExp Dt M) ↔ Dt.digOK rho β := by
  obtain ⟨h1, h2⟩ := lw_zero Dt M hM
  unfold SignedChainData.digOK
  refine forall_congr' (fun j => forall_congr' (fun m => forall_congr' (fun a => ?_)))
  rw [Finsupp.add_apply, phExp_inr, h1, zero_add]
  split_ifs with h
  · rw [h2, add_zero, Nat.add_mul_mod_self_left]
  · rw [add_zero, Nat.add_mul_mod_self_left]

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_notin_range _ _ hw`.
-/
theorem liftMon_notin (mo : TL J Dt.nL r × Fin r →₀ ℕ) (w : ML J Dt.nL r × Fin r)
    (hw : w ∉ Set.range Dt.liftVar) : liftMon Dt mo w = 0 :=
  Finsupp.mapDomain_notin_range _ _ hw

/- English proof (translation)
Apply the tactic sequence `rintro ⟨⟨j, l | m⟩, a⟩ ⟨⟨j', l' | m'⟩, a'⟩ h <;> simp only [SignedChainData.liftVar] at h <;> cases h <;> rfl`.
-/
private theorem liftVar_injective' {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {r J : ℕ} (Dt : SignedChainData p O r J) : Function.Injective Dt.liftVar := by
  rintro ⟨⟨j, l | m⟩, a⟩ ⟨⟨j', l' | m'⟩, a'⟩ h <;> simp only [SignedChainData.liftVar] at h <;> cases h <;> rfl

/- English proof (translation)
Apply the tactic sequence `rcases v with ⟨⟨j, l | m⟩, a⟩ <;> simp [liftE, Pof, SignedChainData.liftExp]`.
-/
private theorem liftE_apply_eq_liftExp {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {r J : ℕ} (Dt : SignedChainData p O r J) (γ : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    liftE Dt γ v = Dt.liftExp γ v := by
  rcases v with ⟨⟨j, l | m⟩, a⟩ <;> simp [liftE, Pof, SignedChainData.liftExp]

/- English proof (translation)
Take `⟨h1, h2⟩` from `lw_zero Dt M hM`. Use extensionality with `w`. Distinguish the cases in `hw : w ∈ Set.range Dt.liftVar`. Take `⟨x, rfl⟩` from `hw`. Simplify using `only [liftMon, Finsupp.add_apply, Finsupp.mapDomain_apply (liftVar_injective' Dt)]`.

Break down `x with ⟨⟨j, l | m⟩, a⟩` into its components or cases. Simplify using `[liftE, Pof, phExp_inl, SignedChainData.liftVar]`. Simplify using `only [liftE, Finsupp.onFinset_apply, Pof, Finsupp.add_apply, phExp_inr, h1, zero_add, SignedChainData.liftVar] split_ifs with h`. Rewrite using `[h2, add_zero, Nat.add_mul_div_left _ _ (hP j m)]`. Rewrite using `[add_zero, Nat.add_mul_div_left _ _ (hP j m)]`.

Rewrite using `[Finsupp.add_apply, liftMon_notin Dt _ w hw, liftMon_notin Dt _ w hw, zero_add]`. Break down `w with ⟨v, a⟩` into its components or cases. Consider the cases of `v with`. Consider the case `ll j l => exact absurd ⟨(⟨j, Sum.inl l⟩, a), rfl⟩ hw`. Consider the case `wc j m => exact absurd ⟨(⟨j, Sum.inr m⟩, a), rfl⟩ hw`.

Consider the case `lab j m => exact (h1 j m a).symm`. Consider the case `tp j m h => exact (h2 j m h a).symm`.
-/
theorem liftMon_phExp (hP : ∀ j m, 0 < Dt.P j m) (β : TL J Dt.nL r × Fin r →₀ ℕ) (M : ML J Dt.nL r × Fin r →₀ ℕ)
    (hM : ∀ v ∈ M.support, IsLW v.1) : liftMon Dt (β + phExp Dt M) = liftMon Dt β + M := by
  obtain ⟨h1, h2⟩ := lw_zero Dt M hM
  ext w
  by_cases hw : w ∈ Set.range Dt.liftVar
  · obtain ⟨x, rfl⟩ := hw
    simp only [liftMon, Finsupp.add_apply, Finsupp.mapDomain_apply (liftVar_injective' Dt)]
    rcases x with ⟨⟨j, l | m⟩, a⟩
    · simp [liftE, Pof, phExp_inl, SignedChainData.liftVar]
    · simp only [liftE, Finsupp.onFinset_apply, Pof, Finsupp.add_apply, phExp_inr, h1, zero_add,
        SignedChainData.liftVar]
      split_ifs with h
      · rw [h2, add_zero, Nat.add_mul_div_left _ _ (hP j m)]
      · rw [add_zero, Nat.add_mul_div_left _ _ (hP j m)]
  · rw [Finsupp.add_apply, liftMon_notin Dt _ w hw, liftMon_notin Dt _ w hw, zero_add]
    rcases w with ⟨v, a⟩
    cases v with
    | ll j l => exact absurd ⟨(⟨j, Sum.inl l⟩, a), rfl⟩ hw
    | wc j m => exact absurd ⟨(⟨j, Sum.inr m⟩, a), rfl⟩ hw
    | lab j m => exact (h1 j m a).symm
    | tp j m h => exact (h2 j m h a).symm

end Dig

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Simplify using `[hb, SignedChainData.Fdig]`. Unfold `SignedChainData.Fdig`. Rewrite using `[support_monomial, if_neg hb]`. Distinguish the cases in `hd : Dt.digOK rho γ`.

Simplify using `only [Finset.filter_singleton, hd, if_true, Finset.sum_singleton, coeff_monomial]`. Rewrite using `[liftMon, ← rename_monomial, monomial_eq, map_mul, rename_C, Finsupp.prod, map_prod]`. Use `congr 1`. Simplify using `only [map_pow, rename_X, liftE_apply_eq_liftExp]`. Use `(Finset.prod_subset Finsupp.support_onFinset_subset fun v _ hv => ?_).symm` and prove the remaining obligations.

Establish `h0 : Dt.liftExp γ v = 0`. Rewrite using `[← liftE_apply_eq_liftExp]`. Assume the negation of the conclusion as `h`. Conclude with `hv (Finsupp.mem_support_iff.2 h)`. Rewrite using `[h0, pow_zero]`.

Simplify using `[Finset.filter_singleton, hd]`.
-/
private theorem fdig_monomial {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {r J : ℕ} (Dt : SignedChainData p O r J) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (γ : TL J Dt.nL r × Fin r →₀ ℕ) (b : KK O) :
    Dt.Fdig rho (monomial γ b) = if Dt.digOK rho γ then monomial (liftMon Dt γ) b else 0 := by
  by_cases hb : b = 0
  · simp [hb, SignedChainData.Fdig]
  unfold SignedChainData.Fdig
  rw [support_monomial, if_neg hb]
  by_cases hd : Dt.digOK rho γ
  · simp only [Finset.filter_singleton, hd, if_true, Finset.sum_singleton, coeff_monomial]
    rw [liftMon, ← rename_monomial, monomial_eq, map_mul, rename_C, Finsupp.prod, map_prod]
    congr 1
    simp only [map_pow, rename_X, liftE_apply_eq_liftExp]
    refine (Finset.prod_subset Finsupp.support_onFinset_subset fun v _ hv => ?_).symm
    have h0 : Dt.liftExp γ v = 0 := by
      rw [← liftE_apply_eq_liftExp]
      by_contra h
      exact hv (Finsupp.mem_support_iff.2 h)
    rw [h0, pow_zero]
  · simp [Finset.filter_singleton, hd]

/- English proof (translation)
Introduce `p O _ _ _ r J _ Dt hP rho β c F hF`. Establish `hsupp : ∀ mo ∈ F.support, ∀ v ∈ mo.support, IsLW v.1`. Introduce `mo hmo v hv`. Conclude with `(mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars v).2 ⟨mo, hmo, hv⟩))`. Establish `hs` using `fdigSum p O r J Dt rho _ F.support (fun mo => monomial β c * Dt.ph (monomial mo (coeff mo F)))`.

Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, Finset.mul_sum, hs]`. Simplify using `only [ph_monomial_mul, fdig_monomial]`. Distinguish the cases in `hd : Dt.digOK rho β`. Rewrite using `[if_pos hd] conv_rhs => rw [F.as_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun mo hmo => ?_)` and prove the remaining obligations. Rewrite using `[if_pos ((digOK_phExp Dt hP rho β mo (hsupp mo hmo)).2 hd), liftMon_phExp Dt hP β mo (hsupp mo hmo), monomial_mul]`. Rewrite using `[if_neg hd]`. Use `Finset.sum_eq_zero (fun mo hmo => ?_)` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hd ((digOK_phExp Dt hP rho β mo (hsupp mo hmo)).1 h))]`.
-/
theorem fdigPh : FdigPh := by
  intro p O _ _ _ r J _ Dt hP rho β c F hF
  have hsupp : ∀ mo ∈ F.support, ∀ v ∈ mo.support, IsLW v.1 := by
    intro mo hmo v hv
    exact (mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars v).2 ⟨mo, hmo, hv⟩))
  have hs := fdigSum p O r J Dt rho _ F.support
    (fun mo => monomial β c * Dt.ph (monomial mo (coeff mo F)))
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum, hs]
  simp only [ph_monomial_mul, fdig_monomial]
  by_cases hd : Dt.digOK rho β
  · rw [if_pos hd]
    conv_rhs => rw [F.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun mo hmo => ?_)
    rw [if_pos ((digOK_phExp Dt hP rho β mo (hsupp mo hmo)).2 hd),
      liftMon_phExp Dt hP β mo (hsupp mo hmo), monomial_mul]
  · rw [if_neg hd]
    refine Finset.sum_eq_zero (fun mo hmo => ?_)
    rw [if_neg (fun h => hd ((digOK_phExp Dt hP rho β mo (hsupp mo hmo)).1 h))]

end Formalism.MainNotions.LetterSubstitution
