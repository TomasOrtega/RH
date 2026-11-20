import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Unfold `relDim`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card]`. Both sides reduce to the same expression.
-/
theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

/- English proof (translation)
Rewrite using `[relDim_bot]`. Simplify using `[Fintype.card_sigma]`. Both sides reduce to the same expression.
-/
theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

/- English proof (translation)
Unfold `binomFn`. Break down `lt_trichotomy t 0 with h | rfl | h` into its components or cases. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega)]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Take `⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1` from `⟨(t - 1).toNat, by omega⟩`. Rewrite using `[if_pos (by omega), if_pos (by omega), if_pos (by omega)]`. Establish `h1 : ((u : ℤ) + 1).toNat = u + 1` using `by omega`. Establish `h2 : ((u : ℤ) + 1 - 1).toNat = u` using `by omega`. Establish `h3` using `Nat.choose_succ_succ (u + N + 1) N`.

Rewrite using `[h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3, show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]`. Simplify using `[blockWeight]`.
-/
theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

/- English proof (translation)
Establish `hinj : Function.Injective (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap`. Introduce `x y h`. Simplify `h` using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero]`. Unfold `gradedPiece`. Rewrite using `[← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _), weightedHomogeneousSubmodule_eq_finsupp_supported]`.

Set `s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)` to `{d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}`. Set `e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ))` to `Equiv.subtypeEquivRight fun d => by`. Rewrite using `[Finset.mem_finsuppAntidiag]`. Simplify using `only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← weight_projIdx]`. Conclude with `congrFun h ()`. Introduce `h`. Use function extensionality and compare the values at `u`.

Rewrite using `[weight_projIdx]`. Conclude with `h`. Establish `: Fintype s` using `Fintype.ofEquiv _ e.symm`. Rewrite using `[LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self, Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]`. Simplify using `[Fintype.card_sigma]`.

Rewrite using `[add_comm, Nat.choose_symm_add]`.
-/
theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

/- English proof (translation)
Unfold `hilbFn binomFn`. Distinguish the cases in `hm : 0 ≤ m ()`. Rewrite using `[if_pos (fun k => hm), if_pos hm]`. Establish `: (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat` using `rfl`. Rewrite using `[this, finrank_gradedPiece_projectiveSpace]`.

Rewrite using `[if_neg (fun h => hm (h ())), if_neg hm]`.
-/
theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]

/- English proof (translation)
Proceed by induction on `j generalizing N with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]`. Use function extensionality and compare the values at `m`.

Simplify using `only [diffStep, Pi.sub_apply, Pi.one_apply]`. Conclude with `binomFn_sub N (m ())`.
-/
theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

/- English proof (translation)
Establish `hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ())`. Use function extensionality and compare the values at `m`. Rewrite using `[zero_add, hilbFn_projectiveSpace]`. Unfold `intNum mixedDiff`. Rewrite using `[List.ofFn_const, hh, foldr_diffStep_binomFn]`.

Establish `hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1` using `(Filter.eventually_ge_atTop 0).mono fun m hm => by`. Establish `: (0 : ℤ) ≤ m ()` using `hm ()`. Simplify using `[binomFn, this]`. Establish `hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c` using `⟨1, hev⟩`. Unfold `eventualValue`.

Rewrite using `[dif_pos hex]`. Take `⟨m, h1, h2⟩` from `(hex.choose_spec.and hev).exists`. Conclude with `h1.symm.trans h2`.
-/
theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

/- English proof (translation)
Introduce and unpack `⟨a, x⟩ ⟨b, y⟩ h`. Simplify using `only [blockIncl, Sigma.mk.inj_iff] at h`. Take `⟨h1, h2⟩` from `h`. Consider the cases of `j.injective h1`. Rewrite using `[eq_of_heq h2]`.
-/
theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

/- English proof (translation)
The claim follows from `Ideal.comap_bot_of_injective _ (rename_injective _ (blockIncl_injective j ι'))`.
-/
theorem contractPrime_bot {K K' : Type*} {F : Type*} [Field F] (j : K ↪ K') (ι' : K' → Type*) :
    contractPrime j (⊥ : Ideal (MRing ι' F)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ (blockIncl_injective j ι'))

/- English proof (translation)
The claim follows from `Ideal.map_bot`.
-/
theorem addBlockPrime_bot {K : Type*} {F : Type*} [Field F] (ι : K → Type) (N : ℕ) :
    addBlockPrime N (⊥ : Ideal (MRing ι F)) = ⊥ :=
  Ideal.map_bot

/- English proof (translation)
The claim follows from `isMultiProjPrime_bot.multiHomog`.
-/
theorem isMultiHomogIdeal_bot_projectiveSpace (N : ℕ) :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx N) ℚ)) :=
  isMultiProjPrime_bot.multiHomog

/- English proof (translation)
The claim follows from `isWeightedHomogeneous_X _ _ _`.
-/
theorem coordinate_isMultiHomog (N : ℕ) (i : Fin (N + 1)) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) (blockWeight (ProjIdx N) ⟨(), 0⟩) :=
  isWeightedHomogeneous_X _ _ _

/- English proof (translation)
Rewrite using `[Ideal.mem_bot]`. Conclude with `X_ne_zero _`.
-/
theorem coordinate_not_mem_bot (N : ℕ) (i : Fin (N + 1)) :
    (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx N) ℚ)) := by
  rw [Ideal.mem_bot]
  exact X_ne_zero _

/- English proof (translation)
Assemble the required witnesses or components as `⟨isMultiHomogIdeal_bot_projectiveSpace 1, coordinate_isMultiHomog 1 0⟩`.
-/
theorem HilbExactDivide.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) :=
  ⟨isMultiHomogIdeal_bot_projectiveSpace 1, coordinate_isMultiHomog 1 0⟩

/- English proof (translation)
Introduce and unpack `⟨⟩`. Use `⟨1, Or.inr (by simp), Filter.Eventually.of_forall fun m => ?_⟩` and prove the remaining obligations. Simplify using `[diffStep]`.
-/
theorem PolyOfDiffs.hypotheses_example :
    ∀ k : Unit, ∃ q : MvPolynomial Unit ℚ, (q = 0 ∨ q.totalDegree < 1) ∧
      EventuallyPoly (diffStep (Pi.single k 1) (fun m : Unit → ℤ => m ())) q := by
  rintro ⟨⟩
  refine ⟨1, Or.inr (by simp), Filter.Eventually.of_forall fun m => ?_⟩
  simp [diffStep]

/- English proof (translation)
The claim follows from `(Filter.eventually_ge_atTop 0).mono fun m hm => by have ht : (0 : ℤ) ≤ m () := hm () rw [hilbFn_projectiveSpace, binomFn, if_pos ht, Nat.choose_one_right] have e : (((m ()).toNat : ℕ) : ℤ) = m () := Int.toNat_of_nonneg ht have e' : (((m ()).toNat : ℕ) : ℚ) = (m () : ℚ) := by exac …`.
-/
theorem eventuallyPoly_projectiveLine :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  (Filter.eventually_ge_atTop 0).mono fun m hm => by
    have ht : (0 : ℤ) ≤ m () := hm ()
    rw [hilbFn_projectiveSpace, binomFn, if_pos ht, Nat.choose_one_right]
    have e : (((m ()).toNat : ℕ) : ℤ) = m () := Int.toNat_of_nonneg ht
    have e' : (((m ()).toNat : ℕ) : ℚ) = (m () : ℚ) := by exact_mod_cast e
    simp only [map_add, eval_X, map_one]
    push_cast
    rw [e']

/- English proof (translation)
Use `⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant, eventuallyPoly_projectiveLine, fun h => ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (MvPolynomial.eval fun _ => (0 : ℚ)) h`.
-/
theorem HilbDegreeBound.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) ∧
      (X () + 1 : MvPolynomial Unit ℚ) ≠ 0 := by
  refine ⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant,
    eventuallyPoly_projectiveLine, fun h => ?_⟩
  simpa using congrArg (MvPolynomial.eval fun _ => (0 : ℚ)) h

/- English proof (translation)
Assemble the required witnesses or components as `⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant, relDim_projectiveSpace 1⟩`.
-/
theorem MixedDiffConst.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = (1 : ℕ) :=
  ⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant,
    relDim_projectiveSpace 1⟩

/- English proof (translation)
Use `⟨isMultiHomogIdeal_bot_projectiveSpace 1, ?_⟩` and prove the remaining obligations. Rewrite using `[relDim_projectiveSpace]`. Use `show (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((2 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))`. Conclude with `WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))`.
-/
theorem IntNumZeroSlot.hypotheses_example :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) < (2 : ℕ) := by
  refine ⟨isMultiHomogIdeal_bot_projectiveSpace 1, ?_⟩
  rw [relDim_projectiveSpace]
  show (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((2 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))

/- English proof (translation)
Use `⟨isMultiProjPrime_bot, ?_⟩` and prove the remaining obligations. Rewrite using `[relDim_projectiveSpace]`. Both sides reduce to the same expression.
-/
theorem IntNumBase.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = 0 := by
  refine ⟨isMultiProjPrime_bot, ?_⟩
  rw [relDim_projectiveSpace]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨isMultiProjPrime_bot, relDim_projectiveSpace 1, coordinate_isMultiHomog 1 0, coordinate_not_mem_bot 1 0⟩`.
-/
theorem CutRegular.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = ((0 + 1 : ℕ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) :=
  ⟨isMultiProjPrime_bot, relDim_projectiveSpace 1, coordinate_isMultiHomog 1 0,
    coordinate_not_mem_bot 1 0⟩

/- English proof (translation)
Use `⟨isMultiProjPrime_bot, ?_, coordinate_isMultiHomog 1 0, coordinate_isMultiHomog 1 1, coordinate_not_mem_bot 1 0, coordinate_not_mem_bot 1 1⟩` and prove the remaining obligations. Rewrite using `[relDim_projectiveSpace]`. Both sides reduce to the same expression.
-/
theorem CutRational.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = 1 ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      IsMultiHomog (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) := by
  refine ⟨isMultiProjPrime_bot, ?_, coordinate_isMultiHomog 1 0, coordinate_isMultiHomog 1 1,
    coordinate_not_mem_bot 1 0, coordinate_not_mem_bot 1 1⟩
  rw [relDim_projectiveSpace]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨isMultiProjPrime_bot, map_one _⟩`.
-/
theorem IntNumBaseChange.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (algebraMap ℚ (RatFunc ℚ)) 1 = 1 :=
  ⟨isMultiProjPrime_bot, map_one _⟩

/- English proof (translation)
Use `⟨isMultiProjPrime_bot, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[relDim_bot]`. Both sides reduce to the same expression. Rewrite using `[contractPrime_bot, relDim_bot] show (((0 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))`. Conclude with `WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))`.
-/
theorem ProjectionFormulaContracted.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ))) < (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    show (((0 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))

/- English proof (translation)
Use `⟨isMultiProjPrime_bot, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[relDim_bot]`. Both sides reduce to the same expression. Rewrite using `[contractPrime_bot, relDim_bot]`. Both sides reduce to the same expression.
-/
theorem ProjectionFormulaDegree.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ))) = (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨isMultiProjPrime_bot, relDim_projectiveSpace 0, rfl⟩`.
-/
theorem ProductWithProjectiveSpace.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = (0 : ℕ) ∧ 0 + 1 = 0 + 1 :=
  ⟨isMultiProjPrime_bot, relDim_projectiveSpace 0, rfl⟩

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[h]`. Assume the negation of the conclusion as `hne`.

Establish `hw` using `hf hne`. Establish `hd : d = Finsupp.single ⟨(), 0⟩ (b ())`. Use extensionality with `i`. Take `⟨⟨⟩, i⟩` from `i`. Establish `hi : i = 0` using `Fin.fin_one_eq_zero i`.

Substitute `hi` using the available equality. Rewrite using `[Finsupp.single_eq_same, ← congrFun hw (), weight_projIdx, Fintype.sum_eq_single ⟨(), 0⟩]`. Introduce and unpack `⟨⟨⟩, j⟩ hj`. Conclude with `absurd (by rw [Fin.fin_one_eq_zero j]) hj`. Conclude with `h hd.symm`.
-/
theorem eq_monomial_of_isMultiHomog_point {F : Type*} [Field F] (f : MRing (ProjIdx 0) F)
    (b : Unit → ℕ) (hf : IsMultiHomog f b) :
    f = monomial (Finsupp.single ⟨(), 0⟩ (b ())) (coeff (Finsupp.single ⟨(), 0⟩ (b ())) f) := by
  ext d
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · by_contra hne
    have hw := hf hne
    have hd : d = Finsupp.single ⟨(), 0⟩ (b ()) := by
      ext i
      obtain ⟨⟨⟩, i⟩ := i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      rw [Finsupp.single_eq_same, ← congrFun hw (), weight_projIdx,
        Fintype.sum_eq_single ⟨(), 0⟩]
      rintro ⟨⟨⟩, j⟩ hj
      exact absurd (by rw [Fin.fin_one_eq_zero j]) hj
    exact h hd.symm

/- English proof (translation)
Unfold `resDeg`. Rewrite using `[dif_pos Ideal.isPrime_bot]`. Establish `hle : homFracDegZero (⊥ : Ideal (MRing (ProjIdx 0) F)) = ⊥`. Use `le_antisymm ?_ bot_le` and prove the remaining obligations. Unfold `homFracDegZero`.

Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `x ⟨b, f, g, hf, hg, hgP, rfl⟩`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_bot]`. Establish `ef` using `eq_monomial_of_isMultiHomog_point f b hf`. Establish `eg` using `eq_monomial_of_isMultiHomog_point g b hg`.

Rewrite `ef`, `eg` using `[← C_mul_X_pow_eq_monomial]`. Generalize the expression as in `coeff (Finsupp.single ⟨(), 0⟩ (b ())) f = a at ef`. Generalize the expression as in `coeff (Finsupp.single ⟨(), 0⟩ (b ())) g = c at eg`. Generalize the expression as in `b () = n at ef eg`. Use `set v : (Σ _ : Unit, ProjIdx 0 ()) := ⟨(), 0⟩`.

Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Apply `hgP` to reduce the goal to its premises. Rewrite using `[eg, C_0, zero_mul]`. Conclude with `Ideal.zero_mem _`.

Establish `hY : algebraMap (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F))) (FractionRing (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F)))) (Ideal.Quotient.mk _ (X v ^ n)) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]`. Conclude with `pow_ne_zero _ (X_ne_zero _)`. Use `⟨a / c, ?_⟩` and prove the remaining obligations. Rewrite using `[ef, eg, map_mul, map_mul, map_mul, map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, mul_div_mul_right _ _ hY, map_div₀]`.

Rewrite using `[hle, IntermediateField.finrank_bot]`.
-/
theorem resDeg_point (F : Type*) [Field F] : resDeg (⊥ : Ideal (MRing (ProjIdx 0) F)) = 1 := by
  unfold resDeg
  rw [dif_pos Ideal.isPrime_bot]
  have hle : homFracDegZero (⊥ : Ideal (MRing (ProjIdx 0) F)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_bot]
    have ef := eq_monomial_of_isMultiHomog_point f b hf
    have eg := eq_monomial_of_isMultiHomog_point g b hg
    rw [← C_mul_X_pow_eq_monomial] at ef eg
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) f = a at ef
    generalize coeff (Finsupp.single ⟨(), 0⟩ (b ())) g = c at eg
    generalize b () = n at ef eg
    set v : (Σ _ : Unit, ProjIdx 0 ()) := ⟨(), 0⟩
    have hc : c ≠ 0 := by
      rintro rfl
      apply hgP
      rw [eg, C_0, zero_mul]
      exact Ideal.zero_mem _
    have hY : algebraMap (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F)))
        (FractionRing (MRing (ProjIdx 0) F ⧸ (⊥ : Ideal (MRing (ProjIdx 0) F))))
        (Ideal.Quotient.mk _ (X v ^ n)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_bot]
      exact pow_ne_zero _ (X_ne_zero _)
    refine ⟨a / c, ?_⟩
    rw [ef, eg, map_mul, map_mul, map_mul, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      mul_div_mul_right _ _ hY, map_div₀]
  rw [hle, IntermediateField.finrank_bot]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
