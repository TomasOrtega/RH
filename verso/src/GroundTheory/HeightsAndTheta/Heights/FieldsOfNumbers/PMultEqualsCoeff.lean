import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

namespace MultEqualsCoeff

variable {K : Type*}

/- English proof (translation)
The claim follows from `tendsto_atTop_atTop.2 fun a => ⟨a + c, fun _ hm => le_sub_iff_add_le.mpr hm⟩`.
-/
theorem tendsto_sub (c : K → ℤ) : Tendsto (fun m : K → ℤ => m - c) atTop atTop :=
  tendsto_atTop_atTop.2 fun a => ⟨a + c, fun _ hm => le_sub_iff_add_le.mpr hm⟩

/- English proof (translation)
The claim follows from `| [] => rfl | b :: L => by simp only [List.foldr_cons] rw [foldr_diffStep_sum s f L] funext m simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]`.
-/
theorem foldr_diffStep_sum {J : Type*} (s : Finset J) (f : J → (K → ℤ) → ℤ) :
    ∀ L : List (K → ℤ), L.foldr diffStep (∑ j ∈ s, f j) = ∑ j ∈ s, L.foldr diffStep (f j)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_sum s f L]
      funext m
      simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]

/- English proof (translation)
The claim follows from `| [] => rfl | b :: L => by simp only [List.foldr_cons, foldr_diffStep_zero L] funext m simp [diffStep]`.
-/
theorem foldr_diffStep_zero : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons, foldr_diffStep_zero L]
      funext m
      simp [diffStep]

/- English proof (translation)
The claim follows from `| [] => rfl | b :: L => by simp only [List.foldr_cons] rw [foldr_diffStep_shift h c L] funext m simp only [diffStep, sub_right_comm m b c]`.
-/
theorem foldr_diffStep_shift (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_shift h c L]
      funext m
      simp only [diffStep, sub_right_comm m b c]

/- English proof (translation)
The claim follows from `| [] => e | b :: L => by have e' := foldr_diffStep_eventuallyEq e L filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2 simp only [List.foldr_cons, diffStep] rw [h1, h2]`.
-/
theorem foldr_diffStep_eventuallyEq {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  | [] => e
  | b :: L => by
      have e' := foldr_diffStep_eventuallyEq e L
      filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2
      simp only [List.foldr_cons, diffStep]
      rw [h1, h2]

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))`. Consider the case `coe y`. Proceed by induction on `y using WithTop.recTopCoe with`. Consider the case `top => exact absurd h (not_lt.mpr (by simp))`.

Consider the case `coe z`. Establish `hz0 : 0 ≤ z` using `by exact_mod_cast h0`. Take `⟨d, rfl⟩` from `Int.eq_ofNat_of_zero_le hz0`. Establish `hdn : (d : ℤ) < n` using `by exact_mod_cast h`. Conclude with `⟨d, by norm_cast, by omega⟩`.
-/
theorem exists_nat_of_nonneg_of_lt {x : WithBot (WithTop ℤ)} {n : ℕ} (h0 : 0 ≤ x)
    (h : x < n) : ∃ d : ℕ, x = d ∧ d < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h (not_lt.mpr (by simp))
    | coe z =>
      have hz0 : 0 ≤ z := by exact_mod_cast h0
      obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
      have hdn : (d : ℤ) < n := by exact_mod_cast h
      exact ⟨d, by norm_cast, by omega⟩

variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

omit [DecidableEq K] in

/- English proof (translation)
Unfold `relDim`. Generalize the expression as in `ringKrullDim (MRing ι F ⧸ I) = x at h ⊢`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))`. Consider the case `coe y`.

Proceed by induction on `y using ENat.recTopCoe with`. Consider the case `top => exact WithBot.coe_le_coe.mpr le_top`. Consider the case `coe e`. Establish `he : Fintype.card K ≤ e` using `by exact_mod_cast h`. Establish `: (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞)`.

Express the relevant statement in the definitionally equal form `(0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)`. Conclude with `(by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)` after adjusting the coercions. Conclude with `WithBot.coe_le_coe.mpr this`.
-/
theorem relDim_nonneg_of_card_le (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by
  unfold relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe e =>
      have he : Fintype.card K ≤ e := by exact_mod_cast h
      have : (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) := by
        change (0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
        exact_mod_cast (by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)
      exact WithBot.coe_le_coe.mpr this

/- English proof (translation)
Simplify using `only [IsRelevant, not_forall, not_exists, not_not] at hI`. Take `⟨k, hk⟩` from `hI`. Use `filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm`. Unfold `hilbFn`. Use `split_ifs with h0`.

Establish `hbot : gradedPiece I (fun k => (m k).toNat) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨f, hf, rfl⟩`. Rewrite using `[Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]`. Use `Ideal.sum_mem _ fun s hs => ?_` and prove the remaining obligations.

Establish `hw` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by`. Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists, not_and] at hne`. Establish `h1` using `congrFun hw k`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero fun v hv => by`. Simplify using `[blockWeight, Ne.symm (hne v hv)]] at h1`. Use `hm k` as an intermediate fact. Simplify using `only [Pi.one_apply] at this`. Use linear arithmetic over natural numbers and integers.

Establish `hle : Finsupp.single v 1 ≤ s`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)`. Establish `hX : (X v : MRing ι F) ∈ I`. Take `⟨k', i⟩` from `v`.

Substitute `hvk` using the available equality. Conclude with `hk i`. Establish `e : monomial s (coeff s f) = X v * monomial (s - Finsupp.single v 1) (coeff s f)`. Rewrite using `[show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul, one_mul, add_tsub_cancel_of_le hle]`. Rewrite using `[e]`.

Conclude with `I.mul_mem_right _ hX`. Rewrite using `[hbot]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem hilbFn_eventually_zero_of_not_relevant (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by
  simp only [IsRelevant, not_forall, not_exists, not_not] at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  unfold hilbFn
  split_ifs with h0
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]
      refine Ideal.sum_mem _ fun s hs => ?_
      have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)
      obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have h1 := congrFun hw k
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
          Finset.sum_eq_zero fun v hv => by
            simp [blockWeight, Ne.symm (hne v hv)]] at h1
        have := hm k
        simp only [Pi.one_apply] at this
        omega
      have hle : Finsupp.single v 1 ≤ s := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hX : (X v : MRing ι F) ∈ I := by
        obtain ⟨k', i⟩ := v
        subst hvk
        exact hk i
      have e : monomial s (coeff s f) = X v * monomial (s - Finsupp.single v 1) (coeff s f) := by
        rw [show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul,
          one_mul, add_tsub_cancel_of_le hle]
      rw [e]
      exact I.mul_mem_right _ hX
    rw [hbot]
    simp
  · rfl

end MultEqualsCoeff

open MultEqualsCoeff in

/- English proof (translation)
Introduce `F _ K _ _ ι _ I hI hrel n hn bs`. Take `⟨r, Q, c, hQ, hsum, hmult, hcase⟩` from `h1 F K ι I hI`. Set `top : Ideal (MRing ι F) → Prop` to `fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n`. Set `val : Ideal (MRing ι F) → ℤ` to `fun W => if top W then intNum F W bs else 0`. Establish `hpiece : ∀ j, ∀ᶠ m in atTop, mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j)`.

Introduce `j`. Use `(tendsto_sub fun k => (c j k : ℤ)).eventually (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_` and prove the remaining obligations. Take `⟨hpr, hhom, -⟩` from `hQ j`. Distinguish the cases in `hr : IsRelevant (Q j)`. Break down `(hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩` into its components or cases.

Rewrite `hlt` using `[hn]`. Establish `hnt : ¬ top (Q j)` using `fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)`. Simplify using `only [val, if_neg hnt]`. Take `⟨d, hd, hdn⟩` from `exists_nat_of_nonneg_of_lt (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt`. Conclude with `(h2 F K ι (Q j) hhom hr d hd).2 n hdn bs`.

Establish `ht : top (Q j)` using `⟨hmin, hr, heq.trans hn⟩`. Simplify using `only [val, if_pos ht]`. Conclude with `(h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs`. Establish `hnt : ¬ top (Q j)` using `fun ht => hr ht.2.1`. Simplify using `only [val, if_neg hnt]`.

Use `filter_upwards [foldr_diffStep_eventuallyEq (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm`. Unfold `mixedDiff`. Rewrite using `[hm]`. Conclude with `congrFun (foldr_diffStep_zero _) m`. Establish `hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j)`.

Establish `e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop] mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ)))`. Apply `foldr_diffStep_eventuallyEq` to reduce the goal to its premises. Use `filter_upwards [hsum] with m hm`. Rewrite using `[hm, Finset.sum_apply]`. Use `filter_upwards [e1, eventually_all.2 hpiece] with m hm hall`.

Rewrite using `[hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[foldr_diffStep_shift]`. Conclude with `hall j`. Establish `hval : intNum F I bs = ∑ j, val (Q j)`.

Take `⟨m, ha, hb⟩` from `(((h2 F K ι I hI hrel n hn).1 bs).and hI').exists`. Rewrite using `[← ha, hb]`. Establish `hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆ (Finset.univ.image Q : Set (Ideal (MRing ι F)))`. Introduce `W hW`. Assume the negation of the conclusion as `hWQ`.

Apply `hW` to reduce the goal to its premises. Simplify using `only [topCycle]`. Use `split_ifs with h`. Establish `hm` using `hmult W h.1 h.2.1 (h.2.2.trans hn.symm)`. Establish `h0 : (Finset.univ.filter fun j => Q j = W) = ∅`.

Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`. Introduce and unpack `rfl`. Conclude with `hWQ (by simp)`. Rewrite `hm` using `[h0, Finset.card_empty]`.

Rewrite using `[← hm]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q) (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const, nsmul_eq_mul]`. Simplify using `only [topCycle, val, top]`. Use `split_ifs with h`. Rewrite using `[← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem MultEqualsCoeff.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : MixedDiffConst.Statement.{u}) (h3 : RelevantPrimeDimGe.Statement.{u}) :
    MultEqualsCoeff.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs
  classical
  obtain ⟨r, Q, c, hQ, hsum, hmult, hcase⟩ := h1 F K ι I hI
  let top : Ideal (MRing ι F) → Prop := fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n
  let val : Ideal (MRing ι F) → ℤ := fun W => if top W then intNum F W bs else 0
  have hpiece : ∀ j, ∀ᶠ m in atTop,
      mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j) := by
    intro j
    refine (tendsto_sub fun k => (c j k : ℤ)).eventually
      (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_
    obtain ⟨hpr, hhom, -⟩ := hQ j
    by_cases hr : IsRelevant (Q j)
    · rcases (hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩
      · rw [hn] at hlt
        have hnt : ¬ top (Q j) := fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)
        simp only [val, if_neg hnt]
        obtain ⟨d, hd, hdn⟩ := exists_nat_of_nonneg_of_lt
          (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt
        exact (h2 F K ι (Q j) hhom hr d hd).2 n hdn bs
      · have ht : top (Q j) := ⟨hmin, hr, heq.trans hn⟩
        simp only [val, if_pos ht]
        exact (h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs
    · have hnt : ¬ top (Q j) := fun ht => hr ht.2.1
      simp only [val, if_neg hnt]
      filter_upwards [foldr_diffStep_eventuallyEq
        (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm
      unfold mixedDiff
      rw [hm]
      exact congrFun (foldr_diffStep_zero _) m
  have hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j) := by
    have e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop]
        mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ))) := by
      apply foldr_diffStep_eventuallyEq
      filter_upwards [hsum] with m hm
      rw [hm, Finset.sum_apply]
    filter_upwards [e1, eventually_all.2 hpiece] with m hm hall
    rw [hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [foldr_diffStep_shift]
    exact hall j
  have hval : intNum F I bs = ∑ j, val (Q j) := by
    obtain ⟨m, ha, hb⟩ := (((h2 F K ι I hI hrel n hn).1 bs).and hI').exists
    rw [← ha, hb]
  have hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆
      (Finset.univ.image Q : Set (Ideal (MRing ι F))) := by
    intro W hW
    by_contra hWQ
    apply hW
    simp only [topCycle]
    split_ifs with h
    · have hm := hmult W h.1 h.2.1 (h.2.2.trans hn.symm)
      have h0 : (Finset.univ.filter fun j => Q j = W) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hWQ (by simp)
      rw [h0, Finset.card_empty] at hm
      rw [← hm]
      simp
    · simp
  rw [hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q)
      (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  simp only [topCycle, val, top]
  split_ifs with h
  · rw [← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]
    simp
  · simp

end GroundTheory.Heights₂.Heights.FieldNumbers
