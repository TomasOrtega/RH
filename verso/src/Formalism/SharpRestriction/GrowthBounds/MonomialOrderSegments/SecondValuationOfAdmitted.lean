import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

section V2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe j`. Establish `h1 : (k : ℝ) ≤ (j : ℝ)` using `h j rfl`. Establish `h2 : k ≤ j` using `by exact_mod_cast h1`.

Conclude with `h2` after adjusting the coercions.
-/
theorem br_geZ_int (x : WithTop ℤ) (k : ℤ) (h : Formalism.MainNotions.PlaneGramData.geZ x (k : ℝ)) : ((k : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe j =>
    have h1 : (k : ℝ) ≤ (j : ℝ) := h j rfl
    have h2 : k ≤ j := by exact_mod_cast h1
    exact_mod_cast h2

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem br_wt_sub (a b : WithTop ℤ) (n : ℤ) (h : a ≤ b + ((n : ℤ) : WithTop ℤ)) :
    a + ((-n : ℤ) : WithTop ℤ) ≤ b := by
  calc a + ((-n : ℤ) : WithTop ℤ) ≤ (b + ((n : ℤ) : WithTop ℤ)) + ((-n : ℤ) : WithTop ℤ) := by gcongr
    _ = b := by rw [add_assoc, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero, add_zero]

/- English proof (translation)
Use extensionality with `⟨j, b⟩`. Unfold `onLetter Formalism.MainNotions.PlaneGramData.atLetter`. Rewrite using `[Finsupp.coe_finset_sum, Finset.sum_apply]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Rewrite using `[Finsupp.mapDomain_apply (fun a a' h => by simpa using h)]`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `a _ hab`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hab (congrArg Prod.snd h)`. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.mapDomain_notin_range]`. Use `(Finset.sum_eq_zero fun a _ => ?_).symm` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hj (congrArg Prod.fst h).symm`. Introduce and unpack `⟨a, ha⟩`. Conclude with `hj (congrArg Prod.fst ha).symm`.
-/
theorem br_onLetter {L : Type} {r : ℕ} (i : L) (β : Fin r →₀ ℕ) :
    onLetter i β = Formalism.MainNotions.PlaneGramData.atLetter i (fun a => β a) := by
  classical
  ext ⟨j, b⟩
  unfold onLetter Formalism.MainNotions.PlaneGramData.atLetter
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  by_cases hj : j = i
  · subst hj
    rw [Finsupp.mapDomain_apply (fun a a' h => by simpa using h)]
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hab (congrArg Prod.snd h)
    · simp
  · rw [Finsupp.mapDomain_notin_range]
    · refine (Finset.sum_eq_zero fun a _ => ?_).symm
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (congrArg Prod.fst h).symm
    · rintro ⟨a, ha⟩
      exact hj (congrArg Prod.fst ha).symm

/- English proof (translation)
Unfold `absE`. Conclude with `Finsupp.sum_fintype _ _ (fun _ => rfl)`.
-/
theorem br_absE {r : ℕ} (β : Fin r →₀ ℕ) : absE β = ∑ a, β a := by
  unfold absE
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

/- English proof (translation)
Introduce `L _ _ sg r _ S`. Take `⟨ha, hb⟩` from `h`. Take `⟨ha1, ha2⟩` from `ha r L (⟨sg⟩ : Letters L) (↑S : Set L)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i a`.

Rewrite using `[valS_eq]`. Consider the cases of `hs : sg i with`. Consider the case `true`. Use `(ha1 i a).1 hs` as an intermediate fact. Simplify `this)` using `using br_geZ_int _ 0 (by simpa`.

Consider the case `false`. Use `(ha1 i a).2 hs` as an intermediate fact. Simplify `this)` using `using br_geZ_int _ (-1) (by simpa`. Introduce `i β F`. Rewrite using `[valS_eq, valS_eq, ddiv_eq_divDer, br_onLetter]`.

Consider the cases of `hs : sg i with`. Consider the case `true`. Use `(ha2 i (fun a => β a) F).1 hs` as an intermediate fact. Simplify using `only [if_true]`. Rewrite using `[br_absE]`.

Conclude with `br_wt_sub _ _ _ this`. Consider the case `false`. Use `(ha2 i (fun a => β a) F).2 hs` as an intermediate fact. Simplify using `using this`. Introduce `S' hsub hvec F`.

Rewrite using `[valS_eq, valS_eq]`. Establish `e : (↑S' : Set L) = (↑S : Set L) ∪ (↑(S' \ S) : Set L)`. Rewrite using `[← Finset.coe_union, Finset.union_sdiff_of_subset hsub]`. Rewrite using `[e]`. Use `(hb r L (⟨sg⟩ : Letters L) (↑S : Set L)).1 _ ?_ F` and prove the remaining obligations.

Introduce `i hi`. Establish `hi'` using `Finset.mem_sdiff.mp (Finset.mem_coe.mp hi)`. Conclude with `hvec i hi'.1 hi'.2`. Introduce `d S' hsub hvec F hF`. Rewrite using `[valS_eq, valS_eq]`.

Establish `e : (↑S' : Set L) = (↑S : Set L) \ (↑(S \ S') : Set L)`. Rewrite using `[← Finset.coe_sdiff, Finset.sdiff_sdiff_eq_self hsub]`. Rewrite using `[e]`. Use `br_wt_sub _ _ _ ?_` and prove the remaining obligations. Use `(hb r L (⟨sg⟩ : Letters L) (↑S : Set L)).2 (S \ S') d ?_ ?_ F hF` and prove the remaining obligations.

Conclude with `Finset.coe_subset.mpr Finset.sdiff_subset`. Introduce `i hi`. Establish `hi'` using `Finset.mem_sdiff.mp hi`. Conclude with `hvec i hi'.1 hi'.2`.
-/
theorem second_valuation_of_admitted [CharZero (KK O)] (h : Formalism.MainNotions.PlaneGramData.ValuationStabilityAtRing O) : V2 (KK O) := by
  classical
  intro L _ _ sg r _ S
  obtain ⟨ha, hb⟩ := h
  obtain ⟨ha1, ha2⟩ := ha r L (⟨sg⟩ : Letters L) (↑S : Set L)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a
    rw [valS_eq]
    cases hs : sg i with
    | true =>
      have := (ha1 i a).1 hs
      simpa using br_geZ_int _ 0 (by simpa using this)
    | false =>
      have := (ha1 i a).2 hs
      simpa using br_geZ_int _ (-1) (by simpa using this)
  · intro i β F
    rw [valS_eq, valS_eq, ddiv_eq_divDer, br_onLetter]
    cases hs : sg i with
    | true =>
      have := (ha2 i (fun a => β a) F).1 hs
      simp only [if_true]
      rw [br_absE]
      exact br_wt_sub _ _ _ this
    | false =>
      have := (ha2 i (fun a => β a) F).2 hs
      simpa using this
  · intro S' hsub hvec F
    rw [valS_eq, valS_eq]
    have e : (↑S' : Set L) = (↑S : Set L) ∪ (↑(S' \ S) : Set L) := by
      rw [← Finset.coe_union, Finset.union_sdiff_of_subset hsub]
    rw [e]
    refine (hb r L (⟨sg⟩ : Letters L) (↑S : Set L)).1 _ ?_ F
    intro i hi
    have hi' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hi)
    exact hvec i hi'.1 hi'.2
  · intro d S' hsub hvec F hF
    rw [valS_eq, valS_eq]
    have e : (↑S' : Set L) = (↑S : Set L) \ (↑(S \ S') : Set L) := by
      rw [← Finset.coe_sdiff, Finset.sdiff_sdiff_eq_self hsub]
    rw [e]
    refine br_wt_sub _ _ _ ?_
    refine (hb r L (⟨sg⟩ : Letters L) (↑S : Set L)).2 (S \ S') d ?_ ?_ F hF
    · exact Finset.coe_subset.mpr Finset.sdiff_subset
    · intro i hi
      have hi' := Finset.mem_sdiff.mp hi
      exact hvec i hi'.1 hi'.2

end V2

section Fock

variable {K : Type} [Field K]

/- English proof (translation)
Unfold `Formalism.MainNotions.G.fock`. Conclude with `Finset.sum_subset hS (fun m _ hm => by`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at hm`. Rewrite using `[hm]`. Use the proof step `ring)`.
-/
private theorem fock_eq_sum_coeff_mul_expFact_of_support_subset {σ : Type} (F G : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : F.support ⊆ S) : Formalism.MainNotions.G.fock F G = ∑ m ∈ S, F.coeff m * G.coeff m * (expFact m : K) := by
  unfold Formalism.MainNotions.G.fock
  exact Finset.sum_subset hS (fun m _ hm => by
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    rw [hm]
    ring)

/- English proof (translation)
Rewrite using `[fock_eq_sum_coeff_mul_expFact_of_support_subset F G (F.support ∪ G.support) Finset.subset_union_left, fock_eq_sum_coeff_mul_expFact_of_support_subset G F (F.support ∪ G.support) Finset.subset_union_right]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem br_fock_comm {σ : Type} (F G : MvPolynomial σ K) : Formalism.MainNotions.G.fock F G = Formalism.MainNotions.G.fock G F := by
  classical
  rw [fock_eq_sum_coeff_mul_expFact_of_support_subset F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_eq_sum_coeff_mul_expFact_of_support_subset G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Establish `hsub : (F - F').support ⊆ F.support ∪ F'.support` using `MvPolynomial.support_sub σ F F'`. Rewrite using `[fock_eq_sum_coeff_mul_expFact_of_support_subset (F - F') G (F.support ∪ F'.support) hsub, fock_eq_sum_coeff_mul_expFact_of_support_subset F G (F.support ∪ F'.support) Finset.subset_union_left, fock_eq_sum_coeff_mul_expFact_of_support_subset F' G (F.support ∪ F'.support) Finset.s …`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.coeff_sub]; ring`.
-/
theorem br_fock_sub_left {σ : Type} (F F' G : MvPolynomial σ K) :
    Formalism.MainNotions.G.fock (F - F') G = Formalism.MainNotions.G.fock F G - Formalism.MainNotions.G.fock F' G := by
  classical
  have hsub : (F - F').support ⊆ F.support ∪ F'.support := MvPolynomial.support_sub σ F F'
  rw [fock_eq_sum_coeff_mul_expFact_of_support_subset (F - F') G (F.support ∪ F'.support) hsub,
    fock_eq_sum_coeff_mul_expFact_of_support_subset F G (F.support ∪ F'.support) Finset.subset_union_left,
    fock_eq_sum_coeff_mul_expFact_of_support_subset F' G (F.support ∪ F'.support) Finset.subset_union_right, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.coeff_sub]; ring

/- English proof (translation)
Use extensionality with `F`. Use `show ((th : ℤ) : WithTop ℤ) ≤ valS sg S F ↔ ((th : ℤ) : WithTop ℤ) ≤ Formalism.MainNotions.G.valS (⟨sg⟩ : Letters L) (↑S : Set L) F`. Rewrite using `[valS_eq]`.
-/
theorem br_Aset_eq {L : Type} [DecidableEq L] {r : ℕ} [NeZero r] (sg : L → Bool) (S : Finset L) (th : ℤ) :
    (Aset sg S th : Set (MvPolynomial (L × Fin r) K)) = ASet (⟨sg⟩ : Letters L) (↑S : Set L) th := by
  ext F
  show ((th : ℤ) : WithTop ℤ) ≤ valS sg S F ↔ ((th : ℤ) : WithTop ℤ) ≤ Formalism.MainNotions.G.valS (⟨sg⟩ : Letters L) (↑S : Set L) F
  rw [valS_eq]

/- English proof (translation)
Rewrite using `[br_Aset_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun F hF => ⟨(h F hF).1, (h F hF).1, (h F hF).2.1⟩, fun F hF hU => (h F hF).2.2.1 hU.2, ?_⟩` and prove the remaining obligations. Introduce `F hF G hG`.

Establish `h1 : Formalism.MainNotions.G.fock (G - π G) (π F) = 0` using `(h G hG).2.2.2 (π F) (h F hF).1 (h F hF).2.1`. Establish `h2 : Formalism.MainNotions.G.fock (F - π F) (π G) = 0` using `(h F hF).2.2.2 (π G) (h G hG).1 (h G hG).2.1`. Rewrite `h1`, `h2` using `[br_fock_sub_left, sub_eq_zero]`. Rewrite using `[br_fock_comm (π F) G, h1, br_fock_comm (π G) (π F), h2]`. Introduce `h F hF`.

Use `⟨(h.1 F hF).1, (h.1 F hF).2.2, fun hU => h.2.1 F hF ⟨hF, hU⟩, fun G hG hGU => ?_⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.G.fock (F - π F) G = 0`. Rewrite using `[br_fock_sub_left, h.2.2 F hF G hG, h.2.1 G hG ⟨hG, hGU⟩, sub_self]`.
-/
theorem br_proj_iff {L : Type} [DecidableEq L] {r : ℕ} [NeZero r] (sg : L → Bool) (S : Finset L) (d : L → ℕ)
    (th : ℤ) (π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) :
    IsFockProj (K := K) d (Aset sg S th) π ↔
      Formalism.MainNotions.PlaneGramData.IsFockProj d (Formalism.MainNotions.PlaneGramData.AK (K := K) (r := r) (⟨sg⟩ : Letters L) (↑S : Set L) d th) π := by
  rw [br_Aset_eq]
  constructor
  · intro h
    refine ⟨fun F hF => ⟨(h F hF).1, (h F hF).1, (h F hF).2.1⟩, fun F hF hU => (h F hF).2.2.1 hU.2, ?_⟩
    intro F hF G hG
    have h1 : Formalism.MainNotions.G.fock (G - π G) (π F) = 0 := (h G hG).2.2.2 (π F) (h F hF).1 (h F hF).2.1
    have h2 : Formalism.MainNotions.G.fock (F - π F) (π G) = 0 := (h F hF).2.2.2 (π G) (h G hG).1 (h G hG).2.1
    rw [br_fock_sub_left, sub_eq_zero] at h1 h2
    rw [br_fock_comm (π F) G, h1, br_fock_comm (π G) (π F), h2]
  · intro h F hF
    refine ⟨(h.1 F hF).1, (h.1 F hF).2.2, fun hU => h.2.1 F hF ⟨hF, hU⟩, fun G hG hGU => ?_⟩
    show Formalism.MainNotions.G.fock (F - π F) G = 0
    rw [br_fock_sub_left, h.2.2 F hF G hG, h.2.1 G hG ⟨hG, hGU⟩, sub_self]

/- English proof (translation)
Unfold `glAct`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single i]`. Simplify using `[hi]`. Introduce `l _ hl`. Simplify using `[hl]`.

Simplify using the standard rewrite rules.
-/
theorem br_glAct_single {L : Type} [Fintype L] {r : ℕ} (LL : Letters L) (i : L) (hi : LL.vec i = true)
    (a b : Fin r) (F : MvPolynomial (L × Fin r) K) :
    glAct K LL ({i} : Set L) a b F = X (i, a) * pderiv (i, b) F := by
  classical
  unfold glAct
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp [hi]
  · intro l _ hl
    simp [hl]
  · simp

end Fock

section BB

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

/- English proof (translation)
Unfold `vR`. Rewrite using `[AddValuation.map_mul]`. Generalize the expression as in `v x = a`. Generalize the expression as in `v y = b`. Apply the tactic sequence `induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp`.

Use `norm_cast`.
-/
theorem br_vR_mul (x y : K) : vR v (x * y) = vR v x + vR v y := by
  unfold vR
  rw [AddValuation.map_mul]
  generalize v x = a
  generalize v y = b
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp
  norm_cast

/- English proof (translation)
Unfold `vBB`. Rewrite using `[Finset.le_inf_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h α`. Distinguish the cases in `hα : α ∈ F.support`.

Conclude with `h α hα`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hα]`. Simplify using `[vR]`. Introduce `h α _`. Conclude with `h α`.
-/
theorem br_le_vBB_iff {σ : Type} (t : ℝ) (F : MvPolynomial σ K) :
    ((t : ℝ) : WithTop ℝ) ≤ vBB v F ↔ ∀ α, ((t : ℝ) : WithTop ℝ) ≤
      vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ) := by
  unfold vBB
  rw [Finset.le_inf_iff]
  constructor
  · intro h α
    by_cases hα : α ∈ F.support
    · exact h α hα
    · rw [MvPolynomial.notMem_support_iff.1 hα]
      simp [vR]
  · intro h α _
    exact h α

/- English proof (translation)
Rewrite `h`, the goal using `[br_le_vBB_iff]`. Introduce `α`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, br_vR_mul]`. Establish `hvc : vR v c = ((n : ℝ) : WithTop ℝ)`. Unfold `vR`.

Rewrite using `[hc]`. Both sides reduce to the same expression. Rewrite using `[hvc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_comm]`.

Use `norm_cast`. Use `_ ≤ ((n : ℝ) : WithTop ℝ) + (vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ)) := add_le_add le_rfl (h α)`. Use `_ = _ := by rw [add_assoc]`.
-/
theorem br_le_vBB_smul {σ : Type} (c : K) (n : ℚ) (hc : v c = ((n : ℚ) : WithTop ℚ)) (t : ℝ)
    (F : MvPolynomial σ K) (h : ((t : ℝ) : WithTop ℝ) ≤ vBB v F) :
    (((t + n : ℝ)) : WithTop ℝ) ≤ vBB v (c • F) := by
  rw [br_le_vBB_iff] at h ⊢
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, br_vR_mul]
  have hvc : vR v c = ((n : ℝ) : WithTop ℝ) := by
    unfold vR
    rw [hc]
    rfl
  rw [hvc]
  calc (((t + n : ℝ)) : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) + ((t : ℝ) : WithTop ℝ) := by
        rw [add_comm]
        norm_cast
    _ ≤ ((n : ℝ) : WithTop ℝ) + (vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ)) :=
        add_le_add le_rfl (h α)
    _ = _ := by rw [add_assoc]

/- English proof (translation)
Rewrite using `[AddValuation.map_inv, hc]`. Both sides reduce to the same expression.
-/
theorem br_v_inv (c : K) (n : ℚ) (hc : v c = ((n : ℚ) : WithTop ℚ)) : v c⁻¹ = (((-n : ℚ)) : WithTop ℚ) := by
  rw [AddValuation.map_inv, hc]
  rfl

/- English proof (translation)
Use `⟨(p : K) ^ N, ?_⟩` and prove the remaining obligations. Break down `Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩` into its components or cases. Rewrite using `[zpow_natCast, AddValuation.map_pow, hvp]`. Simplify using the standard rewrite rules. Rewrite using `[zpow_neg, zpow_natCast, AddValuation.map_inv, AddValuation.map_pow, hvp]`.

Simplify using the standard rewrite rules.
-/
theorem br_exists_v {p : ℕ} (hvp : v (p : K) = 1) (N : ℤ) : ∃ c : K, v c = (((N : ℤ) : ℚ) : WithTop ℚ) := by
  refine ⟨(p : K) ^ N, ?_⟩
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, AddValuation.map_pow, hvp]
    simp
  · rw [zpow_neg, zpow_natCast, AddValuation.map_inv, AddValuation.map_pow, hvp]
    simp

/- English proof (translation)
Proceed by induction on `y using WithTop.recTopCoe with`. Consider the case `top`. Establish `hz : z = ⊤`. Assume the negation of the conclusion as `hz`. Take `⟨z0, rfl⟩` from `WithTop.ne_top_iff_exists.mp hz`.

Establish `h1` using `h (z0 + e + 1) le_top`. Normalize the coercions in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hz]`. Simplify using the standard rewrite rules.

Consider the case `coe y0`. Establish `h1` using `h y0 le_rfl`. Proceed by induction on `z using WithTop.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe z0`.

Normalize the coercions in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem br_le_add_of_forall (y z : WithTop ℝ) (e : ℝ)
    (h : ∀ t : ℝ, ((t : ℝ) : WithTop ℝ) ≤ y → ((t - e : ℝ) : WithTop ℝ) ≤ z) : y ≤ z + ((e : ℝ) : WithTop ℝ) := by
  induction y using WithTop.recTopCoe with
  | top =>
    have hz : z = ⊤ := by
      by_contra hz
      obtain ⟨z0, rfl⟩ := WithTop.ne_top_iff_exists.mp hz
      have h1 := h (z0 + e + 1) le_top
      norm_cast at h1
      linarith
    rw [hz]
    simp
  | coe y0 =>
    have h1 := h y0 le_rfl
    induction z using WithTop.recTopCoe with
    | top => simp
    | coe z0 =>
      norm_cast at h1 ⊢
      linarith

end BB

section Num

/- English proof (translation)
Unfold `lg`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `ha0 : (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Establish `hpos : (0 : ℝ) < 2 * (a : ℝ) + r` using `by linarith`.

Establish `hlog0 : 0 ≤ Real.logb p (2 * (a : ℝ) + r)` using `Real.logb_nonneg hp1 (by linarith)`. Establish `hmono : Real.logb p (2 * (a : ℝ) + r) ≤ Real.logb p (((2 * b : ℕ) : ℝ) + r)`. Apply `Real.logb_le_logb_of_le hp1 hpos` to reduce the goal to its premises. Use `push_cast`. Establish `: (a : ℝ) ≤ b` using `by exact_mod_cast hab`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hch : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2`. Establish `: r.choose 2 ≤ r ^ 2` using `Nat.choose_le_pow r 2`. Conclude with `this` after adjusting the coercions. Establish `hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2` using `by nlinarith`.

Establish `hprod` using `mul_le_mul hch hmono hlog0 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem br_exp_le {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) (a b : ℕ) (hab : a ≤ b) :
    ((r.choose 2 : ℕ) : ℝ) * Real.logb p (2 * (a : ℝ) + r) + 1 ≤ (r : ℝ) ^ 2 * lg p r (2 * b) := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hpos : (0 : ℝ) < 2 * (a : ℝ) + r := by linarith
  have hlog0 : 0 ≤ Real.logb p (2 * (a : ℝ) + r) := Real.logb_nonneg hp1 (by linarith)
  have hmono : Real.logb p (2 * (a : ℝ) + r) ≤ Real.logb p (((2 * b : ℕ) : ℝ) + r) := by
    apply Real.logb_le_logb_of_le hp1 hpos
    push_cast
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hch : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : r.choose 2 ≤ r ^ 2 := Nat.choose_le_pow r 2
    exact_mod_cast this
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul hch hmono hlog0 (by positivity)
  nlinarith

end Num

section PROJ

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Introduce `hD L _ _ sg r _ d S th`. Establish `hp : p.Prime` using `hD.prime`. Take `⟨⟨π0, hπ0⟩, hall⟩` from `h4 r L (⟨sg⟩ : Letters L) d (↑S : Set L) th`. Use `⟨⟨π0, (br_proj_iff sg S d th π0).mpr hπ0⟩, fun π hπ => ?_⟩` and prove the remaining obligations. Take `⟨hcomm, hBB⟩` from `hall π ((br_proj_iff sg S d th π).mp hπ)`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi hiS a F hF`. Establish `hdis : Disjoint (↑S : Set L) ({i} : Set L)`. Rewrite using `[Set.disjoint_singleton_right]`. Conclude with `fun h => hiS (Finset.mem_coe.mp h)`.

Use `(hcomm {i} (Or.inr hdis)).1 a a F hF` as an intermediate fact. Rewrite `this` using `[br_glAct_single (⟨sg⟩ : Letters L) i hi, br_glAct_single (⟨sg⟩ : Letters L) i hi]`. Conclude with `this`. Introduce `S' hS' th' π' hπ' F hF`. Establish `hS'' : (↑S : Set L) ⊆ (↑S' : Set L) ∨ Disjoint (↑S : Set L) (↑S' : Set L)`.

Break down `hS' with h | h` into its components or cases. Conclude with `Or.inl (Finset.coe_subset.mpr h)`. Conclude with `Or.inr (Finset.disjoint_coe.mpr h)`. Conclude with `(hcomm _ hS'').2 th' π' ((br_proj_iff sg S' d th' π').mp hπ') F hF`. Introduce `F hF`.

Use `br_le_add_of_forall _ _ _ fun t ht => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `br_exists_v (vQ p S0) hD.vp ⌈-t⌉`. Establish `hcF : c • F ∈ Pol (KK O) r d` using `Submodule.smul_mem _ _ hF`. Establish `h1` using `br_le_vBB_smul (vQ p S0) c _ hc t F ht`. Establish `hN1 : -t ≤ (⌈-t⌉ : ℝ)` using `Int.le_ceil _`.

Establish `hN2 : (⌈-t⌉ : ℝ) < -t + 1` using `Int.ceil_lt_add_one _`. Establish `hin : InBB (O` using `O) p (c • F) := by`. Establish `h2 : Formalism.MainNotions.PlaneGramData.geQ (Formalism.MainNotions.G.vBB (O` using `O) p (c • F)) 0 := by`. Rewrite using `[geQ_vBB_iff hp S0]`. Use `le_trans ?_ h1` and prove the remaining obligations.

Rewrite using `[WithTop.coe_le_coe]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `InBB`. Generalize the expression as in `Formalism.MainNotions.G.vBB (O := O) p (c • F) = y at h2`.

Proceed by induction on `y using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe q`. Use `h2 q rfl` as an intermediate fact. Establish `e0 : (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ)` using `rfl`.

Rewrite using `[e0, WithTop.coe_le_coe]`. Conclude with `this` after adjusting the coercions. Establish `h3` using `hBB (c • F) hcF hin`. Rewrite `h3` using `[geQ_vBB_iff hp S0, map_smul]`. Establish `h4'` using `br_le_vBB_smul (vQ p S0) c⁻¹ _ (br_v_inv _ c _ hc) _ _ h3`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[AddValuation.map_zero]`. Conclude with `WithTop.coe_ne_top hc.symm`. Rewrite `h4'` using `[smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Use `le_trans ?_ h4'` and prove the remaining obligations. Rewrite using `[WithTop.coe_le_coe]`. Establish `hdeg : degIn d (↑S : Set L) ≤ ∑ i, d i`. Unfold `degIn`. Use `Finset.sum_le_sum fun l _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `le_rfl`. Conclude with `Nat.zero_le _`. Establish `hnum` using `br_exp_le hp.two_le (NeZero.one_le (n := r)) _ _ hdeg`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem brPROJ (S0 : UniformizedDVR p O) [CharZero (KK O)] (h4 : Formalism.MainNotions.PlaneGramData.FockProjectorAtRing p O) :
    PROJ (KK O) (vQ p S0) p 1 := by
  classical
  intro hD L _ _ sg r _ d S th
  have hp : p.Prime := hD.prime
  obtain ⟨⟨π0, hπ0⟩, hall⟩ := h4 r L (⟨sg⟩ : Letters L) d (↑S : Set L) th
  refine ⟨⟨π0, (br_proj_iff sg S d th π0).mpr hπ0⟩, fun π hπ => ?_⟩
  obtain ⟨hcomm, hBB⟩ := hall π ((br_proj_iff sg S d th π).mp hπ)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hiS a F hF
    have hdis : Disjoint (↑S : Set L) ({i} : Set L) := by
      rw [Set.disjoint_singleton_right]; exact fun h => hiS (Finset.mem_coe.mp h)
    have := (hcomm {i} (Or.inr hdis)).1 a a F hF
    rw [br_glAct_single (⟨sg⟩ : Letters L) i hi, br_glAct_single (⟨sg⟩ : Letters L) i hi] at this
    exact this
  · intro S' hS' th' π' hπ' F hF
    have hS'' : (↑S : Set L) ⊆ (↑S' : Set L) ∨ Disjoint (↑S : Set L) (↑S' : Set L) := by
      rcases hS' with h | h
      · exact Or.inl (Finset.coe_subset.mpr h)
      · exact Or.inr (Finset.disjoint_coe.mpr h)
    exact (hcomm _ hS'').2 th' π' ((br_proj_iff sg S' d th' π').mp hπ') F hF
  · intro F hF
    refine br_le_add_of_forall _ _ _ fun t ht => ?_
    obtain ⟨c, hc⟩ := br_exists_v (vQ p S0) hD.vp ⌈-t⌉
    have hcF : c • F ∈ Pol (KK O) r d := Submodule.smul_mem _ _ hF
    have h1 := br_le_vBB_smul (vQ p S0) c _ hc t F ht
    have hN1 : -t ≤ (⌈-t⌉ : ℝ) := Int.le_ceil _
    have hN2 : (⌈-t⌉ : ℝ) < -t + 1 := Int.ceil_lt_add_one _
    have hin : InBB (O := O) p (c • F) := by
      have h2 : Formalism.MainNotions.PlaneGramData.geQ (Formalism.MainNotions.G.vBB (O := O) p (c • F)) 0 := by
        rw [geQ_vBB_iff hp S0]
        refine le_trans ?_ h1
        rw [WithTop.coe_le_coe]
        push_cast
        linarith
      unfold InBB
      generalize Formalism.MainNotions.G.vBB (O := O) p (c • F) = y at h2
      induction y using WithTop.recTopCoe with
      | top => exact le_top
      | coe q =>
        have := h2 q rfl
        have e0 : (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) := rfl
        rw [e0, WithTop.coe_le_coe]
        exact_mod_cast this
    have h3 := hBB (c • F) hcF hin
    rw [geQ_vBB_iff hp S0, map_smul] at h3
    have h4' := br_le_vBB_smul (vQ p S0) c⁻¹ _ (br_v_inv _ c _ hc) _ _ h3
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [AddValuation.map_zero] at hc
      exact WithTop.coe_ne_top hc.symm
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h4'
    refine le_trans ?_ h4'
    rw [WithTop.coe_le_coe]
    have hdeg : degIn d (↑S : Set L) ≤ ∑ i, d i := by
      unfold degIn
      refine Finset.sum_le_sum fun l _ => ?_
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    have hnum := br_exp_le hp.two_le (NeZero.one_le (n := r)) _ _ hdeg
    push_cast
    linarith

end PROJ

end Formalism.MainNotions.PlaneGram
