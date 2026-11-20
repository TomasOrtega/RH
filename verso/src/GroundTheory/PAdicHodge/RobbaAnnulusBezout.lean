import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
import GroundTheory.PAdicHodge.RobbaDivision
import GroundTheory.PAdicHodge.RobbaPreparation
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Polynomial

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/- English proof (translation)
Establish `h' : ∀ x : R, ∃ p, Ideal.span {x} = Ideal.span {φ p}` using `fun x => by`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by rw [hx, map_zero]⟩`. Take `⟨u, p, hu, rfl⟩` from `h x hx`. Conclude with `⟨p, Ideal.span_singleton_mul_left_unit hu _⟩`.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Take `⟨p, hp⟩` from `h' y`. Rewrite using `[show ({0, y} : Set R) = insert 0 {y} from rfl, Ideal.span_insert_zero]`. Conclude with `⟨p, hp⟩`.

Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Take `⟨p, hp⟩` from `h' x`. Rewrite using `[Set.pair_comm, show ({0, x} : Set R) = insert 0 {x} from rfl, Ideal.span_insert_zero]`. Conclude with `⟨p, hp⟩`.

Take `⟨u, p, hu, rfl⟩` from `h x hx`. Take `⟨v, p', hv, rfl⟩` from `h y hy`. Take `⟨g, hg⟩` from `(IsPrincipalIdealRing.principal (Ideal.span ({p, p'} : Set K[X]))).principal`. Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `e1 : Ideal.span ({u * φ p, v * φ p'} : Set R) = Ideal.map φ (Ideal.span {p, p'})`.

Rewrite using `[Ideal.map_span, Set.image_pair, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_mul_left_unit hu, Ideal.span_singleton_mul_left_unit hv]`. Rewrite using `[e1, hg]`. Express the relevant statement in the definitionally equal form `Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.
-/
theorem exists_span_pair_eq_map {R : Type*} [CommRing R] (φ : K[X] →+* R)
    (h : ∀ x : R, x ≠ 0 → ∃ u p, IsUnit u ∧ x = u * φ p) (x y : R) :
    ∃ d : K[X], Ideal.span ({x, y} : Set R) = Ideal.span {φ d} := by
  have h' : ∀ x : R, ∃ p, Ideal.span {x} = Ideal.span {φ p} := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    · obtain ⟨u, p, hu, rfl⟩ := h x hx
      exact ⟨p, Ideal.span_singleton_mul_left_unit hu _⟩
  by_cases hx : x = 0
  · subst hx
    obtain ⟨p, hp⟩ := h' y
    rw [show ({0, y} : Set R) = insert 0 {y} from rfl, Ideal.span_insert_zero]
    exact ⟨p, hp⟩
  by_cases hy : y = 0
  · subst hy
    obtain ⟨p, hp⟩ := h' x
    rw [Set.pair_comm, show ({0, x} : Set R) = insert 0 {x} from rfl, Ideal.span_insert_zero]
    exact ⟨p, hp⟩
  obtain ⟨u, p, hu, rfl⟩ := h x hx
  obtain ⟨v, p', hv, rfl⟩ := h y hy
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span ({p, p'} : Set K[X]))).principal
  refine ⟨g, ?_⟩
  have e1 : Ideal.span ({u * φ p, v * φ p'} : Set R) = Ideal.map φ (Ideal.span {p, p'}) := by
    rw [Ideal.map_span, Set.image_pair, Ideal.span_insert, Ideal.span_insert,
      Ideal.span_singleton_mul_left_unit hu, Ideal.span_singleton_mul_left_unit hv]
  rw [e1, hg]
  change Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}
  rw [Ideal.map_span, Set.image_singleton]

namespace AnnulusRing

variable {I : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)]

def Tinv : AnnulusRing K I := ⟨Pi.single (-1) 1, fun ρ _ _ => convergesAt_single (-1) 1 ρ⟩

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [coeff_mul, T, Tinv, cmul_single_left, coeff_one, Pi.single_apply, one_mul]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hn, show n - 1 ≠ -1 by omega]`.
-/
theorem T_mul_Tinv : (T : AnnulusRing K I) * Tinv = 1 := by
  ext n
  simp only [coeff_mul, T, Tinv, cmul_single_left, coeff_one, Pi.single_apply, one_mul]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [hn, show n - 1 ≠ -1 by omega]

def unitT : (AnnulusRing K I)ˣ := ⟨T, Tinv, T_mul_Tinv, by rw [mul_comm]; exact T_mul_Tinv⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[pow_succ, coeff_mul, ih, cmul_comm, show (T : AnnulusRing K I).coeff = Pi.single 1 1 from rfl, cmul_single_left]`. Use function extensionality and compare the values at `m`.

Simplify using `only [Pi.single_apply, one_mul]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)`.
-/
theorem coeff_T_pow (n : ℕ) : ((T : AnnulusRing K I) ^ n).coeff = Pi.single (n : ℤ) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, coeff_mul, ih, cmul_comm, show (T : AnnulusRing K I).coeff = Pi.single 1 1 from rfl,
      cmul_single_left]
    funext m
    simp only [Pi.single_apply, one_mul]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)

/- English proof (translation)
Establish `key : ∀ n : ℕ, (((unitT : (AnnulusRing K I)ˣ) ^ (n : ℤ) : (AnnulusRing K I)ˣ) : AnnulusRing K I).coeff = Pi.single (n : ℤ) 1` using `fun n => by`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val]`. Conclude with `coeff_T_pow n`. Establish `keyinv : ∀ n : ℕ, (((unitT⁻¹ : (AnnulusRing K I)ˣ) ^ n : (AnnulusRing K I)ˣ) : AnnulusRing K I).coeff = Pi.single (-(n : ℤ)) 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Units.val_mul, coeff_mul, ih]`. Express the relevant statement in the definitionally equal form `cmul (Pi.single (-(n : ℤ)) 1) (Pi.single (-1) 1) = _`.

Rewrite using `[cmul_single_left]`. Use function extensionality and compare the values at `m`. Simplify using `only [Pi.single_apply, one_mul]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)`. Break down `Int.eq_nat_or_neg L with ⟨n, rfl | rfl⟩` into its components or cases.

Conclude with `key n`. Rewrite using `[zpow_neg, ← inv_zpow, zpow_natCast]`. Conclude with `keyinv n`.
-/
theorem coeff_unitT_zpow (L : ℤ) :
    (((unitT : (AnnulusRing K I)ˣ) ^ L : (AnnulusRing K I)ˣ) : AnnulusRing K I).coeff =
      Pi.single L 1 := by
  have key : ∀ n : ℕ, (((unitT : (AnnulusRing K I)ˣ) ^ (n : ℤ) : (AnnulusRing K I)ˣ) :
      AnnulusRing K I).coeff = Pi.single (n : ℤ) 1 := fun n => by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]; exact coeff_T_pow n
  have keyinv : ∀ n : ℕ, (((unitT⁻¹ : (AnnulusRing K I)ˣ) ^ n : (AnnulusRing K I)ˣ) :
      AnnulusRing K I).coeff = Pi.single (-(n : ℤ)) 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Units.val_mul, coeff_mul, ih]
      change cmul (Pi.single (-(n : ℤ)) 1) (Pi.single (-1) 1) = _
      rw [cmul_single_left]
      funext m
      simp only [Pi.single_apply, one_mul]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)
  rcases Int.eq_nat_or_neg L with ⟨n, rfl | rfl⟩
  · exact key n
  · rw [zpow_neg, ← inv_zpow, zpow_natCast]; exact keyinv n

def _root_.GroundTheory.PAdicHodge.Laurent.polySeq (p : K[X]) : ℤ → K :=
  fun n => if 0 ≤ n then p.coeff n.toNat else 0

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, hp, hq]`. Apply the tactic sequence `funext n; simp only [Pi.add_apply, polySeq, coeff_add]; split_ifs <;> simp`. Consider the case `monomial n c`.

Rewrite using `[aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, coeff_smul, coeff_T_pow]`. Use function extensionality and compare the values at `m`. Simplify using `only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, polySeq, coeff_monomial]`. Distinguish the cases in `hm : m = (n : ℤ)`. Substitute `hm` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `h0 : 0 ≤ m`. Simplify using `[hm, h0, show n ≠ m.toNat by omega]`. Simplify using `[hm, h0]`.
-/
theorem coeff_aeval_alt (p : K[X]) : (aeval (T : AnnulusRing K I) p).coeff = polySeq p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq]
    funext n; simp only [Pi.add_apply, polySeq, coeff_add]; split_ifs <;> simp
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, coeff_smul,
      coeff_T_pow]
    funext m
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, polySeq,
      coeff_monomial]
    by_cases hm : m = (n : ℤ)
    · subst hm; simp
    · by_cases h0 : 0 ≤ m
      · simp [hm, h0, show n ≠ m.toNat by omega]
      · simp [hm, h0]

/- English proof (translation)
Use `⟨∑ i ∈ Finset.range (H - L + 1).toNat, monomial i (P.coeff (L + i)), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[coeff_mul, coeff_unitT_zpow, coeff_aeval_alt, cmul_single_left]`. Simplify using `only [one_mul, polySeq, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]`. Distinguish the cases in `h1 : 0 ≤ n - L`.

Rewrite using `[if_pos h1]`. Distinguish the cases in `h2 : (n - L).toNat < (H - L + 1).toNat`. Rewrite using `[if_pos h2]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h2]; exact hsupp n (Or.inr (by omega))`. Rewrite using `[if_neg h1]; exact hsupp n (Or.inl (by omega))`.
-/
theorem eq_zpow_mul_aeval (P : AnnulusRing K I) {L H : ℤ}
    (hsupp : ∀ n, (n < L ∨ H < n) → P.coeff n = 0) :
    ∃ p : K[X], P = ((unitT ^ L : (AnnulusRing K I)ˣ) : AnnulusRing K I) * aeval T p := by
  refine ⟨∑ i ∈ Finset.range (H - L + 1).toNat, monomial i (P.coeff (L + i)), ?_⟩
  ext n
  rw [coeff_mul, coeff_unitT_zpow, coeff_aeval_alt, cmul_single_left]
  simp only [one_mul, polySeq, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
  by_cases h1 : 0 ≤ n - L
  · rw [if_pos h1]
    by_cases h2 : (n - L).toNat < (H - L + 1).toNat
    · rw [if_pos h2]; congr 1; omega
    · rw [if_neg h2]; exact hsupp n (Or.inr (by omega))
  · rw [if_neg h1]; exact hsupp n (Or.inl (by omega))

section Closed

variable {α β : ℝ} [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)]

/- English proof (translation)
Take `⟨ρ₀, hρ₀, -⟩` from `(Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)`. Establish `hαβ : α ≤ β` using `hρ₀.1.trans hρ₀.2`. Establish `hβ : 0 < β` using `hα.trans_le hαβ`. Establish `hf0 : f.coeff ≠ 0` using `fun e => hf (AnnulusRing.ext e)`. Take `⟨P, u, hPs, hu1, hu2, hb1, hb2, hfe⟩` from `weierstrass_preparation hα hαβ (f.convergesAt ⟨le_rfl, hαβ⟩ hα) (f.convergesAt ⟨hαβ, le_rfl⟩ hβ) hf0`.

Set `Pe : AnnulusRing K (Set.Icc α β)` to `⟨P, fun ρ _ _ => convergesAt_of_support hPs ρ⟩`. Set `Ue : AnnulusRing K (Set.Icc α β)` to `⟨u, fun ρ hρ _ => hu1.of_le_of_le hu2 hα hρ.1 hρ.2⟩`. Establish `hfPU : f = Pe * Ue` using `AnnulusRing.ext hfe`. Take `⟨hUne, hUl, -⟩` from `dominant_zero_of_gaussNorm_sub_one_lt hα hu1 hb1`. Take `⟨-, -, hUh⟩` from `dominant_zero_of_gaussNorm_sub_one_lt hβ hu2 hb2`.

Establish `hU : IsUnit Ue` using `isUnit_of_lowIndex_eq_highIndex hα Ue (fun e => hUne (congrArg AnnulusRing.coeff e)) (hUl.trans hUh.symm)`. Take `⟨p, hp⟩` from `eq_zpow_mul_aeval Pe hPs`. Use `⟨((unitT ^ lowIndex f.coeff α : (AnnulusRing K (Set.Icc α β))ˣ) : AnnulusRing K (Set.Icc α β)) * Ue, p, (Units.isUnit _).mul hU, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hfPU, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isUnit_mul_aeval (hα : 0 < α) (f : AnnulusRing K (Set.Icc α β)) (hf : f ≠ 0) :
    ∃ u : AnnulusRing K (Set.Icc α β), ∃ p : K[X], IsUnit u ∧ f = u * aeval T p := by
  obtain ⟨ρ₀, hρ₀, -⟩ := (Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)
  have hαβ : α ≤ β := hρ₀.1.trans hρ₀.2
  have hβ : 0 < β := hα.trans_le hαβ
  have hf0 : f.coeff ≠ 0 := fun e => hf (AnnulusRing.ext e)
  obtain ⟨P, u, hPs, hu1, hu2, hb1, hb2, hfe⟩ := weierstrass_preparation hα hαβ
    (f.convergesAt ⟨le_rfl, hαβ⟩ hα) (f.convergesAt ⟨hαβ, le_rfl⟩ hβ) hf0
  let Pe : AnnulusRing K (Set.Icc α β) := ⟨P, fun ρ _ _ => convergesAt_of_support hPs ρ⟩
  let Ue : AnnulusRing K (Set.Icc α β) := ⟨u, fun ρ hρ _ => hu1.of_le_of_le hu2 hα hρ.1 hρ.2⟩
  have hfPU : f = Pe * Ue := AnnulusRing.ext hfe
  obtain ⟨hUne, hUl, -⟩ := dominant_zero_of_gaussNorm_sub_one_lt hα hu1 hb1
  obtain ⟨-, -, hUh⟩ := dominant_zero_of_gaussNorm_sub_one_lt hβ hu2 hb2
  have hU : IsUnit Ue := isUnit_of_lowIndex_eq_highIndex hα Ue
    (fun e => hUne (congrArg AnnulusRing.coeff e)) (hUl.trans hUh.symm)
  obtain ⟨p, hp⟩ := eq_zpow_mul_aeval Pe hPs
  refine ⟨((unitT ^ lowIndex f.coeff α : (AnnulusRing K (Set.Icc α β))ˣ) :
    AnnulusRing K (Set.Icc α β)) * Ue, p, (Units.isUnit _).mul hU, ?_⟩
  conv_lhs => rw [hfPU, hp]
  ring

/- English proof (translation)
The claim follows from `exists_span_pair_eq_map (aeval (T : AnnulusRing K (Set.Icc α β))).toRingHom (fun x hx => exists_isUnit_mul_aeval hα x hx) f g`.
-/
theorem exists_span_eq_aeval (hα : 0 < α) (f g : AnnulusRing K (Set.Icc α β)) :
    ∃ d : K[X], Ideal.span ({f, g} : Set (AnnulusRing K (Set.Icc α β))) =
      Ideal.span {aeval (T : AnnulusRing K (Set.Icc α β)) d} :=
  exists_span_pair_eq_map (aeval (T : AnnulusRing K (Set.Icc α β))).toRingHom
    (fun x hx => exists_isUnit_mul_aeval hα x hx) f g

end Closed

end AnnulusRing

end GroundTheory.PAdicHodge
