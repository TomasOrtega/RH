import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImageDoubleCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImagePrincipalPosLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ContractVolume

open ValuativeRel Matrix MeasureTheory GroundTheory.Automorphic.GLnLocal

/- English proof (translation)
Use `set T : ℤ := ∑ a, ∑ b, if a ≤ j ∧ b ≤ j then (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0 with hT`. Establish `hT0 : T = 0`. Establish `h1 : T = -T` using `by conv_lhs => rw [hT, Finset.sum_comm]`. Rewrite using `[hT, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : a ≤ j ∧ b ≤ j`. Rewrite using `[if_pos hab, if_pos hab.symm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hab, if_neg (fun h => hab h.symm)]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ a : Fin h, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) = (∑ b, if a ≤ j ∧ b ≤ j then (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0) + (if a ≤ j then (d a : ℤ) else 0) * ∑ b, if j < b then (d b : ℤ) else 0`. Introduce `a`.

Distinguish the cases in `ha : a ≤ j`. Simplify using `only [ha, if_true, true_and]`. Rewrite using `[modExp, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Fintype.card_fin]`.

Distinguish the cases in `hb : b ≤ j`. Establish `hb' : ¬ j < b` using `not_lt.2 hb`. Simplify using `only [hb, hb', if_true, if_false]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hb' : j < b` using `not_le.1 hb`.

Establish `h3 : a < b` using `lt_of_le_of_lt ha hb'`. Simplify using `[hb, hb', h3, h3.le, not_lt.2 h3.le]`. Simplify using `[ha]`. Rewrite using `[Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_add_distrib, ← hT, hT0, zero_add, Finset.sum_mul]`.
-/
theorem sum_modExp {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    (∑ a, if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a, if a ≤ j then (d a : ℤ) else 0) * ∑ b, if j < b then (d b : ℤ) else 0 := by
  classical
  set T : ℤ := ∑ a, ∑ b, if a ≤ j ∧ b ≤ j then
    (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0 with hT
  have hT0 : T = 0 := by
    have h1 : T = -T := by
      conv_lhs => rw [hT, Finset.sum_comm]
      rw [hT, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a ≤ j ∧ b ≤ j
      · rw [if_pos hab, if_pos hab.symm]; ring
      · rw [if_neg hab, if_neg (fun h => hab h.symm)]; simp
    omega
  have h2 : ∀ a : Fin h, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ b, if a ≤ j ∧ b ≤ j then
        (d a : ℤ) * (d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0)) else 0) +
      (if a ≤ j then (d a : ℤ) else 0) * ∑ b, if j < b then (d b : ℤ) else 0 := by
    intro a
    by_cases ha : a ≤ j
    · simp only [ha, if_true, true_and]
      rw [modExp, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fintype.card_fin]
      by_cases hb : b ≤ j
      · have hb' : ¬ j < b := not_lt.2 hb
        simp only [hb, hb', if_true, if_false]
        split_ifs <;> ring
      · have hb' : j < b := not_le.1 hb
        have h3 : a < b := lt_of_le_of_lt ha hb'
        simp [hb, hb', h3, h3.le, not_lt.2 h3.le]
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_add_distrib, ← hT, hT0, zero_add,
    Finset.sum_mul]

/- English proof (translation)
Establish `hmono` using `GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd`. Establish `h1 : ∀ i l : Fin N, (if i < l then ((if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0) - (if Zl.JC.blockIdx d hd l ≤ j then (n : ℤ) else 0)).toNat else 0) = n * ((if Zl.JC.blockIdx d hd i ≤ j then 1 else 0) * (if j < Zl.JC.blockIdx d hd l then 1 else 0))`. Introduce `i l`. Distinguish the cases in `hi : Zl.JC.blockIdx d hd i ≤ j`. Distinguish the cases in `hl : j < Zl.JC.blockIdx d hd l`.

Establish `hil : i < l`. Assume the negation of the conclusion as `hc`. Conclude with `absurd (hmono (not_lt.1 hc)) (not_le.2 (lt_of_le_of_lt hi hl))`. Simplify using `[hi, hl, hil, not_le.2 hl]`. Establish `hl'` using `not_lt.1 hl`.

Simplify using `[hi, hl, hl']`. Distinguish the cases in `hl : j < Zl.JC.blockIdx d hd l`. Simplify using `[hi, not_le.2 hl]`. Establish `hl'` using `not_lt.1 hl`. Simplify using `only [hi, hl', if_true, if_false, hl]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2 : ∀ P : Fin h → Prop, [DecidablePred P] → (∑ i : Fin N, if P (Zl.JC.blockIdx d hd i) then 1 else 0) = ∑ a, if P a then d a else 0`. Introduce `P _`. Rewrite using `[← Equiv.sum_comp (stdBlocks d hd), Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `[Zl.JC.blockIdx]`. Simplify using `only [h1]`. Rewrite using `[← h2, ← h2, Finset.sum_mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
theorem sum_toNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (j : Fin h) (n : ℕ) :
    (∑ i : Fin N, ∑ l : Fin N, if i < l then
      ((if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0) -
        (if Zl.JC.blockIdx d hd l ≤ j then (n : ℤ) else 0)).toNat else 0) =
      n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0) := by
  classical
  have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd
  have h1 : ∀ i l : Fin N, (if i < l then
      ((if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0) -
        (if Zl.JC.blockIdx d hd l ≤ j then (n : ℤ) else 0)).toNat else 0) =
      n * ((if Zl.JC.blockIdx d hd i ≤ j then 1 else 0) *
        (if j < Zl.JC.blockIdx d hd l then 1 else 0)) := by
    intro i l
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · by_cases hl : j < Zl.JC.blockIdx d hd l
      · have hil : i < l := by
          by_contra hc
          exact absurd (hmono (not_lt.1 hc)) (not_le.2 (lt_of_le_of_lt hi hl))
        simp [hi, hl, hil, not_le.2 hl]
      · have hl' := not_lt.1 hl
        simp [hi, hl, hl']
    · by_cases hl : j < Zl.JC.blockIdx d hd l
      · simp [hi, not_le.2 hl]
      · have hl' := not_lt.1 hl
        simp only [hi, hl', if_true, if_false, hl]
        split_ifs <;> simp
  have h2 : ∀ P : Fin h → Prop, [DecidablePred P] → (∑ i : Fin N, if P (Zl.JC.blockIdx d hd i) then 1 else 0) =
      ∑ a, if P a then d a else 0 := by
    intro P _
    rw [← Equiv.sum_comp (stdBlocks d hd), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Zl.JC.blockIdx]
  simp only [h1]
  rw [← h2, ← h2, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/- English proof (translation)
Establish `hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0` using `(Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)`. Establish `hlt : valuation k (((uniformizer k : 𝒪[k]) : k) ^ m) < 1`. Rewrite using `[map_pow]`. Conclude with `pow_lt_one' (valuation_uniformizer_lt_one k) (by omega)`. Take `⟨H, hH⟩` from `GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N _ (pow_ne_zero m hϖ0) hlt`.

Establish `hint : ∀ g ∈ H, ∀ i j, (g : GL (Fin N) k) i j ∈ 𝒪[k]`. Introduce `g hg i j`. Establish `h1 : g ∈ (H : Set (GL (Fin N) k))` using `hg`. Rewrite `h1` using `[hH]`. Establish `h2` using `h1 i j`.

Establish `h3 : valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1`. Establish `h4 : (g : Matrix (Fin N) (Fin N) k) i j = ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) + (1 : Matrix (Fin N) (Fin N) k) i j` using `by ring`. Rewrite using `[h4]`. Use `(Valuation.map_add _ _ _).trans (max_le (h2.trans hlt.le) ?_)` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Conclude with `(Valuation.mem_integer_iff _ _).2 h3`. Use extensionality with `g`. Rewrite using `[SetLike.mem_coe, mem_congruenceSubgroup_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h2⟩ i j`. Rewrite using `[map_pow]`. Conclude with `h2 i j`. Introduce `hg`. Establish `hgH : g ∈ H`.

Rewrite using `[← SetLike.mem_coe, hH]`. Conclude with `hg`. Use `⟨(mem_integralGL_iff k N).2 ⟨hint g hgH, hint _ (H.inv_mem hgH)⟩, fun i j => ?_⟩` and prove the remaining obligations. Use `hg i j` as an intermediate fact. Rewrite `this` using `[map_pow]`. Then use the resulting hypothesis.
-/
theorem coe_congruenceSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) (hm : 1 ≤ m) :
    (congruenceSubgroup k N m : Set (GL (Fin N) k)) =
      {g : GL (Fin N) k | ∀ i j, valuation k
        ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
          valuation k (((uniformizer k : 𝒪[k]) : k) ^ m)} := by
  have hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0 :=
    (Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)
  have hlt : valuation k (((uniformizer k : 𝒪[k]) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' (valuation_uniformizer_lt_one k) (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N _ (pow_ne_zero m hϖ0) hlt
  have hint : ∀ g ∈ H, ∀ i j, (g : GL (Fin N) k) i j ∈ 𝒪[k] := by
    intro g hg i j
    have h1 : g ∈ (H : Set (GL (Fin N) k)) := hg
    rw [hH] at h1
    have h2 := h1 i j
    have h3 : valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
      have h4 : (g : Matrix (Fin N) (Fin N) k) i j =
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) +
            (1 : Matrix (Fin N) (Fin N) k) i j := by ring
      rw [h4]
      refine (Valuation.map_add _ _ _).trans (max_le (h2.trans hlt.le) ?_)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    exact (Valuation.mem_integer_iff _ _).2 h3
  ext g
  rw [SetLike.mem_coe, mem_congruenceSubgroup_iff]
  constructor
  · rintro ⟨-, h2⟩ i j
    rw [map_pow]
    exact h2 i j
  · intro hg
    have hgH : g ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hg
    refine ⟨(mem_integralGL_iff k N).2 ⟨hint g hgH, hint _ (H.inv_mem hgH)⟩, fun i j => ?_⟩
    have := hg i j
    rwa [map_pow] at this

/- English proof (translation)
Establish `hxi : x ∈ 𝒪[k]` using `(Valuation.mem_integer_iff _ _).2 hx.le`. Establish `h1 : (⟨x, hxi⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Conclude with `hx`. Rewrite `h1` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_uniformizer k), Ideal.mem_span_singleton]`.

Conclude with `(Valuation.integer.integers (valuation k)).le_of_dvd h1`.
-/
theorem le_valuation_uniformizer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((uniformizer k : 𝒪[k]) : k) := by
  have hxi : x ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hx.le
  have h1 : (⟨x, hxi⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_uniformizer k),
    Ideal.mem_span_singleton] at h1
  exact (Valuation.integer.integers (valuation k)).le_of_dvd h1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_diagT]`. Use extensionality with `i l`. Take `⟨⟨a, x⟩, rfl⟩` from `(stdBlocks d hd).surjective i`. Take `⟨⟨b, y⟩, rfl⟩` from `(stdBlocks d hd).surjective l`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[leviEmb_apply_same]`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality.

Apply the tactic sequence `by_cases ha : a ≤ j <;> simp [Zl.JC.zj, Zl.JC.blockIdx, ha, Matrix.GeneralLinearGroup.scalar]`. Establish `hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩` using `fun e => hxy (by`. Use `(stdBlocks d hd).injective e` as an intermediate fact. Simplify using `using this)`. Rewrite using `[Matrix.diagonal_apply_ne _ hne]`.

Apply the tactic sequence `by_cases ha : a ≤ j <;> simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, hxy]`. Establish `hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩` using `fun e => hab (by`. Use `(stdBlocks d hd).injective e` as an intermediate fact. Conclude with `congrArg Sigma.fst this)`. Rewrite using `[Matrix.diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]`.
-/
theorem leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) =
      diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1) := by
  apply Units.ext
  rw [val_diagT]
  ext i l
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hxy : x = y
    · subst hxy
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, Zl.JC.blockIdx, ha, Matrix.GeneralLinearGroup.scalar]
    · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by
        have := (stdBlocks d hd).injective e
        simpa using this)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, hxy]
  · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e => hab (by
      have := (stdBlocks d hd).injective e
      exact congrArg Sigma.fst this)
    rw [Matrix.diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

/- English proof (translation)
Simplify using `[nabs]`.
-/
theorem nabs_pow' (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  simp [nabs]

/- English proof (translation)
Establish `hpos : nabs k t ≠ 0` using `(nabs_pos k t).ne'`. Establish `h1 : ∀ a : Fin h, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) ^ modExp (fun a => Fin (d a)) a = nabs k t ^ (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0)`. Introduce `a`. Distinguish the cases in `ha : a ≤ j`. Establish `h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a`.

Use `ext`. Simplify using `[Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[h2, nabs_pow', if_pos ha, _root_.zpow_mul, zpow_natCast]`. Establish `h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = 1`. Simplify using `[Zl.JC.zj, ha]`.

Rewrite using `[h2, if_neg ha]`. Simplify using `[nabs]`. Rewrite using `[modulus, Finset.prod_congr rfl fun a _ => h1 a]`. Proceed by induction on `(Finset.univ : Finset (Fin h)) using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hpos, ih]`.
-/
theorem modulus_zj {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) :
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ (∑ a, if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) := by
  have hpos : nabs k t ≠ 0 := (nabs_pos k t).ne'
  have h1 : ∀ a : Fin h, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) ^
        modExp (fun a => Fin (d a)) a =
      nabs k t ^ (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) := by
    intro a
    by_cases ha : a ≤ j
    · have h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.val_det_apply]
      rw [h2, nabs_pow', if_pos ha, _root_.zpow_mul, zpow_natCast]
    · have h2 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = 1 := by
        simp [Zl.JC.zj, ha]
      rw [h2, if_neg ha]
      simp [nabs]
  rw [modulus, Finset.prod_congr rfl fun a _ => h1 a]
  induction (Finset.univ : Finset (Fin h)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hpos, ih]

/- English proof (translation)
Establish `hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0` using `(Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)`. Establish `hti : (t : k) ∈ 𝒪[k]` using `(Valuation.mem_integer_iff _ _).2 ht.le`. Establish `ht0 : (⟨t, hti⟩ : 𝒪[k]) ≠ 0` using `fun e => t.ne_zero (congrArg Subtype.val e)`. Take `⟨n, e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ht0 (irreducible_uniformizer k)`. Establish `hu0 : (((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) ≠ 0` using `fun h0 => (e⁻¹).ne_zero (Subtype.ext h0)`.

Use `⟨n, Units.mk0 _ hϖ0, Units.mk0 _ hu0, rfl, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 (e⁻¹).isUnit`. Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (⟨t, hti⟩ : 𝒪[k]) = GroundTheory.Automorphic.GLnLocal.uniformizer k ^ n * ((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k])`. Rewrite using `[← he, mul_assoc, Units.mul_inv, mul_one]`.

Establish `h2` using `congrArg Subtype.val h1`. Simplify using `using h2`.
-/
theorem exists_decomp (t : kˣ) (ht : valuation k (t : k) < 1) :
    ∃ (n : ℕ) (p u : kˣ), (p : k) = ((uniformizer k : 𝒪[k]) : k) ∧ valuation k (u : k) = 1 ∧
      t = p ^ n * u := by
  have hϖ0 : ((uniformizer k : 𝒪[k]) : k) ≠ 0 :=
    (Valuation.ne_zero_iff _).1 (valuation_uniformizer_ne_zero k)
  have hti : (t : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have ht0 : (⟨t, hti⟩ : 𝒪[k]) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht0 (irreducible_uniformizer k)
  have hu0 : (((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) ≠ 0 := fun h0 =>
    (e⁻¹).ne_zero (Subtype.ext h0)
  refine ⟨n, Units.mk0 _ hϖ0, Units.mk0 _ hu0, rfl, ?_, ?_⟩
  · exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 (e⁻¹).isUnit
  · apply Units.ext
    have h1 : (⟨t, hti⟩ : 𝒪[k]) = GroundTheory.Automorphic.GLnLocal.uniformizer k ^ n * ((e⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) := by
      rw [← he, mul_assoc, Units.mul_inv, mul_one]
    have h2 := congrArg Subtype.val h1
    simpa using h2

/- English proof (translation)
Establish `hent : ∀ g : Fin N → kˣ, (∀ i, valuation k (g i : k) = 1) → ∀ i j, (diagT k (Fin N) g : GL (Fin N) k) i j ∈ 𝒪[k]`. Introduce `g hg i j`. Use `show (diagT k (Fin N) g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]`. Rewrite using `[val_diagT, Matrix.diagonal_apply]`. Use `split_ifs`.

Conclude with `(Valuation.mem_integer_iff _ _).2 (hg i).le`. Conclude with `zero_mem _`. Rewrite using `[mem_integralGL_iff]`. Use `⟨hent f hf, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Use `hent _ fun i => ?_` and prove the remaining obligations. Simplify using `[hf i]`.
-/
theorem diagT_mem_integralGL {N : ℕ} (f : Fin N → kˣ) (hf : ∀ i, valuation k (f i : k) = 1) :
    diagT k (Fin N) f ∈ integralGL k N := by
  have hent : ∀ g : Fin N → kˣ, (∀ i, valuation k (g i : k) = 1) → ∀ i j,
      (diagT k (Fin N) g : GL (Fin N) k) i j ∈ 𝒪[k] := by
    intro g hg i j
    show (diagT k (Fin N) g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]
    rw [val_diagT, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (hg i).le
    · exact zero_mem _
  rw [mem_integralGL_iff]
  refine ⟨hent f hf, ?_⟩
  rw [← map_inv]
  refine hent _ fun i => ?_
  simp [hf i]

/- English proof (translation)
Establish `hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * s * y} ⊆ (fun q => (QuotientGroup.mk w : AdGL k N) * q) ⁻¹' ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * (s * w) * y})`. Introduce and unpack `_ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Use `⟨_, ⟨w * x * w⁻¹, hw x hx, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show (QuotientGroup.mk _ : AdGL k N) = QuotientGroup.mk (w * (x * s * y))`. Use `congr 1`.

Rewrite using `[hc.eq]`. Use `group`. Conclude with `(measure_mono hsub).trans_eq (measure_preimage_mul μ _ _)`.
-/
theorem measure_le_translate {N : ℕ} [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)]
    (μ : Measure (AdGL k N)) [μ.IsMulLeftInvariant] (K : Subgroup (GL (Fin N) k))
    (s w : GL (Fin N) k) (hc : Commute s w) (hw : ∀ x ∈ K, w * x * w⁻¹ ∈ K) :
    μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * s * y}) ≤
      μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
        {g | ∃ x ∈ K, ∃ y ∈ K, g = x * (s * w) * y}) := by
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ K, ∃ y ∈ K, g = x * s * y} ⊆
      (fun q => (QuotientGroup.mk w : AdGL k N) * q) ⁻¹'
        ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g | ∃ x ∈ K, ∃ y ∈ K, g = x * (s * w) * y}) := by
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    refine ⟨_, ⟨w * x * w⁻¹, hw x hx, y, hy, rfl⟩, ?_⟩
    show (QuotientGroup.mk _ : AdGL k N) = QuotientGroup.mk (w * (x * s * y))
    congr 1
    rw [hc.eq]
    group
  exact (measure_mono hsub).trans_eq (measure_preimage_mul μ _ _)

/- English proof (translation)
Introduce `k _ _ _ _ h N d hd _ t ht j _ m hm _ _ μ hμ`. Use `haveI := hμ`. Take `⟨n, p, u, hp, hu, htu⟩` from `exists_decomp t ht`. Establish `hK` using `coe_congruenceSubgroup k N m hm`. Rewrite `hK` using `[← hp]`.

Establish `hϖ1 : valuation k (p : k) < 1` using `hp ▸ valuation_uniformizer_lt_one k`. Establish `hunif : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k)` using `fun x hx => hp ▸ le_valuation_uniformizer k x hx`. Take `⟨hpos, hfin⟩` from `GlobalTheory.CompanionTheory.PrincipalCongruence.measure_image_principal_pos_lt_top k N (p : k) m p.ne_zero hϖ1 hunif hm μ hμ`. Rewrite `hpos`, `hfin` using `[← hK]`. Set `a : Fin N → ℤ` to `fun i => if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0`.

Establish `ha : Antitone a`. Introduce `x y hxy`. Establish `hmono` using `GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd hxy`. Use `show (if _ then _ else _) ≤ (if _ then _ else _)`. Distinguish the cases in `hy : Zl.JC.blockIdx d hd y ≤ j`.

Simplify using `[hy, hmono.trans hy]`. Apply the tactic sequence `rw [if_neg hy] split_ifs <;> simp`. Set `D : GL (Fin N) k` to `diagT k (Fin N) (fun i => p ^ a i)`. Establish `hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (p : k) ^ a i)`. Simplify using `[D, val_diagT]`.

Set `w : GL (Fin N) k` to `diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then u else 1)`. Establish `hw : w ∈ integralGL k N`. Use `diagT_mem_integralGL _ fun i => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hu`.

Simplify using the standard rewrite rules. Establish `hfac : leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = D * w`. Rewrite using `[leviEmb_zj, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : Zl.JC.blockIdx d hd i ≤ j`. Simplify using `[a, hi, htu]`. Simplify using `[a, hi]`. Establish `hcomm : Commute D w` using `by show D * w = w * D`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Establish `hmod : (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ = (resCard k : ℝ) ^ (n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0))`. Establish `h1 : nabs k t = ((resCard k : ℝ)⁻¹) ^ n`. Establish `h2` using `nabs_uniformiser (irreducible_uniformizer k) hp`. Establish `h3` using `nabs_eq_one_of_valuation_eq_one hu`. Rewrite using `[htu, show nabs k (p ^ n * u) = nabs k (p ^ n) * nabs k u from nabs_mul k _ _, nabs_pow', h2, h3, mul_one]`.

Establish `h4 : (∑ a, if a ≤ j then (d a : ℤ) else 0) * (∑ b, if j < b then (d b : ℤ) else 0) = (((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0 : ℕ) : ℤ)`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[modulus_zj, sum_modExp, h4, h1, zpow_natCast, ← pow_mul, inv_pow, inv_inv]`. Use `⟨(μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m : Set (GL (Fin N) k)))).toReal, ENNReal.toReal_pos hpos.ne' hfin.ne, fun r => ?_⟩` and prove the remaining obligations.

Establish `hvol` using `GlobalTheory.CompanionTheory.DoubleCosetVolume.measure_image_doubleCoset k N (p : k) m a p.ne_zero hϖ1 hunif hm ha D hD μ hμ r`. Rewrite `hvol` using `[← hK, sum_toNat d hd j n]`. Establish `hle` using `measure_le_translate μ (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (D ^ r) (w ^ r) (hcomm.pow_pow r r) (fun x hx => conj_mem_congruenceSubgroup k N ((integralGL k N).pow_mem hw r) hx)`. Rewrite using `[hfac, hcomm.mul_pow, hmod]`. Use `le_trans (le_of_eq ?_) hle` and prove the remaining obligations.

Simplify using `only [SetLike.mem_coe] at hvol`. Rewrite using `[hvol, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm, ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_comm _ r]`. Both sides reduce to the same expression.
-/
theorem volume_lower_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, ENNReal.ofReal (c * ((modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹) ^ r) ≤ μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd _ t ht j _ m hm _ _ μ hμ
  haveI := hμ
  obtain ⟨n, p, u, hp, hu, htu⟩ := exists_decomp t ht
  have hK := coe_congruenceSubgroup k N m hm
  rw [← hp] at hK
  have hϖ1 : valuation k (p : k) < 1 := hp ▸ valuation_uniformizer_lt_one k
  have hunif : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := fun x hx =>
    hp ▸ le_valuation_uniformizer k x hx
  obtain ⟨hpos, hfin⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.measure_image_principal_pos_lt_top k N (p : k) m
    p.ne_zero hϖ1 hunif hm μ hμ
  rw [← hK] at hpos hfin
  let a : Fin N → ℤ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0
  have ha : Antitone a := by
    intro x y hxy
    have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd hxy
    show (if _ then _ else _) ≤ (if _ then _ else _)
    by_cases hy : Zl.JC.blockIdx d hd y ≤ j
    · simp [hy, hmono.trans hy]
    · rw [if_neg hy]
      split_ifs <;> simp
  let D : GL (Fin N) k := diagT k (Fin N) (fun i => p ^ a i)
  have hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (p : k) ^ a i) := by
    simp [D, val_diagT]
  let w : GL (Fin N) k := diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then u else 1)
  have hw : w ∈ integralGL k N := by
    refine diagT_mem_integralGL _ fun i => ?_
    split_ifs
    · exact hu
    · simp
  have hfac : leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = D * w := by
    rw [leviEmb_zj, ← map_mul]
    congr 1
    funext i
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · simp [a, hi, htu]
    · simp [a, hi]
  have hcomm : Commute D w := by
    show D * w = w * D
    rw [← map_mul, ← map_mul, mul_comm]
  have hmod : (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ =
      (resCard k : ℝ) ^ (n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0)) := by
    have h1 : nabs k t = ((resCard k : ℝ)⁻¹) ^ n := by
      have h2 := nabs_uniformiser (irreducible_uniformizer k) hp
      have h3 := nabs_eq_one_of_valuation_eq_one hu
      rw [htu, show nabs k (p ^ n * u) = nabs k (p ^ n) * nabs k u from nabs_mul k _ _, nabs_pow', h2, h3,
        mul_one]
    have h4 : (∑ a, if a ≤ j then (d a : ℤ) else 0) * (∑ b, if j < b then (d b : ℤ) else 0) =
        (((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [modulus_zj, sum_modExp, h4, h1, zpow_natCast, ← pow_mul, inv_pow, inv_inv]
  refine ⟨(μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m : Set (GL (Fin N) k)))).toReal,
    ENNReal.toReal_pos hpos.ne' hfin.ne, fun r => ?_⟩
  have hvol := GlobalTheory.CompanionTheory.DoubleCosetVolume.measure_image_doubleCoset k N (p : k) m a p.ne_zero hϖ1 hunif
    hm ha D hD μ hμ r
  rw [← hK, sum_toNat d hd j n] at hvol
  have hle := measure_le_translate μ (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (D ^ r) (w ^ r)
    (hcomm.pow_pow r r) (fun x hx => conj_mem_congruenceSubgroup k N ((integralGL k N).pow_mem hw r) hx)
  rw [hfac, hcomm.mul_pow, hmod]
  refine le_trans (le_of_eq ?_) hle
  simp only [SetLike.mem_coe] at hvol
  rw [hvol, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm,
    ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_comm _ r]
  rfl

end GlobalTheory.CompanionTheory.ContractVolume
