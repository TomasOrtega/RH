import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsCharIdemOfIsSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.BadShare GlobalTheory.BadShare.Basic
open scoped Classical

namespace GlobalTheory.GLq.SqSeries

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Take `⟨V, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV, FDRep.char_conj]`.
-/
theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

/- English proof (translation)
Use `haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩`. Unfold `wh tr`. Rewrite using `[Fintype.sum_subsingleton _ 1, eU, coeff_eDat, mul_one]`. Establish `hU : ∀ u : Gn g 0, IsUniUp u.val` using `fun u a => a.elim0`. Establish `hc : Nat.card {u : GG g 0 // IsUniUp u.val} = 1` using `by haveI : Nonempty {u : GG g 0 // IsUniUp u.val} := ⟨⟨1, hU 1⟩⟩`.

Conclude with `Nat.card_unique`. Unfold `eps`. Rewrite using `[if_pos (hU 1), hc]`. Simplify using the standard rewrite rules.
-/
theorem wh_one_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  unfold wh tr
  rw [Fintype.sum_subsingleton _ 1, eU, coeff_eDat, mul_one]
  have hU : ∀ u : Gn g 0, IsUniUp u.val := fun u a => a.elim0
  have hc : Nat.card {u : GG g 0 // IsUniUp u.val} = 1 := by
    haveI : Nonempty {u : GG g 0 // IsUniUp u.val} := ⟨⟨1, hU 1⟩⟩
    exact Nat.card_unique
  unfold eps
  rw [if_pos (hU 1), hc]
  simp

/- English proof (translation)
Unfold `wh tr`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (χ : Gn g n → ℂ) :
    wh ψ (fun x => c * χ x) = c * wh ψ χ := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact wh_one_zero ψ`. Consider the case `cons p L ih`. Establish `hp` using `h p List.mem_cons_self`. Establish `hL` using `fun q hq => h q (List.mem_cons_of_mem p hq)`.

Establish `hch : ∀ q : Pc g, IsCusp q.2 → IsChar q.2` using `fun q hq => by`. Take `⟨V, -, hV⟩` from `hq.2.1`. Conclude with `⟨V, hV⟩`. Establish `c1` using `isClass_of_isChar (hch p hp.1)`. Establish `c2` using `isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ rfl fun q hq => hch q (hL q hq).1).1`.

Rewrite using `[hcL_cons, hc, GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ p.1 (degL L) _ (by simp [degL]) _ (fun y a b => by simp only [c1 a b]) (fun x a b => by simp only [c2 a b])]`. Simplify using `only [wh_const_mul, ih hL, mul_one]`. Conclude with `GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ hp.1 hp.2`.
-/
theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (h : ∀ p ∈ L, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil => exact wh_one_zero ψ
  | cons p L ih =>
    have hp := h p List.mem_cons_self
    have hL := fun q hq => h q (List.mem_cons_of_mem p hq)
    have hch : ∀ q : Pc g, IsCusp q.2 → IsChar q.2 := fun q hq => by
      obtain ⟨V, -, hV⟩ := hq.2.1
      exact ⟨V, hV⟩
    have c1 := isClass_of_isChar (hch p hp.1)
    have c2 := isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ rfl fun q hq => hch q (hL q hq).1).1
    rw [hcL_cons, hc, GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ p.1 (degL L) _ (by simp [degL]) _
      (fun y a b => by simp only [c1 a b]) (fun x a b => by simp only [c2 a b])]
    simp only [wh_const_mul, ih hL, mul_one]
    exact GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ hp.1 hp.2

/- English proof (translation)
Establish `hk : 0 + 0 < n` using `hn`. Use `⟨levOfChar ψ hψ n false 0 0 hk, rfl, ?_⟩` and prove the remaining obligations. Establish `h1 : op V.ρ (levOfChar ψ hψ n false 0 0 hk).e ≠ 0`. Introduce `h0`. Apply `h` to reduce the goal to its premises.

Use `congrArg (LinearMap.trace ℂ V) h0` as an intermediate fact. Rewrite `this` using `[map_zero, op, map_sum]`. Rewrite using `[← this]`. Unfold `wh tr`. Use `Finset.sum_congr (by congr) fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_eU ψ hψ 0 0 hk, map_smul, smul_eq_mul]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, op V.ρ (levOfChar ψ hψ n false 0 0 hk).e y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `h1 (LinearMap.ext hc)`. Use `⟨_, hy, fun u hu => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.BadShare.EpsProj.mem_range_iff V.ρ (mem_one _) (fun _ _ => mem_mul _) (chi_one _) (fun _ _ => chi_mul _) _).1 ⟨y, rfl⟩ u ⟨hu, fun hs => absurd hs (by simp [levOfChar])⟩`.
-/
theorem isGeneric_of_wh (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {n : ℕ} (hn : 0 < n) (V : FDRep ℂ (GG g n))
    (h : wh ψ V.character ≠ 0) : IsGeneric V.ρ := by
  have hk : 0 + 0 < n := hn
  refine ⟨levOfChar ψ hψ n false 0 0 hk, rfl, ?_⟩
  have h1 : op V.ρ (levOfChar ψ hψ n false 0 0 hk).e ≠ 0 := by
    intro h0
    apply h
    have := congrArg (LinearMap.trace ℂ V) h0
    rw [map_zero, op, map_sum] at this
    rw [← this]
    unfold wh tr
    refine Finset.sum_congr (by congr) fun x _ => ?_
    rw [coeff_eU ψ hψ 0 0 hk, map_smul, smul_eq_mul]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, op V.ρ (levOfChar ψ hψ n false 0 0 hk).e y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h1 (LinearMap.ext hc)
  refine ⟨_, hy, fun u hu => ?_⟩
  exact (GlobalTheory.BadShare.EpsProj.mem_range_iff V.ρ (mem_one _) (fun _ _ => mem_mul _) (chi_one _) (fun _ _ => chi_mul _) _).1
    ⟨y, rfl⟩ u ⟨hu, fun hs => absurd hs (by simp [levOfChar])⟩

/- English proof (translation)
Establish `H` using `GlobalTheory.T.harishChandraProductList_degree g L n hn`. Establish `e1 : (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod * (L.map fun p => p.2 1).prod`. Rewrite using `[← List.prod_map_mul]`. Use `congr 1`. Use `List.map_congr_left fun p hp => ?_` and prove the remaining obligations.

Rewrite using `[(h p hp).2, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (h p hp).1, mul_comm]`. Establish `e2 : (L.map fun p => p.2 1).prod ≠ 0`. Use `List.prod_ne_zero fun h0 => ?_` and prove the remaining obligations. Take `⟨p, hp, h1⟩` from `List.mem_map.1 h0`. Rewrite `h1` using `[(h p hp).2, Finset.prod_eq_zero_iff]`.

Take `⟨i, hi, h2⟩` from `h1`. Establish `h3 : g ^ i = 1` using `by exact_mod_cast sub_eq_zero.1 h2`. Establish `h4` using `(Fact.out : g.Prime).one_lt`. Establish `h5` using `(Finset.mem_Ico.1 hi).1`. Use `Nat.one_lt_pow (n := i) (by omega) h4` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite `H` using `[e1, ← mul_assoc]`. Rewrite using `[mul_right_cancel₀ e2 H, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]`. Simplify using `[add_comm]`.
-/
theorem deg_hcL (L : List (Pc g)) (n : ℕ) (hn : n = degL L)
    (h : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    hcL L n 1 * (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod = ∏ i ∈ Finset.range n, ((g : ℂ) ^ (i + 1) - 1) := by
  have H := GlobalTheory.T.harishChandraProductList_degree g L n hn
  have e1 : (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod * (L.map fun p => p.2 1).prod := by
    rw [← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [(h p hp).2, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (h p hp).1, mul_comm]
  have e2 : (L.map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    rw [(h p hp).2, Finset.prod_eq_zero_iff] at h1
    obtain ⟨i, hi, h2⟩ := h1
    have h3 : g ^ i = 1 := by exact_mod_cast sub_eq_zero.1 h2
    have h4 := (Fact.out : g.Prime).one_lt
    have h5 := (Finset.mem_Ico.1 hi).1
    have := Nat.one_lt_pow (n := i) (by omega) h4
    omega
  rw [e1, ← mul_assoc] at H
  rw [mul_right_cancel₀ e2 H, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

/- English proof (translation)
Introduce `hG g _ L n hg hn`. Take `⟨H1, -, H3⟩` from `GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n`. Establish `H4` using `fun (f : (ZMod g)[X]) (hf : f ∈ sqSet g n) => H3 f (mem_sqSet.1 hf).1 (mem_sqSet.1 hf).2.1 (mem_sqSet.1 hf).2.2.2 (mem_sqSet.1 hf).2.2.1`. Use `choose! Q Q1 Q2 Q3 Q4 using H4`. Establish `hmem : ∀ f ∈ sqSet g n, IsIrr (hcL ((Q f).map Prod.snd) n) ∧ HasLabel L (hcL ((Q f).map Prod.snd) n) f`.

Introduce `f hf`. Establish `: hcL ((Q f).map Prod.snd) n ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}`. Rewrite using `[Q4 f hf]`. Both sides reduce to the same expression. Conclude with `this`.

Use `⟨fun f => hcL ((Q f).map Prod.snd) n, ⟨fun f hf f' hf' h => ?_, fun f hf => ?_⟩, fun f hf x => ?_⟩` and prove the remaining obligations. Establish `a` using `hmem f hf`. Establish `b` using `(hmem f' hf').2`. Establish `h' : hcL ((Q f).map Prod.snd) n = hcL ((Q f').map Prod.snd) n` using `h`. Rewrite `b` using `[← h']`.

Conclude with `(H1 _ a.1).unique a.2 b`. Take `⟨V, hs, hV⟩` from `(hmem f hf).1`. Establish `hV' : V.character = hcL ((Q f).map Prod.snd) n` using `funext hV`. Establish `hc : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)`. Introduce `p hp`.

Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hp`. Conclude with `⟨(Q1 f hf q hq).1.2.1, (Q1 f hf q hq).2⟩`. Use `⟨V, hs, hV', ?_, ?_⟩` and prove the remaining obligations. Establish `hψ` using `(levStandard g n false 0 0 hn).hψ`. Use `isGeneric_of_wh _ hψ hn V ?_` and prove the remaining obligations.

Establish `h1` using `wh_hcL _ hψ _ hc`. Rewrite `h1` using `[Q3 f hf]`. Rewrite using `[hV', h1]`. Conclude with `one_ne_zero`. Establish `h1` using `deg_hcL _ n (Q3 f hf).symm fun p hp => ⟨(hc p hp).1.1, (hc p hp).2⟩`.

Establish `hpos : ∀ i, 1 ≤ g ^ i` using `fun i => Nat.one_le_pow _ _ (by omega)`. Establish `h2 : (torusCard g f : ℂ) = (((Q f).map Prod.snd).map fun p => ((g : ℂ) ^ p.1 - 1)).prod`. Rewrite using `[torusCard, degType, ← Q2 f hf]`. Simplify using `only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Nat.cast_list_prod]`. Use `congr 1`.

Use `List.map_congr_left fun q hq => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[(Q1 f hf q hq).1.1.2.2.2, Nat.cast_sub (hpos _)]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← hV', FDRep.char_one, ← h2]`.

Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Rewrite using `[Nat.cast_mul, h1, Nat.cast_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sub (hpos _)]`. Simplify using the standard rewrite rules.

Rewrite using `[eSerC, Q4 f hf, finsum_mem_singleton]`. Conclude with `coeff_alg (zc _) x`.
-/
theorem exists_series : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  intro hG g _ L n hg hn
  obtain ⟨H1, -, H3⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have H4 := fun (f : (ZMod g)[X]) (hf : f ∈ sqSet g n) =>
    H3 f (mem_sqSet.1 hf).1 (mem_sqSet.1 hf).2.1 (mem_sqSet.1 hf).2.2.2 (mem_sqSet.1 hf).2.2.1
  choose! Q Q1 Q2 Q3 Q4 using H4
  have hmem : ∀ f ∈ sqSet g n, IsIrr (hcL ((Q f).map Prod.snd) n) ∧ HasLabel L (hcL ((Q f).map Prod.snd) n) f := by
    intro f hf
    have : hcL ((Q f).map Prod.snd) n ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} := by
      rw [Q4 f hf]; rfl
    exact this
  refine ⟨fun f => hcL ((Q f).map Prod.snd) n, ⟨fun f hf f' hf' h => ?_, fun f hf => ?_⟩, fun f hf x => ?_⟩
  · have a := hmem f hf
    have b := (hmem f' hf').2
    have h' : hcL ((Q f).map Prod.snd) n = hcL ((Q f').map Prod.snd) n := h
    rw [← h'] at b
    exact (H1 _ a.1).unique a.2 b
  · obtain ⟨V, hs, hV⟩ := (hmem f hf).1
    have hV' : V.character = hcL ((Q f).map Prod.snd) n := funext hV
    have hc : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(Q1 f hf q hq).1.2.1, (Q1 f hf q hq).2⟩
    refine ⟨V, hs, hV', ?_, ?_⟩
    · have hψ := (levStandard g n false 0 0 hn).hψ
      refine isGeneric_of_wh _ hψ hn V ?_
      have h1 := wh_hcL _ hψ _ hc
      rw [Q3 f hf] at h1
      rw [hV', h1]
      exact one_ne_zero
    · have h1 := deg_hcL _ n (Q3 f hf).symm fun p hp => ⟨(hc p hp).1.1, (hc p hp).2⟩
      have hpos : ∀ i, 1 ≤ g ^ i := fun i => Nat.one_le_pow _ _ (by omega)
      have h2 : (torusCard g f : ℂ) = (((Q f).map Prod.snd).map fun p => ((g : ℂ) ^ p.1 - 1)).prod := by
        rw [torusCard, degType, ← Q2 f hf]
        simp only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Nat.cast_list_prod]
        congr 1
        refine List.map_congr_left fun q hq => ?_
        simp only [Function.comp]
        rw [(Q1 f hf q hq).1.1.2.2.2, Nat.cast_sub (hpos _)]
        simp
      rw [← hV', FDRep.char_one, ← h2] at h1
      apply Nat.cast_injective (R := ℂ)
      rw [Nat.cast_mul, h1, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hpos _)]
      simp
  · rw [eSerC, Q4 f hf, finsum_mem_singleton]
    exact coeff_alg (zc _) x

end GlobalTheory.GLq.SqSeries
