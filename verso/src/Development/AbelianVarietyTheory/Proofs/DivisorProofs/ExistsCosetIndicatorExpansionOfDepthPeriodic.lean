import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

/- English proof (translation)
Take `⟨u, hu, -, rfl⟩` from `h`. Rewrite using `[nsmul_add]`. Conclude with `add_mem hr (nsmul_mem (nsmul_mem hu K) K)`.
-/
theorem nsmul_mem_of_mem_halfCoset {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {r x : Mx D m n}
    (hr : K • r ∈ Λ) (h : x ∈ halfCoset e Λ K r) : K • x ∈ Λ := by
  obtain ⟨u, hu, -, rfl⟩ := h
  rw [nsmul_add]
  exact add_mem hr (nsmul_mem (nsmul_mem hu K) K)

/- English proof (translation)
Use `hR3 r hr r₀ hr₀ ?_` and prove the remaining obligations. Rewrite using `[← halfCoset_eq hm, halfCoset_eq hm₀]`. Conclude with `mem_halfCoset_self _ _ _ _`.
-/
theorem eq_of_mem_halfCoset_reps {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {R : Finset (Mx D m n)}
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') {r r₀ x : Mx D m n} (hr : r ∈ R) (hr₀ : r₀ ∈ R)
    (hm : x ∈ halfCoset e Λ K r) (hm₀ : x ∈ halfCoset e Λ K r₀) : r = r₀ := by
  refine hR3 r hr r₀ hr₀ ?_
  rw [← halfCoset_eq hm, halfCoset_eq hm₀]
  exact mem_halfCoset_self _ _ _ _

/- English proof (translation)
Introduce `D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep`. Distinguish the cases in `hτ : τ = 0`. Substitute `hτ` using the available equality. Conclude with `⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩`. Take `⟨d₀, hd₀⟩` from `Finsupp.support_nonempty_iff.2 hτ`.

Establish `hP0` using `hexp.1 d₀ hd₀`. Establish `hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))), (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧ (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧ ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairL …` using `fun j => exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))`. Establish `hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧ (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧ ∀ r …` using `fun i => exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))`. Use `choose R1 hR1 using hR1`. Use `choose R2 hR2 using hR2`.

Set `dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) → (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t` to `fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))`. Use `set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2, Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'`. Establish `hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ'`. Introduce `d' hd'`. Rewrite `hd'` using `[hτ']`.

Take `⟨ρ, hρ, h2⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')`. Take `⟨ρ', hρ', h3⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)`. Conclude with `⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩`. Use `⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩` and prove the remaining obligations. Take `⟨ρ, -, ρ', -, rfl⟩` from `hsupp d' hd'`.

Use `⟨fun j => ?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨a, b, c⟩` from `hP0.1 j`. Conclude with `⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩`. Take `⟨a, b, c⟩` from `hP0.2 i`. Conclude with `⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩`.

Set `g : PureDat G t → ℂ → ℂ` to `fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)`. Establish `h0 : ∀ d, g d 0 = 0` using `fun d => by simp [g]`. Establish `hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂` using `fun d b₁ b₂ => by simp only [g]; ring`. Express the relevant statement in the definitionally equal form `Finsupp.sum τ' g = _`. Rewrite using `[hτ', ← Finsupp.sum_finsetSum_index h0 hadd]`.

Repeatedly rewrite using `[← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]`. Establish `hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) = (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)` using `fun ρ hρ j => congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1 ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)`. Establish `hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) = (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i)` using `fun ρ' hρ' i => congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1 ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)`. Simplify using `only [g, dat]`. Establish `hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2, flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) = flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j …` using `fun ρ hρ ρ' hρ' => by`.

Rewrite using `[Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]`. Rewrite using `[Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']`. Use `show _ = flatProd S t Φ β x y`. Distinguish the cases in `hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)`. Establish `h1` using `fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)`.

Establish `h2` using `fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)`. Use `choose ρ0 hρ0 hxρ0 using h1`. Use `choose ρ0' hρ0' hyρ0' using h2`. Establish `hmem : ρ0 ∈ Fintype.piFinset R1` using `Fintype.mem_piFinset.2 hρ0`. Establish `hmem' : ρ0' ∈ Fintype.piFinset R2` using `Fintype.mem_piFinset.2 hρ0'`.

Establish `hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 → ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ)`. Introduce `ρ hρ hne`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hne (funext hc)`. Use `Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)` and prove the remaining obligations. Conclude with `eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)`. Establish `hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' → ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ)`. Introduce `ρ' hρ' hne`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (funext hc)`. Use `Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)` and prove the remaining obligations.

Conclude with `eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)`. Rewrite using `[Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]`. Use `case s1 =>`. Introduce `ρ hρ hne`. Conclude with `Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _`.

Use `case s2 =>`. Introduce `ρ' hρ' hne`. Conclude with `mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)`. Use `(congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_)) (Finset.prod_eq_one fun i _ => ?_)).trans ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_mem (hxρ0 j) _`.

Conclude with `Set.indicator_of_mem (hyρ0' i) _`. Rewrite using `[mul_one, mul_one]`. Use `choose u hu hu' hxu using hxρ0`. Use `choose v hv hv' hyv using hyρ0'`. Establish `hx' : x = ρ0 + K • u` using `funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j`.

Establish `hy' : y = ρ0' + K • v` using `funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i`. Rewrite using `[hx', hy']`. Conclude with `(hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1) (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm`. Establish `hzero : flatProd S t Φ β x y = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hin (hdep.1 x y hx hy h)`. Rewrite using `[hzero]`. Use `Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_` and prove the remaining obligations. Rewrite `hρ`, `hρ'` using `[Fintype.mem_piFinset]`. Break down `not_and_or.1 hin with h | h` into its components or cases.

Use `push_neg at h`. Take `⟨j, hj⟩` from `h`. Conclude with `mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _`. Use `push_neg at h`. Take `⟨i, hi⟩` from `h`.

Conclude with `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))`. Take `⟨ρ, hρ, ρ', hρ', rfl⟩` from `hsupp d' hd'`. Rewrite `hρ`, `hρ'` using `[Fintype.mem_piFinset]`. Use `⟨fun j => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `(hR1 j).1 _ (hρ j)`.

Conclude with `isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2`. Establish `h` using `(hR2 i).1 _ (hρ' i)`. Conclude with `isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2`.
-/
theorem exists_cosetExpansion_of_depthOK : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  classical
  intro D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep
  by_cases hτ : τ = 0
  · subst hτ
    exact ⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩
  obtain ⟨d₀, hd₀⟩ := Finsupp.support_nonempty_iff.2 hτ
  have hP0 := hexp.1 d₀ hd₀
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  let dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) →
      (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t :=
    fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))
  set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'
  have hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ' := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := hP0.1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := hP0.2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    change Finsupp.sum τ' g = _
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) =
        (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) := fun ρ hρ j =>
      congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1
        ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)
    have hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ' hρ' i =>
      congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1
        ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)
    simp only [g, dat]
    have hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2,
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)) *
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ hρ ρ' hρ' => by
      rw [Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]
    rw [Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']
    show _ = flatProd S t Φ β x y
    by_cases hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)
    · have h1 := fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)
      have h2 := fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)
      choose ρ0 hρ0 hxρ0 using h1
      choose ρ0' hρ0' hyρ0' using h2
      have hmem : ρ0 ∈ Fintype.piFinset R1 := Fintype.mem_piFinset.2 hρ0
      have hmem' : ρ0' ∈ Fintype.piFinset R2 := Fintype.mem_piFinset.2 hρ0'
      have hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 →
          ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ) := by
        intro ρ hρ hne
        obtain ⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)
        exact eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)
      have hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' →
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ) := by
        intro ρ' hρ' hne
        obtain ⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)
        exact eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)
      rw [Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]
      case s1 =>
        intro ρ hρ hne
        exact Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _
      case s2 =>
        intro ρ' hρ' hne
        exact mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)
      refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_))
        (Finset.prod_eq_one fun i _ => ?_)).trans ?_
      · exact Set.indicator_of_mem (hxρ0 j) _
      · exact Set.indicator_of_mem (hyρ0' i) _
      rw [mul_one, mul_one]
      choose u hu hu' hxu using hxρ0
      choose v hv hv' hyv using hyρ0'
      have hx' : x = ρ0 + K • u := funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j
      have hy' : y = ρ0' + K • v := funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i
      rw [hx', hy']
      exact (hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1)
        (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm
    · have hzero : flatProd S t Φ β x y = 0 := by
        by_contra h
        exact hin (hdep.1 x y hx hy h)
      rw [hzero]
      refine Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_
      rw [Fintype.mem_piFinset] at hρ hρ'
      rcases not_and_or.1 hin with h | h
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem
          (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem
          (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))
  · obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2

end GlobalTheory.DepthUnf

end
