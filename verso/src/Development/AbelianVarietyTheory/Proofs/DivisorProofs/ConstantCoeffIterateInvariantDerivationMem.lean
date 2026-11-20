import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Kernel

variable {R : Type} [CommRing R] {d : ℕ}

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.coeff_subst_restrict_sum G).1 α`.
-/
private lemma coeff_atZero_eq_coeff_mapDomain_inl {S : Type} [CommRing S] {n : ℕ}
    (G : MvPowerSeries (Fin n ⊕ Fin n) S) (α : Fin n →₀ ℕ) :
    coeff α (_root_.GlobalTheory.LawDer.atZero G) = coeff (Finsupp.mapDomain Sum.inl α) G :=
  (_root_.GlobalTheory.coeff_subst_restrict_sum G).1 α

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
/- English proof (translation)
Rewrite using `[coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]`. Use `finsum_congr fun e => ?_` and prove the remaining obligations. Rewrite using `[← Finsupp.prod_mapDomain_index (h := fun t k => (X t : MvPowerSeries τ S) ^ k) (by simp) (by intros; simp [pow_add]), ← monomial_one_eq, coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma coeff_subst_X_comp_eq_finsum {σ τ S : Type} [CommRing S] [Finite σ] [DecidableEq τ] (g : σ → τ)
    (F : MvPowerSeries σ S) (γ : τ →₀ ℕ) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      ∑ᶠ e : σ →₀ ℕ, if γ = Finsupp.mapDomain g e then coeff e F else 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  refine finsum_congr fun e => ?_
  rw [← Finsupp.prod_mapDomain_index (h := fun t k => (X t : MvPowerSeries τ S) ^ k) (by simp)
    (by intros; simp [pow_add]), ← monomial_one_eq, coeff_monomial]
  split_ifs <;> simp

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
/- English proof (translation)
Rewrite using `[coeff_subst_X_comp_eq_finsum]`. Conclude with `(finsum_congr fun e => if_neg fun h => hγ ⟨e, h.symm⟩).trans finsum_zero`.
-/
private lemma coeff_subst_X_comp_eq_zero_of_not_mem_range {σ τ S : Type} [CommRing S] [Finite σ] (g : σ → τ)
    (F : MvPowerSeries σ S) {γ : τ →₀ ℕ} (hγ : γ ∉ Set.range (Finsupp.mapDomain g)) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) = 0 := by
  classical
  rw [coeff_subst_X_comp_eq_finsum]
  exact (finsum_congr fun e => if_neg fun h => hγ ⟨e, h.symm⟩).trans finsum_zero

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
/- English proof (translation)
Rewrite using `[coeff_subst_X_comp_eq_finsum, finsum_eq_single _ e, if_pos rfl]`. Introduce `e' he'`. Rewrite using `[if_neg]`. Conclude with `fun h => he' (Finsupp.mapDomain_injective hg h).symm`.
-/
private lemma coeff_mapDomain_subst_X_comp_of_injective {σ τ S : Type} [CommRing S] [Finite σ] {g : σ → τ}
    (hg : Function.Injective g) (F : MvPowerSeries σ S) (e : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain g e) (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      coeff e F := by
  classical
  rw [coeff_subst_X_comp_eq_finsum, finsum_eq_single _ e, if_pos rfl]
  intro e' he'
  rw [if_neg]
  exact fun h => he' (Finsupp.mapDomain_injective hg h).symm

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in

/- English proof (translation)
Introduce `B Q _ _ _ d μ hμ N l j hc hl u n hn`. Take `⟨m, rfl⟩ : ∃ m, n = m + 2` from `⟨n - 2, by omega⟩`. Unfold `_root_.GlobalTheory.QLog.In at hc`. Use `set μ' := _root_.GlobalTheory.QLog.up Q μ with hμ'`. Use `set D := _root_.GlobalTheory.LawDer.invDer μ' (fun i => algebraMap B Q (u i)) with hD`.

Set `S : Submodule B Q` to `Submodule.map (Algebra.linearMap B Q) N`. Establish `memS : ∀ x : Q, x ∈ S ↔ ∃ b ∈ N, x = algebraMap B Q b` using `fun x => by`. Simplify using `only [S, Submodule.mem_map, Algebra.linearMap_apply]`. Conclude with `⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩`. Establish `hμ0 : ∀ i, constantCoeff (μ' i) = 0` using `fun i => by`.

Simplify using `[μ', _root_.GlobalTheory.QLog.up, constantCoeff_map, hμ i]`. Establish `hlin` using `_root_.GlobalTheory.LawDer.Linear.invDer_linear Q d μ' hμ0 (fun i => algebraMap B Q (u i))`. Establish `hlinD : ∀ F G : MvPowerSeries (Fin d) Q, D (F + G) = D F + D G` using `hlin.1`. Establish `hcoeffD : ∀ (F : MvPowerSeries (Fin d) Q) (β : Fin d →₀ ℕ), coeff β (D F) = ∑ i, algebraMap B Q (u i) * (coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1) (subst μ' F) * ((Finsupp.mapDomain Sum.inl β (Sum.inr i) : Q) + 1))`. Introduce `F β`.

Rewrite using `[hD]`. Unfold `_root_.GlobalTheory.LawDer.invDer`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, coeff_atZero_eq_coeff_mapDomain_inl, coeff_pderiv]`.

Establish `hP : ∀ F : MvPowerSeries (Fin d) Q, (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D F) ∈ S`. Introduce `F hF β`. Rewrite using `[hcoeffD]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`.

Use `S.smul_mem _ ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]`. Conclude with `nsmul_mem (_root_.GlobalTheory.SubstSub.coeff_subst_up_mem B Q (Fin d) (Fin d ⊕ Fin d) S F μ hμ hF _) _`. Establish `hPit : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) Q), (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D^[k] F) ∈ S`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro F hF`. Simplify using `using hF`. Consider the case `succ k ih => intro F hF`. Rewrite using `[Function.iterate_succ_apply]`.

Conclude with `ih _ (hP F hF)`. Establish `hadd : ∀ (k : ℕ) (F G : MvPowerSeries (Fin d) Q), D^[k] (F + G) = D^[k] F + D^[k] G`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro F G`.

Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `F G`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hlinD, ih]`. Establish `hD0 : D 0 = 0`.

Establish `h` using `hlinD 0 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Establish `hDC : ∀ c : Q, D (C c) = 0`. Introduce `c`.

Use extensionality with `β`. Rewrite using `[hcoeffD]`. Simplify using `[subst_C, coeff_C]`. Establish `hCit : ∀ (k : ℕ) (c : Q), D^[k + 1] (C c) = 0` using `fun k c => by`. Rewrite using `[Function.iterate_succ_apply, hDC, Function.iterate_fixed hD0]`.

Establish `hzero : ∀ (β : Fin d →₀ ℕ) (i : Fin d), Finsupp.mapDomain Sum.inl β (Sum.inr i) = 0` using `fun β i => Finsupp.mapDomain_notin_range _ _ (by simp)`. Establish `hsplit : subst μ' l = _root_.GlobalTheory.Katz.cob1 μ' l + _root_.GlobalTheory.Katz.inL l + _root_.GlobalTheory.Katz.inR l`. Unfold `_root_.GlobalTheory.Katz.cob1`. Expand and normalize the polynomial expressions, which then agree. Establish `hleft : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inL l) = 0`.

Introduce `β i`. Unfold `_root_.GlobalTheory.Katz.inL`. Apply `coeff_subst_X_comp_eq_zero_of_not_mem_range` to reduce the goal to its premises. Introduce and unpack `⟨e, he⟩`. Establish `h` using `congrArg (fun x => x (Sum.inr i)) he`.

Simplify using `[hzero] at h`. Establish `hright : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inR l) = if β = 0 then (Pi.single j 1 : Fin d → Q) i else 0`. Introduce `β i`. Unfold `_root_.GlobalTheory.Katz.inR`. Use `split_ifs with hβ`.

Substitute `hβ` using the available equality. Rewrite using `[Finsupp.mapDomain_zero, zero_add, ← Finsupp.mapDomain_single, coeff_mapDomain_subst_X_comp_of_injective Sum.inr_injective, ← hl]`. Both sides reduce to the same expression. Apply `coeff_subst_X_comp_eq_zero_of_not_mem_range` to reduce the goal to its premises. Introduce and unpack `⟨e, he⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, β k ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hβ (Finsupp.ext h)`. Establish `h` using `congrArg (fun x => x (Sum.inl k)) he`.

Rewrite `h` using `[Finsupp.mapDomain_notin_range _ _ (by simp)]`. Simplify using `[Finsupp.mapDomain_apply Sum.inl_injective] at h`. Use linear arithmetic over natural numbers and integers. Establish `hg : ∀ β, coeff β (D l - C (algebraMap B Q (u j))) ∈ S`. Introduce `β`.

Establish `hsum : coeff β (D l - C (algebraMap B Q (u j))) = ∑ i, algebraMap B Q (u i) * coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.cob1 μ' l)`. Rewrite using `[map_sub, hcoeffD]`. Simplify using `only [hsplit, map_add, hleft, hright, hzero, Nat.cast_zero, zero_add, add_zero, mul_one, mul_add, Finset.sum_add_distrib]`. Apply the tactic sequence `by_cases hβ : β = 0 <;> simp [hβ, Pi.single_apply, coeff_C]`. Rewrite using `[hsum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`. Use `S.smul_mem _ ((memS _).2 ?_)` and prove the remaining obligations. Take `⟨b, hb, h⟩` from `hc (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)`. Conclude with `⟨b, hb, h⟩`.

Establish `key : D^[m + 2] l = D^[m + 1] (D l - C (algebraMap B Q (u j)))` using `by conv_lhs => rw [Function.iterate_succ_apply, ← sub_add_cancel (D l) (C (algebraMap B Q (u j)))]`. Rewrite using `[hadd, hCit, add_zero]`. Rewrite using `[key]`. Take `⟨b, hb, h⟩` from `(memS _).1 (hPit (m + 1) _ hg 0)`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `h`.
-/
theorem _root_.GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), _root_.GlobalTheory.QLog.In N (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) l) → _root_.GlobalTheory.Katz.lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((_root_.GlobalTheory.LawDer.invDer (_root_.GlobalTheory.QLog.up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  intro B Q _ _ _ d μ hμ N l j hc hl u n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold _root_.GlobalTheory.QLog.In at hc
  set μ' := _root_.GlobalTheory.QLog.up Q μ with hμ'
  set D := _root_.GlobalTheory.LawDer.invDer μ' (fun i => algebraMap B Q (u i)) with hD
  let S : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N
  have memS : ∀ x : Q, x ∈ S ↔ ∃ b ∈ N, x = algebraMap B Q b := fun x => by
    simp only [S, Submodule.mem_map, Algebra.linearMap_apply]
    exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩
  have hμ0 : ∀ i, constantCoeff (μ' i) = 0 := fun i => by
    simp [μ', _root_.GlobalTheory.QLog.up, constantCoeff_map, hμ i]
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear Q d μ' hμ0 (fun i => algebraMap B Q (u i))
  have hlinD : ∀ F G : MvPowerSeries (Fin d) Q, D (F + G) = D F + D G := hlin.1
  have hcoeffD : ∀ (F : MvPowerSeries (Fin d) Q) (β : Fin d →₀ ℕ), coeff β (D F) =
      ∑ i, algebraMap B Q (u i) * (coeff (Finsupp.mapDomain Sum.inl β +
        Finsupp.single (Sum.inr i) 1) (subst μ' F) *
          ((Finsupp.mapDomain Sum.inl β (Sum.inr i) : Q) + 1)) := by
    intro F β
    rw [hD]
    unfold _root_.GlobalTheory.LawDer.invDer
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_smul, coeff_atZero_eq_coeff_mapDomain_inl, coeff_pderiv]
  have hP : ∀ F : MvPowerSeries (Fin d) Q, (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D F) ∈ S := by
    intro F hF β
    rw [hcoeffD]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ?_
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (_root_.GlobalTheory.SubstSub.coeff_subst_up_mem B Q (Fin d) (Fin d ⊕ Fin d) S F μ
      hμ hF _) _
  have hPit : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) Q), (∀ α, coeff α F ∈ S) →
      ∀ β, coeff β (D^[k] F) ∈ S := by
    intro k
    induction k with
    | zero => intro F hF; simpa using hF
    | succ k ih => intro F hF; rw [Function.iterate_succ_apply]; exact ih _ (hP F hF)
  have hadd : ∀ (k : ℕ) (F G : MvPowerSeries (Fin d) Q), D^[k] (F + G) = D^[k] F + D^[k] G := by
    intro k
    induction k with
    | zero => intro F G; rfl
    | succ k ih =>
      intro F G
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        hlinD, ih]
  have hD0 : D 0 = 0 := by
    have h := hlinD 0 0
    rw [add_zero] at h
    simpa using h
  have hDC : ∀ c : Q, D (C c) = 0 := by
    intro c
    ext β
    rw [hcoeffD]
    simp [subst_C, coeff_C]
  have hCit : ∀ (k : ℕ) (c : Q), D^[k + 1] (C c) = 0 := fun k c => by
    rw [Function.iterate_succ_apply, hDC, Function.iterate_fixed hD0]
  have hzero : ∀ (β : Fin d →₀ ℕ) (i : Fin d), Finsupp.mapDomain Sum.inl β (Sum.inr i) = 0 :=
    fun β i => Finsupp.mapDomain_notin_range _ _ (by simp)
  have hsplit : subst μ' l = _root_.GlobalTheory.Katz.cob1 μ' l + _root_.GlobalTheory.Katz.inL l +
      _root_.GlobalTheory.Katz.inR l := by
    unfold _root_.GlobalTheory.Katz.cob1
    ring
  have hleft : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inL l) = 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inL
    apply coeff_subst_X_comp_eq_zero_of_not_mem_range
    rintro ⟨e, he⟩
    have h := congrArg (fun x => x (Sum.inr i)) he
    simp [hzero] at h
  have hright : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inR l) =
        if β = 0 then (Pi.single j 1 : Fin d → Q) i else 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inR
    split_ifs with hβ
    · subst hβ
      rw [Finsupp.mapDomain_zero, zero_add, ← Finsupp.mapDomain_single,
        coeff_mapDomain_subst_X_comp_of_injective Sum.inr_injective, ← hl]
      rfl
    · apply coeff_subst_X_comp_eq_zero_of_not_mem_range
      rintro ⟨e, he⟩
      obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hβ (Finsupp.ext h)
      have h := congrArg (fun x => x (Sum.inl k)) he
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)] at h
      simp [Finsupp.mapDomain_apply Sum.inl_injective] at h
      omega
  have hg : ∀ β, coeff β (D l - C (algebraMap B Q (u j))) ∈ S := by
    intro β
    have hsum : coeff β (D l - C (algebraMap B Q (u j))) = ∑ i, algebraMap B Q (u i) *
        coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
          (_root_.GlobalTheory.Katz.cob1 μ' l) := by
      rw [map_sub, hcoeffD]
      simp only [hsplit, map_add, hleft, hright, hzero, Nat.cast_zero, zero_add, add_zero,
        mul_one, mul_add, Finset.sum_add_distrib]
      by_cases hβ : β = 0 <;> simp [hβ, Pi.single_apply, coeff_C]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ((memS _).2 ?_)
    obtain ⟨b, hb, h⟩ := hc (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
    exact ⟨b, hb, h⟩
  have key : D^[m + 2] l = D^[m + 1] (D l - C (algebraMap B Q (u j))) := by
    conv_lhs => rw [Function.iterate_succ_apply, ← sub_add_cancel (D l) (C (algebraMap B Q (u j)))]
    rw [hadd, hCit, add_zero]
  rw [key]
  obtain ⟨b, hb, h⟩ := (memS _).1 (hPit (m + 1) _ hg 0)
  refine ⟨b, hb, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h

end GlobalTheory.LawDer.Kernel
