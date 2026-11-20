import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SmallSecond.ToO

/- English proof (translation)
Rewrite using `[frob, expand, substAlgHom_apply]`.
-/
theorem frob_eq_expand {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) : frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

/- English proof (translation)
Rewrite using `[frob_eq_expand p hp, coeff_expand_smul, coeff_map]`.
-/
theorem coeff_frob_smul {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) (β : τ →₀ ℕ) : coeff (p • β) (frob p s f) = s (coeff β f) := by
  rw [frob_eq_expand p hp, coeff_expand_smul, coeff_map]

/- English proof (translation)
Rewrite using `[frob_eq_expand p hp]`. Conclude with `coeff_expand_of_not_dvd p hp _ h`.
-/
theorem coeff_frob_of_not_dvd {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) {α : τ →₀ ℕ} {i : τ} (h : ¬ p ∣ α i) : coeff α (frob p s f) = 0 := by
  rw [frob_eq_expand p hp]
  exact coeff_expand_of_not_dvd p hp _ h

/- English proof (translation)
Use `formalCoboundary_add h (f - g) g` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this, add_sub_cancel_right]`.
-/
theorem formalGroupLawCoboundaryOne_sub {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `formalCoboundary_smul h 0 0` as an intermediate fact. Simplify using `using this`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, formalCoboundary_add h, ih]`.
-/
theorem formalGroupLawCoboundaryOne_finset_sum {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} (S : Finset ι) (f : ι → MvPowerSeries (Fin d) Q) :
    cob1 μ (∑ i ∈ S, f i) = ∑ i ∈ S, cob1 μ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := formalCoboundary_smul h 0 0
    simpa using this
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, formalCoboundary_add h, ih]

end GlobalTheory.SmallSecond.ToO

open GlobalTheory.SmallSecond.ToO in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε F d μ μ' hlift hmap k e he W b hW hT hC`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : IsLocalRing O := ValuationRing.isLocalRing O`. Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Use `set m := IsLocalRing.maximalIdeal O with hm`.

Establish `memm : ∀ x : O, x ∈ m ↔ ¬IsUnit x` using `fun x => by`. Rewrite using `[hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `hpm : (p : O) ∈ m` using `(memm _).2 Fact.out`. Establish `hθp : ∀ x : F.B, F.θ ((p : F.B) * x) ∈ m` using `fun x => by`. Rewrite using `[map_mul, map_natCast]`.

Conclude with `m.mul_mem_right _ hpm`. Establish `hWm : ∀ l, F.θ (W l) ∈ m` using `fun l => (memm _).2 (hW l)`. Establish `hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0` using `fun i => by`. Rewrite using `[up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hlift.const, map_zero]`. Establish `hcomb : ∀ c : Fin d ⊕ Fin k → F.B, cob1 (up F.Q μ') (comb c e) = ∑ l, algebraMap F.B F.Q (c l) • cob1 (up F.Q μ') (e l)`.

Introduce `c`. Unfold `comb`. Rewrite using `[formalGroupLawCoboundaryOne_finset_sum hμQ]`. Conclude with `Finset.sum_congr rfl fun l _ => formalCoboundary_smul hμQ _ _`. Use `choose g _ hg using fun l => (he l).2.2`.

Use `choose c1 _ hc1 using fun l => (he l).2.1`. Establish `hSm : ∀ α, F.θ (∑ l, W l * g l α) ∈ m` using `fun α => by`. Rewrite using `[map_sum]`. Conclude with `m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l)`. Establish `hF : In (⊤ : Ideal F.B) (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => (0 : F.B)) b) e))`.

Introduce `α`. Use `⟨∑ l, Sum.elim (fun _ => (0 : F.B)) b l * g l α, trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomb, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_smul, hg, map_mul]`.

Take `⟨F₁, hF₁⟩` from `In.top_iff.1 hF`. Take `⟨T, hTT⟩` from `In.top_iff.1 hT`. Establish `hcobT : ∀ α, coeff α (cob1 μ (map F.θ T)) = F.θ (coeff α (cob1 μ' T))`. Introduce `α`. Establish `hμeq : μ = fun i => map F.θ (μ' i)` using `funext fun i => (hmap i).symm`.

Rewrite using `[hμeq, ← map_formalGroupLawCoboundaryOne_eq F.θ μ' hlift.const T, coeff_map]`. Establish `hup : map (algebraMap F.B F.Q) (cob1 μ' T) = cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) - ∑ l, algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)`. Rewrite using `[map_formalGroupLawCoboundaryOne_eq (algebraMap F.B F.Q) μ' hlift.const T]`. Express the relevant statement in the definitionally equal form `cob1 (up F.Q μ') (map (algebraMap F.B F.Q) T) = _`. Rewrite using `[hTT, formalGroupLawCoboundaryOne_sub hμQ, hcomb]`.

Use `choose r hr hrC using hC`. Establish `hgen : ∀ α, algebraMap F.B F.Q (coeff α (cob1 μ' T)) = coeff α (frob p F.s (map (algebraMap F.B F.Q) F₁)) + algebraMap F.B F.Q (r α) - algebraMap F.B F.Q (∑ l, W l * g l α)`. Introduce `α`. Establish `h1` using `congrArg (coeff α) hup`. Rewrite `h1` using `[coeff_map]`.

Rewrite using `[h1, ← hrC α, map_sub, map_sub, hF₁, map_sum, map_sum]`. Establish `h2 : ∑ l, coeff α (algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)) = ∑ l, algebraMap F.B F.Q (W l * g l α)` using `Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_smul, hg, map_mul]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨F₁, map F.θ T, hF₁, fun i => (memm _).1 ?_, fun β => (memm _).1 ?_, fun α ⟨i, hi⟩ => (memm _).1 ?_⟩` and prove the remaining obligations.

Establish `key : coeff (Finsupp.single i 1) T = -∑ l, W l * c1 l i`. Apply `F.frame.inj` to reduce the goal to its premises. Establish `h1` using `congrArg (coeff (Finsupp.single i 1)) hTT`. Rewrite `h1` using `[coeff_map]`. Establish `hnd : ¬ p ∣ (Finsupp.single i 1 : Fin d →₀ ℕ) i`.

Rewrite using `[Finsupp.single_eq_same]`. Conclude with `(Fact.out : p.Prime).not_dvd_one`. Rewrite using `[h1, map_sub, coeff_frob_of_not_dvd p hp0 _ _ hnd, zero_sub, map_neg, map_sum]`. Unfold `comb`. Rewrite using `[map_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `hc1 l i` as an intermediate fact. Simplify using `only [lin] at this`. Rewrite using `[MvPowerSeries.coeff_smul, this, map_mul]`.

Unfold `lin`. Rewrite using `[coeff_map, key, map_neg, map_sum]`. Conclude with `m.neg_mem (m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l))`. Establish `h1` using `hgen (p • β)`. Rewrite `h1` using `[coeff_frob_smul p hp0, coeff_map, F.s_alg, ← map_add, ← map_sub]`.

Rewrite using `[hcobT, F.frame.inj h1]`. Take `⟨y, hy⟩` from `F.σ_pow (coeff β F₁)`. Take `⟨r', hr'⟩` from `Ideal.mem_span_singleton.1 (hr (p • β))`. Establish `e1 : F.θ (F.σ (coeff β F₁) + r (p • β) - ∑ l, W l * g l (p • β)) - F.θ (coeff β F₁) ^ p = F.θ (F.σ (coeff β F₁) - coeff β F₁ ^ p) + F.θ (r (p • β)) - F.θ (∑ l, W l * g l (p • β))`. Simplify using `only [map_sub, map_add, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, hy, hr']`. Conclude with `m.sub_mem (m.add_mem (hθp y) (hθp r')) (hSm _)`. Establish `h1` using `hgen α`. Rewrite `h1` using `[coeff_frob_of_not_dvd p hp0 _ _ hi, zero_add, ← map_sub]`.

Rewrite using `[hcobT, F.frame.inj h1, map_sub]`. Take `⟨r', hr'⟩` from `Ideal.mem_span_singleton.1 (hr α)`. Rewrite using `[hr']`. Conclude with `m.sub_mem (hθp r') (hSm _)`.
-/
theorem GlobalTheory.SmallSecond.frob_congr_to_O : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε F d μ μ' hlift hmap k e he W b hW hT hC
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set m := IsLocalRing.maximalIdeal O with hm
  have memm : ∀ x : O, x ∈ m ↔ ¬IsUnit x := fun x => by
    rw [hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpm : (p : O) ∈ m := (memm _).2 Fact.out
  have hθp : ∀ x : F.B, F.θ ((p : F.B) * x) ∈ m := fun x => by
    rw [map_mul, map_natCast]; exact m.mul_mem_right _ hpm
  have hWm : ∀ l, F.θ (W l) ∈ m := fun l => (memm _).2 (hW l)
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hlift.const, map_zero]
  have hcomb : ∀ c : Fin d ⊕ Fin k → F.B, cob1 (up F.Q μ') (comb c e) =
      ∑ l, algebraMap F.B F.Q (c l) • cob1 (up F.Q μ') (e l) := by
    intro c
    unfold comb
    rw [formalGroupLawCoboundaryOne_finset_sum hμQ]
    exact Finset.sum_congr rfl fun l _ => formalCoboundary_smul hμQ _ _
  choose g _ hg using fun l => (he l).2.2
  choose c1 _ hc1 using fun l => (he l).2.1
  have hSm : ∀ α, F.θ (∑ l, W l * g l α) ∈ m := fun α => by
    rw [map_sum]
    exact m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l)
  have hF : In (⊤ : Ideal F.B) (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) := by
    intro α
    refine ⟨∑ l, Sum.elim (fun _ => (0 : F.B)) b l * g l α, trivial, ?_⟩
    rw [hcomb, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPowerSeries.coeff_smul, hg, map_mul]
  obtain ⟨F₁, hF₁⟩ := In.top_iff.1 hF
  obtain ⟨T, hTT⟩ := In.top_iff.1 hT
  have hcobT : ∀ α, coeff α (cob1 μ (map F.θ T)) = F.θ (coeff α (cob1 μ' T)) := by
    intro α
    have hμeq : μ = fun i => map F.θ (μ' i) := funext fun i => (hmap i).symm
    rw [hμeq, ← map_formalGroupLawCoboundaryOne_eq F.θ μ' hlift.const T, coeff_map]
  have hup : map (algebraMap F.B F.Q) (cob1 μ' T) =
      cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) -
        ∑ l, algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l) := by
    rw [map_formalGroupLawCoboundaryOne_eq (algebraMap F.B F.Q) μ' hlift.const T]
    change cob1 (up F.Q μ') (map (algebraMap F.B F.Q) T) = _
    rw [hTT, formalGroupLawCoboundaryOne_sub hμQ, hcomb]
  choose r hr hrC using hC
  have hgen : ∀ α, algebraMap F.B F.Q (coeff α (cob1 μ' T)) =
      coeff α (frob p F.s (map (algebraMap F.B F.Q) F₁)) + algebraMap F.B F.Q (r α) -
        algebraMap F.B F.Q (∑ l, W l * g l α) := by
    intro α
    have h1 := congrArg (coeff α) hup
    rw [coeff_map] at h1
    rw [h1, ← hrC α, map_sub, map_sub, hF₁, map_sum, map_sum]
    have h2 : ∑ l, coeff α (algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)) =
        ∑ l, algebraMap F.B F.Q (W l * g l α) :=
      Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_smul, hg, map_mul]
    rw [h2]; ring
  refine ⟨F₁, map F.θ T, hF₁, fun i => (memm _).1 ?_, fun β => (memm _).1 ?_,
    fun α ⟨i, hi⟩ => (memm _).1 ?_⟩
  · have key : coeff (Finsupp.single i 1) T = -∑ l, W l * c1 l i := by
      apply F.frame.inj
      have h1 := congrArg (coeff (Finsupp.single i 1)) hTT
      rw [coeff_map] at h1
      have hnd : ¬ p ∣ (Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        rw [Finsupp.single_eq_same]; exact (Fact.out : p.Prime).not_dvd_one
      rw [h1, map_sub, coeff_frob_of_not_dvd p hp0 _ _ hnd, zero_sub, map_neg, map_sum]
      unfold comb
      rw [map_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have := hc1 l i
      simp only [lin] at this
      rw [MvPowerSeries.coeff_smul, this, map_mul]
    unfold lin
    rw [coeff_map, key, map_neg, map_sum]
    exact m.neg_mem (m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l))
  · have h1 := hgen (p • β)
    rw [coeff_frob_smul p hp0, coeff_map, F.s_alg, ← map_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1]
    obtain ⟨y, hy⟩ := F.σ_pow (coeff β F₁)
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr (p • β))
    have e1 : F.θ (F.σ (coeff β F₁) + r (p • β) - ∑ l, W l * g l (p • β)) - F.θ (coeff β F₁) ^ p =
        F.θ (F.σ (coeff β F₁) - coeff β F₁ ^ p) + F.θ (r (p • β)) -
          F.θ (∑ l, W l * g l (p • β)) := by
      simp only [map_sub, map_add, map_pow]; ring
    rw [e1, hy, hr']
    exact m.sub_mem (m.add_mem (hθp y) (hθp r')) (hSm _)
  · have h1 := hgen α
    rw [coeff_frob_of_not_dvd p hp0 _ _ hi, zero_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1, map_sub]
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr α)
    rw [hr']
    exact m.sub_mem (hθp r') (hSm _)
