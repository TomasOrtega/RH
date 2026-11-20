import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPartStatement

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.StepGen

section Nat

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {σ τ : Type}

/- English proof (translation)
The claim follows from `map_subst (hasSubst_of_constantCoeff_zero hu) f`.
-/
theorem map_subst0 [Finite σ] (φ : R →+* S) {u : σ → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (f : MvPowerSeries σ R) :
    map φ (subst u f) = subst (fun i => map φ (u i)) (map φ f) :=
  map_subst (hasSubst_of_constantCoeff_zero hu) f

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hu) hu hf`.
-/
theorem cc_subst0 [Finite σ] {u : σ → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    constantCoeff (subst u f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hu) hu hf

/- English proof (translation)
Consider the cases of `i with`. Consider the case `inl i => exact hu i`. Consider the case `inr i => exact hv i`.
-/
theorem cc_elim {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d ⊕ Fin d) :
    constantCoeff (Sum.elim u v i) = 0 := by
  cases i with
  | inl i => exact hu i
  | inr i => exact hv i

/- English proof (translation)
Unfold `at2`. Rewrite using `[map_subst0 φ (cc_elim hu hv)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> rfl`.
-/
theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst0 φ (cc_elim hu hv)]
  congr 1
  funext i
  cases i <;> rfl

/- English proof (translation)
Unfold `at2`. Rewrite using `[subst_add (hasSubst_of_constantCoeff_zero (cc_elim hu hv)), subst_smul (hasSubst_of_constantCoeff_zero (cc_elim hu hv))]`.
-/
theorem at2_lin {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (n : R)
    (c r : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 (n • c + r) u v = n • at2 c u v + at2 r u v := by
  unfold at2
  rw [subst_add (hasSubst_of_constantCoeff_zero (cc_elim hu hv)),
    subst_smul (hasSubst_of_constantCoeff_zero (cc_elim hu hv))]

/- English proof (translation)
Use `at2_lin hu hv (-1) 0 0` as an intermediate fact. Rewrite `this` using `[smul_zero, add_zero]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem at2_zero {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 0 u v = 0 := by
  have := at2_lin hu hv (-1) 0 0
  rw [smul_zero, add_zero] at this
  rw [this]; simp

/- English proof (translation)
The claim follows from `cc_subst0 (cc_elim hu hv) (h i)`.
-/
theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := cc_subst0 (cc_elim hu hv) (h i)

/- English proof (translation)
The claim follows from `constantCoeff_X _`.
-/
theorem c1 (i : Fin d) : constantCoeff (x1 (R := R) i) = 0 := constantCoeff_X _
/- English proof (translation)
The claim follows from `constantCoeff_X _`.
-/
theorem c2 (i : Fin d) : constantCoeff (x2 (R := R) i) = 0 := constantCoeff_X _
/- English proof (translation)
The claim follows from `constantCoeff_X _`.
-/
theorem c3 (i : Fin d) : constantCoeff (x3 (R := R) i) = 0 := constantCoeff_X _

/- English proof (translation)
Establish `e1 : (fun i => map φ (x1 (R` using `R) (d := d) i)) = x1 := funext fun i => map_X _ _`. Establish `e2 : (fun i => map φ (x2 (R` using `R) (d := d) i)) = x2 := funext fun i => map_X _ _`. Establish `e3 : (fun i => map φ (x3 (R` using `R) (d := d) i)) = x3 := funext fun i => map_X _ _`. Establish `o1 : (fun i => map φ (op μ x1 x2 i)) = op (fun i => map φ (μ i)) x1 x2`. Use function extensionality and compare the values at `fun i => by unfold op; rw [mvPowerSeriesMap_evalTwoGroups φ c1 c2, e1, e2]`.

Establish `o2 : (fun i => map φ (op μ x2 x3 i)) = op (fun i => map φ (μ i)) x2 x3`. Use function extensionality and compare the values at `fun i => by unfold op; rw [mvPowerSeriesMap_evalTwoGroups φ c2 c3, e2, e3]`. Unfold `cob2`. Rewrite using `[map_sub, map_add, map_sub, mvPowerSeriesMap_evalTwoGroups φ c2 c3, mvPowerSeriesMap_evalTwoGroups φ (cc_op h c1 c2) c3, mvPowerSeriesMap_evalTwoGroups φ c1 (cc_op h c2 c3), mvPowerSeriesMap_evalTwoGroups φ c1 c2, o1, o2, e1, e2, e3]`.
-/
theorem map_formalGroupLawCoboundaryTwo (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map φ (cob2 μ c) = cob2 (fun i => map φ (μ i)) (map φ c) := by
  have e1 : (fun i => map φ (x1 (R := R) (d := d) i)) = x1 := funext fun i => map_X _ _
  have e2 : (fun i => map φ (x2 (R := R) (d := d) i)) = x2 := funext fun i => map_X _ _
  have e3 : (fun i => map φ (x3 (R := R) (d := d) i)) = x3 := funext fun i => map_X _ _
  have o1 : (fun i => map φ (op μ x1 x2 i)) = op (fun i => map φ (μ i)) x1 x2 :=
    funext fun i => by unfold op; rw [mvPowerSeriesMap_evalTwoGroups φ c1 c2, e1, e2]
  have o2 : (fun i => map φ (op μ x2 x3 i)) = op (fun i => map φ (μ i)) x2 x3 :=
    funext fun i => by unfold op; rw [mvPowerSeriesMap_evalTwoGroups φ c2 c3, e2, e3]
  unfold cob2
  rw [map_sub, map_add, map_sub, mvPowerSeriesMap_evalTwoGroups φ c2 c3, mvPowerSeriesMap_evalTwoGroups φ (cc_op h c1 c2) c3,
    mvPowerSeriesMap_evalTwoGroups φ c1 (cc_op h c2 c3), mvPowerSeriesMap_evalTwoGroups φ c1 c2, o1, o2, e1, e2, e3]

/- English proof (translation)
Unfold `cob2`. Rewrite using `[at2_lin c2 c3, at2_lin (cc_op h c1 c2) c3, at2_lin c1 (cc_op h c2 c3), at2_lin c1 c2]`. Simplify using `only [smul_sub, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem formalGroupLawCoboundaryTwo_smul_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (n : R) (c r : MvPowerSeries (Fin d ⊕ Fin d) R) :
    cob2 μ (n • c + r) = n • cob2 μ c + cob2 μ r := by
  unfold cob2
  rw [at2_lin c2 c3, at2_lin (cc_op h c1 c2) c3, at2_lin c1 (cc_op h c2 c3), at2_lin c1 c2]
  simp only [smul_sub, smul_add]
  abel

/- English proof (translation)
Unfold `cob2`. Rewrite using `[at2_zero c2 c3, at2_zero (cc_op h c1 c2) c3, at2_zero c1 (cc_op h c2 c3), at2_zero c1 c2]`. Simplify using the standard rewrite rules.
-/
theorem formalGroupLawCoboundaryTwo_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) : cob2 μ 0 = 0 := by
  unfold cob2
  rw [at2_zero c2 c3, at2_zero (cc_op h c1 c2) c3, at2_zero c1 (cc_op h c2 c3), at2_zero c1 c2]
  simp

/- English proof (translation)
Unfold `swap`. Rewrite using `[mvPowerSeriesMap_evalTwoGroups φ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]`. Simplify using `only [map_X]`.
-/
theorem map_swap (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map φ (swap c) = swap (map φ c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups φ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
  simp only [map_X]

/- English proof (translation)
Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, map_subst0 φ h, map_subst0 φ (fun _ => constantCoeff_X _), map_subst0 φ (fun _ => constantCoeff_X _)]`. Simplify using `only [map_X]`.
-/
theorem map_formalGroupLawCoboundaryOne_eq (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst0 φ h, map_subst0 φ (fun _ => constantCoeff_X _),
    map_subst0 φ (fun _ => constantCoeff_X _)]
  simp only [map_X]

/- English proof (translation)
Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, cc_subst0 h hf, cc_subst0 (fun _ => constantCoeff_X _) hf, cc_subst0 (fun _ => constantCoeff_X _) hf]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_formalGroupLawCoboundaryOne {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (cob1 μ f) = 0 := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, cc_subst0 h hf, cc_subst0 (fun _ => constantCoeff_X _) hf,
    cc_subst0 (fun _ => constantCoeff_X _) hf]
  simp

/- English proof (translation)
Rewrite using `[constantCoeff_map, hf, map_zero]`.
-/
theorem cc_map (φ : R →+* S) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    constantCoeff (map φ f) = 0 := by
  rw [constantCoeff_map, hf, map_zero]

/- English proof (translation)
Rewrite using `[MvPowerSeries.ext_iff]`. Use `forall_congr' fun α => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem mem_iff_map (J : Ideal R) (f : MvPowerSeries σ R) :
    (∀ α, coeff α f ∈ J) ↔ map (Ideal.Quotient.mk J) f = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun α => ?_
  rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Rewrite `hr`, the goal using `[mem_iff_map]`. Rewrite using `[map_formalGroupLawCoboundaryTwo _ h, hr, formalGroupLawCoboundaryTwo_zero fun i => cc_map _ (h i)]`.
-/
theorem coeff_formalGroupLawCoboundaryTwo_mem_ideal {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (J : Ideal R) {r : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hr : ∀ α, coeff α r ∈ J) : ∀ α, coeff α (cob2 μ r) ∈ J := by
  rw [mem_iff_map] at hr ⊢
  rw [map_formalGroupLawCoboundaryTwo _ h, hr, formalGroupLawCoboundaryTwo_zero fun i => cc_map _ (h i)]

/- English proof (translation)
Rewrite `hr`, the goal using `[mem_iff_map]`. Rewrite using `[map_swap, hr]`. Conclude with `at2_zero (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)`.
-/
theorem swap_mem (J : Ideal R) {r : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hr : ∀ α, coeff α r ∈ J) : ∀ α, coeff α (swap r) ∈ J := by
  rw [mem_iff_map] at hr ⊢
  rw [map_swap, hr]
  exact at2_zero (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)

end Nat

section Closure

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

/- English proof (translation)
The claim follows from `cc_map _ (h i)`.
-/
theorem cc_up (h : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up Q μ i) = 0 :=
  cc_map _ (h i)

/- English proof (translation)
Use `⟨by rw [map_add, hf.1, hg.1, add_zero], fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Take `⟨a, -, ha⟩` from `hf.2.1 i`. Take `⟨b, -, hb⟩` from `hg.2.1 i`. Conclude with `⟨a + b, trivial, by rw [map_add, ← ha, ← hb]; exact map_add _ _ _⟩`. Take `⟨a, -, ha⟩` from `hf.2.2 α`.

Take `⟨b, -, hb⟩` from `hg.2.2 α`. Conclude with `⟨a + b, trivial, by rw [formalCoboundary_add (cc_up h), map_add, ha, hb, map_add]⟩`.
-/
theorem ql_add (h : ∀ i, constantCoeff (μ i) = 0) {f g : MvPowerSeries (Fin d) Q}
    (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) : QL μ ⊤ (f + g) := by
  refine ⟨by rw [map_add, hf.1, hg.1, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, -, ha⟩ := hf.2.1 i
    obtain ⟨b, -, hb⟩ := hg.2.1 i
    exact ⟨a + b, trivial, by rw [map_add, ← ha, ← hb]; exact map_add _ _ _⟩
  · obtain ⟨a, -, ha⟩ := hf.2.2 α
    obtain ⟨b, -, hb⟩ := hg.2.2 α
    exact ⟨a + b, trivial, by rw [formalCoboundary_add (cc_up h), map_add, ha, hb, map_add]⟩

/- English proof (translation)
Use `⟨by rw [constantCoeff_smul, hf.1, smul_zero], fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Take `⟨a, -, ha⟩` from `hf.2.1 i`. Conclude with `⟨r * a, trivial, by rw [map_mul, ← ha]; exact coeff_smul _ _ _⟩`. Take `⟨a, -, ha⟩` from `hf.2.2 α`. Conclude with `⟨r * a, trivial, by rw [formalCoboundary_smul (cc_up h), coeff_smul, ha, map_mul]⟩`.
-/
theorem ql_smul (h : ∀ i, constantCoeff (μ i) = 0) (r : B) {f : MvPowerSeries (Fin d) Q}
    (hf : QL μ ⊤ f) : QL μ ⊤ (algebraMap B Q r • f) := by
  refine ⟨by rw [constantCoeff_smul, hf.1, smul_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, -, ha⟩ := hf.2.1 i
    exact ⟨r * a, trivial, by rw [map_mul, ← ha]; exact coeff_smul _ _ _⟩
  · obtain ⟨a, -, ha⟩ := hf.2.2 α
    exact ⟨r * a, trivial, by rw [formalCoboundary_smul (cc_up h), coeff_smul, ha, map_mul]⟩

/- English proof (translation)
Use `⟨cc_map _ hs, fun i => ⟨lin s i, trivial, coeff_map _ _ _⟩, fun α => ?_⟩` and prove the remaining obligations. Use `⟨coeff α (cob1 μ s), trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_map, map_formalGroupLawCoboundaryOne_eq _ h]`. Both sides reduce to the same expression.
-/
theorem ql_map (h : ∀ i, constantCoeff (μ i) = 0) {s : MvPowerSeries (Fin d) B}
    (hs : constantCoeff s = 0) : QL μ ⊤ (map (algebraMap B Q) s) := by
  refine ⟨cc_map _ hs, fun i => ⟨lin s i, trivial, coeff_map _ _ _⟩, fun α => ?_⟩
  refine ⟨coeff α (cob1 μ s), trivial, ?_⟩
  rw [← coeff_map, map_formalGroupLawCoboundaryOne_eq _ h]
  rfl

/- English proof (translation)
Unfold `comb`. Use `Finset.sum_induction _ (QL μ ⊤) (fun _ _ => ql_add h) ?_ fun i _ => ql_smul h _ (he i)` and prove the remaining obligations. Simplify using `using ql_map (Q := Q) h (s := 0) (map_zero _)`.
-/
theorem ql_comb (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → B)
    {e : ι → MvPowerSeries (Fin d) Q} (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  refine Finset.sum_induction _ (QL μ ⊤) (fun _ _ => ql_add h) ?_ fun i _ => ql_smul h _ (he i)
  simpa using ql_map (Q := Q) h (s := 0) (map_zero _)

end Closure

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ hF d μ hμ C _ _ hC Θ hΘ ι _ e he hb N' N hS f hf`. Take `⟨n, a, hap, hN, hna⟩` from `hS`. Establish `hc` using `hμ.const`. Establish `hnN : n ∈ N` using `hN ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self n)`. Establish `dec : ∀ b ∈ N, ∃ c r, r ∈ N' ∧ b = n * c + r`.

Introduce `b hb`. Rewrite `hb` using `[hN]`. Take `⟨r, hr, t, ht, rfl⟩` from `Submodule.mem_sup.1 hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ht`. Conclude with `⟨c, r, hr, by ring⟩`.

Establish `hker : ∀ b, θ b = 0 → b * n ∈ N'` using `fun b h => (hna b).2 (h ▸ dvd_zero a)`. Establish `hIN : RingHom.ker θ * N ≤ N'`. Use `Ideal.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨c, r, hr, rfl⟩` from `dec y hy`. Establish `: x * (n * c + r) = (x * n) * c + x * r` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (hker x hx)) (Ideal.mul_mem_left _ _ hr)`. Establish `h1 : ∀ α, ∃ c r : B, (α = 0 → c = 0) ∧ r ∈ N' ∧ coeff α (cob1 (up Q μ) f) = algebraMap B Q (n * c + r)`. Introduce `α`. Distinguish the cases in `h : α = 0`.

Use `⟨0, 0, fun _ => rfl, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[h, coeff_zero_eq_constantCoeff_apply, constantCoeff_formalGroupLawCoboundaryOne (cc_up hc) hf.1]`. Simplify using the standard rewrite rules. Take `⟨b, hb, hb'⟩` from `hf.2.2 α`. Take `⟨c, r, hr, rfl⟩` from `dec b hb`.

Conclude with `⟨c, r, fun h' => (h h').elim, hr, hb'⟩`. Use `choose c₁ r₁ hc0 hr₁ hcr using h1`. Set `c : MvPowerSeries (Fin d ⊕ Fin d) B` to `c₁`. Set `r : MvPowerSeries (Fin d ⊕ Fin d) B` to `r₁`. Establish `hr : ∀ α, coeff α r ∈ N'` using `hr₁`.

Establish `hcc : constantCoeff c = 0` using `hc0 0 rfl`. Establish `hcob : cob1 (up Q μ) f = map (algebraMap B Q) (n • c + r)`. Use extensionality with `α`. Rewrite using `[hcr, coeff_map, map_add (coeff α), coeff_smul]`. Both sides reduce to the same expression.

Establish `h2 : ∀ i, ∃ w t : B, t ∈ N' ∧ lin f i = algebraMap B Q (n * w + t)`. Introduce `i`. Take `⟨b, hb, hb'⟩` from `hf.2.1 i`. Take `⟨c, r, hr, rfl⟩` from `dec b hb`. Conclude with `⟨c, r, hr, hb'⟩`.

Use `choose w t ht hwt using h2`. Take `⟨k1, k2⟩` from `GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ hF d μ hμ N f (GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hμ N f hf)`. Establish `hco : ∀ α, a ∣ coeff α (cob2 (fun i => map θ (μ i)) (map θ c))`. Introduce `α`. Rewrite using `[← map_formalGroupLawCoboundaryTwo θ hc, coeff_map, ← hna]`.

Take `⟨b, hb, hb'⟩` from `k1 α`. Rewrite `hb'` using `[hcob]`. Establish `e1` using `map_formalGroupLawCoboundaryTwo (algebraMap B Q) hc (n • c + r)`. Express the relevant statement in the definitionally equal form `_ = cob2 (up Q μ) _ at e1`. Rewrite `hb'` using `[← e1, coeff_map, formalGroupLawCoboundaryTwo_smul_add hc, map_add (coeff α), coeff_smul]`.

Use `hF.inj hb'` as an intermediate fact. Establish `e2 : coeff α (cob2 μ c) * n = b - coeff α (cob2 μ r)` using `by rw [← this]; ring`. Rewrite using `[e2]`. Conclude with `sub_mem (hIN hb) (coeff_formalGroupLawCoboundaryTwo_mem_ideal hc N' hr α)`. Establish `hsw : ∀ α, a ∣ coeff α (swap (map θ c) - map θ c)`.

Introduce `α`. Rewrite using `[← map_swap, ← map_sub, coeff_map, ← hna]`. Rewrite `k2` using `[hcob, ← map_swap]`. Establish `k3` using `congrArg (coeff α) k2`. Rewrite `k3` using `[coeff_map, coeff_map]`.

Establish `k4` using `hF.inj k3`. Establish `e3 : swap (n • c + r) = n • swap c + swap r` using `at2_lin (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) n c r`. Rewrite `k4` using `[e3, map_add, map_add, coeff_smul, coeff_smul]`. Establish `e2 : coeff α (swap c - c) * n = coeff α r - coeff α (swap r)`. Rewrite using `[map_sub]`.

Take the linear combination `k4`. Rewrite using `[e2]`. Conclude with `sub_mem (hr α) (swap_mem N' hr α)`. Establish `hc' : ∀ i, constantCoeff (map θ (μ i)) = 0` using `hμ.law.const`. Take `⟨g₀, g1, g2, g3⟩` from `GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog p O C hC d _ hμ.law a hap (map θ c) (cc_map θ hcc) hco hsw`.

Take `⟨l, l1, l2, l3⟩` from `GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O C hC d _ hμ.law (fun i => θ (w i))`. Establish `hl : QL (fun i => map θ (μ i)) ⊤ l` using `⟨l1, fun i => ⟨_, trivial, l2 i⟩, fun α => ⟨0, trivial, by rw [l3]; simp⟩⟩`. Establish `hg` using `ql_add hc' g1 hl`. Take `⟨β, hβ, -⟩` from `hb.2 _ hg`. Establish `h3 : ∀ α, ∃ s : B, (α = 0 → s = 0) ∧ coeff α (g₀ + l - comb β fun i => map Θ (e i)) = algebraMap O C (θ s)`.

Introduce `α`. Distinguish the cases in `h : α = 0`. Use `⟨0, fun _ => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[h, coeff_zero_eq_constantCoeff_apply, map_sub, hg.1, (ql_comb hc' β hb.1).1]`. Simplify using the standard rewrite rules.

Take `⟨b, -, hb'⟩` from `hβ α`. Take `⟨s, rfl⟩` from `hF.surj b`. Conclude with `⟨s, fun h' => (h h').elim, hb'⟩`. Use `choose s₁ hs0 hs₁ using h3`. Set `s : MvPowerSeries (Fin d) B` to `s₁`.

Establish `hsc : constantCoeff s = 0` using `hs0 0 rfl`. Use `choose γ hγ using fun i => hF.surj (β i)`. Establish `hh : QL μ ⊤ (comb γ e + map (algebraMap B Q) s)` using `ql_add hc (ql_comb hc γ he) (ql_map hc hsc)`. Establish `hΘh : map Θ (comb γ e + map (algebraMap B Q) s) = g₀ + l`. Use extensionality with `α`.

Use `hs₁ α` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_iff_eq_add]`. Rewrite using `[this, coeff_map, map_add (coeff α), map_add Θ, coeff_map, hΘ, add_comm]`. Use `congr 1`. Unfold `comb`.

Simplify using `only [map_sum, coeff_smul, map_mul, hΘ, hγ, coeff_map]`. Establish `hup : (fun i => map Θ (up Q μ i)) = up C fun i => map θ (μ i)`. Use function extensionality and compare the values at `i`. Use extensionality with `α`. Simplify using `only [up, coeff_map, hΘ]`.

Establish `hdiff : f - comb (fun i => n * γ i) e - map (algebraMap B Q) (n • s) = f + (-algebraMap B Q n) • (comb γ e + map (algebraMap B Q) s)`. Use extensionality with `α`. Unfold `comb`. Simplify using `only [map_sub, map_add, map_sum, coeff_smul, coeff_map, map_mul, mul_add, Finset.mul_sum, neg_mul, mul_assoc, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun i => n * γ i, map (algebraMap B Q) (n • s), fun i => Ideal.mul_mem_right _ _ hnN, fun α => ⟨n * coeff α s, Ideal.mul_mem_right _ _ hnN, by rw [coeff_map, coeff_smul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hdiff]`. Generalize the expression as in `comb γ e + map (algebraMap B Q) s = h at hh hΘh`. Use `⟨by rw [map_add, constantCoeff_smul, hf.1, hh.1]; simp, fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Take `⟨u, -, hu⟩` from `hh.2.1 i`.

Establish `e1 : algebraMap O C (θ u) = algebraMap O C (θ (w i))`. Rewrite using `[← hΘ, ← hu, ← l2]`. Establish `e2 : Θ (lin h i) = lin (map Θ h) i` using `(coeff_map _ _ _).symm`. Establish `e3 : lin (g₀ + l) i = lin g₀ i + lin l i` using `map_add _ _ _`. Rewrite using `[e2, hΘh, e3, g2]`.

Simplify using the standard rewrite rules. Establish `e4 : θ (w i - u) = 0` using `by rw [map_sub, hC.inj e1, sub_self]`. Use `⟨(w i - u) * n + t i, add_mem (hker _ e4) (ht i), ?_⟩` and prove the remaining obligations. Establish `e5 : lin (f + (-algebraMap B Q n) • h) i = lin f i + (-algebraMap B Q n) * lin h i`. Unfold `lin`.

Rewrite using `[map_add, coeff_smul]`. Rewrite using `[e5, hwt, hu]`. Simplify using `only [map_add, map_mul, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, -, hu⟩` from `hh.2.2 α`.

Take `⟨v, hv, hv'⟩` from `g3 α`. Rewrite `hv'` using `[map_sub, coeff_map, coeff_map, sub_eq_iff_eq_add]`. Establish `e1 : algebraMap O C (θ u) = algebraMap O C (v + θ (coeff α c))`. Rewrite using `[← hΘ, ← hu, ← coeff_map, map_formalGroupLawCoboundaryOne_eq Θ (cc_up hc), hup, hΘh, formalCoboundary_add (cc_up hc'), l3, add_zero, hv', map_add]`. Establish `e4 : a ∣ θ (coeff α c - u)`.

Rewrite using `[map_sub, hC.inj e1]`. Simplify using `using Ideal.mem_span_singleton.1 hv`. Use `⟨(coeff α c - u) * n + coeff α r, add_mem ((hna _).2 e4) (hr α), ?_⟩` and prove the remaining obligations. Rewrite using `[formalCoboundary_add (cc_up hc), formalCoboundary_smul (cc_up hc), map_add, coeff_smul, hu, hcob, coeff_map, map_add (coeff α), coeff_smul]`. Simplify using `only [map_add, map_mul, map_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem step_generation : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ f, QL μ N f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) ∧ In N s ∧ QL μ N' (f - comb b e - s) := by
  intro p _ B O Q _ _ _ _ θ hF d μ hμ C _ _ hC Θ hΘ ι _ e he hb N' N hS f hf
  obtain ⟨n, a, hap, hN, hna⟩ := hS
  have hc := hμ.const
  have hnN : n ∈ N := hN ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self n)
  have dec : ∀ b ∈ N, ∃ c r, r ∈ N' ∧ b = n * c + r := by
    intro b hb
    rw [hN] at hb
    obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.1 hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    exact ⟨c, r, hr, by ring⟩
  have hker : ∀ b, θ b = 0 → b * n ∈ N' := fun b h => (hna b).2 (h ▸ dvd_zero a)
  have hIN : RingHom.ker θ * N ≤ N' := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨c, r, hr, rfl⟩ := dec y hy
    have : x * (n * c + r) = (x * n) * c + x * r := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (hker x hx)) (Ideal.mul_mem_left _ _ hr)

  have h1 : ∀ α, ∃ c r : B, (α = 0 → c = 0) ∧ r ∈ N' ∧
      coeff α (cob1 (up Q μ) f) = algebraMap B Q (n * c + r) := by
    intro α
    by_cases h : α = 0
    · refine ⟨0, 0, fun _ => rfl, zero_mem _, ?_⟩
      rw [h, coeff_zero_eq_constantCoeff_apply, constantCoeff_formalGroupLawCoboundaryOne (cc_up hc) hf.1]
      simp
    · obtain ⟨b, hb, hb'⟩ := hf.2.2 α
      obtain ⟨c, r, hr, rfl⟩ := dec b hb
      exact ⟨c, r, fun h' => (h h').elim, hr, hb'⟩
  choose c₁ r₁ hc0 hr₁ hcr using h1
  let c : MvPowerSeries (Fin d ⊕ Fin d) B := c₁
  let r : MvPowerSeries (Fin d ⊕ Fin d) B := r₁
  have hr : ∀ α, coeff α r ∈ N' := hr₁
  have hcc : constantCoeff c = 0 := hc0 0 rfl
  have hcob : cob1 (up Q μ) f = map (algebraMap B Q) (n • c + r) := by
    ext α
    rw [hcr, coeff_map, map_add (coeff α), coeff_smul]
    rfl
  have h2 : ∀ i, ∃ w t : B, t ∈ N' ∧ lin f i = algebraMap B Q (n * w + t) := by
    intro i
    obtain ⟨b, hb, hb'⟩ := hf.2.1 i
    obtain ⟨c, r, hr, rfl⟩ := dec b hb
    exact ⟨c, r, hr, hb'⟩
  choose w t ht hwt using h2
  obtain ⟨k1, k2⟩ := GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ hF d μ hμ N f (GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hμ N f hf)
  have hco : ∀ α, a ∣ coeff α (cob2 (fun i => map θ (μ i)) (map θ c)) := by
    intro α
    rw [← map_formalGroupLawCoboundaryTwo θ hc, coeff_map, ← hna]
    obtain ⟨b, hb, hb'⟩ := k1 α
    rw [hcob] at hb'
    have e1 := map_formalGroupLawCoboundaryTwo (algebraMap B Q) hc (n • c + r)
    change _ = cob2 (up Q μ) _ at e1
    rw [← e1, coeff_map, formalGroupLawCoboundaryTwo_smul_add hc, map_add (coeff α), coeff_smul] at hb'
    have := hF.inj hb'
    have e2 : coeff α (cob2 μ c) * n = b - coeff α (cob2 μ r) := by rw [← this]; ring
    rw [e2]
    exact sub_mem (hIN hb) (coeff_formalGroupLawCoboundaryTwo_mem_ideal hc N' hr α)
  have hsw : ∀ α, a ∣ coeff α (swap (map θ c) - map θ c) := by
    intro α
    rw [← map_swap, ← map_sub, coeff_map, ← hna]
    rw [hcob, ← map_swap] at k2
    have k3 := congrArg (coeff α) k2
    rw [coeff_map, coeff_map] at k3
    have k4 := hF.inj k3
    have e3 : swap (n • c + r) = n • swap c + swap r :=
      at2_lin (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) n c r
    rw [e3, map_add, map_add, coeff_smul, coeff_smul] at k4
    have e2 : coeff α (swap c - c) * n = coeff α r - coeff α (swap r) := by
      rw [map_sub]; linear_combination k4
    rw [e2]
    exact sub_mem (hr α) (swap_mem N' hr α)
  have hc' : ∀ i, constantCoeff (map θ (μ i)) = 0 := hμ.law.const
  obtain ⟨g₀, g1, g2, g3⟩ := GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog p O C hC d _ hμ.law a hap (map θ c) (cc_map θ hcc) hco hsw
  obtain ⟨l, l1, l2, l3⟩ := GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O C hC d _ hμ.law (fun i => θ (w i))
  have hl : QL (fun i => map θ (μ i)) ⊤ l :=
    ⟨l1, fun i => ⟨_, trivial, l2 i⟩, fun α => ⟨0, trivial, by rw [l3]; simp⟩⟩
  have hg := ql_add hc' g1 hl
  obtain ⟨β, hβ, -⟩ := hb.2 _ hg
  have h3 : ∀ α, ∃ s : B, (α = 0 → s = 0) ∧
      coeff α (g₀ + l - comb β fun i => map Θ (e i)) = algebraMap O C (θ s) := by
    intro α
    by_cases h : α = 0
    · refine ⟨0, fun _ => rfl, ?_⟩
      rw [h, coeff_zero_eq_constantCoeff_apply, map_sub, hg.1, (ql_comb hc' β hb.1).1]
      simp
    · obtain ⟨b, -, hb'⟩ := hβ α
      obtain ⟨s, rfl⟩ := hF.surj b
      exact ⟨s, fun h' => (h h').elim, hb'⟩
  choose s₁ hs0 hs₁ using h3
  let s : MvPowerSeries (Fin d) B := s₁
  have hsc : constantCoeff s = 0 := hs0 0 rfl
  choose γ hγ using fun i => hF.surj (β i)
  have hh : QL μ ⊤ (comb γ e + map (algebraMap B Q) s) :=
    ql_add hc (ql_comb hc γ he) (ql_map hc hsc)
  have hΘh : map Θ (comb γ e + map (algebraMap B Q) s) = g₀ + l := by
    ext α
    have := hs₁ α
    rw [map_sub, sub_eq_iff_eq_add] at this
    rw [this, coeff_map, map_add (coeff α), map_add Θ, coeff_map, hΘ, add_comm]
    congr 1
    unfold comb
    simp only [map_sum, coeff_smul, map_mul, hΘ, hγ, coeff_map]
  have hup : (fun i => map Θ (up Q μ i)) = up C fun i => map θ (μ i) := by
    funext i
    ext α
    simp only [up, coeff_map, hΘ]
  have hdiff : f - comb (fun i => n * γ i) e - map (algebraMap B Q) (n • s) =
      f + (-algebraMap B Q n) • (comb γ e + map (algebraMap B Q) s) := by
    ext α
    unfold comb
    simp only [map_sub, map_add, map_sum, coeff_smul, coeff_map, map_mul, mul_add, Finset.mul_sum,
      neg_mul, mul_assoc, Finset.sum_neg_distrib]
    ring
  refine ⟨fun i => n * γ i, map (algebraMap B Q) (n • s), fun i => Ideal.mul_mem_right _ _ hnN,
    fun α => ⟨n * coeff α s, Ideal.mul_mem_right _ _ hnN, by rw [coeff_map, coeff_smul]⟩, ?_⟩
  rw [hdiff]
  generalize comb γ e + map (algebraMap B Q) s = h at hh hΘh
  refine ⟨by rw [map_add, constantCoeff_smul, hf.1, hh.1]; simp, fun i => ?_, fun α => ?_⟩
  · obtain ⟨u, -, hu⟩ := hh.2.1 i
    have e1 : algebraMap O C (θ u) = algebraMap O C (θ (w i)) := by
      rw [← hΘ, ← hu, ← l2]
      have e2 : Θ (lin h i) = lin (map Θ h) i := (coeff_map _ _ _).symm
      have e3 : lin (g₀ + l) i = lin g₀ i + lin l i := map_add _ _ _
      rw [e2, hΘh, e3, g2]
      simp
    have e4 : θ (w i - u) = 0 := by rw [map_sub, hC.inj e1, sub_self]
    refine ⟨(w i - u) * n + t i, add_mem (hker _ e4) (ht i), ?_⟩
    have e5 : lin (f + (-algebraMap B Q n) • h) i = lin f i + (-algebraMap B Q n) * lin h i := by
      unfold lin
      rw [map_add, coeff_smul]
    rw [e5, hwt, hu]
    simp only [map_add, map_mul, map_sub]
    ring
  · obtain ⟨u, -, hu⟩ := hh.2.2 α
    obtain ⟨v, hv, hv'⟩ := g3 α
    rw [map_sub, coeff_map, coeff_map, sub_eq_iff_eq_add] at hv'
    have e1 : algebraMap O C (θ u) = algebraMap O C (v + θ (coeff α c)) := by
      rw [← hΘ, ← hu, ← coeff_map, map_formalGroupLawCoboundaryOne_eq Θ (cc_up hc), hup, hΘh, formalCoboundary_add (cc_up hc'), l3,
        add_zero, hv', map_add]
    have e4 : a ∣ θ (coeff α c - u) := by
      rw [map_sub, hC.inj e1]
      simpa using Ideal.mem_span_singleton.1 hv
    refine ⟨(coeff α c - u) * n + coeff α r, add_mem ((hna _).2 e4) (hr α), ?_⟩
    rw [formalCoboundary_add (cc_up hc), formalCoboundary_smul (cc_up hc), map_add, coeff_smul, hu, hcob, coeff_map,
      map_add (coeff α), coeff_smul]
    simp only [map_add, map_mul, map_sub]
    ring

end GlobalTheory.QLog.StepGen
