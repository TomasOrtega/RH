import Formalism.PeriodIntegrals.OrbRestr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.KillSubst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

variable {σ τ υ R : Type*} [CommRing R]

/- English proof (translation)
Simplify `(substAlgHom ha).map_zero` using `[coe_substAlgHom]`.
-/
theorem subst_zero_fam {a : σ → MvPowerSeries τ R} (ha : HasSubst a) : subst a (0 : MvPowerSeries σ R) = 0 := by
  simpa [coe_substAlgHom] using (substAlgHom ha).map_zero

/- English proof (translation)
Establish `hc : ∀ (F : MvPowerSeries τ R) (x : υ →₀ ℕ), coeff x (killCompl e F) = coeff (embDomain e x) F` using `fun F x => rfl`. Establish `key : ∀ (x : υ →₀ ℕ) (d : τ →₀ ℕ), coeff (embDomain e x) (d.prod fun s n => g s ^ n) = coeff x (d.prod fun s n => killCompl e (g s) ^ n)`. Introduce `x d`. Rewrite using `[← hc, map_finsuppProd]`. Simplify using `only [map_pow]`.

Use extensionality with `x`. Rewrite using `[hc, coeff_subst hg, coeff_subst hK]`. Repeatedly rewrite using `[key x]`. Establish `hRR : (∑ᶠ d' : υ →₀ ℕ, coeff d' (killCompl e f) • coeff x (d'.prod fun s n => K s ^ n)) = ∑ᶠ d ∈ Set.range (embDomain e : (υ →₀ ℕ) → τ →₀ ℕ), coeff d f • coeff x (d.prod fun s n => killCompl e (g s) ^ n)`. Rewrite using `[finsum_mem_range (embDomain_injective e)]`.

Use `finsum_congr fun d' => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.prod_embDomain, hc]`. Simplify using `only [h1]`. Rewrite using `[hRR]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[finsum_eq_if]`. Use `split_ifs with hd`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hnot⟩ : ∃ t ∈ d.support, ¬ ∃ w, e w = t := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hd ⟨_, embDomain_comapDomain (f := e) (g := d) (fun t ht => hall t ht)⟩`. Establish `hz : (d.prod fun s n => killCompl e (g s) ^ n) = 0` using `Finset.prod_eq_zero ht (by show killCompl e (g t) ^ d t = 0`. Rewrite using `[h0 t hnot]`. Conclude with `zero_pow (Finsupp.mem_support_iff.mp ht))`.

Rewrite using `[hz, map_zero, smul_zero]`.
-/
theorem killCompl_subst_of (e : υ ↪ τ) (g : τ → MvPowerSeries τ R) (K : υ → MvPowerSeries υ R)
    (hg : HasSubst g) (hK : HasSubst K) (h1 : ∀ w, killCompl e (g (e w)) = K w)
    (h0 : ∀ t, (¬ ∃ w, e w = t) → killCompl e (g t) = 0) (f : MvPowerSeries τ R) :
    killCompl e (subst g f) = subst K (killCompl e f) := by
  have hc : ∀ (F : MvPowerSeries τ R) (x : υ →₀ ℕ),
      coeff x (killCompl e F) = coeff (embDomain e x) F := fun F x => rfl
  have key : ∀ (x : υ →₀ ℕ) (d : τ →₀ ℕ), coeff (embDomain e x) (d.prod fun s n => g s ^ n) =
      coeff x (d.prod fun s n => killCompl e (g s) ^ n) := by
    intro x d
    rw [← hc, map_finsuppProd]
    simp only [map_pow]
  ext x
  rw [hc, coeff_subst hg, coeff_subst hK]
  simp_rw [key x]
  have hRR : (∑ᶠ d' : υ →₀ ℕ, coeff d' (killCompl e f) • coeff x (d'.prod fun s n => K s ^ n)) =
      ∑ᶠ d ∈ Set.range (embDomain e : (υ →₀ ℕ) → τ →₀ ℕ),
        coeff d f • coeff x (d.prod fun s n => killCompl e (g s) ^ n) := by
    rw [finsum_mem_range (embDomain_injective e)]
    refine finsum_congr fun d' => ?_
    rw [Finsupp.prod_embDomain, hc]
    simp only [h1]
  rw [hRR]
  refine finsum_congr fun d => ?_
  rw [finsum_eq_if]
  split_ifs with hd
  · rfl
  · obtain ⟨t, ht, hnot⟩ : ∃ t ∈ d.support, ¬ ∃ w, e w = t := by
      by_contra hall
      push_neg at hall
      exact hd ⟨_, embDomain_comapDomain (f := e) (g := d) (fun t ht => hall t ht)⟩
    have hz : (d.prod fun s n => killCompl e (g s) ^ n) = 0 :=
      Finset.prod_eq_zero ht (by
        show killCompl e (g t) ^ d t = 0
        rw [h0 t hnot]
        exact zero_pow (Finsupp.mem_support_iff.mp ht))
    rw [hz, map_zero, smul_zero]

/- English proof (translation)
Use `show jetLogG l d w 0 = 0`. Unfold `jetLogG`. Use `Finset.sum_eq_zero fun e _ => if_neg fun h => ?_` and prove the remaining obligations. Conclude with `pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)`.
-/
theorem cc_jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (w : ZMod d × β) :
    constantCoeff (jetLogG l d w) = 0 := by
  show jetLogG l d w 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

/- English proof (translation)
Use `show logPl D p v 0 = 0`. Unfold `logPl`. Use `Finset.sum_eq_zero fun e _ => if_neg fun h => ?_` and prove the remaining obligations. Conclude with `pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)`.
-/
theorem cc_logPl (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) :
    constantCoeff (logPl D p v) = 0 := by
  show logPl D p v 0 = 0
  unfold logPl
  refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Unfold `OJ.B3 at h`. Establish `h0` using `h 0 (by rwa [coeff_zero_eq_constantCoeff_apply])`. Conclude with `h0.1 (by simp [OJ.bideg])`.
-/
theorem constant_coeff_zero_of_vanishing_alt (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : OJ.B3 l d be) :
    constantCoeff be = 0 := by
  by_contra hc
  unfold OJ.B3 at h
  have h0 := h 0 (by rwa [coeff_zero_eq_constantCoeff_apply])
  exact h0.1 (by simp [OJ.bideg])

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[show coeff x (killCompl e (X t : MvPowerSeries τ R)) = coeff (embDomain e x) (X t : MvPowerSeries τ R) from rfl, coeff_X, if_neg, map_zero]`. Introduce `hx`. Establish `h1 : (embDomain e x) t ≠ 0` using `by rw [hx]; simp`. Rewrite `h1` using `[← Finsupp.mem_support_iff, Finsupp.support_embDomain, Finset.mem_map]`.

Take `⟨w, _, hw⟩` from `h1`. Conclude with `ht ⟨w, hw⟩`.
-/
private theorem killCompl_X_of_not_mem_range (e : υ ↪ τ) (t : τ) (ht : ¬ ∃ w, e w = t) :
    killCompl e (X t : MvPowerSeries τ R) = 0 := by
  ext x
  rw [show coeff x (killCompl e (X t : MvPowerSeries τ R)) =
      coeff (embDomain e x) (X t : MvPowerSeries τ R) from rfl, coeff_X, if_neg, map_zero]
  intro hx
  have h1 : (embDomain e x) t ≠ 0 := by rw [hx]; simp
  rw [← Finsupp.mem_support_iff, Finsupp.support_embDomain, Finset.mem_map] at h1
  obtain ⟨w, _, hw⟩ := h1
  exact ht ⟨w, hw⟩

/- English proof (translation)
Unfold `IsReps at hR`. Use `killCompl_X_of_not_mem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨s0, c⟩, hw⟩`. Establish `h1 : orbMap D p r s0 = orbMap D p r' s` using `congrArg Prod.fst hw`. Conclude with `hne ((hR (orbMap D p r' s)).unique ⟨hr, s0.val, h1⟩ ⟨hr', s.val, rfl⟩).symm`.
-/
theorem killCompl_orbX_off (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    {r r' : Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (hne : r' ≠ r) (s : ZMod (nP D p)) (a : Fin N0) (b : Fin N1) :
    killCompl (orbEmb D p r (Fin N0 × Fin N1))
      (X (orbMap D p r' s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = 0 := by
  unfold IsReps at hR
  refine killCompl_X_of_not_mem_range _ _ ?_
  rintro ⟨⟨s0, c⟩, hw⟩
  have h1 : orbMap D p r s0 = orbMap D p r' s := congrArg Prod.fst hw
  exact hne ((hR (orbMap D p r' s)).unique ⟨hr, s0.val, h1⟩ ⟨hr', s.val, rfl⟩).symm

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)`.
-/
theorem hasSubst_orbX (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (r : Pl D) (a : Fin N0) (b : Fin N1) :
    HasSubst (fun s : ZMod (nP D p) =>
      (X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) := hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)

/- English proof (translation)
Use `show coeff (embDomain e x) (subst a f) = _`. Rewrite using `[coeff_subst ha]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations. Rewrite using `[show coeff (embDomain e x) (d.prod fun s n => a s ^ n) = coeff x (killCompl e (d.prod fun s n => a s ^ n)) from rfl, map_finsuppProd]`. Simplify using `only [map_pow]`.
-/
private theorem coeff_killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (x : υ →₀ ℕ) :
    coeff x (killCompl e (subst a f)) =
      ∑ᶠ d : σ →₀ ℕ, coeff d f • coeff x (d.prod fun s n => killCompl e (a s) ^ n) := by
  show coeff (embDomain e x) (subst a f) = _
  rw [coeff_subst ha]
  refine finsum_congr fun d => ?_
  rw [show coeff (embDomain e x) (d.prod fun s n => a s ^ n) =
      coeff x (killCompl e (d.prod fun s n => a s ^ n)) from rfl, map_finsuppProd]
  simp only [map_pow]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[show coeff x (killCompl e (X (e w) : MvPowerSeries τ R)) = coeff (embDomain e x) (X (e w) : MvPowerSeries τ R) from rfl, coeff_X, coeff_X]`. Distinguish the cases in `hx : x = single w 1`. Rewrite using `[if_pos hx, if_pos (by rw [hx, embDomain_single])]`. Rewrite using `[if_neg hx, if_neg (fun h => hx (embDomain_injective e (h.trans (embDomain_single e w 1).symm)))]`.
-/
private theorem killCompl_X_emb (e : υ ↪ τ) (w : υ) :
    killCompl e (X (e w) : MvPowerSeries τ R) = X w := by
  ext x
  rw [show coeff x (killCompl e (X (e w) : MvPowerSeries τ R)) =
      coeff (embDomain e x) (X (e w) : MvPowerSeries τ R) from rfl, coeff_X, coeff_X]
  by_cases hx : x = single w 1
  · rw [if_pos hx, if_pos (by rw [hx, embDomain_single])]
  · rw [if_neg hx, if_neg (fun h => hx (embDomain_injective e (h.trans (embDomain_single e w 1).symm)))]

/- English proof (translation)
Unfold `beAll`. Rewrite using `[map_sum, Finset.sum_eq_single r ?_ (fun h => absurd hr h)]`. Rewrite using `[map_smul, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hX : ∀ s : ZMod (nP D p), killCompl (orbEmb D p r (Fin N0 × Fin N1)) (X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = X (s, a, b)` using `fun s => killCompl_X_emb (orbEmb D p r (Fin N0 × Fin N1)) (s, a, b)`. Use extensionality with `x`. Rewrite using `[coeff_killCompl_subst _ (hasSubst_orbX D p r a b), coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]`.

Simplify using `only [hX]`. Introduce `r' hr' hne`. Rewrite using `[map_smul, map_sum, Finset.sum_eq_zero, smul_zero]`. Introduce `a _`. Rewrite using `[map_sum]`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[coeff_killCompl_subst _ (hasSubst_orbX D p r' a b), map_zero]`. Use `finsum_eq_zero_of_forall_eq_zero fun d => ?_` and prove the remaining obligations. Simplify using `only [killCompl_orbX_off D p R hR hr hr' hne]`.

Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Rewrite using `[coeff_zero_eq_constantCoeff_apply, hcc r' hr', zero_smul]`. Take `⟨s, hs⟩` from `Finsupp.support_nonempty_iff.mpr hd`. Use `smul_eq_zero_of_right _ ((congrArg (coeff x) ?_).trans (map_zero _))` and prove the remaining obligations.

Conclude with `Finset.prod_eq_zero hs (zero_pow (Finsupp.mem_support_iff.mp hs))`.
-/
theorem killCompl_beAll (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) {r : Pl D} (hr : r ∈ R) :
    killCompl (orbEmb D p r (Fin N0 × Fin N1)) (beAll D p (N0 := N0) (N1 := N1) R sg be) =
      sg r • ∑ a : Fin N0, ∑ b : Fin N1, subst (fun s : ZMod (nP D p) =>
        (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) (be r) := by
  unfold beAll
  rw [map_sum, Finset.sum_eq_single r ?_ (fun h => absurd hr h)]
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hX : ∀ s : ZMod (nP D p), killCompl (orbEmb D p r (Fin N0 × Fin N1))
        (X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = X (s, a, b) :=
      fun s => killCompl_X_emb (orbEmb D p r (Fin N0 × Fin N1)) (s, a, b)
    ext x
    rw [coeff_killCompl_subst _ (hasSubst_orbX D p r a b),
      coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
    simp only [hX]
  · intro r' hr' hne
    rw [map_smul, map_sum, Finset.sum_eq_zero, smul_zero]
    intro a _
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    ext x
    rw [coeff_killCompl_subst _ (hasSubst_orbX D p r' a b), map_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    simp only [killCompl_orbX_off D p R hR hr hr' hne]
    by_cases hd : d = 0
    · subst hd
      rw [coeff_zero_eq_constantCoeff_apply, hcc r' hr', zero_smul]
    · obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
      refine smul_eq_zero_of_right _ ((congrArg (coeff x) ?_).trans (map_zero _))
      exact Finset.prod_eq_zero hs (zero_pow (Finsupp.mem_support_iff.mp hs))

end PI.OrbJet.OrbW
