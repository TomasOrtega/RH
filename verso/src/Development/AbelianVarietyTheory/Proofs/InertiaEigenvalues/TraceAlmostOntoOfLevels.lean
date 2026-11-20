import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AlmostTrace

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Unfold `Ks Kinf`. Conclude with `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun (x : Om l) (hx : x ^ l ^ i = 1) => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _`.
-/
theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono _ _ _
    fun (x : Om l) (hx : x ^ l ^ i = 1) => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _

/- English proof (translation)
Introduce `i j hij`. Unfold `Ks`. Use `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _` and prove the remaining obligations. Take `⟨c, hc⟩` from `pow_dvd_pow l hij`. Establish `hx' : x ^ l ^ i = 1` using `hx`.

Use `show x ^ l ^ j = 1`. Rewrite using `[hc, pow_mul, hx', one_pow]`.
-/
theorem Ks_mono (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]

/- English proof (translation)
Use `le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)` and prove the remaining obligations. Establish `h0 : K0 K ≤ Ks K 0`. Unfold `Ks`. Conclude with `le_sup_left`. Unfold `Kinf`.

Use `sup_le (h0.trans (le_iSup (Ks K) 0)) ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `x ⟨j, hj⟩`. Establish `hx : x ∈ Ks K j`. Unfold `Ks`.

Conclude with `(le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _) (IntermediateField.subset_adjoin _ _ hj)`. Conclude with `le_iSup (Ks K) j hx`.
-/
theorem Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx

/- English proof (translation)
Rewrite `hx` using `[Kinf_eq_iSup]`. Establish `h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l))` using `hx`. Rewrite `h` using `[IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion]`. Conclude with `h`.
-/
theorem exists_mem_Ks (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h

/- English proof (translation)
Unfold `Hinf Gj`. Conclude with `IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)`.
-/
theorem Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)

/- English proof (translation)
Establish `hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l)))` using `fun i => InfiniteGalois.fixingSubgroup_isClosed (Ks K i)`. Establish `hanti : Antitone fun i => ((Gj K i : Set (GQ l)))` using `fun i j hij => IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)`. Establish `hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅`. Use extensionality with `σ`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`.

Introduce and unpack `⟨hσU, hσ⟩`. Apply `hσU` to reduce the goal to its premises. Apply `hH` to reduce the goal to its premises. Use `show σ ∈ (Kinf K).fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Take `⟨i, hi⟩` from `exists_mem_Ks K hx`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi`. Take `⟨i₀, hi₀⟩` from `hU.isClosed_compl.isCompact.elim_directed_family_closed (fun i => (Gj K i : Set (GQ l))) hcl hinter hanti.directed_ge`. Use `⟨i₀, fun i hi σ hσ => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hσU`. Establish `hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l))` using `⟨hσU, hanti hi hσ⟩`. Rewrite `hmem` using `[hi₀]`. Conclude with `hmem`.
-/
theorem exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl hinter hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  rw [hi₀] at hmem
  exact hmem

/- English proof (translation)
Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]`. Introduce `h hh`. Establish `hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup` using `fun s hs => (hrep (h * s) (mul_mem hh (hS s hs))).exists`. Use `choose! φ hφS hφF using hex`. Rewrite using `[map_sum]`.

Use `Finset.sum_nbij φ hφS ?_ ?_ ?_` and prove the remaining obligations. Introduce `s₁ hs₁ s₂ hs₂ he`. Establish `h₁` using `hφF s₁ hs₁`. Establish `h₂` using `hφF s₂ hs₂`. Rewrite `h₁` using `[he]`.

Establish `hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup`. Use `mul_mem (inv_mem h₁) h₂` as an intermediate fact. Rewrite `this` using `[show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group]`. Then use the resulting hypothesis. Conclude with `(hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩`. Introduce `t ht`.

Take `⟨s, ⟨hs, hsm⟩, -⟩` from `hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))`. Use `⟨s, Finset.mem_coe.2 hs, ?_⟩` and prove the remaining obligations. Establish `hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup`. Use `inv_mem hsm` as an intermediate fact. Rewrite `this` using `[show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group]`. Then use the resulting hypothesis.

Conclude with `(hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩`. Introduce `s hs`. Establish `hfix` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb`. Establish `key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b)`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]`.

Rewrite `key` using `[hfix]`. Conclude with `key.symm`.
-/
theorem sum_mem_Kinf (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex
  rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm

/- English proof (translation)
Establish `hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x`. Introduce `s hs t ht hst`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `hst` to reduce the goal to its premises.

Establish `hmem : s⁻¹ * t ∈ L.fixingSubgroup` using `(IntermediateField.mem_fixingSubgroup_iff _ _).2 hne`. Conclude with `(hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩`. Use `choose! xf hxL hxne using hsep`. Set `T : Finset (Om l)` to `((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2`. Establish `hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l))`.

Introduce `s hs t ht hst`. Simplify using `only [T, Finset.coe_image, Finset.coe_filter]`. Conclude with `⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩`. Set `L' : FinExt l` to `⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)), IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩`. Establish `hL'L : L'.1 ≤ L` using `by show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L`.

Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Simplify using `only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx`. Take `⟨p, ⟨hp, hpne⟩, rfl⟩` from `hx`. Take `⟨hp1, hp2⟩` from `Finset.mem_product.1 hp`.

Conclude with `hxL p.1 hp1 p.2 hp2 hpne`. Establish `: FiniteDimensional ℚ_[l] L'.1` using `L'.2`. Set `U : Set (GQ l)` to `⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}`. Establish `hUo : IsOpen U` using `isOpen_biUnion fun s _ => (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)`. Establish `hHU : (Hinf K : Set (GQ l)) ⊆ U`.

Introduce `σ hσ`. Take `⟨s, ⟨hs, hsm⟩, -⟩` from `hrep σ hσ`. Conclude with `Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)`. Take `⟨i₀, hi₀⟩` from `exists_Gj_subset K hUo hHU`. Use `⟨L', hL'L, i₀, fun i hi h hh => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, hsm⟩` from `Set.mem_iUnion₂.1 (hi₀ i hi hh)`. Establish `hsG : s⁻¹ * h ∈ Gj K i` using `mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh`. Use `⟨s, ⟨hs, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.fixingSubgroup_sup]`. Conclude with `⟨hsm, hsG⟩`.

Introduce and unpack `t ⟨ht, htm⟩`. Assume the negation of the conclusion as `hts`. Establish `htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup` using `IntermediateField.fixingSubgroup_antitone le_sup_left htm`. Establish `hm : t⁻¹ * s ∈ L'.1.fixingSubgroup`. Use `mul_mem htm' (inv_mem hsm)` as an intermediate fact.

Rewrite `this` using `[show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group]`. Then use the resulting hypothesis. Establish `hxT : xf t s ∈ L'.1` using `IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)`. Conclude with `hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)`.
-/
theorem exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)

/- English proof (translation)
Distinguish the cases in `ha0 : a = 0`. Conclude with `⟨0, zero_mem _, by simp, by simp [ha0]⟩`. Take `⟨L', hL'L, i₀, hi₀⟩` from `exists_finite_level K L S hS hrep`. Establish `hε : 0 < 1 - ‖a‖` using `by linarith`. Take `⟨i₁, hi₁⟩` from `hd K L' (1 - ‖a‖) hε`.

Take `⟨b₀, hb₀, hb₀1, htr⟩` from `hi₁ (max i₀ i₁) (le_max_right _ _) S (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))`. Establish `hb₀L : b₀ ∈ L` using `(sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀`. Establish `htK : ∑ s ∈ S, s b₀ ∈ Kinf K` using `sum_mem_Kinf K L S hS hrep hb₀L`. Use `set t := ∑ s ∈ S, s b₀ with ht`. Establish `hta : ‖a‖ ≤ ‖t‖` using `by linarith`.

Establish `ht0 : t ≠ 0`. Introduce `h0`. Rewrite `hta` using `[h0, norm_zero]`. Conclude with `ha0 (norm_le_zero_iff.1 hta)`. Establish `hc : a / t ∈ Kinf K` using `div_mem ha htK`.

Use `⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_div]`. Establish `h1 : ‖a‖ / ‖t‖ ≤ 1` using `(div_le_one (norm_pos_iff.2 ht0)).2 hta`. Combine the equalities or inequalities in the displayed calculation. Establish `hfix : ∀ s ∈ S, s (a / t) = a / t` using `fun s hs => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc`.

Rewrite using `[Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum, ← ht, div_mul_cancel₀ a ht0]`.
-/
theorem trace_almost_onto_of_levels
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]

end GlobalTheory.Cyc.AlmostTrace
