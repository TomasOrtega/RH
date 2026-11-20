import Mathlib
open MeasureTheory Topology

namespace GlobalTheory.KernelCovolume

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
The claim follows from `mul_left_cancel (a := c 0) (by rw [mul_one, ← hca, add_zero])`.
-/
lemma c_zero {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) : c 0 = 1 :=
  mul_left_cancel (a := c 0) (by rw [mul_one, ← hca, add_zero])

/- English proof (translation)
The claim follows from `inv_eq_of_mul_eq_one_right (by rw [← hca, add_neg_cancel, c_zero hca])`.
-/
lemma c_neg {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (r : ℝ) : (c r)⁻¹ = c (-r) :=
  inv_eq_of_mul_eq_one_right (by rw [← hca, add_neg_cancel, c_zero hca])

def cHom (c : ℝ → G) (hca : ∀ x y, c (x + y) = c x * c y) : Multiplicative ℝ →* G where
  toFun x := c (Multiplicative.toAdd x)
  map_one' := c_zero hca
  map_mul' x y := hca _ _

/- English proof (translation)
Establish `h` using `map_zpow (cHom c hca) (Multiplicative.ofAdd (1:ℝ)) n`. Rewrite `h` using `[← ofAdd_zsmul, zsmul_one]`. Conclude with `h`.
-/
lemma c_int {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (n : ℤ) : c n = c 1 ^ n := by
  have h := map_zpow (cHom c hca) (Multiplicative.ofAdd (1:ℝ)) n
  rw [← ofAdd_zsmul, zsmul_one] at h
  exact h

/- English proof (translation)
Rewrite using `[hH, hsa, hsc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mem_of_split {H : Subgroup G} {s : G → ℝ} {c : ℝ → G}
    (hsa : ∀ g h, s (g * h) = s g + s h) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0)
    (g : G) : g * c (-s g) ∈ H := by
  rw [hH, hsa, hsc]; ring

def splitHomeo {H : Subgroup G} {s : G → ℝ} {c : ℝ → G} (hs : Continuous s)
    (hsa : ∀ g h, s (g * h) = s g + s h) (hc : Continuous c)
    (hca : ∀ x y, c (x + y) = c x * c y) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0) :
    H × ℝ ≃ₜ G where
  toFun p := (p.1 : G) * c p.2
  invFun g := (⟨g * c (-s g), mem_of_split hsa hsc hH g⟩, s g)
  left_inv p := by
    rcases p with ⟨⟨h, hh⟩, t⟩
    have h0 : s h = 0 := (hH h).1 hh
    have e : s (h * c t) = t := by rw [hsa, hsc, h0, zero_add]
    refine Prod.ext (Subtype.ext ?_) ?_
    · show h * c t * c (-s (h * c t)) = h
      rw [e, mul_assoc, ← hca, add_neg_cancel, c_zero hca, mul_one]
    · exact e
  right_inv g := by
    show g * c (-s g) * c (s g) = g
    rw [mul_assoc, ← hca, neg_add_cancel, c_zero hca, mul_one]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd)
  continuous_invFun := (Continuous.subtype_mk (continuous_id.mul (hc.comp hs.neg)) _).prodMk hs

end GlobalTheory.KernelCovolume

open scoped Pointwise
open GlobalTheory.KernelCovolume in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H Γ Λ s c hs hsa hc hca hcc hsc hH hΓ hΛ _hdisc hfin π D hπ hD`. Establish `hcl : IsClosed (H : Set G)`. Establish `: (H : Set G) = s ⁻¹' {0}` using `by ext g; exact hH g`. Rewrite using `[this]`. Conclude with `isClosed_singleton.preimage hs`.

Use `haveI : LocallyCompactSpace H := hcl.locallyCompactSpace`. Use `haveI : SigmaCompactSpace H := hcl.sigmaCompactSpace`. Use `haveI : SigmaFinite π := inferInstance`. Use `set φ : H × ℝ ≃ₜ G := splitHomeo hs hsa hc hca hsc hH with hφdef`. Establish `hφ : ∀ p : H × ℝ, φ p = (p.1 : G) * c p.2` using `fun p => rfl`.

Use `set μ0 : Measure (H × ℝ) := π.prod volume with hμ0`. Use `set ν : Measure G := μ0.map φ with hνdef`. Establish `hνapp : ∀ A, ν A = μ0 (φ ⁻¹' A)` using `fun A => φ.toMeasurableEquiv.map_apply A`. Establish `hmulφ : ∀ (γ : H) (r : ℝ) (p : H × ℝ), (γ : G) * c r * φ p = φ (γ * p.1, r + p.2)`. Introduce `γ r p`.

Simplify using `only [hφ, Subgroup.coe_mul, hca, mul_assoc]`. Rewrite using `[← mul_assoc (c r) (p.1 : G), hcc r, mul_assoc]`. Use `haveI : (Subgroup.zpowers (c 1)).Normal := ⟨fun n hn g => by`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hn`. Establish `hcomm : Commute ((c 1) ^ k) g` using `(Commute.zpow_left (hcc 1 g) k)`.

Rewrite using `[hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]`. Conclude with `Subgroup.zpow_mem_zpowers _ _⟩`. Establish `hdec : ∀ l ∈ Λ, ∃ γ ∈ Γ, ∃ n : ℤ, l = γ * c n`. Introduce `l hl`. Rewrite `hl` using `[hΛ]`.

Take `⟨y, hy, z, hz, rfl⟩` from `Subgroup.mem_sup_of_normal_right.1 hl`. Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hz`. Conclude with `⟨y, hy, n, by rw [c_int hca]⟩`. Establish `hmemΛ : ∀ γ ∈ Γ, ∀ n : ℤ, γ * c n ∈ Λ`. Introduce `γ hγ n`.

Rewrite using `[hΛ, c_int hca]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))`. Establish `hνHaar : ν.IsHaarMeasure` using `by haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ0 φ haveI : ν.IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective haveI : ν.IsMulLeftInvariant := ⟨fun g => by`. Take `⟨p0, rfl⟩` from `φ.surjective g`. Use extensionality with `A hA`.

Rewrite using `[Measure.map_apply (measurable_const_mul _) hA, hνapp, hνapp]`. Establish `hpre : φ ⁻¹' ((fun x => φ p0 * x) ⁻¹' A) = (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) ⁻¹' (φ ⁻¹' A)`. Use extensionality with `p`. Simplify using `only [Set.mem_preimage, Prod.map]`. Rewrite using `[show φ p0 = (p0.1 : G) * c p0.2 from rfl, hmulφ]`.

Establish `hT : μ0.map (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) = μ0`. Rewrite using `[hμ0, ← Measure.map_prod_map π volume (measurable_const_mul _) (measurable_const_add _), map_mul_left_eq_self, map_add_left_eq_self]`. Rewrite using `[hpre, ← Measure.map_apply ((measurable_const_mul _).prodMap (measurable_const_add _)) (φ.measurable hA), hT]⟩`. Conclude with `⟨⟩`. Use `set S : Set (H × ℝ) := D ×ˢ Set.Ico (0:ℝ) 1 with hS`.

Use `set D' : Set G := φ.symm ⁻¹' S with hD'`. Establish `hφD' : φ ⁻¹' D' = S` using `by ext p; simp [hD']`. Establish `hsub : ∀ (l : Λ) (γ : G) (hγ : γ ∈ Γ) (n : ℤ), (l : G) = γ * c n → ∀ p : H × ℝ, φ p ∈ l • D' → (⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1 ∈ D ∧ ((-n : ℤ) : ℝ) + p.2 ∈ Set.Ico (0:ℝ) 1`. Introduce `l γ hγ n e p hp`. Rewrite `hp` using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Establish `hx : l⁻¹ • φ p = φ ((⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1, ((-n : ℤ) : ℝ) + p.2)`. Rewrite using `[← hmulφ, Subgroup.smul_def, smul_eq_mul]`. Use `congr 1`. Simplify using `only [Subgroup.coe_inv, e, mul_inv_rev, c_neg hca, Int.cast_neg]`. Conclude with `hcc _ _`.

Rewrite `hp` using `[hx]`. Simplify `hp` using `[hD', hS]`. Establish `hFD : IsFundamentalDomain Λ D' ν`. Use `{ nullMeasurableSet := ?_, ae_covers := ?_, aedisjoint := ?_ }` and prove the remaining obligations. Conclude with `(hD.nullMeasurableSet.prod measurableSet_Ico.nullMeasurableSet).preimage (φ.toMeasurableEquiv.quasiMeasurePreserving_symm μ0)`.

Rewrite using `[hνdef, show (⇑φ : H × ℝ → G) = ⇑φ.toMeasurableEquiv from rfl, φ.toMeasurableEquiv.measurableEmbedding.ae_map_iff] filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp`. Take `⟨γ, hγ⟩` from `hp`. Establish `hγΓ : ((γ : H) : G) ∈ Γ` using `Subgroup.mem_subgroupOf.1 γ.2`. Use `⟨⟨((γ : H) : G) * c ((-⌊p.2⌋ : ℤ) : ℝ), hmemΛ _ hγΓ _⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul]`.

Use `show _ ∈ φ.symm ⁻¹' S`. Rewrite using `[Set.mem_preimage, show (φ.toMeasurableEquiv p) = φ p from rfl, hmulφ, φ.symm_apply_apply]`. Establish `hfr : ((-⌊p.2⌋ : ℤ) : ℝ) + p.2 = Int.fract p.2`. Rewrite using `[Int.cast_neg, Int.fract]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfr]`. Conclude with `Set.mk_mem_prod hγ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩`. Introduce `l1 l2 hne`. Take `⟨γ1, hγ1, n1, e1⟩` from `hdec l1 l1.2`. Take `⟨γ2, hγ2, n2, e2⟩` from `hdec l2 l2.2`.

Use `show ν ((l1 • D') ∩ (l2 • D')) = 0`. Rewrite using `[hνapp]`. Distinguish the cases in `hn : n1 = n2`. Substitute `hn` using the available equality. Establish `hγne : γ1 ≠ γ2`.

Introduce and unpack `rfl`. Conclude with `hne (Subtype.ext (e1.trans e2.symm))`. Set `g1 : Γ.subgroupOf H` to `⟨⟨γ1, hΓ hγ1⟩, Subgroup.mem_subgroupOf.2 hγ1⟩`. Set `g2 : Γ.subgroupOf H` to `⟨⟨γ2, hΓ hγ2⟩, Subgroup.mem_subgroupOf.2 hγ2⟩`. Establish `hg : g1 ≠ g2` using `fun h => hγne (congrArg (fun x : Γ.subgroupOf H => ((x : H) : G)) h)`.

Establish `h0 : π (g1 • D ∩ g2 • D) = 0` using `hD.aedisjoint hg`. Use `measure_mono_null (t := (g1 • D ∩ g2 • D) ×ˢ Set.univ) ?_ ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp1, hp2⟩`. Use `Set.mk_mem_prod ⟨?_, ?_⟩ (Set.mem_univ _)` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Conclude with `(hsub l1 γ1 hγ1 n1 e1 p hp1).1`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Conclude with `(hsub l2 γ2 hγ2 n1 e2 p hp2).1`. Rewrite using `[hμ0, Measure.prod_prod, h0, zero_mul]`. Use `measure_mono_null (t := ∅) ?_ measure_empty` and prove the remaining obligations.

Introduce and unpack `p ⟨hp1, hp2⟩`. Establish `a1` using `(hsub l1 γ1 hγ1 n1 e1 p hp1).2`. Establish `a2` using `(hsub l2 γ2 hγ2 n2 e2 p hp2).2`. Simplify using `only [Set.mem_Ico, Int.cast_neg] at a1 a2`. Establish `b1 : (n1 : ℝ) < n2 + 1` using `by linarith`.

Establish `b2 : (n2 : ℝ) < n1 + 1` using `by linarith`. Establish `c1 : n1 < n2 + 1` using `by exact_mod_cast b1`. Establish `c2 : n2 < n1 + 1` using `by exact_mod_cast b2`. Conclude with `absurd (by omega : n1 = n2) hn`. Establish `hfinν` using `hfin ν D' hνHaar hFD`.

Establish `hνD' : ν D' = π D`. Rewrite using `[hνapp, hφD', hS, hμ0, Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]`. Rewrite `hfinν` using `[hνD']`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.finiteCovolume_kernel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H Γ Λ s c hs hsa hc hca hcc hsc hH hΓ hΛ _hdisc hfin π D hπ hD
  have hcl : IsClosed (H : Set G) := by
    have : (H : Set G) = s ⁻¹' {0} := by ext g; exact hH g
    rw [this]; exact isClosed_singleton.preimage hs
  haveI : LocallyCompactSpace H := hcl.locallyCompactSpace
  haveI : SigmaCompactSpace H := hcl.sigmaCompactSpace
  haveI : SigmaFinite π := inferInstance
  set φ : H × ℝ ≃ₜ G := splitHomeo hs hsa hc hca hsc hH with hφdef
  have hφ : ∀ p : H × ℝ, φ p = (p.1 : G) * c p.2 := fun p => rfl
  set μ0 : Measure (H × ℝ) := π.prod volume with hμ0
  set ν : Measure G := μ0.map φ with hνdef
  have hνapp : ∀ A, ν A = μ0 (φ ⁻¹' A) := fun A => φ.toMeasurableEquiv.map_apply A
  have hmulφ : ∀ (γ : H) (r : ℝ) (p : H × ℝ), (γ : G) * c r * φ p = φ (γ * p.1, r + p.2) := by
    intro γ r p
    simp only [hφ, Subgroup.coe_mul, hca, mul_assoc]
    rw [← mul_assoc (c r) (p.1 : G), hcc r, mul_assoc]

  haveI : (Subgroup.zpowers (c 1)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute ((c 1) ^ k) g := (Commute.zpow_left (hcc 1 g) k)
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers _ _⟩
  have hdec : ∀ l ∈ Λ, ∃ γ ∈ Γ, ∃ n : ℤ, l = γ * c n := by
    intro l hl
    rw [hΛ] at hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨y, hy, n, by rw [c_int hca]⟩
  have hmemΛ : ∀ γ ∈ Γ, ∀ n : ℤ, γ * c n ∈ Λ := by
    intro γ hγ n
    rw [hΛ, c_int hca]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

  have hνHaar : ν.IsHaarMeasure := by
    haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ0 φ
    haveI : ν.IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
    haveI : ν.IsMulLeftInvariant := ⟨fun g => by
      obtain ⟨p0, rfl⟩ := φ.surjective g
      ext A hA
      rw [Measure.map_apply (measurable_const_mul _) hA, hνapp, hνapp]
      have hpre : φ ⁻¹' ((fun x => φ p0 * x) ⁻¹' A) =
          (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) ⁻¹' (φ ⁻¹' A) := by
        ext p
        simp only [Set.mem_preimage, Prod.map]
        rw [show φ p0 = (p0.1 : G) * c p0.2 from rfl, hmulφ]
      have hT : μ0.map (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) = μ0 := by
        rw [hμ0, ← Measure.map_prod_map π volume (measurable_const_mul _) (measurable_const_add _),
          map_mul_left_eq_self, map_add_left_eq_self]
      rw [hpre, ← Measure.map_apply ((measurable_const_mul _).prodMap (measurable_const_add _))
        (φ.measurable hA), hT]⟩
    exact ⟨⟩

  set S : Set (H × ℝ) := D ×ˢ Set.Ico (0:ℝ) 1 with hS
  set D' : Set G := φ.symm ⁻¹' S with hD'
  have hφD' : φ ⁻¹' D' = S := by ext p; simp [hD']
  have hsub : ∀ (l : Λ) (γ : G) (hγ : γ ∈ Γ) (n : ℤ), (l : G) = γ * c n → ∀ p : H × ℝ,
      φ p ∈ l • D' → (⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1 ∈ D ∧ ((-n : ℤ) : ℝ) + p.2 ∈ Set.Ico (0:ℝ) 1 := by
    intro l γ hγ n e p hp
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hp
    have hx : l⁻¹ • φ p = φ ((⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1, ((-n : ℤ) : ℝ) + p.2) := by
      rw [← hmulφ, Subgroup.smul_def, smul_eq_mul]
      congr 1
      simp only [Subgroup.coe_inv, e, mul_inv_rev, c_neg hca, Int.cast_neg]
      exact hcc _ _
    rw [hx] at hp
    simpa [hD', hS] using hp
  have hFD : IsFundamentalDomain Λ D' ν := by
    refine { nullMeasurableSet := ?_, ae_covers := ?_, aedisjoint := ?_ }
    · exact (hD.nullMeasurableSet.prod measurableSet_Ico.nullMeasurableSet).preimage
        (φ.toMeasurableEquiv.quasiMeasurePreserving_symm μ0)
    · rw [hνdef, show (⇑φ : H × ℝ → G) = ⇑φ.toMeasurableEquiv from rfl,
        φ.toMeasurableEquiv.measurableEmbedding.ae_map_iff]
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp
      obtain ⟨γ, hγ⟩ := hp
      have hγΓ : ((γ : H) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      refine ⟨⟨((γ : H) : G) * c ((-⌊p.2⌋ : ℤ) : ℝ), hmemΛ _ hγΓ _⟩, ?_⟩
      rw [Subgroup.smul_def, smul_eq_mul]
      show _ ∈ φ.symm ⁻¹' S
      rw [Set.mem_preimage, show (φ.toMeasurableEquiv p) = φ p from rfl, hmulφ, φ.symm_apply_apply]
      have hfr : ((-⌊p.2⌋ : ℤ) : ℝ) + p.2 = Int.fract p.2 := by
        rw [Int.cast_neg, Int.fract]; ring
      rw [hfr]
      exact Set.mk_mem_prod hγ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro l1 l2 hne
      obtain ⟨γ1, hγ1, n1, e1⟩ := hdec l1 l1.2
      obtain ⟨γ2, hγ2, n2, e2⟩ := hdec l2 l2.2
      show ν ((l1 • D') ∩ (l2 • D')) = 0
      rw [hνapp]
      by_cases hn : n1 = n2
      · subst hn
        have hγne : γ1 ≠ γ2 := by
          rintro rfl; exact hne (Subtype.ext (e1.trans e2.symm))
        let g1 : Γ.subgroupOf H := ⟨⟨γ1, hΓ hγ1⟩, Subgroup.mem_subgroupOf.2 hγ1⟩
        let g2 : Γ.subgroupOf H := ⟨⟨γ2, hΓ hγ2⟩, Subgroup.mem_subgroupOf.2 hγ2⟩
        have hg : g1 ≠ g2 := fun h => hγne (congrArg (fun x : Γ.subgroupOf H => ((x : H) : G)) h)
        have h0 : π (g1 • D ∩ g2 • D) = 0 := hD.aedisjoint hg
        refine measure_mono_null (t := (g1 • D ∩ g2 • D) ×ˢ Set.univ) ?_ ?_
        · rintro p ⟨hp1, hp2⟩
          refine Set.mk_mem_prod ⟨?_, ?_⟩ (Set.mem_univ _)
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l1 γ1 hγ1 n1 e1 p hp1).1
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l2 γ2 hγ2 n1 e2 p hp2).1
        · rw [hμ0, Measure.prod_prod, h0, zero_mul]
      · refine measure_mono_null (t := ∅) ?_ measure_empty
        rintro p ⟨hp1, hp2⟩
        have a1 := (hsub l1 γ1 hγ1 n1 e1 p hp1).2
        have a2 := (hsub l2 γ2 hγ2 n2 e2 p hp2).2
        simp only [Set.mem_Ico, Int.cast_neg] at a1 a2
        have b1 : (n1 : ℝ) < n2 + 1 := by linarith
        have b2 : (n2 : ℝ) < n1 + 1 := by linarith
        have c1 : n1 < n2 + 1 := by exact_mod_cast b1
        have c2 : n2 < n1 + 1 := by exact_mod_cast b2
        exact absurd (by omega : n1 = n2) hn
  have hfinν := hfin ν D' hνHaar hFD
  have hνD' : ν D' = π D := by
    rw [hνapp, hφD', hS, hμ0, Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
      mul_one]
  rwa [hνD'] at hfinν
