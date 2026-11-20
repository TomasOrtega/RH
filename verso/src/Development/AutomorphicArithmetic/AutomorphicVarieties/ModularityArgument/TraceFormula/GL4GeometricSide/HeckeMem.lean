import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private def cos (U : Subgroup G) (a : G) : Set G := {y | a⁻¹ * y ∈ U}

/- English proof (translation)
Simplify using `[cos, U.one_mem]`.
-/
private theorem cos_self (U : Subgroup G) (a : G) : a ∈ cos U a := by
  simp [cos, U.one_mem]

/- English proof (translation)
The claim follows from `hU.preimage (continuous_const.mul continuous_id)`.
-/
private theorem isOpen_cos {U : Subgroup G} (hU : IsOpen (U : Set G)) (a : G) : IsOpen (cos U a) :=
  hU.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Take `⟨t, -, ht⟩` from `hC.elim_nhds_subcover (fun g => cos U g) (fun g _ => (isOpen_cos hU g).mem_nhds (cos_self U g))`. Use `⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ U))).image Quotient.out, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb y hya hyb`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 ha`. Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hb`.

Establish `hab : (Quotient.out q)⁻¹ * Quotient.out q' ∈ U`. Use `U.mul_mem hya (U.inv_mem hyb)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `: (QuotientGroup.mk (Quotient.out q) : G ⧸ U) = QuotientGroup.mk (Quotient.out q')` using `QuotientGroup.eq.2 hab`. Establish `e : q = q'`.

Simplify `this` using `[QuotientGroup.out_eq']`. Rewrite using `[e]`. Introduce `y hy`. Take `⟨g, hg, hyg⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Establish `hr : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ U)) : G ⧸ U) = QuotientGroup.mk g` using `QuotientGroup.out_eq' _`.

Establish `hgr : (Quotient.out (QuotientGroup.mk g : G ⧸ U))⁻¹ * g ∈ U` using `QuotientGroup.eq.1 hr`. Use `Set.mem_iUnion₂.2 ⟨Quotient.out (QuotientGroup.mk g : G ⧸ U), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hg), ?_⟩` and prove the remaining obligations. Use `U.mul_mem hgr hyg` as an intermediate fact. Simplify `this` using `[cos, mul_assoc]`.
-/
private theorem exists_reps {U : Subgroup G} (hU : IsOpen (U : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ s : Finset G, (∀ a ∈ s, ∀ b ∈ s, ∀ y, y ∈ cos U a → y ∈ cos U b → a = b) ∧
      C ⊆ ⋃ a ∈ s, cos U a := by
  classical
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun g => cos U g)
    (fun g _ => (isOpen_cos hU g).mem_nhds (cos_self U g))
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ U))).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb y hya hyb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb
    have hab : (Quotient.out q)⁻¹ * Quotient.out q' ∈ U := by
      have := U.mul_mem hya (U.inv_mem hyb)
      simpa [mul_assoc] using this
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ U) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.2 hab
    have e : q = q' := by
      simpa [QuotientGroup.out_eq'] using this
    rw [e]
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hr : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ U)) : G ⧸ U) = QuotientGroup.mk g :=
      QuotientGroup.out_eq' _
    have hgr : (Quotient.out (QuotientGroup.mk g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 hr
    refine Set.mem_iUnion₂.2 ⟨Quotient.out (QuotientGroup.mk g : G ⧸ U),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hg), ?_⟩
    have := U.mul_mem hgr hyg
    simpa [cos, mul_assoc] using this

/- English proof (translation)
Take `⟨s, hdis, hcov⟩` from `exists_reps hU hc.isCompact`. Use `⟨s, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hmeas : ∀ a, μ (cos U a) = μ (U : Set G)` using `fun a => measure_preimage_mul μ a⁻¹ (U : Set G)`. Establish `hval : ∀ a y, y ∈ cos U a → h y * f y = h a * f a`. Introduce `a y hy`.

Establish `e : y = a * (a⁻¹ * y)` using `by group`. Rewrite using `[e, hinv a _ hy, hf a _ hy]`. Establish `hsum : (fun y => h y * f y) = fun y => ∑ a ∈ s, (cos U a).indicator (fun _ => h a * f a) y`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : ∃ a ∈ s, y ∈ cos U a`.

Take `⟨a, ha, hya⟩` from `hy`. Rewrite using `[Finset.sum_eq_single a, Set.indicator_of_mem hya, hval a y hya]`. Introduce `b hb hba`. Conclude with `Set.indicator_of_notMem (fun hyb => hba (hdis b hb a ha y hyb hya)) _`. Conclude with `fun h' => (h' ha).elim`.

Establish `hy0 : h y = 0`. Use `image_eq_zero_of_notMem_tsupport fun hmem => hy ?_` and prove the remaining obligations. Take `⟨a, ha, hya⟩` from `Set.mem_iUnion₂.1 (hcov hmem)`. Conclude with `⟨a, ha, hya⟩`. Rewrite using `[hy0, zero_mul]`.

Conclude with `(Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (fun hya => hy ⟨a, ha, hya⟩) _).symm`. Rewrite using `[hsum, integral_finset_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (isOpen_cos hU a).measurableSet]`. Simplify using `only [Measure.real, hmeas a, Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a _`. Use `(integrable_indicator_iff (isOpen_cos hU a).measurableSet).2 ?_` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hmeas a]; exact hfin)`.
-/
private theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hfin : μ (U : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ U, h (g * k) = h g) :
    ∃ s : Finset G, ∀ f : G → ℂ, (∀ g, ∀ k ∈ U, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ a ∈ s, (h a * (μ.real (U : Set G) : ℂ)) * f a := by
  classical
  obtain ⟨s, hdis, hcov⟩ := exists_reps hU hc.isCompact
  refine ⟨s, fun f hf => ?_⟩
  have hmeas : ∀ a, μ (cos U a) = μ (U : Set G) := fun a => measure_preimage_mul μ a⁻¹ (U : Set G)
  have hval : ∀ a y, y ∈ cos U a → h y * f y = h a * f a := by
    intro a y hy
    have e : y = a * (a⁻¹ * y) := by group
    rw [e, hinv a _ hy, hf a _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ a ∈ s, (cos U a).indicator (fun _ => h a * f a) y := by
    funext y
    by_cases hy : ∃ a ∈ s, y ∈ cos U a
    · obtain ⟨a, ha, hya⟩ := hy
      rw [Finset.sum_eq_single a, Set.indicator_of_mem hya, hval a y hya]
      · intro b hb hba
        exact Set.indicator_of_notMem (fun hyb => hba (hdis b hb a ha y hyb hya)) _
      · exact fun h' => (h' ha).elim
    · have hy0 : h y = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.1 (hcov hmem)
        exact ⟨a, ha, hya⟩
      rw [hy0, zero_mul]
      exact (Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (fun hya => hy ⟨a, ha, hya⟩) _).symm
  rw [hsum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_indicator_const _ (isOpen_cos hU a).measurableSet]
    simp only [Measure.real, hmeas a, Complex.real_smul]
    ring
  · intro a _
    refine (integrable_indicator_iff (isOpen_cos hU a).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas a]; exact hfin)

end Abs

/- English proof (translation)
Introduce `E _ _ _ n π K hKo hKc _ _ μf _ h hh ψ`. Set `St : Subgroup (GL (Fin n) (Af E))` to `{ carrier := {k | finRep E n k ψ.1 = ψ.1} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`.

Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`.

Establish `hSt : IsOpen (St : Set (GL (Fin n) (Af E)))` using `(π.cusp ψ.1 ψ.2).1.level`. Establish `hU : IsOpen ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E)))` using `hKo.inter hSt`. Establish `hfin : μf ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) ≠ ⊤` using `((measure_mono Set.inter_subset_left).trans_lt hKc.measure_lt_top).ne`. Take `⟨s, hs⟩` from `integral_eq_sum μf hU hfin hh.1 (fun g k hk => by`. Simplify using `using hh.2 1 K.one_mem k hk.1 g)`.

Set `c : GL (Fin n) (Af E) → ℂ` to `fun a => h a * (μf.real ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) : ℂ)`. Establish `hmem : ∑ g ∈ s, c g • finRep E n g ψ.1 ∈ π.V` using `Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.stable (.fin g) ψ.1 ψ.2)`. Establish `hop : (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 = heckeOp μf h ψ.1.1`. Use function extensionality and compare the values at `x`. Establish `hinv` using `hs (fun g => ψ.1.1 (x * finGL E n g)) (fun g k hk => by`.

Establish `e` using `congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n k ψ.1 = ψ.1 from hk.2)`. Establish `e' : ψ.1.1 (x * finGL E n g * finGL E n k) = ψ.1.1 (x * finGL E n g)` using `e`. Simplify `e')` using `[mul_assoc]`. Rewrite using `[heckeOp, hinv]`. Simplify using `[c, Submodule.coe_sum, Finset.sum_apply]`.

Both sides reduce to the same expression. Use `⟨s, c, ⟨_, hmem⟩, rfl, hop, fun k hk => ?_⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 (x * finGL E n k) = (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 x`. Rewrite using `[hop]`.

Establish `e` using `integral_mul_left_eq_self (μ := μf) (fun g => h g * ψ.1.1 (x * finGL E n g)) k`. Simplify using `only [heckeOp]`. Rewrite using `[← e]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `e2 : h (k * g) = h g` using `by simpa using hh.2 k hk 1 K.one_mem g`.

Simplify using `[e2, map_mul, mul_assoc]`.
-/
theorem heckeMem : HeckeMem := by
  intro E _ _ _ n π K hKo hKc _ _ μf _ h hh ψ
  let St : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | finRep E n k ψ.1 = ψ.1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSt : IsOpen (St : Set (GL (Fin n) (Af E))) := (π.cusp ψ.1 ψ.2).1.level
  have hU : IsOpen ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) := hKo.inter hSt
  have hfin : μf ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hKc.measure_lt_top).ne
  obtain ⟨s, hs⟩ := integral_eq_sum μf hU hfin hh.1 (fun g k hk => by
    simpa using hh.2 1 K.one_mem k hk.1 g)
  let c : GL (Fin n) (Af E) → ℂ := fun a => h a * (μf.real ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) : ℂ)
  have hmem : ∑ g ∈ s, c g • finRep E n g ψ.1 ∈ π.V :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.stable (.fin g) ψ.1 ψ.2)
  have hop : (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 = heckeOp μf h ψ.1.1 := by
    funext x
    have hinv := hs (fun g => ψ.1.1 (x * finGL E n g)) (fun g k hk => by
      have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n k ψ.1 = ψ.1 from hk.2)
      have e' : ψ.1.1 (x * finGL E n g * finGL E n k) = ψ.1.1 (x * finGL E n g) := e
      simpa [mul_assoc] using e')
    rw [heckeOp, hinv]
    simp [c, Submodule.coe_sum, Finset.sum_apply]
    rfl
  refine ⟨s, c, ⟨_, hmem⟩, rfl, hop, fun k hk => ?_⟩
  refine Subtype.ext (funext fun x => ?_)
  change (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 (x * finGL E n k) = (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 x
  rw [hop]
  have e := integral_mul_left_eq_self (μ := μf) (fun g => h g * ψ.1.1 (x * finGL E n g)) k
  simp only [heckeOp]
  rw [← e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e2 : h (k * g) = h g := by simpa using hh.2 k hk 1 K.one_mem g
  simp [e2, map_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting
