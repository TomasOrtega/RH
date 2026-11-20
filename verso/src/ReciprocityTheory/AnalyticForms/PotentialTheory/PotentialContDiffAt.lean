import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    ContDiffAt ℝ 2 (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  have h := hP.1 ((A.chart j).symm y) j
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)).mem_nhds ⟨hy, P.mem_U _⟩
  exact (h.contDiffAt hmem).of_le (by norm_cast)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem locDens_cons (A : FinHolAtlas (e + 1) X) (P : LocPot X) (Φ : Fin e → LocPot X)
    (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) j y = ((e + 1).factorial : ℝ) * (2 / Real.pi) ^ (e + 1) *
      (mdisc (Fin.cons (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
        (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) :
          Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)).re := by
  unfold locDens maDens
  congr 3
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locDens_cons_rsmul (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by
  rw [locDens_cons, locDens_cons]
  have : (fun y' => (P.rsmul c).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => c * P.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_const_mul', mdisc_cons_smul, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locDens_cons_add (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by
  rw [locDens_cons, locDens_cons, locDens_cons]
  have : (fun y' => (P + Q).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y') +
        Q.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_add' _ _ _ (potential_contDiffAt A P hP j hy) (potential_contDiffAt A Q hQ j hy),
    mdisc_cons_add, Complex.add_re]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem locDens_nonneg (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hψ : ∀ i, IsPsh A (Φ i)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  unfold locDens
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  exact hessC_posSemidef _ _ (potential_contDiffAt A (Φ k) (hΦ k) j hy)
    fun w => hψ k ((A.chart j).symm y) j y ⟨hy, (Φ k).mem_U _⟩ w

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem integrableOn_weight [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  set K := (A.chart j) '' tsupport (P.χ j)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : K ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    (hg j K hKt hKc).continuousOn_mul (hχc.mono hKt) hKc
  have h2 := h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet (by
    rintro y ⟨hy, hyK⟩
    have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
      hyK ⟨_, h, (A.chart j).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this])
  simpa only [mul_assoc] using h2

end Chart

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
private theorem mdisc_comp_perm_potential {D : ℕ} (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    ReciprocityTheory.AnForm.mdisc (B ∘ σ) = ReciprocityTheory.AnForm.mdisc B := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mIntSymm : MIntSymmStatement := by
  intro e X _ A Φ σ g
  have hloc : ∀ j y, locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
    intro j y
    unfold locDens maDens
    congr 2
    exact mdisc_comp_perm_potential (fun k => ReciprocityTheory.AnForm.hessC
      (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
  unfold mInt integralWith
  simp only [hloc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mIntAdd : MIntAddStatement := by
  intro e X _ _ _ A P Q Φ hP hQ hΦ g hgP hgQ
  unfold mInt integralWith
  split_ifs with h
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some (Fin.cons P Φ) g hgP j
    have i2 := integrableOn_weight A h.some (Fin.cons Q Φ) g hgQ j
    rw [← integral_add i1 i2]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    show _ = _ + _
    rw [locDens_cons_add A P Q Φ hP hQ j hy]
    ring
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem mIntRsmul : MIntRsmulStatement := by
  intro e X _ A c P Φ hP hΦ g
  unfold mInt integralWith
  split_ifs with h
  · simp only [locDens_cons_rsmul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mIntZsmul : MIntZsmulStatement := by
  intro e X _ A m P Φ hP hΦ g
  exact mIntRsmul A (m : ℝ) P Φ hP hΦ g

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mIntLinear : MIntLinearStatement := by
  intro e X _ _ _ A Φ hΦ c g g' hg hg'
  unfold mInt integralWith
  split_ifs with h
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some Φ g hg j
    have i2 := integrableOn_weight A h.some Φ g' hg' j
    rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
    congr 1
    funext y
    ring
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mIntNonneg : MIntNonnegStatement := by
  intro e X _ A Φ hΦ hψ g hg
  unfold mInt integralWith
  split_ifs with h
  · exact Finset.sum_nonneg fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet
      fun y hy => mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg _)) (locDens_nonneg A Φ hΦ hψ j hy)
  · exact le_rfl

end

end ReciprocityTheory.AnForm.M
