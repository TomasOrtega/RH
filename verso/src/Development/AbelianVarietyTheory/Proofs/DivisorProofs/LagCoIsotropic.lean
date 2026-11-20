import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.LinPair

noncomputable section

namespace GlobalTheory.LagrFormLine

open MeasureTheory ValuativeRel

/- English proof (translation)
Establish `hle : Λ ≤ (GlobalTheory.LagrInvForm.symp k κ).orthogonal Λ` using `fun b hb a ha => sub_eq_zero.2 (h a ha b hb)`. Establish `hr` using `LinearMap.BilinForm.finrank_orthogonal (GlobalTheory.LagrInvForm.symp_nondeg k κ) Λ`. Establish `h3` using `Submodule.finrank_mono hle`. Rewrite `hr` using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank k Λ ≤ Fintype.card κ := by
  have hle : Λ ≤ (GlobalTheory.LagrInvForm.symp k κ).orthogonal Λ := fun b hb a ha => sub_eq_zero.2 (h a ha b hb)
  have hr := LinearMap.BilinForm.finrank_orthogonal (GlobalTheory.LagrInvForm.symp_nondeg k κ) Λ
  have h3 := Submodule.finrank_mono hle
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at hr
  omega

/- English proof (translation)
Establish `h1` using `finrank_le Λ h`. Establish `h2` using `finrank_le Λ' h'`. Establish `h3` using `Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'`. Rewrite `h3` using `[hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ Λ' : Submodule k ((κ → k) × (κ → k)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank k Λ = Fintype.card κ := by
  have h1 := finrank_le Λ h
  have h2 := finrank_le Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

/- English proof (translation)
Set `χ : AddChar k Circle` to `{ toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch ψ hψ x)⟩ map_zero_eq_one' := Circle.ext (by simp) map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }`. Establish `hχ : ∀ x, (χ x : ℂ) = ψ x` using `fun _ => rfl`. Establish `hχc : Continuous χ` using `continuous_induced_rng.2 hψ`. Establish `hχ1 : χ ≠ 1` using `fun h => hψ1 (by`. Use extensionality with `x`.

Rewrite using `[← hχ, h]`. Use the proof step `simp)`. Take `⟨c0, hc0⟩` from `GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1`. Conclude with `hc0.isLocallyConstant.comp (fun z : Circle => (z : ℂ))`.
-/
theorem isLocallyConstant_char (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) : IsLocallyConstant (ψ : k → ℂ) := by
  let χ : AddChar k Circle :=
    { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch ψ hψ x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
  have hχ : ∀ x, (χ x : ℂ) = ψ x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hψ
  have hχ1 : χ ≠ 1 := fun h => hψ1 (by
    ext x
    rw [← hχ, h]
    simp)
  obtain ⟨c0, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact hc0.isLocallyConstant.comp (fun z : Circle => (z : ℂ))

/- English proof (translation)
Establish `h1 : IsCompact (𝒪[k] : Set k)` using `isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))`. Establish `h2 : IsOpen (𝒪[k] : Set k)`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Conclude with `Valued.isOpen_integer k`.

Conclude with `⟨Set.pi Set.univ fun _ => (𝒪[k] : Set k), isOpen_set_pi Set.finite_univ fun _ _ => h2, isCompact_univ_pi fun _ => h1, fun _ _ => zero_mem _⟩`.
-/
theorem exists_compact_open (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (κ : Type) [Fintype κ] : ∃ U : Set (κ → k), IsOpen U ∧ IsCompact U ∧ 0 ∈ U := by
  have h1 : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have h2 : IsOpen (𝒪[k] : Set k) := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    exact Valued.isOpen_integer k
  exact ⟨Set.pi Set.univ fun _ => (𝒪[k] : Set k), isOpen_set_pi Set.finite_univ fun _ _ => h2,
    isCompact_univ_pi fun _ => h1, fun _ _ => zero_mem _⟩

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Establish `hlc` using `isLocallyConstant_char k ψ hψ hψ1`. Take `⟨n, m, e, s, hs, hb⟩` from `GlobalTheory.LagrInvForm.exists_coord Λ hiso hdim`. Use `letI : MeasurableSpace (Fin m → k) := borel _`. Use `haveI : BorelSpace (Fin m → k) := ⟨rfl⟩`.

Set `ν : Measure (Fin m → k)` to `Measure.addHaar`. Set `j : (Fin m → k) →ₗ[k] (κ → k)` to `e.toLinearMap ∘ₗ LinearMap.inr k _ _`. Establish `hj : ∀ a, j a = e (0, a)` using `fun _ => rfl`. Set `p : (κ → k) →ₗ[k] (Fin m → k)` to `LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap`. Establish `hpj : ∀ a, p (j a) = a` using `fun a => by simp [p, hj]`.

Establish `hjc : Continuous j` using `LinearMap.continuous_on_pi j`. Establish `hpc : Continuous p` using `LinearMap.continuous_on_pi p`. Establish `hsc : Continuous s` using `LinearMap.continuous_on_pi s`. Set `q : (Fin m → k) → k` to `fun a => ⅟(2 : k) * (j a ⬝ᵥ s a)`. Establish `hqc : Continuous q` using `continuous_const.mul (hjc.dotProduct hsc)`.

Establish `hw : ∀ w ∈ Λ, j (p w.1) = w.1` using `fun w hw => by`. Establish `h0 : (e.symm w.1).1 = 0`. Use function extensionality and compare the values at `i`. Take `⟨b', h1, h2⟩` from `hb (Pi.single i 1)`. Establish `h3` using `hiso w hw _ h1`.

Simplify using `only [zero_dotProduct] at h3`. Rewrite `h3` using `[h2]`. Simplify using `using h3`. Rewrite using `[hj, ← h0]`. Conclude with `e.apply_symm_apply w.1`.

Establish `hcs : ∀ φ ∈ SB (κ → k), HasCompactSupport (φ ∘ j)` using `fun φ hφ => by`. Use `IsCompact.of_isClosed_subset (hφ.2.image hpc) isClosed_closure ?_` and prove the remaining obligations. Use `closure_minimal ?_ (hφ.2.image hpc).isClosed` and prove the remaining obligations. Introduce `x hx`. Conclude with `⟨j x, subset_tsupport _ hx, hpj x⟩`.

Establish `hint : ∀ φ ∈ SB (κ → k), Integrable (fun a => ψ (q a) * φ (j a)) ν` using `fun φ hφ => ((hψ.comp hqc).mul (hφ.1.continuous.comp hjc)).integrable_of_hasCompactSupport (hcs φ hφ).mul_left`. Set `f : SB (κ → k) →ₗ[ℂ] ℂ` to `{ toFun := fun φ => ∫ a, ψ (q a) * φ.1 (j a) ∂ν map_add' := fun φ φ' => by`. Simplify using `only [Submodule.coe_add, Pi.add_apply, mul_add]`. Conclude with `integral_add (hint _ φ.2) (hint _ φ'.2)`. Use the proof step `map_smul' := fun c φ => by`.

Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]`. Conclude with `integral_const_mul c _ }`. Take `⟨l, hl⟩` from `LinearMap.exists_extend f`. Establish `hl' : ∀ φ ∈ SB (κ → k), l φ = ∫ a, ψ (q a) * φ (j a) ∂ν` using `fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩`. Use `⟨l, fun w hwΛ φ hφ => ?_, ?_⟩` and prove the remaining obligations.

Establish `hm : schr ψ w φ ∈ SB (κ → k)` using `⟨(hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)).mul (hφ.1.comp_continuous (continuous_id.add continuous_const)), (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩`. Rewrite using `[hl' _ hm, hl' _ hφ, ← integral_add_right_eq_self (μ := ν) (fun a => ψ (q a) * φ (j a)) (p w.1)]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `h1` using `hw w hwΛ`.

Establish `h2` using `hiso _ (hs a) _ hwΛ`. Establish `h3` using `hiso _ (hs (p w.1)) _ hwΛ`. Establish `h4` using `hiso _ (hs a) _ (hs (p w.1))`. Establish `h5 : (2 : k) * ⅟(2 : k) = 1` using `mul_invOf_self _`. Simplify using `only [← hj, h1] at h2 h3 h4`.

Simplify using `only [schr, q, map_add j, map_add s, h1, add_dotProduct, dotProduct_add]`. Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Take the linear combination `h2 + ⅟(2 : k) * h3 - ⅟(2 : k) * h4 - (w.1 ⬝ᵥ s a) * h5`. Take `⟨U, hUo, hUc, hU0⟩` from `exists_compact_open k κ`.

Establish `hUl : IsLocallyConstant (U.indicator fun _ => (1 : ℂ))` using `(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant`. Establish `hm : (fun x => ψ (-q (p x)) * U.indicator (fun _ => (1 : ℂ)) x) ∈ SB (κ → k)` using `⟨(hlc.comp_continuous (hqc.comp hpc).neg).mul hUl, (HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _).mul_left⟩`. Use `⟨_, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[hl' _ hm]`. Establish `hSo : IsOpen (j ⁻¹' U)` using `hUo.preimage hjc`.

Establish `hfin : ν (j ⁻¹' U) < ⊤` using `lt_of_le_of_lt (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)`. Establish `hpos : 0 < ν (j ⁻¹' U)` using `hSo.measure_pos ν ⟨0, by simpa using hU0⟩`. Establish `heq : (fun a => ψ (q a) * (ψ (-q (p (j a))) * U.indicator (fun _ => (1 : ℂ)) (j a))) = (j ⁻¹' U).indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `a`. Rewrite using `[hpj, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]`.

Both sides reduce to the same expression. Rewrite using `[heq, integral_indicator_const _ hSo.measurableSet]`. Conclude with `smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero`.
-/
theorem exists_form (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hdim : Module.finrank k Λ = Fintype.card κ) :
    ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) ∧ ∃ φ ∈ SB (κ → k), l φ ≠ 0 := by
  classical
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hlc := isLocallyConstant_char k ψ hψ hψ1
  obtain ⟨n, m, e, s, hs, hb⟩ := GlobalTheory.LagrInvForm.exists_coord Λ hiso hdim
  letI : MeasurableSpace (Fin m → k) := borel _
  haveI : BorelSpace (Fin m → k) := ⟨rfl⟩
  let ν : Measure (Fin m → k) := Measure.addHaar
  let j : (Fin m → k) →ₗ[k] (κ → k) := e.toLinearMap ∘ₗ LinearMap.inr k _ _
  have hj : ∀ a, j a = e (0, a) := fun _ => rfl
  let p : (κ → k) →ₗ[k] (Fin m → k) := LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap
  have hpj : ∀ a, p (j a) = a := fun a => by simp [p, hj]
  have hjc : Continuous j := LinearMap.continuous_on_pi j
  have hpc : Continuous p := LinearMap.continuous_on_pi p
  have hsc : Continuous s := LinearMap.continuous_on_pi s
  let q : (Fin m → k) → k := fun a => ⅟(2 : k) * (j a ⬝ᵥ s a)
  have hqc : Continuous q := continuous_const.mul (hjc.dotProduct hsc)
  have hw : ∀ w ∈ Λ, j (p w.1) = w.1 := fun w hw => by
    have h0 : (e.symm w.1).1 = 0 := by
      funext i
      obtain ⟨b', h1, h2⟩ := hb (Pi.single i 1)
      have h3 := hiso w hw _ h1
      simp only [zero_dotProduct] at h3
      rw [h2] at h3
      simpa using h3
    rw [hj, ← h0]
    exact e.apply_symm_apply w.1
  have hcs : ∀ φ ∈ SB (κ → k), HasCompactSupport (φ ∘ j) := fun φ hφ => by
    refine IsCompact.of_isClosed_subset (hφ.2.image hpc) isClosed_closure ?_
    refine closure_minimal ?_ (hφ.2.image hpc).isClosed
    intro x hx
    exact ⟨j x, subset_tsupport _ hx, hpj x⟩
  have hint : ∀ φ ∈ SB (κ → k), Integrable (fun a => ψ (q a) * φ (j a)) ν := fun φ hφ =>
    ((hψ.comp hqc).mul (hφ.1.continuous.comp hjc)).integrable_of_hasCompactSupport (hcs φ hφ).mul_left
  let f : SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ a, ψ (q a) * φ.1 (j a) ∂ν
      map_add' := fun φ φ' => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2) (hint _ φ'.2)
      map_smul' := fun c φ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ c]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend f
  have hl' : ∀ φ ∈ SB (κ → k), l φ = ∫ a, ψ (q a) * φ (j a) ∂ν := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hwΛ φ hφ => ?_, ?_⟩
  · have hm : schr ψ w φ ∈ SB (κ → k) :=
      ⟨(hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)).mul
        (hφ.1.comp_continuous (continuous_id.add continuous_const)),
        (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩
    rw [hl' _ hm, hl' _ hφ, ← integral_add_right_eq_self (μ := ν) (fun a => ψ (q a) * φ (j a)) (p w.1)]
    congr 1
    funext a
    have h1 := hw w hwΛ
    have h2 := hiso _ (hs a) _ hwΛ
    have h3 := hiso _ (hs (p w.1)) _ hwΛ
    have h4 := hiso _ (hs a) _ (hs (p w.1))
    have h5 : (2 : k) * ⅟(2 : k) = 1 := mul_invOf_self _
    simp only [← hj, h1] at h2 h3 h4
    simp only [schr, q, map_add j, map_add s, h1, add_dotProduct, dotProduct_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    linear_combination h2 + ⅟(2 : k) * h3 - ⅟(2 : k) * h4 - (w.1 ⬝ᵥ s a) * h5
  · obtain ⟨U, hUo, hUc, hU0⟩ := exists_compact_open k κ
    have hUl : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
      (LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant
    have hm : (fun x => ψ (-q (p x)) * U.indicator (fun _ => (1 : ℂ)) x) ∈ SB (κ → k) :=
      ⟨(hlc.comp_continuous (hqc.comp hpc).neg).mul hUl,
        (HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _).mul_left⟩
    refine ⟨_, hm, ?_⟩
    rw [hl' _ hm]
    have hSo : IsOpen (j ⁻¹' U) := hUo.preimage hjc
    have hfin : ν (j ⁻¹' U) < ⊤ :=
      lt_of_le_of_lt (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)
    have hpos : 0 < ν (j ⁻¹' U) := hSo.measure_pos ν ⟨0, by simpa using hU0⟩
    have heq : (fun a => ψ (q a) * (ψ (-q (p (j a))) * U.indicator (fun _ => (1 : ℂ)) (j a))) =
        (j ⁻¹' U).indicator (fun _ => (1 : ℂ)) := by
      funext a
      rw [hpj, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
      rfl
    rw [heq, integral_indicator_const _ hSo.measurableSet]
    exact smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero

section Pair

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [Fintype β] [Fintype ν] [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

/- English proof (translation)
Establish `h1 : ∀ x y : Matrix α β E, hTens c JA JB x y = ∑ i, ∑ i', JA i i' * (x * JB * (y.map c)ᵀ) i i'` using `fun x y => by`. Unfold `hTens`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (z' * Cᵀ).map c = z'.map c * (C.map c)ᵀ` using `Matrix.map_mul (f := c.toRingHom)`.

Establish `h3 : z * Cᵀ * JB * (z'.map c * (C.map c)ᵀ)ᵀ = z * (Cᵀ * JB * C.map c) * (z'.map c)ᵀ`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[h1, h2, h3, h]`. Simplify using the standard rewrite rules.
-/
theorem hTens_eq_zero {C : Matrix β ν E} (h : Cᵀ * JB * C.map c = 0) (z z' : Matrix α ν E) :
    hTens c JA JB (z * Cᵀ) (z' * Cᵀ) = 0 := by
  have h1 : ∀ x y : Matrix α β E, hTens c JA JB x y = ∑ i, ∑ i', JA i i' * (x * JB * (y.map c)ᵀ) i i' := fun x y => by
    unfold hTens
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have h2 : (z' * Cᵀ).map c = z'.map c * (C.map c)ᵀ := Matrix.map_mul (f := c.toRingHom)
  have h3 : z * Cᵀ * JB * (z'.map c * (C.map c)ᵀ)ᵀ = z * (Cᵀ * JB * C.map c) * (z'.map c)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, h2, h3, h]
  simp

def lagCo (co : Darboux (symp c ξ JA JB) κ) (C : Matrix β ν E) : Submodule k ((κ → k) × (κ → k)) where
  carrier := Set.range fun z : Matrix α ν E => co.e (z * Cᵀ)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by simp only [Matrix.add_mul, map_add]⟩
  smul_mem' := by
    rintro a _ ⟨z, rfl⟩
    exact ⟨a • z, by simp only [Matrix.smul_mul, map_smul]⟩

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩ _ ⟨z', rfl⟩`. Rewrite using `[← sub_eq_zero, ← co.form, symp, hTens_eq_zero h, mul_zero, map_zero]`.
-/
theorem lagCo_isotropic (co : Darboux (symp c ξ JA JB) κ) {C : Matrix β ν E} (h : Cᵀ * JB * C.map c = 0) :
    ∀ a ∈ lagCo co C, ∀ b ∈ lagCo co C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
  rw [← sub_eq_zero, ← co.form, symp, hTens_eq_zero h, mul_zero, map_zero]

/- English proof (translation)
Take `⟨h0, Cx, M, hx, h1, -⟩` from `h`. Use `finrank_eq _ (lagCo co Cx) (lagCo_isotropic co h0) (lagCo_isotropic co hx) ?_` and prove the remaining obligations. Rewrite `h1` using `[← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows]`. Rewrite using `[eq_top_iff]`. Introduce `w _`.

Take `⟨u, rfl⟩` from `co.e.surjective w`. Establish `hu : u = u * M.toRows₁ᵀ * Cᵀ + u * M.toRows₂ᵀ * Cxᵀ`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[hu, map_add]`. Conclude with `Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩`.
-/
theorem finrank_lagCo [DecidableEq β] [DecidableEq ν] (co : Darboux (symp c ξ JA JB) κ) {C : Matrix β ν E}
    (h : IsLagr c JB C) : Module.finrank k (lagCo co C) = Fintype.card κ := by
  obtain ⟨h0, Cx, M, hx, h1, -⟩ := h
  refine finrank_eq _ (lagCo co Cx) (lagCo_isotropic co h0) (lagCo_isotropic co hx) ?_
  rw [← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows] at h1
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, rfl⟩ := co.e.surjective w
  have hu : u = u * M.toRows₁ᵀ * Cᵀ + u * M.toRows₂ᵀ * Cxᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, h1, Matrix.transpose_one, Matrix.mul_one]
  rw [hu, map_add]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

end Pair

/- English proof (translation)
Introduce `k _ _ _ _ _ _ E _ _ _ _ c δ _ ψ hψ _ hψ1 α β ν κ _ _ _ _ _ _ _ ξ JA JB co Cy hC`. Establish `hiso` using `lagCo_isotropic co hC.1`. Establish `hdim` using `finrank_lagCo co hC`. Establish `hinv : ∀ l, IsYInv c ψ co Cy l → ∀ w ∈ lagCo co Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ`. Introduce and unpack `l hl _ ⟨z, rfl⟩ φ hφ`.

Conclude with `hl z φ hφ`. Use `⟨?_, fun l₁ l₂ h₁ h₂ => GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 κ _ hiso hdim l₁ l₂ (hinv _ h₁) (hinv _ h₂.1) h₂.2⟩` and prove the remaining obligations. Take `⟨l, h1, h2⟩` from `exists_form k ψ hψ hψ1 κ _ hiso hdim`. Conclude with `⟨l, fun z φ hφ => h1 _ ⟨z, rfl⟩ φ hφ, h2⟩`.
-/
theorem yform_line : ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (α β ν κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
    (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (co : Darboux (symp c ξ JA JB) κ) (Cy : Matrix β ν E), IsLagr c JB Cy →
    (∃ l, IsYForm c ψ co Cy l) ∧ ∀ l₁ l₂, IsYInv c ψ co Cy l₁ → IsYForm c ψ co Cy l₂ → ∃ z : ℂ, ∀ φ ∈ SB (κ → k), l₁ φ = z * l₂ φ := by
  intro k _ _ _ _ _ _ E _ _ _ _ c δ _ ψ hψ _ hψ1 α β ν κ _ _ _ _ _ _ _ ξ JA JB co Cy hC
  have hiso := lagCo_isotropic co hC.1
  have hdim := finrank_lagCo co hC
  have hinv : ∀ l, IsYInv c ψ co Cy l → ∀ w ∈ lagCo co Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by
    rintro l hl _ ⟨z, rfl⟩ φ hφ
    exact hl z φ hφ
  refine ⟨?_, fun l₁ l₂ h₁ h₂ => GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 κ _ hiso hdim l₁ l₂ (hinv _ h₁) (hinv _ h₂.1) h₂.2⟩
  obtain ⟨l, h1, h2⟩ := exists_form k ψ hψ hψ1 κ _ hiso hdim
  exact ⟨l, fun z φ hφ => h1 _ ⟨z, rfl⟩ φ hφ, h2⟩

end GlobalTheory.LagrFormLine

end
