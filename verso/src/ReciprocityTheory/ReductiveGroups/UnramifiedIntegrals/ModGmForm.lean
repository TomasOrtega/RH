import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmSlash

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `e : f = ⇑g` using `funext fun τ => (hg τ).symm`. Substitute `e` using the available equality. Conclude with `ModularFormClass.holo g`.
-/
theorem IsMF.mdiff {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : MDiff f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.holo g

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `e : f = ⇑g` using `funext fun τ => (hg τ).symm`. Substitute `e` using the available equality. Conclude with `ModularFormClass.bdd_at_infty g`.
-/
theorem IsMF.bdd {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : IsBoundedAtImInfty f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.bdd_at_infty g

/- English proof (translation)
Establish `h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im`. Rewrite using `[Complex.div_natCast_im]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im`.

Rewrite using `[h1]`. Use `τ.im_pos` as an intermediate fact. Establish `ha' : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Check the signs of the components of the expression.

Unfold `pt`. Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos hpos]`. Conclude with `h1`.
-/
theorem pt_im {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    (pt a b e τ).im = (a : ℝ) / e * τ.im := by
  have h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im := by
    rw [Complex.div_natCast_im]
    simp
    ring
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im := by
    rw [h1]
    have := τ.im_pos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  exact h1

/- English proof (translation)
Rewrite `hf`, the goal using `[UpperHalfPlane.mdifferentiable_iff]`. Establish `hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im}`. Introduce `z hz`. Establish `h` using `pt_im ha he b ⟨z, hz⟩`. Establish `h2` using `congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)`.

Establish `h3` using `(pt a b e ⟨z, hz⟩).im_pos`. Rewrite `h2` using `[UpperHalfPlane.coe_im]`. Rewrite `h3` using `[h2]`. Conclude with `h3`. Establish `hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im}` using `by fun_prop`.

Use `(hf.comp hd hmap).congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]`.
-/
theorem mdiff_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (fun τ => f (pt a b e τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rw [h2] at h3
    exact h3
  have hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} := by
    fun_prop
  refine (hf.comp hd hmap).congr fun z hz => ?_
  simp only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]

/- English proof (translation)
Rewrite using `[UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]`. Establish `h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im` using `funext fun τ => pt_im ha he b τ`. Rewrite using `[h]`. Establish `ha' : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`.

Establish `hc : (0 : ℝ) < (a : ℝ) / e` using `by positivity`. Conclude with `Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap`.
-/
theorem tendsto_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) :
    Filter.Tendsto (pt a b e) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im := funext fun τ => pt_im ha he b τ
  rw [h]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : (0 : ℝ) < (a : ℝ) / e := by positivity
  exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap

/- English proof (translation)
Conclude with `hf.comp_tendsto (tendsto_pt ha he b)`.
-/
theorem bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (fun τ => f (pt a b e τ)) := by
  exact hf.comp_tendsto (tendsto_pt ha he b)

/- English proof (translation)
Establish `hA` using `isMF_AA.mdiff`. Establish `hD` using `isMF_DD.mdiff`. Conclude with `(hA.mul (mdiff_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)`.
-/
theorem fac_mdiff {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : MDiff (fac t) := by
  have hA := isMF_AA.mdiff
  have hD := isMF_DD.mdiff
  exact (hA.mul (mdiff_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

/- English proof (translation)
Establish `hA` using `isMF_AA.bdd`. Establish `hD` using `isMF_DD.bdd`. Conclude with `(hA.mul (bdd_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)`.
-/
theorem fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty (fac t) := by
  have hA := isMF_AA.bdd
  have hD := isMF_DD.bdd
  exact (hA.mul (bdd_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

/- English proof (translation)
Unfold `Gm`. Establish `key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Simplify using `using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))`. Consider the case `insert t s ht ih`. Introduce `hs`. Simplify using `only [Finset.prod_insert ht]`.

Conclude with `(fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))`. Conclude with `key _ subset_rfl`.
-/
theorem Gm_mdiff {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact (fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

/- English proof (translation)
Unfold `Gm`. Establish `key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → IsBoundedAtImInfty (fun τ => ∏ t ∈ s, fac t τ)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Simplify using `only [Finset.prod_empty]`. Conclude with `Filter.const_boundedAtFilter atImInfty (1 : ℂ)`. Consider the case `insert t s ht ih`. Introduce `hs`.

Simplify using `only [Finset.prod_insert ht]`. Conclude with `Filter.BoundedAtFilter.mul (fac_bdd (Tm_pos hm (hs (Finset.mem_insert_self t s)))) (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))`. Conclude with `key _ subset_rfl`.
-/
theorem Gm_bdd {m : ℕ} (hm : 0 < m) : IsBoundedAtImInfty (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → IsBoundedAtImInfty (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact Filter.BoundedAtFilter.mul (fac_bdd (Tm_pos hm (hs (Finset.mem_insert_self t s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Rewrite using `[SL_slash_apply, Gm_smul hm γ τ]`. Establish `hd : denom γ τ ≠ 0` using `denom_ne_zero _ τ`. Establish `: (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[this, zpow_neg, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem Gm_slash {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ τ
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp

/- English proof (translation)
Use `⟨{ toFun := Gm m slash_action_eq' := ?_ holo' := Gm_mdiff hm bdd_at_cusps' := ?_ }, fun τ => rfl⟩` and prove the remaining obligations. Introduce `A hA`. Take `⟨A, rfl⟩` from `hA`. Conclude with `Gm_slash hm A`. Introduce `c hc`.

Rewrite using `[OnePoint.isBoundedAt_iff_forall_SL2Z hc]`. Introduce `γ _`. Rewrite using `[Gm_slash hm γ]`. Conclude with `Gm_bdd hm`.
-/
theorem gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) (Gm m) := by
  refine ⟨{ toFun := Gm m
            slash_action_eq' := ?_
            holo' := Gm_mdiff hm
            bdd_at_cusps' := ?_ }, fun τ => rfl⟩
  · intro A hA
    obtain ⟨A, rfl⟩ := hA
    exact Gm_slash hm A
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [Gm_slash hm γ]
    exact Gm_bdd hm

end ReciprocityTheory.ChartRestriction.L1
