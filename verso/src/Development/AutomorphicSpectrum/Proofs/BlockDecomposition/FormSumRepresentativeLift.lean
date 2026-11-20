import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Collapse
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem form_sum_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    {ι : Type} [Fintype ι] (a : ι → ℤ) (w : ι → Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (∑ i, a i • w i) u = ∑ i, a i • E.form σ I (w i) u := by
  unfold Frame.form
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, mul_smul_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem form_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    (a : ℤ) (w : Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (a • w) u = a • E.form σ I w u := by
  unfold Frame.form
  rw [map_zsmul, mul_smul_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sgn_eq_zero_of_not_injective {m : ℕ} (I : Idx m d) {J : Fin m → Fin d} (h : ¬ Function.Injective J) :
    sgn I J = 0 := by
  refine Finset.sum_eq_zero fun π _ => if_neg ?_
  intro e
  exact h (e ▸ I.2.injective.comp π.injective)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem exists_increasing {m : ℕ} {J : Fin m → Fin d} (h : Function.Injective J) :
    ∃ (I : Idx m d) (π : Equiv.Perm (Fin m)), J = I.1 ∘ π := by
  refine ⟨⟨J ∘ Tuple.sort J, (Tuple.monotone_sort J).strictMono_of_injective
    (h.comp (Tuple.sort J).injective)⟩, (Tuple.sort J)⁻¹, ?_⟩
  funext k
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sgn_comp_self {m : ℕ} (I : Idx m d) (π : Equiv.Perm (Fin m)) :
    sgn I (I.1 ∘ π) = (Equiv.Perm.sign π : ℤ) := by
  unfold sgn
  rw [Finset.sum_eq_single π]
  · simp
  · intro b _ hb
    refine if_neg fun e => hb ?_
    exact (Equiv.ext fun k => I.2.injective (congrFun e k)).symm
  · simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sgn_comp_of_ne {m : ℕ} {I I' : Idx m d} (π : Equiv.Perm (Fin m)) (h : I' ≠ I) :
    sgn I' (I.1 ∘ π) = 0 := by
  refine Finset.sum_eq_zero fun π' _ => if_neg fun e => h (Subtype.ext ?_)
  refine (StrictMono.range_inj I'.2 I.2).1 ?_
  have e' := congrArg Set.range e
  rw [π.surjective.range_comp, π'.surjective.range_comp] at e'
  exact e'.symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem rep_finset_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (t : Finset ι)
    {z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : ι → CH.H (sq a b) j}
    (h : ∀ i, CrystallineSemistableComparison.Pb.Rep a b (z i) (c i)) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i ∈ t, z i s) (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rep_zero fun s => Ideal.zero_mem _
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact rep_add (h i) ih

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rep_collapse_one {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (m : ℕ) (r : ℤ) (hr : r = m) (J : Fin m → Fin d) (w : Φ.A.obj E.D)
    (c : CH.H (gr Fil r) m) (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ J w) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (sgn I J • w) u) c := by
  have hw : w ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  by_cases hJ : Function.Injective J
  · obtain ⟨I, π, rfl⟩ := exists_increasing hJ
    obtain ⟨c₀, h₀⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 I.1 w hw
    have h₁ := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 I.1 w hw c₀ h₀).2.1 π
    obtain rfl := rep_unique h h₁
    have h₂ := GlobalTheory.CompanionTheory.AltForm.Rep.zsmul (Equiv.Perm.sign π : ℤ) h₀
    refine rep_congr h₂ fun u => ?_
    rw [Finset.sum_eq_single I, sgn_comp_self, form_zsmul, Pi.smul_apply, sub_self]
    · exact Ideal.zero_mem _
    · intro I' _ hI'
      rw [sgn_comp_of_ne π hI', zero_smul]
      unfold Frame.form
      simp
    · simp
  · obtain rfl := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 J w hw c h).1 hJ
    refine rep_zero fun u => ?_
    rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    · intro I _
      rw [sgn_eq_zero_of_not_injective I hJ, zero_smul]
      unfold Frame.form
      simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rep_collapse : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  intro R _ C _ Φ Fil d hF E σ hc m r hr ι _ J w x h
  have hw : ∀ i, w i ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun i => by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  choose c hcl using fun i => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 (J i) (w i) (hw i)
  obtain rfl := rep_unique h (rep_finset_sum Finset.univ hcl)
  have h₂ := rep_finset_sum Finset.univ fun i => rep_collapse_one hF E σ hc m r hr (J i) (w i) (c i) (hcl i)
  refine rep_congr h₂ fun u => ?_
  rw [Finset.sum_comm]
  have e : ∀ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u = ∑ i, E.form σ I.1 (sgn I (J i) • w i) u := by
    intro I
    rw [form_sum_zsmul]
    exact Finset.sum_congr rfl fun i _ => (form_zsmul E σ I.1 _ _ u).symm
  simp only [e, sub_self]
  exact Ideal.zero_mem _

end Collapse

end GlobalTheory.CompanionTheory.ConeLocal
