import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `X' Z' i' _ Y' hY N hN`. Set `K : Ideal Γ(X', Y')` to `{ carrier := {f | X'.basicOpen f ≤ N} add_mem' hf hg := (X'.basicOpen_add_le _ _).trans (sup_le hf hg) zero_mem' := by simp smul_mem' c f hf := by`. Express the relevant statement in the definitionally equal form `X'.basicOpen (c * f) ≤ N`. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `inf_le_right.trans hf }`.

Establish `hmem (z : Spec Γ(X', Y')) (f : Γ(X', Y')) : hY.fromSpec z ∈ X'.basicOpen f ↔ f ∉ z.asIdeal`. Express the relevant statement in the definitionally equal form `z ∈ hY.fromSpec ⁻¹ᵁ X'.basicOpen f ↔ _`. Rewrite using `[hY.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Establish `hJ : RingHom.ker (i'.app Y').hom ⊔ K = ⊤`.

Assume the negation of the conclusion as `h`. Take `⟨m, hm, hJm⟩` from `Ideal.exists_le_maximal _ h`. Set `z : Spec Γ(X', Y')` to `⟨m, hm.isPrime⟩`. Establish `hyY : hY.fromSpec z ∈ Y'` using `hY.range_fromSpec.le ⟨z, rfl⟩`. Distinguish the cases in `hy : hY.fromSpec z ∈ Set.range i'`.

Take `⟨w, hw⟩` from `hy`. Establish `hwN : hY.fromSpec z ∈ N` using `hw ▸ hN w (hw ▸ hyY)`. Take `⟨f, hfN, hf⟩` from `hY.exists_basicOpen_le (V := N) ⟨_, hwN⟩ hyY`. Conclude with `(hmem z f).mp hf (hJm (Ideal.mem_sup_right hfN))`. Establish `h1 : hY.fromSpec z ∉ (i'.ker.support : Set X')`.

Rewrite using `[Scheme.Hom.support_ker, i'.isClosedEmbedding.isClosed_range.closure_eq]`. Conclude with `hy`. Establish `h2 : hY.fromSpec z ∉ X'.zeroLocus (U` using `Y') (i'.ker.ideal ⟨Y', hY⟩ : Set Γ(X', Y')) := fun h ↦ h1 ((i'.ker.coe_support_inter ⟨Y', hY⟩).ge ⟨h, hyY⟩).1`. Rewrite `h2` using `[Scheme.mem_zeroLocus_iff]`. Use `push_neg at h2`.

Take `⟨a, ha, hya⟩` from `h2`. Establish `ha' : a ∈ RingHom.ker (i'.app Y').hom`. Rewrite `ha` using `[Scheme.Hom.ker_apply]`. Conclude with `ha`. Conclude with `(hmem z a).mp hya (hJm (Ideal.mem_sup_left ha'))`.

Establish `h1 : (1 : Γ(X', Y')) ∈ RingHom.ker (i'.app Y').hom ⊔ K` using `hJ ▸ Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1`. Use `⟨b, ?_, hb⟩` and prove the remaining obligations. Establish `ha0 : (i'.app Y').hom a = 0` using `ha`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion :
    ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  intro X' Z' i' _ Y' hY N hN
  classical
  let K : Ideal Γ(X', Y') :=
    { carrier := {f | X'.basicOpen f ≤ N}
      add_mem' hf hg := (X'.basicOpen_add_le _ _).trans (sup_le hf hg)
      zero_mem' := by simp
      smul_mem' c f hf := by
        change X'.basicOpen (c * f) ≤ N
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  have hmem (z : Spec Γ(X', Y')) (f : Γ(X', Y')) :
      hY.fromSpec z ∈ X'.basicOpen f ↔ f ∉ z.asIdeal := by
    change z ∈ hY.fromSpec ⁻¹ᵁ X'.basicOpen f ↔ _
    rw [hY.fromSpec_preimage_basicOpen]
    rfl
  have hJ : RingHom.ker (i'.app Y').hom ⊔ K = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ h
    let z : Spec Γ(X', Y') := ⟨m, hm.isPrime⟩
    have hyY : hY.fromSpec z ∈ Y' := hY.range_fromSpec.le ⟨z, rfl⟩
    by_cases hy : hY.fromSpec z ∈ Set.range i'
    · obtain ⟨w, hw⟩ := hy
      have hwN : hY.fromSpec z ∈ N := hw ▸ hN w (hw ▸ hyY)
      obtain ⟨f, hfN, hf⟩ := hY.exists_basicOpen_le (V := N) ⟨_, hwN⟩ hyY
      exact (hmem z f).mp hf (hJm (Ideal.mem_sup_right hfN))
    · have h1 : hY.fromSpec z ∉ (i'.ker.support : Set X') := by
        rw [Scheme.Hom.support_ker, i'.isClosedEmbedding.isClosed_range.closure_eq]
        exact hy
      have h2 : hY.fromSpec z ∉ X'.zeroLocus (U := Y') (i'.ker.ideal ⟨Y', hY⟩ : Set Γ(X', Y')) :=
        fun h ↦ h1 ((i'.ker.coe_support_inter ⟨Y', hY⟩).ge ⟨h, hyY⟩).1
      rw [Scheme.mem_zeroLocus_iff] at h2
      push_neg at h2
      obtain ⟨a, ha, hya⟩ := h2
      have ha' : a ∈ RingHom.ker (i'.app Y').hom := by
        rw [Scheme.Hom.ker_apply] at ha
        exact ha
      exact (hmem z a).mp hya (hJm (Ideal.mem_sup_left ha'))
  have h1 : (1 : Γ(X', Y')) ∈ RingHom.ker (i'.app Y').hom ⊔ K := hJ ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  refine ⟨b, ?_, hb⟩
  have ha0 : (i'.app Y').hom a = 0 := ha
  calc (i'.app Y').hom b = (i'.app Y').hom (a + b) := by rw [map_add, ha0, zero_add]
    _ = 1 := by rw [hab, map_one]

end GlobalTheory
