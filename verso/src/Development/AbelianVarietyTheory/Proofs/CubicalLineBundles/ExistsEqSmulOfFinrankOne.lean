import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LatData

section General

variable {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_span_smul_mem {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ (v : Fin r → M) (c : R), c ≠ 0 ∧ ∀ m : M, ∃ s : Fin r → R, c • m = ∑ i, s i • v i := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  refine ⟨v, c, nonZeroDivisors.ne_zero hc0, fun m => ?_⟩
  have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_range_iff_exists_fun] at h3
  obtain ⟨s, hs⟩ := h3
  exact ⟨s, hs.symm⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem finrank_add_le_of_disjoint {A B : Submodule R M} (h : Disjoint A B) :
    Module.finrank R A + Module.finrank R B ≤ Module.finrank R M := by
  have h1 := A.finrank_quotient_add_finrank
  have h2 : Module.finrank R B ≤ Module.finrank R (M ⧸ A) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := A.mkQ ∘ₗ B.subtype) ?_
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact Subtype.ext (Submodule.disjoint_def.1 h _ ((Submodule.Quotient.mk_eq_zero A).1 hb) b.2)
  omega

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := fun h => by
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have := H.sqrt_neg_disc_sq
  rw [h0] at this
  exact H.d_prime.ne_zero (by simpa using this)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem exists_embedding (H : Host E) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : ∃ τ : E →+* ℂ, τ (H.rt : E) = ρ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans hρ.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    have hre : ρ.re = 0 := by
      have e1 := congrArg Complex.re hρ
      have e2 := congrArg Complex.im hρ
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
      simp [pow_two] at e1 e2
      have e3 : ρ.re * ρ.im = 0 := by linarith
      rcases mul_eq_zero.1 e3 with e | e
      · exact e
      · rw [e] at e1
        nlinarith [mul_self_nonneg ρ.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem card_le_finrank_lat {ρ ρ' : ℂ} (hne : ρ ≠ ρ') {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP ρ ⊔ PureType.lat hP ρ') {τ : E →+* ℂ} (hτ : τ (H.rt : E) = ρ) :
    Nat.card {i // ty i = τ} ≤ Module.finrank (𝓞 E) (PureType.lat hP ρ) := by
  classical
  have := D.fin
  obtain ⟨v, c, hc, hv⟩ := exists_span_smul_mem (R := 𝓞 E) (M := PureType.lat hP ρ) rfl
  let pr : (Fin g → ℂ) →ₗ[ℂ] ({i // ty i = τ} → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  have hsm : ∀ (s : 𝓞 E) (a : D.La), pr (Pe (s • a)) = τ (s : E) • pr (Pe a) := fun s a => by
    funext i
    simp only [pr, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
    rw [hP.1, i.2]
  let W : Submodule ℂ ({i // ty i = τ} → ℂ) := Submodule.span ℂ (Set.range fun i => pr (Pe (v i)))
  have h1 : ∀ a : PureType.lat hP ρ, pr (Pe a) ∈ W := fun a => by
    obtain ⟨s, hs⟩ := hv a
    have hc' : τ (c : E) ≠ 0 := by simpa using hc
    rw [← W.smul_mem_iff hc', ← hsm, ← Submodule.coe_smul, hs, Submodule.coe_sum, map_sum, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [Submodule.coe_smul, hsm]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ a : D.La, pr (Pe a) ∈ W := fun a => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hs a)
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hy0 : pr (Pe y) = 0 := funext fun i => hy i (by rw [i.2, hτ]; exact hne)
    rw [← W.smul_mem_iff hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul, ← hxy, map_add, map_add, hy0,
      add_zero]
    exact h1 ⟨x, hx⟩
  have h3 : W = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨z, rfl⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ
      (Subtype.val : {i // ty i = τ} → Fin g) Subtype.val_injective w
    have hz : z ∈ Submodule.span ℝ (Set.range Pe) := by rw [hP.2.2.2.1]; trivial
    have : Submodule.span ℝ (Set.range Pe) ≤ (W.comap pr).restrictScalars ℝ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h2 a)
    exact this hz
  have h4 := finrank_le_of_span_eq_top h3
  simpa [Nat.card_eq_fintype_card] using h4

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_lat (ht : IsTypeFn H D.p D.q ty) {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP H.rt0 ⊔ PureType.lat hP (-H.rt0)) :
    Module.finrank (𝓞 E) (PureType.lat hP H.rt0) = D.p ∧
      Module.finrank (𝓞 E) (PureType.lat hP (-H.rt0)) = D.q := by
  have := D.fin
  have hne := rt0_ne_neg H
  obtain ⟨τ, hτ⟩ := exists_embedding H H.sqrt_neg_disc_sq
  obtain ⟨τ', hτ'⟩ := exists_embedding H (ρ := -H.rt0) (by rw [neg_sq, H.sqrt_neg_disc_sq])
  have h1 := card_le_finrank_lat hP hne hn hs hτ
  have h2 := card_le_finrank_lat hP hne.symm hn (fun a => sup_comm (PureType.lat hP H.rt0) _ ▸ hs a) hτ'
  rw [(ht τ).1 hτ] at h1
  rw [(ht τ').2 (by rw [hτ']; exact hne.symm)] at h2
  have h3 := finrank_add_le_of_disjoint (PureType.disjoint_lat hP hne)
  rw [D.rank] at h3
  omega

end GlobalTheory.CM.LatData

namespace GlobalTheory.CM

end GlobalTheory.CM
