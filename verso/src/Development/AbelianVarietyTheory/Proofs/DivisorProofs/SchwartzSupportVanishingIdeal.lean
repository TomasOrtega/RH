import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

namespace GlobalTheory.SBVanish

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Assume the negation of the conclusion and derive a contradiction. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem mem_of_sep {G β : Type} [AddCommGroup G] (e : β → G → ℂ) (B : Set β)
    (he : ∀ b t u, e b (t + u) = e b t * e b u) (S W : Submodule ℂ (G → ℂ))
    (hS : ∀ f ∈ S, ∀ b, (fun t => e b t * f t) ∈ S)
    (hW : ∀ f ∈ S, ∀ b ∈ B, (fun t => e b t * f t) - f ∈ W) (K : AddSubgroup G) (P : Finset G) :
    (∀ p ∈ P, ∃ b ∈ B, (∀ u ∈ K, e b u = 1) ∧ e b p ≠ 1) →
    ∀ f ∈ S, (∀ t, f t ≠ 0 → ∃ p ∈ P, ∃ u ∈ K, t = p + u) → f ∈ W := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro _ f _ h3
    convert W.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro hsep f hf h3
    obtain ⟨b, hbB, hb1, hne⟩ := hsep s (Finset.mem_insert_self _ _)
    have hne' : e b s - 1 ≠ 0 := sub_ne_zero.2 hne
    have h1 : (e b s • f - fun t => e b t * f t) ∈ W := by
      refine ih (fun p hp => hsep p (Finset.mem_insert_of_mem hp)) _
        (sub_mem (S.smul_mem _ hf) (hS f hf b)) fun t ht => ?_
      have hft : f t ≠ 0 := fun h => ht (by simp [h])
      obtain ⟨p, hp, u, hu, rfl⟩ := h3 t hft
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact absurd (by simp [he, hb1 u hu]) ht
      · exact ⟨p, hp, u, hu, rfl⟩
    have h2 := W.smul_mem (e b s - 1)⁻¹ (add_mem h1 (hW f hf b hbB))
    convert h2 using 1
    funext t
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_span_of_vanish : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, ‖ψ0 x‖ = 1) → ψ0 ≠ 1 → ∀ (I : Set (Y × Y')) (φ : Matrix Y Y' k → ℂ), φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k) →
    (∀ t : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t r q = 0) → φ t = 0) →
    φ ∈ Submodule.span ℂ {f | ∃ z : Matrix Y Y' k, (∀ r q, (r, q) ∉ I → z r q = 0) ∧
      ∃ φ' ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), f = (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ' t) - φ'} := by
  intro k _ _ _ _ _ Y Y' _ _ _ _ ψ0 hc hn1 hne I φ hφ hv
  classical
  let ψk : AddChar k Circle :=
    { toFun := fun x => ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (hn1 x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun x y => Circle.ext (ψ0.map_add_eq_mul x y) }
  have hψk : ∀ x, (ψk x : ℂ) = ψ0 x := fun _ => rfl
  have hck : Continuous ψk := hc.subtype_mk _
  have hk1 : ψk ≠ 1 := fun h => hne (by
    ext x
    rw [← hψk, h]
    simp)
  obtain ⟨n, hn, hinv, hsupp⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' φ hφ
  obtain ⟨P, hP⟩ := GlobalTheory.IrredSB.cover (k := k) (Y := Y) (Y' := Y') hn hn
  have hn' : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  refine mem_of_sep (fun b t => (ψk (GlobalTheory.IrredSB.pair b t) : ℂ)) {z | ∀ r q, (r, q) ∉ I → z r q = 0}
    (fun b t u => by rw [GlobalTheory.IrredSB.pair_add_right, AddChar.map_add_eq_mul, Circle.coe_mul])
    (GlobalTheory.WeilM.SB (Matrix Y Y' k)) _ (fun f hf b => GlobalTheory.IrredSB.modul_mem_SB ψk hck hf b)
    ?_ (GlobalTheory.IrredSB.lat k Y Y' n)
    (P.filter fun p => φ p ≠ 0) ?_ φ hφ ?_
  · intro f hf b hb
    refine Submodule.subset_span ⟨b, hb, f, hf, ?_⟩
    simp only [hψk, GlobalTheory.IrredSB.pair, mul_comm (b _ _)]
  · intro p hp
    have hp0 : φ p ≠ 0 := (Finset.mem_filter.1 hp).2
    have : ¬ ∀ r q, (r, q) ∈ I → (n : k)⁻¹ * p r q ∈ 𝒪[k] := fun h => hp0 (by
      let u : Matrix Y Y' k := fun r q => if (r, q) ∈ I then -((n : k)⁻¹ * p r q) else 0
      have hu : ∀ r q, u r q ∈ 𝒪[k] := fun r q => by
        by_cases hI : (r, q) ∈ I
        · simp only [u, if_pos hI]
          exact neg_mem (h r q hI)
        · simp only [u, if_neg hI]
          exact zero_mem _
      rw [← hinv u hu p]
      refine hv _ fun r q hI => ?_
      show p r q + n • u r q = 0
      simp only [u, if_pos hI, nsmul_eq_mul]
      field_simp
      ring)
    push Not at this
    obtain ⟨r, q, hI, hrq⟩ := this
    obtain ⟨b, hb, hb'⟩ := GlobalTheory.IrredSB.exists_sep ψk hck hk1 hrq
    refine ⟨Matrix.single r q (b * (n : k)⁻¹), fun r' q' h' => ?_, ?_, ?_⟩
    · refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact h' hI
    · rintro _ ⟨u, hu, rfl⟩
      rw [GlobalTheory.IrredSB.pair_single]
      have : b * (n : k)⁻¹ * (nsmulAddMonoidHom n u : Matrix Y Y' k) r q = b * u r q := by
        show b * (n : k)⁻¹ * (n • u r q) = b * u r q
        rw [nsmul_eq_mul]
        field_simp
      rw [this, hb _ (hu r q)]
      rfl
    · rw [GlobalTheory.IrredSB.pair_single, mul_assoc]
      exact fun h => hb' (Circle.ext h)
  · intro t ht
    obtain ⟨p, hp, _, ⟨u, hu, rfl⟩, rfl⟩ := hP t (hsupp t ht)
    refine ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩, _, ⟨u, hu, rfl⟩, rfl⟩
    rw [← hinv u hu p]
    exact ht

end GlobalTheory.SBVanish
