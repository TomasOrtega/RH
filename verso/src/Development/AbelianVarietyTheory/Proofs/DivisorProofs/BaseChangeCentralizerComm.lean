import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKCentAf

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem baseChange_centralizer_comm (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
      y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  intro y
  rw [← sub_eq_zero, had, hex' y]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hmap z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hmap z).symm⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem commute_of_centralizer (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [CommRing A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) (y z : k ⊗[K] B)
    (hy : y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y)
    (hz : z * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * z) : y * z = z * y := by
  obtain ⟨y', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent y).1 hy
  obtain ⟨z', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent z).1 hz
  rw [← map_mul, ← map_mul, mul_comm]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cent_iff_mem (P : Pair G) (y : G.C) :
    y * (P.γ : G.C) = (P.γ : G.C) * y ↔
      y ∈ Set.range ((Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro h
    have hy : y ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      simpa using h.symm
    rw [hcsa] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [hcsa]; exact w.2
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact (hw _ rfl).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_commute (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t)
    (a : G.GAf) (ha : a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self)) :
    (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
      ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) *
        (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom P.γ with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C) := rfl
  have hδ : ((P.toAf x t hx P.self : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
  simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
  rw [hδ] at h1
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
    calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
      _ = U * (x⁻¹ * A * x) := by group
  rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem twCent_comm : ∀ {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
    ∀ a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self),
    ∀ b ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self), a * b = b * a := by
  intro p _ G P x t hx a ha b hb
  have hc := commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _ (cent_iff_mem P) _ _
    (conj_commute P x t hx a ha) (conj_commute P x t hx b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

end GlobalTheory.LKCentAf
