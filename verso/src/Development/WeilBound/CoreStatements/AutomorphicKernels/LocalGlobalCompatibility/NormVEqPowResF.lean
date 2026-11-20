import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

open scoped Pointwise Topology

namespace PositivityTheory.Pf1.CLGD.DescRes

section Groups

variable {E E' Ω : Type} [Field E] [Field E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω]

variable (E) in

def resG : G E' Ω →* G E Ω := AlgEquiv.restrictScalarsHom E

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resG_apply (σ : G E' Ω) (x : Ω) : resG E σ x = σ x := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resG_injective : Function.Injective (resG E (E' := E') (Ω := Ω)) :=
  AlgEquiv.restrictScalarsHom_injective E

variable [NumberField E] [NumberField E'] {A : ValuationSubring Ω}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem resG_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) : resG E σ ∈ Dec (F := E) A := by
  have h1 : σ • A = A := hσ
  show resG E σ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

variable (E A) in

def resDec : ↥(Dec (F := E') A) →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Dec σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_resDec (σ : ↥(Dec (F := E') A)) : ((resDec E A σ : ↥(Dec (F := E) A)) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure.

Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Equip the data with the indicated structure.

Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_normV_pow (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : ∃ f : ℕ, normV w' = normV w ^ f := by
  classical
  have hcomap : w.asIdeal = w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    ext x
    rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 E) (𝓞 E') x)]
    have e : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E E' Ω]
      rfl
    rw [e]
  have := w.isMaximal
  have := w'.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  letI := Ideal.Quotient.field w'.asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : Finite (𝓞 E' ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  letI := Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)
  letI : Algebra (𝓞 E ⧸ w.asIdeal) (𝓞 E' ⧸ w'.asIdeal) :=
    (Ideal.quotientMap w'.asIdeal (algebraMap (𝓞 E) (𝓞 E')) hcomap.le).toAlgebra
  refine ⟨Module.finrank (𝓞 E ⧸ w.asIdeal) (𝓞 E' ⧸ w'.asIdeal), ?_⟩
  rw [normV, normV, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

def resF (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : ℕ := (exists_normV_pow h h').choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normV_eq_pow_resF (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : normV w' = normV w ^ resF h h' :=
  (exists_normV_pow h h').choose_spec

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem actsAs_resG {f : ℕ} (hf : normV w' = normV w ^ f) {σ : G E' Ω} {a b : ℕ}
    (hσ : ActsAs A (normV w') σ a b) : ActsAs A (normV w) (resG E σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  rw [hf, ← pow_mul, ← pow_mul] at h1
  exact h1

variable (h : IsPlaceOver A w) (h' : IsPlaceOver A w')

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem resG_mem_Weil (σ : ↥(Weil h')) : resG E (σ : G E' Ω) ∈ Weil h := by
  obtain ⟨a, b, hσ⟩ := σ.2
  exact ⟨_, _, actsAs_resG (normV_eq_pow_resF h h') hσ⟩

def resW : ↥(Weil h') →* ↥(Weil h) where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_resW (σ : ↥(Weil h')) : ((resW h h' σ : ↥(Weil h)) : G E Ω) = resG E (σ : G E' Ω) := rfl

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_resW (σ : ↥(Weil h')) : deg (resW h h' σ) = (resF h h' : ℤ) * deg σ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  rw [deg_eq (σ := resW h h' σ) (actsAs_resG (normV_eq_pow_resF h h') hσ), deg_eq hσ]
  push_cast; ring

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem resG_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) : resG E σ ∈ Ine (F := E) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

omit [NumberField E] [NumberField E'] [IsAlgClosure E Ω] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_resG : Continuous (resG E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (resG E) ?_
  intro s hs
  rw [map_one] at hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).mp hs
  let b := Module.finBasis E L
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  refine ⟨IntermediateField.adjoin E' (Set.range fun i => (b i : Ω)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun σ hσ => hLs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  have hb : ∀ i, σ (b i : Ω) = b i := fun i => hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have hx' := congrArg (fun y : L => (y : Ω)) (b.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hx'
  rw [← hx']
  show (resG E σ) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, resG_apply, hb]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem IsSmooth.resW {M : Type*} [Monoid M] {φ : ↥(Weil h) →* M} (hφ : IsSmooth φ) :
    IsSmooth (φ.comp (resW h h')) := by
  have hc : Continuous fun σ : ↥(Ine (F := E') A) =>
      (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : ↥(Ine (F := E) A)) :=
    (continuous_resG.comp continuous_subtype_val).subtype_mk _
  exact hφ.preimage hc

end Groups

section WDRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def resRep (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := IsSmooth.resW h h' a.smooth
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have e : ((normV w' : ℕ) : ℂ) ^ deg σ = ((normV w : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      rw [deg_resW, normV_eq_pow_resF h h', Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    rw [e]
    exact a.comm _

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resRep_ρ (a : WDRep h V) (σ : ↥(Weil h')) : (resRep h h' a).ρ σ = a.ρ (resW h h' σ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resRep_N (a : WDRep h V) : (resRep h h' a).N = a.N := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem iso_resRep {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : (resRep h h' a).Iso (resRep h h' b) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => h1 _ v, h2⟩

def WD.res : WD h → WD h' :=
  Quotient.map (fun a => ⟨a.1, resRep h h' a.2⟩) (fun _ _ hab => iso_resRep h h' hab)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem WD.res_mk (a : WDRep h V) : WD.res h h' (WD.mk a) = WD.mk (resRep h h' a) := by
  show Quotient.mk _ (⟨_, resRep h h' (WD.std a).2⟩ : Σ n : ℕ, WDRep h' (Fin n → ℂ)) = _
  rw [WD.quotientMk_eq]
  exact WD.sound (iso_resRep h h' (WD.iso_std a).symm)

end WDRes

end PositivityTheory.Pf1.CLGD.DescRes
