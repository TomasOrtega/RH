import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger

namespace GroundTheory.LocalField.Abstract

section FixedModule

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]

def fixedModule (H : Subgroup G) : Subgroup A where
  carrier := {a | ∀ g ∈ H, g • a = a}
  mul_mem' {a b} ha hb g hg := by rw [smul_mul', ha g hg, hb g hg]
  one_mem' g _ := smul_one g
  inv_mem' {a} ha g hg := by rw [smul_inv', ha g hg]

variable {A}

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_fixedModule {H : Subgroup G} {a : A} :
    a ∈ fixedModule A H ↔ ∀ g ∈ H, g • a = a :=
  Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem fixedModule_anti {H H' : Subgroup G} (h : H ≤ H') : fixedModule A H' ≤ fixedModule A H :=
  fun _ ha g hg => ha g (h hg)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem coe_fixedModule (H : Subgroup G) :
    (fixedModule A H : Set A) = MulAction.fixedPoints H A := by
  ext a
  simp only [SetLike.mem_coe, mem_fixedModule, MulAction.mem_fixedPoints, Subtype.forall,
    Subgroup.mk_smul]

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem smul_mem_fixedModule {H : Subgroup G} {a : A} (ha : a ∈ fixedModule A H) (g : G) :
    g • a ∈ fixedModule A (H.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨h, hh, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← mul_smul]
  rw [show g * h * g⁻¹ * g = g * h by group, mul_smul, ha h hh]

end FixedModule

section Discrete

class IsDiscreteModule (G : Type*) [Group G] [TopologicalSpace G] (A : Type*) [CommGroup A]
    [MulDistribMulAction G A] : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (MulAction.stabilizer G a : Set G)

variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isDiscreteModule_iff [ContinuousMul G] :
    IsDiscreteModule G A ↔ ∀ a : A, ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) := by
  constructor
  · intro h a
    exact ⟨⟨MulAction.stabilizer G a, h.isOpen_stabilizer a⟩, fun g hg => hg⟩
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨U, hU⟩ := h a
    exact Subgroup.isOpen_mono (H₁ := (U : Subgroup G)) (fun g hg => hU g hg) U.isOpen

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_openSubgroup_mem_fixedModule [IsDiscreteModule G A] (a : A) :
    ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) :=
  ⟨⟨MulAction.stabilizer G a, IsDiscreteModule.isOpen_stabilizer a⟩, fun _ hg => hg⟩

end Discrete

section Norm

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)

def cosetSMul (a : fixedModule A L) : K ⧸ L.subgroupOf K → A :=
  Quotient.lift (fun σ : K => (σ : G) • (a : A)) fun σ τ hστ => by
    have h : σ⁻¹ * τ ∈ L.subgroupOf K := QuotientGroup.leftRel_apply.mp hστ
    rw [Subgroup.mem_subgroupOf] at h
    have ha := a.2 _ h
    calc (σ : G) • (a : A) = (σ : G) • ((((σ⁻¹ * τ : K)) : G) • (a : A)) := by rw [ha]
      _ = (τ : G) • (a : A) := by rw [smul_smul]; simp

variable {A K L}

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cosetSMul_mk (a : fixedModule A L) (σ : K) :
    cosetSMul A K L a (σ : K ⧸ L.subgroupOf K) = (σ : G) • (a : A) :=
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately.
-/
theorem cosetSMul_one (q : K ⧸ L.subgroupOf K) : cosetSMul A K L 1 q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp

/- English proof (translation)
Proceed by induction. Treat this case separately.
-/
theorem cosetSMul_mul (a b : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    cosetSMul A K L (a * b) q = cosetSMul A K L a q * cosetSMul A K L b q := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp [smul_mul']

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem smul_cosetSMul (a : fixedModule A L) (g : K) (q : K ⧸ L.subgroupOf K) :
    (g : G) • cosetSMul A K L a q = cosetSMul A K L a (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, smul_smul]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation.
-/
theorem smul_mem_fixedModule_of_normal (hLK : L ≤ K) [hN : (L.subgroupOf K).Normal] {g : G}
    (hg : g ∈ K) {a : A} (ha : a ∈ fixedModule A L) : g • a ∈ fixedModule A L := by
  intro h hh
  have hc : g⁻¹ * h * g ∈ L := by
    have := hN.conj_mem ⟨h, hLK hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh) ⟨g, hg⟩⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  calc h • g • a = g • (g⁻¹ * h * g) • a := by simp [smul_smul, mul_assoc]
    _ = g • a := by rw [ha _ hc]

variable (A K L)

noncomputable def normFun (a : fixedModule A L) : A :=
  ∏ᶠ q, cosetSMul A K L a q

variable [(L.subgroupOf K).FiniteIndex]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem normFun_mem_fixedModule (a : fixedModule A L) : normFun A K L a ∈ fixedModule A K := by
  intro g hg
  unfold normFun
  rw [smul_finprod']
  simp_rw [smul_cosetSMul a ⟨g, hg⟩]
  exact finprod_comp_equiv (MulAction.toPerm (⟨g, hg⟩ : K))

noncomputable def norm : fixedModule A L →* fixedModule A K where
  toFun a := ⟨normFun A K L a, normFun_mem_fixedModule A K L a⟩
  map_one' := by
    ext
    simp [normFun, cosetSMul_one]
  map_mul' a b := by
    classical
    let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
    ext
    simp only [normFun, Subgroup.coe_mul, finprod_eq_prod_of_fintype, cosetSMul_mul,
      Finset.prod_mul_distrib]

variable {A K L}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_norm (a : fixedModule A L) :
    (norm A K L a : A) = ∏ᶠ q, cosetSMul A K L a q :=
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_smul [(L.subgroupOf K).Normal] (g : K) (a : fixedModule A L)
    (hga : (g : G) • (a : A) ∈ fixedModule A L) :
    norm A K L ⟨(g : G) • (a : A), hga⟩ = norm A K L a := by
  ext
  rw [coe_norm, coe_norm]
  have h : ∀ q : K ⧸ L.subgroupOf K,
      cosetSMul A K L ⟨(g : G) • (a : A), hga⟩ q = cosetSMul A K L a (q * (g : K ⧸ L.subgroupOf K)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [← QuotientGroup.mk_mul, cosetSMul_mk, cosetSMul_mk]
      simp [smul_smul]
  simp_rw [h]
  exact finprod_comp_equiv (Equiv.mulRight _)

variable (A K L)

def augmentation : Subgroup A :=
  Subgroup.closure {x | ∃ g ∈ K, ∃ a ∈ fixedModule A L, x = g • a / a}

abbrev tateZero : Type _ :=
  fixedModule A K ⧸ (norm A K L).range

abbrev tateNegOne : Type _ :=
  (norm A K L).ker ⧸
    (augmentation A K L).comap ((fixedModule A L).subtype.comp (norm A K L).ker.subtype)

variable {A K L}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem augmentation_le_map_ker (hLK : L ≤ K) [(L.subgroupOf K).Normal] :
    augmentation A K L ≤ (norm A K L).ker.map (fixedModule A L).subtype := by
  rw [augmentation, Subgroup.closure_le]
  rintro _ ⟨g, hg, a, ha, rfl⟩
  have hga := smul_mem_fixedModule_of_normal hLK hg ha
  refine ⟨⟨g • a, hga⟩ / ⟨a, ha⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_div, div_eq_one]
  exact norm_smul ⟨g, hg⟩ ⟨a, ha⟩ hga

end Norm

section Data

instance finiteIndex_openSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

variable {G : Type*} [Group G]

noncomputable def inertiaDegree (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  (K.map d).index

noncomputable def ramificationIndex (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  K.relIndex d.ker

variable (G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (A : Type*) [CommGroup A] [MulDistribMulAction G A]

structure ClassFieldData where

  deg : G →* Multiplicative ℤ̂
  continuous_deg : Continuous deg
  surjective_deg : Function.Surjective deg

  val : fixedModule A (⊤ : Subgroup G) →* Multiplicative ℤ̂

  intCast_mem_range_val : ∀ n : ℤ, Multiplicative.ofAdd (n : ℤ̂) ∈ val.range

  exists_eq_intCast_add_nsmul : ∀ n : ℕ, 0 < n → ∀ a : fixedModule A (⊤ : Subgroup G),
    ∃ (m : ℤ) (b : fixedModule A (⊤ : Subgroup G)),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b)

  range_val_comp_norm : ∀ K : OpenSubgroup G,
    (val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range =
      val.range.map (powMonoidHom (inertiaDegree deg (K : Subgroup G)))

def ClassFieldAxiom : Prop :=
  ∀ K L : OpenSubgroup G, L ≤ K → ∀ [((L : Subgroup G).subgroupOf K).Normal],
    IsCyclic (K ⧸ (L : Subgroup G).subgroupOf K) →
      Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) = (L : Subgroup G).relIndex K ∧
        Nat.card (tateNegOne A (K : Subgroup G) (L : Subgroup G)) = 1

structure ClassFieldTheory extends ClassFieldData G A where
  isDiscreteModule : IsDiscreteModule G A
  classFieldAxiom : ClassFieldAxiom G A

end Data

end GroundTheory.LocalField.Abstract
