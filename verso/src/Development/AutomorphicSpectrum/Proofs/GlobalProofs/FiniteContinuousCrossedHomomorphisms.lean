import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Cocycles

section Algebra

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem cocycle_map_one (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : f 1 = 0 := by
  simpa using hf 1 1

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cocycle_map_inv (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (a : G) :
    f a⁻¹ = -ρ a⁻¹ (f a) := by
  have h := hf a⁻¹ a
  rw [inv_mul_cancel, cocycle_map_one hf] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def cocycleKer (ρ : Representation k G V) (f : G → V)
    (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : Subgroup G where
  carrier := {g | ρ g = 1 ∧ f g = 0}
  one_mem' := ⟨map_one ρ, cocycle_map_one hf⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    rw [hf, ha', hb', map_zero, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have h2 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [ha, mul_one] at h2
    refine ⟨h1, ?_⟩
    rw [cocycle_map_inv hf, ha', map_zero, neg_zero]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by
  exact Iff.rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem cocycle_mul_mem (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by
  have hc' := ((mem_cocycleKer hf c).1 hc).2
  rw [hf, hc', map_zero, add_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem inv_mul_mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by
  refine (mem_cocycleKer hf _).2 ⟨?_, ?_⟩
  · rw [map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
  · rw [hf, cocycle_map_inv hf, h1, neg_add_cancel]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem injective_out_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    Function.Injective fun q : G ⧸ cocycleKer ρ f hf =>
      ((f q.out, ⇑(ρ q.out)) : V × (V → V)) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ρ q₁.out = ρ q₂.out := LinearMap.coe_injective h2
  rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
  exact inv_mul_mem_cocycleKer hf h1 h2'

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem index_cocycleKer [Finite V] (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    (cocycleKer ρ f hf).index ≠ 0 ∧
      (cocycleKer ρ f hf).index ≤ Nat.card (V × (V → V)) := by
  have hinj := injective_out_cocycleKer hf
  haveI : Finite (G ⧸ cocycleKer ρ f hf) := Finite.of_injective _ hinj
  exact ⟨Subgroup.index_ne_zero_of_finite, Nat.card_le_card_of_injective _ hinj⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_right_invariant [Finite V] (H : Subgroup G) (hH : H.index ≠ 0) :
    {f : G → V | ∀ g, ∀ c ∈ H, f (g * c) = f g}.Finite := by
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hH
  refine (Set.finite_range (fun φ : G ⧸ H → V => φ ∘ (QuotientGroup.mk : G → G ⧸ H))).subset ?_
  intro f₀ hf₀
  simp only [Set.mem_ofPred_eq] at hf₀
  refine ⟨fun q => f₀ q.out, ?_⟩
  funext g
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul H g
  simp only [Function.comp_apply]
  rw [hc]
  exact hf₀ g c c.2

end Algebra

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isOpen_cocycleKer {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by
  have hU : IsOpen ((⋂ v : A.V, (stabilizer A.ρ v : Set G)) ∩ {g | f g = 0}) :=
    (isOpen_iInter_of_finite fun v => IsDiscreteRep.isOpen_stabilizer v).inter (hlc.isOpen_fiber 0)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨Set.mem_iInter.2 fun v => ?_, cocycle_map_one hf⟩) ?_
  · rw [SetLike.mem_coe, mem_stabilizer, map_one]
    rfl
  · rintro g ⟨hg1, hg2⟩
    refine ⟨LinearMap.ext fun v => ?_, hg2⟩
    exact (mem_stabilizer A.ρ v g).1 (Set.mem_iInter.1 hg1 v)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem finite_cocycles : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V →
    (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) →
    {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  intro k G _ _ _ _ A _ hV hN
  refine ((hN (Nat.card (A.V × (A.V → A.V)))).biUnion (fun H hH => finite_right_invariant H hH.2.1)).subset ?_
  rintro f ⟨hlc, hf⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨cocycleKer A.ρ f hf, ⟨isOpen_cocycleKer A hlc hf, index_cocycleKer hf⟩,
    fun g c hc => cocycle_mul_mem hf g hc⟩

end GlobalTheory.CompanionTheory.Cocycles
