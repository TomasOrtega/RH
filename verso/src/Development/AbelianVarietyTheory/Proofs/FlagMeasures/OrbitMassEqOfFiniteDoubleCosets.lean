import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolumeStatement
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H g`. Establish `hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆ {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0}`. Introduce `γ hγ`. Simplify using `only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ`.

Use `⟨hγ.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `hγ.2`. Rewrite `h2` using `[MulAction.Quotient.smul_coe, QuotientGroup.eq]`. Use `K0.inv_mem h2` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Establish `hfin` using `(hF g).subset hsub`. Establish `hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty` using `⟨1, Subgroup.one_mem _⟩`. Prove the components needed by the constructor for the conclusion. Rewrite using `[ne_eq, ENNReal.inv_eq_zero]`. Introduce `h`.

Establish `: (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤`. Conclude with `h` after adjusting the coercions. Conclude with `(Set.encard_ne_top_iff.2 hfin) this`. Rewrite using `[ne_eq, ENNReal.inv_eq_top]`. Introduce `h`.

Establish `: (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0`. Conclude with `h` after adjusting the coercions. Conclude with `hne.ne_empty (Set.encard_eq_zero.1 this)`.
-/
theorem inv_encard_stab_ne {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) (y : G ⧸ K0) :
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ 0 ∧
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ ⊤ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆
        {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0} := by
      intro γ hγ
      simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
      refine ⟨hγ.1, ?_⟩
      have h2 := hγ.2
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
      have := K0.inv_mem h2
      simpa [mul_assoc] using this
    have hfin := (hF g).subset hsub
    have hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty :=
      ⟨1, Subgroup.one_mem _⟩
    constructor
    · rw [ne_eq, ENNReal.inv_eq_zero]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤ := by
        exact_mod_cast h
      exact (Set.encard_ne_top_iff.2 hfin) this
    · rw [ne_eq, ENNReal.inv_eq_top]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0 := by
        exact_mod_cast h
      exact hne.ne_empty (Set.encard_eq_zero.1 this)

/- English proof (translation)
Take `⟨S, hS⟩` from `hS`. Establish `hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))`. Set `f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0)` to `fun a => Quotient.mk _ ((a.1 : G) : G ⧸ K0)`. Use `Finite.of_surjective f ?_` and prove the remaining obligations. Introduce `o`.

Proceed by induction on `o using Quotient.inductionOn with`. Consider the case `h y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H g`. Take `⟨a, ha, γ, hγ, κ, hκ, rfl⟩` from `hS g`.

Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Apply `Quotient.sound` to reduce the goal to its premises. Use `⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩` and prove the remaining obligations. Use `show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _`. Rewrite using `[MulAction.Quotient.smul_coe, QuotientGroup.eq]`.

Simplify `K0.inv_mem hκ` using `[mul_assoc]`. Use `Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite using `[ne_eq, ENNReal.tsum_eq_zero, not_forall]`. Conclude with `⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩`.

Rewrite using `[tsum_fintype]`. Conclude with `ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)`.
-/
theorem mass_quotient_pos_finite {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) :
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ 0 ∧
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ ⊤ := by
  obtain ⟨S, hS⟩ := hS
  have hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0)) := by
    let f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0) := fun a =>
      Quotient.mk _ ((a.1 : G) : G ⧸ K0)
    refine Finite.of_surjective f ?_
    intro o
    induction o using Quotient.inductionOn with
    | h y =>
      induction y using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Quotient.sound
        refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
        show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _
        rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa [mul_assoc] using K0.inv_mem hκ
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))
  constructor
  · rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    exact ⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)

/- English proof (translation)
Introduce `G _ Γ K0 hS hF`. Take `⟨V, hV⟩` from `GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0`. Establish `hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0` using `MulAction.stabilizer_quotient K0`. Establish `h0` using `hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)`. Establish `horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0)`.

Introduce `y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩`. Simplify using `only [horb, ite_true, hstab] at h0`. Rewrite `h0` using `[show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one, mul_one]`.

Take `⟨hV0, hVt⟩` from `mass_quotient_pos_finite Γ K0 hS hF`. Establish `hV0' : V ≠ 0` using `by rw [← h0]; exact hV0`. Establish `hVt' : V ≠ ⊤` using `by rw [← h0]; exact hVt`. Use `⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']`.
-/
theorem mass_orbit_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0 hS hF
  obtain ⟨V, hV⟩ := GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0 := MulAction.stabilizer_quotient K0
  have h0 := hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
    (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
  have horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩
  simp only [horb, ite_true, hstab] at h0
  rw [show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one,
    mul_one] at h0
  obtain ⟨hV0, hVt⟩ := mass_quotient_pos_finite Γ K0 hS hF
  have hV0' : V ≠ 0 := by rw [← h0]; exact hV0
  have hVt' : V ≠ ⊤ := by rw [← h0]; exact hVt
  refine ⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩
  rw [hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']

end GlobalTheory.HL
