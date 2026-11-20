import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `Γ _ K K₀ K₁ KN KM hMN hNK hN0 hM1 h10 hnorm hdec b₀ hb₀ u hu`. Take `⟨a, haK, ha0, hau⟩` from `hdec u⁻¹ (inv_mem hu)`. Establish `hconj : ∀ m ∈ KM, a⁻¹ * m * a ∈ KM`. Introduce `m hm`. Simplify using `using hnorm a⁻¹ (inv_mem ha0) m hm`.

Establish `hmem : ∀ (c : ↥K ⧸ KN.subgroupOf K) (n : ↥KN ⧸ KM.subgroupOf KN), b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹ ∈ K₁ → b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a ∈ K ⊓ K₁`. Introduce `c n hcn`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb₀) (Quotient.out c).2) (hNK (Quotient.out n).2)) haK`. Establish `hua : u * a ∈ K₁` using `by simpa using K₁.inv_mem hau`.

Rewrite using `[show b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a = (b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹) * (u * a) by group]`. Conclude with `K₁.mul_mem hcn hua`. Use `Eq.trans (b := Nat.card ((K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ?_ rfl` and prove the remaining obligations. Use `Nat.card_eq_of_bijective (fun cn => (QuotientGroup.mk ⟨_, hmem cn.1.1 cn.1.2 cn.2⟩ : (K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨c₁, n₁⟩, h₁⟩ ⟨⟨c₂, n₂⟩, h₂⟩ h`.

Rewrite `h` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv] at h`. Establish `h' : ((Quotient.out n₁ : ↥KN) : Γ)⁻¹ * ((Quotient.out c₁ : ↥K) : Γ)⁻¹ * ((Quotient.out c₂ : ↥K) : Γ) * ((Quotient.out n₂ : ↥KN) : Γ) ∈ KM`. Use `hnorm a ha0 _ h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Establish `hc : c₁ = c₂`. Rewrite using `[← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `KN.mul_mem (KN.mul_mem (Quotient.out n₁).2 (hMN h')) (KN.inv_mem (Quotient.out n₂).2)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Substitute `hc` using the available equality. Establish `hn : n₁ = n₂`. Rewrite using `[← QuotientGroup.out_eq' n₁, ← QuotientGroup.out_eq' n₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `h' using 1` and compare the differences between its conclusion and the goal. Use `group`. Substitute `hn` using the available equality. Both sides reduce to the same expression.

Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`. Take `⟨x, hK, hK1⟩` from `x`. Set `g : ↥K` to `⟨b₀ * x * a⁻¹, K.mul_mem (K.mul_mem hb₀ hK) (K.inv_mem haK)⟩`.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (KN.subgroupOf K) g`. Establish `hkN : ((k : ↥K) : Γ) ∈ KN` using `k.2`. Set `n₀ : ↥KN` to `⟨((k : ↥K) : Γ)⁻¹, KN.inv_mem hkN⟩`. Take `⟨m, hm⟩` from `QuotientGroup.mk_out_eq_mul (KM.subgroupOf KN) n₀`. Establish `hmM : ((m : ↥KN) : Γ) ∈ KM` using `m.2`.

Establish `key : ((Quotient.out (QuotientGroup.mk g : ↥K ⧸ KN.subgroupOf K) : ↥K) : Γ) * ((Quotient.out (QuotientGroup.mk n₀ : ↥KN ⧸ KM.subgroupOf KN) : ↥KN) : Γ) = b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)`. Rewrite using `[hk, hm]`. Simplify using `only [Subgroup.coe_mul, g, n₀]`. Use `group`. Use `⟨⟨(QuotientGroup.mk g, QuotientGroup.mk n₀), ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[mul_assoc b₀⁻¹, key, show b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * u⁻¹ = x * (a⁻¹ * ((m : ↥KN) : Γ) * a) * (a⁻¹ * u⁻¹) by group]`. Conclude with `K₁.mul_mem (K₁.mul_mem hK1 (hM1 (hconj _ hmM))) hau`. Simplify using `only`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[mul_assoc b₀⁻¹, key, show (b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * a)⁻¹ * x = (a⁻¹ * ((m : ↥KN) : Γ) * a)⁻¹ by group]`. Conclude with `KM.inv_mem (hconj _ hmM)`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.lGrp_holds :
    LGrp := by
  intro Γ _ K K₀ K₁ KN KM hMN hNK hN0 hM1 h10 hnorm hdec b₀ hb₀ u hu
  obtain ⟨a, haK, ha0, hau⟩ := hdec u⁻¹ (inv_mem hu)
  have hconj : ∀ m ∈ KM, a⁻¹ * m * a ∈ KM := by
    intro m hm
    simpa using hnorm a⁻¹ (inv_mem ha0) m hm
  have hmem : ∀ (c : ↥K ⧸ KN.subgroupOf K) (n : ↥KN ⧸ KM.subgroupOf KN),
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹ ∈ K₁ →
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a ∈ K ⊓ K₁ := by
    intro c n hcn
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb₀) (Quotient.out c).2) (hNK (Quotient.out n).2)) haK
    · have hua : u * a ∈ K₁ := by simpa using K₁.inv_mem hau
      rw [show b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a
          = (b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹) * (u * a) by group]
      exact K₁.mul_mem hcn hua
  refine Eq.trans (b := Nat.card ((K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ?_ rfl
  refine Nat.card_eq_of_bijective (fun cn => (QuotientGroup.mk ⟨_, hmem cn.1.1 cn.1.2 cn.2⟩ : (K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ⟨?_, ?_⟩
  · rintro ⟨⟨c₁, n₁⟩, h₁⟩ ⟨⟨c₂, n₂⟩, h₂⟩ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    have h' : ((Quotient.out n₁ : ↥KN) : Γ)⁻¹ * ((Quotient.out c₁ : ↥K) : Γ)⁻¹
        * ((Quotient.out c₂ : ↥K) : Γ) * ((Quotient.out n₂ : ↥KN) : Γ) ∈ KM := by
      have := hnorm a ha0 _ h
      convert this using 1
      group
    have hc : c₁ = c₂ := by
      rw [← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := KN.mul_mem (KN.mul_mem (Quotient.out n₁).2 (hMN h')) (KN.inv_mem (Quotient.out n₂).2)
      convert this using 1
      group
    subst hc
    have hn : n₁ = n₂ := by
      rw [← QuotientGroup.out_eq' n₁, ← QuotientGroup.out_eq' n₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert h' using 1
      group
    subst hn
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x, hK, hK1⟩ := x
      let g : ↥K := ⟨b₀ * x * a⁻¹, K.mul_mem (K.mul_mem hb₀ hK) (K.inv_mem haK)⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KN.subgroupOf K) g
      have hkN : ((k : ↥K) : Γ) ∈ KN := k.2
      let n₀ : ↥KN := ⟨((k : ↥K) : Γ)⁻¹, KN.inv_mem hkN⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (KM.subgroupOf KN) n₀
      have hmM : ((m : ↥KN) : Γ) ∈ KM := m.2
      have key : ((Quotient.out (QuotientGroup.mk g : ↥K ⧸ KN.subgroupOf K) : ↥K) : Γ)
          * ((Quotient.out (QuotientGroup.mk n₀ : ↥KN ⧸ KM.subgroupOf KN) : ↥KN) : Γ)
          = b₀ * x * a⁻¹ * ((m : ↥KN) : Γ) := by
        rw [hk, hm]
        simp only [Subgroup.coe_mul, g, n₀]
        group
      refine ⟨⟨(QuotientGroup.mk g, QuotientGroup.mk n₀), ?_⟩, ?_⟩
      · dsimp only
        rw [mul_assoc b₀⁻¹, key,
          show b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * u⁻¹
            = x * (a⁻¹ * ((m : ↥KN) : Γ) * a) * (a⁻¹ * u⁻¹) by group]
        exact K₁.mul_mem (K₁.mul_mem hK1 (hM1 (hconj _ hmM))) hau
      · dsimp only
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [mul_assoc b₀⁻¹, key,
          show (b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * a)⁻¹ * x
            = (a⁻¹ * ((m : ↥KN) : Γ) * a)⁻¹ by group]
        exact KM.inv_mem (hconj _ hmM)
