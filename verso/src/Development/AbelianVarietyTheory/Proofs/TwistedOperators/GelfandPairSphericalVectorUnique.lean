import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsMore
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩`.
-/
theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

def stabSub (K : Subgroup G) (g : G) : Subgroup G where
  carrier := {h | h ∈ K ∧ g⁻¹ * h * g ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    convert K.mul_mem ha' hb' using 1
    group
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K.inv_mem ha, ?_⟩
    convert K.inv_mem ha' using 1
    group

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stabSub {K : Subgroup G} {g h : G} : h ∈ stabSub K g ↔ h ∈ K ∧ g⁻¹ * h * g ∈ K := Iff.rfl

def heckeOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (g : G)
    [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Module.End ℂ V :=
  ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g)

/- English proof (translation)
Simplify using `[heckeOp, LinearMap.sum_apply]`.
-/
theorem heckeOp_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g) v := by
  simp [heckeOp, LinearMap.sum_apply]

def repSet (K : Subgroup G) (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Finset G :=
  Finset.univ.map ⟨fun q : K ⧸ (stabSub K g).subgroupOf K => (q.out : G) * g, fun q q' e => by
    have : (q.out : G) = q'.out := mul_right_cancel e
    exact Quotient.out_inj.1 (Subtype.ext this)⟩

/- English proof (translation)
Rewrite using `[heckeOp_apply, repSet, Finset.sum_map]`. Both sides reduce to the same expression.
-/
theorem heckeOp_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ γ ∈ repSet K g, ρ γ v := by
  rw [heckeOp_apply, repSet, Finset.sum_map]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `γ hγ`. Take `⟨q, -, rfl⟩` from `Finset.mem_map.1 hγ`. Use `⟨q.out, q.out.2, 1, K.one_mem, ?_⟩` and prove the remaining obligations. Use `show (q.out : G) * a = (q.out : G) * a * 1`.

Simplify using the standard rewrite rules. Introduce and unpack `x ⟨k₁, hk₁, k₂, hk₂, rfl⟩`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) (⟨k₁, hk₁⟩ : K)`. Establish `hh' : ((h : K) : G) ∈ stabSub K a` using `Subgroup.mem_subgroupOf.1 h.2`. Use `set q : K ⧸ (stabSub K a).subgroupOf K := ((⟨k₁, hk₁⟩ : K) : K ⧸ (stabSub K a).subgroupOf K)`.

Establish `hq : ((q.out : K) : G) = k₁ * ((h : K) : G)`. Rewrite using `[hh]`. Both sides reduce to the same expression. Use `⟨(q.out : G) * a, ⟨Finset.mem_map.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`.

Establish `: a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K` using `(mem_stabSub.1 (inv_mem hh')).2`. Use `K.mul_mem this hk₂ using 1` and compare the differences between its conclusion and the goal. Use `group`. Introduce and unpack `y ⟨hy, hyx⟩`. Take `⟨p, -, rfl⟩` from `Finset.mem_map.1 hy`.

Express the relevant statement in the definitionally equal form `(p.out : G) * a = (q.out : G) * a`. Use `congr 1`. Establish `hx1 : ((q.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K`. Rewrite using `[hq]`. Establish `: a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K` using `(mem_stabSub.1 (inv_mem hh')).2`.

Use `K.mul_mem this hk₂ using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hx2 : ((p.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K` using `hyx`. Establish `hu : ((p.out : K)⁻¹ * q.out : K) ∈ (stabSub K a).subgroupOf K`. Rewrite using `[Subgroup.mem_subgroupOf]`.

Use `⟨(p.out⁻¹ * q.out : K).2, ?_⟩` and prove the remaining obligations. Use `K.mul_mem hx2 (K.inv_mem hx1) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Establish `: (p.out : K ⧸ (stabSub K a).subgroupOf K) = q.out` using `QuotientGroup.eq.2 hu`.

Rewrite `this` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Rewrite using `[this]`.
-/
theorem repSet_spec (K : Subgroup G) (a : G) [Fintype (K ⧸ (stabSub K a).subgroupOf K)] :
    (∀ γ ∈ repSet K a, GelfandTrick.InDoubleCoset K a γ) ∧
    (∀ x : G, GelfandTrick.InDoubleCoset K a x → ∃! γ, γ ∈ repSet K a ∧ γ⁻¹ * x ∈ K) := by
  constructor
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hγ
    refine ⟨q.out, q.out.2, 1, K.one_mem, ?_⟩
    show (q.out : G) * a = (q.out : G) * a * 1
    simp
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) (⟨k₁, hk₁⟩ : K)
    have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
    set q : K ⧸ (stabSub K a).subgroupOf K := ((⟨k₁, hk₁⟩ : K) : K ⧸ (stabSub K a).subgroupOf K)
    have hq : ((q.out : K) : G) = k₁ * ((h : K) : G) := by
      rw [hh]; rfl
    refine ⟨(q.out : G) * a, ⟨Finset.mem_map.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · rw [hq]
      have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
      convert K.mul_mem this hk₂ using 1
      group
    · rintro y ⟨hy, hyx⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hy
      change (p.out : G) * a = (q.out : G) * a
      congr 1
      have hx1 : ((q.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := by
        rw [hq]
        have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
        convert K.mul_mem this hk₂ using 1
        group
      have hx2 : ((p.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := hyx
      have hu : ((p.out : K)⁻¹ * q.out : K) ∈ (stabSub K a).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨(p.out⁻¹ * q.out : K).2, ?_⟩
        convert K.mul_mem hx2 (K.inv_mem hx1) using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have : (p.out : K ⧸ (stabSub K a).subgroupOf K) = q.out := QuotientGroup.eq.2 hu
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      rw [this]

/- English proof (translation)
Set `f : G ⧸ K → V` to `fun c => F c.out`. Establish `hf : ∀ g : G, f (g : G ⧸ K) = F g` using `fun g => by`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K g`. Simplify using `only [f, hk, hF k k.2]`. Establish `key : ∀ A B : Finset G, ∑ γ ∈ A, ∑ δ ∈ B, F (γ * δ) = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ K)` using `fun A B => by`.

Rewrite using `[Finset.sum_product]`. Simplify using `only [hf]`. Rewrite using `[key, key]`. Set `T : Finset (G ⧸ K)` to `(R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ K)) ∪ (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ K))`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T) (g := fun p => ((p.1 * p.2 : G) : G ⧸ K)) (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f, ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T) (g := fun p => ((p.1 * p.2 : G) : G ⧸ K)) (fun p …`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.sum_const]`. Use `congr 1`. Apply `le_antisymm` to reduce the goal to its premises. Use `GelfandTrick.card_pairs_le K τ hmul hinv hdc hK α β R S hR hR' hS hS' c` and compare the differences between its conclusion and the goal.

Use `GelfandTrick.card_pairs_le K τ hmul hinv hdc hK β α S R hS hS' hR hR' c` and compare the differences between its conclusion and the goal.
-/
theorem sum_comm_anti {V : Type} [AddCommGroup V] (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, GelfandTrick.InDoubleCoset K α γ)
    (hR' : ∀ x : G, GelfandTrick.InDoubleCoset K α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K)
    (hS : ∀ γ ∈ S, GelfandTrick.InDoubleCoset K β γ)
    (hS' : ∀ x : G, GelfandTrick.InDoubleCoset K β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ K)
    (F : G → V) (hF : ∀ k ∈ K, ∀ g, F (g * k) = F g) :
    ∑ γ ∈ R, ∑ δ ∈ S, F (γ * δ) = ∑ δ ∈ S, ∑ γ ∈ R, F (δ * γ) := by
  classical
  let f : G ⧸ K → V := fun c => F c.out
  have hf : ∀ g : G, f (g : G ⧸ K) = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [f, hk, hF k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ∑ δ ∈ B, F (γ * δ)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ K) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf]
  rw [key, key]
  let T : Finset (G ⧸ K) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ K)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ K))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK β α S R hS hS' hR hR' c

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hK : ∀ k ∈ K, τ k ∈ K` using `fun k hk => by`. Take `⟨k₁, h₁, k₂, h₂, e⟩` from `hdc k`. Rewrite using `[e]`. Conclude with `K.mul_mem (K.mul_mem h₁ hk) h₂`. Use `sum_comm_anti K τ hmul hinv hdc hK a b _ _ (repSet_spec K a).1 (repSet_spec K a).2 (repSet_spec K b).1 (repSet_spec K b).2 (fun g => ρ g v) (fun k hk g => by simp only [map_mul, Module.End.mul_apply, hv k hk])` as an intermediate fact.

Rewrite using `[heckeOp_eq_sum ρ K a (heckeOp ρ K b v), heckeOp_eq_sum ρ K b v, heckeOp_eq_sum ρ K b (heckeOp ρ K a v), heckeOp_eq_sum ρ K a v]`. Simplify `this` using `only [map_sum, map_mul, Module.End.mul_apply]`.
-/
theorem heckeOp_comm (ρ : Representation ℂ G V) (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (a b : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] [Fintype (K ⧸ (stabSub K b).subgroupOf K)]
    {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    heckeOp ρ K a (heckeOp ρ K b v) = heckeOp ρ K b (heckeOp ρ K a v) := by
  have hK : ∀ k ∈ K, τ k ∈ K := fun k hk => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc k
    rw [e]; exact K.mul_mem (K.mul_mem h₁ hk) h₂
  have := sum_comm_anti K τ hmul hinv hdc hK a b _ _ (repSet_spec K a).1 (repSet_spec K a).2
    (repSet_spec K b).1 (repSet_spec K b).2 (fun g => ρ g v)
    (fun k hk g => by simp only [map_mul, Module.End.mul_apply, hv k hk])
  rw [heckeOp_eq_sum ρ K a (heckeOp ρ K b v), heckeOp_eq_sum ρ K b v,
    heckeOp_eq_sum ρ K b (heckeOp ρ K a v), heckeOp_eq_sum ρ K a v]
  simpa only [map_sum, map_mul, Module.End.mul_apply] using this

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) y`. Establish `hh' : ((h : K) : G) ∈ stabSub K a` using `Subgroup.mem_subgroupOf.1 h.2`. Rewrite using `[hh]`. Establish `e : ((y * (h : K) : K) : G) * a = (y : G) * a * (a⁻¹ * ((h : K) : G) * a)`. Simplify using `only [Subgroup.coe_mul]`.

Use `group`. Rewrite using `[e, map_mul, Module.End.mul_apply, hv _ hh'.2]`.
-/
theorem heckeTerm_eq (ρ : Representation ℂ G V) (K : Subgroup G) (a : G) {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) (y : K) :
    ρ ((((y : K ⧸ (stabSub K a).subgroupOf K)).out : G) * a) v = ρ ((y : G) * a) v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) y
  have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
  rw [hh]
  have e : ((y * (h : K) : K) : G) * a = (y : G) * a * (a⁻¹ * ((h : K) : G) * a) := by
    simp only [Subgroup.coe_mul]; group
  rw [e, map_mul, Module.End.mul_apply, hv _ hh'.2]

/- English proof (translation)
Introduce `k hk`. Rewrite using `[heckeOp_apply, map_sum]`. Use `Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_` and prove the remaining obligations. Establish `hq : (MulAction.toPerm (⟨k, hk⟩ : K) q : K ⧸ (stabSub K a).subgroupOf K) = ((⟨k, hk⟩ * q.out : K) : K ⧸ (stabSub K a).subgroupOf K)` using `by show (⟨k, hk⟩ : K) • q = _ conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.

Rewrite using `[hq, heckeTerm_eq ρ K a hv, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem heckeOp_fixed (ρ : Representation ℂ G V) (K : Subgroup G) (a : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    ∀ k ∈ K, ρ k (heckeOp ρ K a v) = heckeOp ρ K a v := by
  intro k hk
  rw [heckeOp_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm (⟨k, hk⟩ : K) q : K ⧸ (stabSub K a).subgroupOf K) =
      ((⟨k, hk⟩ * q.out : K) : K ⧸ (stabSub K a).subgroupOf K) := by
    show (⟨k, hk⟩ : K) • q = _
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq, heckeTerm_eq ρ K a hv, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]
  rfl

/- English proof (translation)
Use `haveI : H'.FiniteIndex := Subgroup.finiteIndex_of_le hle`. Set `e` to `Subgroup.quotientEquivProdOfLE hle`. Use `haveI : Finite ((K ⧸ H') × (H' ⧸ H.subgroupOf H')) := Finite.of_equiv _ e`. Use `haveI : Finite (H' ⧸ H.subgroupOf H') := Finite.prod_right (K ⧸ H')`. Use `haveI := Fintype.ofFinite (K ⧸ H)`.

Use `haveI := Fintype.ofFinite (K ⧸ H')`. Use `haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Establish `h1 : ∀ q : K ⧸ H, F q.out = F (e q).1.out`. Introduce `q`.

Establish `: (e q).1 = ((q.out : K) : K ⧸ H')` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[this]`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H' q.out`. Rewrite using `[hh, hF _ _ h.2]`.

Rewrite using `[Finset.sum_congr rfl fun q _ => h1 q, Fintype.sum_equiv e _ (fun y => F y.1.out) (fun _ => rfl), Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]`. Rewrite using `[Finset.smul_sum]`.
-/
theorem finsum_quot_le {K W : Type} [Group K] [AddCommGroup W] {H H' : Subgroup K} (hle : H ≤ H')
    [H.FiniteIndex] (F : K → W) (hF : ∀ y, ∀ h ∈ H', F (y * h) = F y) :
    ∑ᶠ q : K ⧸ H, F q.out = Nat.card (H' ⧸ H.subgroupOf H') • ∑ᶠ p : K ⧸ H', F p.out := by
  classical
  haveI : H'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite ((K ⧸ H') × (H' ⧸ H.subgroupOf H')) := Finite.of_equiv _ e
  haveI : Finite (H' ⧸ H.subgroupOf H') := Finite.prod_right (K ⧸ H')
  haveI := Fintype.ofFinite (K ⧸ H)
  haveI := Fintype.ofFinite (K ⧸ H')
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h1 : ∀ q : K ⧸ H, F q.out = F (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : K) : K ⧸ H') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' q.out
    rw [hh, hF _ _ h.2]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Fintype.sum_equiv e _ (fun y => F y.1.out) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Finset.smul_sum]

end GlobalTheory.GelfandLine

open GlobalTheory.GelfandLine in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.GroupAverageProjection.main`. Consider the case `exact _root_.GlobalTheory.GroupAverageProjection.main`. Consider the case `(apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)`.
-/
theorem GlobalTheory.fixed_eq_span_of_gelfandPair : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first
  | exact @_root_.GlobalTheory.GroupAverageProjection.main
  | exact _root_.GlobalTheory.GroupAverageProjection.main
  | (apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)
