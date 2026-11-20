import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBij

variable {E : Type} [Field E] [NumberField E]

def diag : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_diag (a : Eˣ) : (diag a : Af E) = algebraMap E (Af E) a := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, rfl⟩`.
-/
theorem diag_mem_princ (a : Eˣ) : diag a ∈ (princ : Subgroup (Af E)ˣ) := ⟨a, rfl⟩

/- English proof (translation)
Rewrite using `[mem_hatOUnits, ← map_inv, ← map_inv]`. Conclude with `⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c _)⟩`.
-/
theorem diag_unit_mem (c : Ideal (OF E)) (u : (OF E)ˣ) :
    diag (Units.map (algebraMap (OF E) E).toMonoidHom u) ∈ hatOUnits c := by
  rw [mem_hatOUnits, ← map_inv, ← map_inv]
  exact ⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c _)⟩

def rep {c : Ideal (OF E)} {y : (Af E)ˣ} (a : modUnits (lattice c y)) : Eˣ := Units.mk0 a.1.out (out_mem_lattice a).2

def toIdele (c : Ideal (OF E)) (p : Σ q : PicO c, modUnits (lattice c q.out)) :
    {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} :=
  ⟨QuotientGroup.mk (diag (rep p.2) * p.1.out⁻¹), _, rfl, (out_mem_lattice p.2).1⟩

/- English proof (translation)
Introduce and unpack `⟨_, y, rfl, hy⟩`. Set `q : PicO c` to `QuotientGroup.mk y⁻¹`. Establish `hq : (q.out)⁻¹ * y⁻¹ ∈ princ ⊔ hatOUnits c` using `QuotientGroup.eq.1 (Quotient.out_eq q)`. Take `⟨_, ⟨α, rfl⟩, u, hu, h⟩` from `Subgroup.mem_sup.1 hq`. Express the relevant statement in the definitionally equal form `diag α * u = _ at h`.

Establish `h1 : diag α⁻¹ * q.out⁻¹ = y * u`. Rewrite using `[map_inv, eq_mul_inv_iff_mul_eq.1 h |>.symm, mul_assoc, inv_mul_cancel_left, mul_comm]`. Establish `hx : ((α⁻¹ : Eˣ) : E) ∈ lattice c q.out`. Rewrite using `[mem_lattice, ← coe_diag, ← Units.val_mul, h1, Units.val_mul]`. Conclude with `mul_mem hy hu.1`.

Set `a : modUnits (lattice c q.out)` to `⟨Quotient.mk _ ((α⁻¹ : Eˣ) : E), _, hx, Units.ne_zero _, rfl⟩`. Take `⟨w, hw⟩ : (unitRel (E` from `E)).r ((α⁻¹ : Eˣ) : E) a.1.out := Quotient.exact (Quotient.out_eq a.1).symm`. Establish `hr : rep a = Units.map (algebraMap (OF E) E).toMonoidHom w * α⁻¹` using `Units.ext hw`. Use `⟨⟨q, a⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `(QuotientGroup.eq.2 ?_ : (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = _).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y⁻¹ * (diag (rep a) * q.out⁻¹) ∈ _`. Rewrite using `[hr, map_mul, mul_assoc, h1, mul_left_comm, inv_mul_cancel_left]`. Conclude with `mul_mem (diag_unit_mem c w) hu`.
-/
theorem toIdele_surjective (c : Ideal (OF E)) : Function.Surjective (toIdele c) := by
  rintro ⟨_, y, rfl, hy⟩
  let q : PicO c := QuotientGroup.mk y⁻¹
  have hq : (q.out)⁻¹ * y⁻¹ ∈ princ ⊔ hatOUnits c := QuotientGroup.eq.1 (Quotient.out_eq q)
  obtain ⟨_, ⟨α, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.1 hq
  change diag α * u = _ at h
  have h1 : diag α⁻¹ * q.out⁻¹ = y * u := by
    rw [map_inv, eq_mul_inv_iff_mul_eq.1 h |>.symm, mul_assoc, inv_mul_cancel_left, mul_comm]
  have hx : ((α⁻¹ : Eˣ) : E) ∈ lattice c q.out := by
    rw [mem_lattice, ← coe_diag, ← Units.val_mul, h1, Units.val_mul]
    exact mul_mem hy hu.1
  let a : modUnits (lattice c q.out) := ⟨Quotient.mk _ ((α⁻¹ : Eˣ) : E), _, hx, Units.ne_zero _, rfl⟩
  obtain ⟨w, hw⟩ : (unitRel (E := E)).r ((α⁻¹ : Eˣ) : E) a.1.out := Quotient.exact (Quotient.out_eq a.1).symm
  have hr : rep a = Units.map (algebraMap (OF E) E).toMonoidHom w * α⁻¹ := Units.ext hw
  refine ⟨⟨q, a⟩, Subtype.ext ?_⟩
  refine (QuotientGroup.eq.2 ?_ : (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = _).symm
  change y⁻¹ * (diag (rep a) * q.out⁻¹) ∈ _
  rw [hr, map_mul, mul_assoc, h1, mul_left_comm, inv_mul_cancel_left]
  exact mul_mem (diag_unit_mem c w) hu

/- English proof (translation)
Introduce and unpack `⟨q, a⟩ ⟨q', a'⟩ h`. Establish `h1 : (diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹) ∈ hatOUnits c` using `QuotientGroup.eq.1 (congrArg Subtype.val h)`. Establish `hq : q = q'`. Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations.

Establish `: q.out⁻¹ * q'.out = diag ((rep a)⁻¹ * rep a') * ((diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹))⁻¹`. Rewrite using `[map_mul, map_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `mul_mem (Subgroup.mem_sup_left (diag_mem_princ _)) (Subgroup.mem_sup_right (inv_mem h1))`. Substitute `hq` using the available equality. Establish `h2 : diag ((rep a)⁻¹ * rep a') ∈ hatOUnits c`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_mul, map_inv, mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]`. Establish `key : ∀ b : Eˣ, diag b ∈ hatOUnits c → (b : E) ∈ orderC c` using `fun b hb => by`. Establish `: (b : E) ∈ lattice c 1`. Rewrite using `[mem_lattice, inv_one, Units.val_one, mul_one]`. Conclude with `hb.1`.

Rewrite `this` using `[hcap]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `hun _ (Units.ne_zero _) (key _ h2) (by`. Rewrite using `[← Units.val_inv_eq_inv_val]`. Conclude with `key _ (by rw [map_inv]; exact inv_mem h2))`. Establish `h3 : a = a'`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq a.1, ← Quotient.out_eq a'.1]`. Use `Quotient.sound ⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu]`. Express the relevant statement in the definitionally equal form `((rep a' : Eˣ) : E) = _ * ((rep a : Eˣ) : E)`.

Rewrite using `[← Units.val_mul, mul_comm, mul_inv_cancel_left]`. Rewrite using `[h3]`.
-/
theorem toIdele_injective (c : Ideal (OF E)) (hcap : lattice c 1 = (orderC c : Set E))
    (hun : ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u) :
    Function.Injective (toIdele c) := by
  rintro ⟨q, a⟩ ⟨q', a'⟩ h
  have h1 : (diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹) ∈ hatOUnits c :=
    QuotientGroup.eq.1 (congrArg Subtype.val h)
  have hq : q = q' := by
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    refine QuotientGroup.eq.2 ?_
    have : q.out⁻¹ * q'.out = diag ((rep a)⁻¹ * rep a') *
        ((diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹))⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (diag_mem_princ _)) (Subgroup.mem_sup_right (inv_mem h1))
  subst hq
  have h2 : diag ((rep a)⁻¹ * rep a') ∈ hatOUnits c := by
    convert h1 using 1
    rw [map_mul, map_inv, mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  have key : ∀ b : Eˣ, diag b ∈ hatOUnits c → (b : E) ∈ orderC c := fun b hb => by
    have : (b : E) ∈ lattice c 1 := by
      rw [mem_lattice, inv_one, Units.val_one, mul_one]
      exact hb.1
    rwa [hcap] at this
  obtain ⟨u, hu⟩ := hun _ (Units.ne_zero _) (key _ h2) (by
    rw [← Units.val_inv_eq_inv_val]
    exact key _ (by rw [map_inv]; exact inv_mem h2))
  have h3 : a = a' := by
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq a'.1]
    refine Quotient.sound ⟨u, ?_⟩
    rw [← hu]
    change ((rep a' : Eˣ) : E) = _ * ((rep a : Eˣ) : E)
    rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
  rw [h3]

/- English proof (translation)
Introduce `E _ _ _ 𝔣 c h𝔣 hc hc0`. Use `⟨Equiv.ofBijective (toIdele c) ⟨toIdele_injective c (GlobalTheory.T.idelicRingClassLattice_one_eq_order E c hc0) (GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hc), toIdele_surjective c⟩, fun p y hy => ?_⟩` and prove the remaining obligations. Establish `: y = diag (rep p.2) * p.1.out⁻¹` using `Units.ext hy`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ →
    ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃
      {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c},
      ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) →
        (e p).1 = QuotientGroup.mk y := by
  intro E _ _ _ 𝔣 c h𝔣 hc hc0
  refine ⟨Equiv.ofBijective (toIdele c) ⟨toIdele_injective c (GlobalTheory.T.idelicRingClassLattice_one_eq_order E c hc0) (GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hc),
    toIdele_surjective c⟩, fun p y hy => ?_⟩
  have : y = diag (rep p.2) * p.1.out⁻¹ := Units.ext hy
  rw [this]
  rfl

end GlobalTheory.CMVal.LatBij
