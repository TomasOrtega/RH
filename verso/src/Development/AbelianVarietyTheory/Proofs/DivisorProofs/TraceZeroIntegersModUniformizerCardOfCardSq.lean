import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Introduce `hI L _ _ ϖ σ q hU`. Establish `hq` using `hI L ϖ σ q hU`. Take `⟨hσσ, hv, hϖ, -, ⟨x, hx, hδ⟩, -, -⟩` from `hU`. Establish `hσO : ∀ y ∈ intL L, σ y ∈ intL L` using `fun y hy => by show Valued.v (σ y) ≤ 1`. Rewrite using `[hv]`.

Conclude with `hy`. Establish `hδ0 : σ x - x ≠ 0` using `fun h => by rw [h, map_zero] at hδ; exact zero_ne_one hδ`. Establish `hδ1 : x - σ x ≠ 0` using `fun h => hδ0 (by linear_combination -h)`. Establish `hδi : (σ x - x)⁻¹ ∈ intL L` using `by show Valued.v (σ x - x)⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hδ, inv_one]`.

Use `set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT`. Establish `memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y = -y` using `fun y => by`. Rewrite using `[hT, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, ← add_eq_zero_iff_eq_neg]`. Both sides reduce to the same expression. Establish `hw : ∀ y ∈ intL L, σ y - y ∈ T` using `fun y hy => (memT _).2 ⟨sub_mem (hσO y hy) hy, by rw [map_sub, hσσ]; ring⟩`.

Establish `hu : ∀ y ∈ intL L, σ x * y - x * σ y ∈ T` using `fun y hy => (memT _).2 ⟨sub_mem (mul_mem (hσO x hx) hy) (mul_mem hx (hσO y hy)), by`. Rewrite using `[map_sub, map_mul, map_mul, hσσ, hσσ]`. Use the proof step `ring⟩`. Set `f : T × T →+ (intL L).toAddSubgroup` to `{ toFun := fun p => ⟨(σ x - x)⁻¹ * (p.1.1 + x * p.2.1), (intL L).mul_mem hδi ((intL L).add_mem ((memT _).1 p.1.2).1 ((intL L).mul_mem hx ((memT _).1 p.2.2).1))⟩ map_zero' := Subtype.ext (by simp) map_add' := fun a b => Subtype.ext (by simp; ring) }`. Establish `hf : ∀ p, (f p : L) = (σ x - x)⁻¹ * (p.1.1 + x * p.2.1)` using `fun _ => rfl`.

Establish `hsurj : Function.Surjective f` using `fun y => ⟨(⟨_, hu y.1 y.2⟩, ⟨_, hw y.1 y.2⟩), Subtype.ext (by rw [hf]; field_simp; ring)⟩`. Establish `hc : (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup).comap f = ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T).prod ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T)`. Use extensionality with `⟨u, w⟩`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, hf, AddMonoidHom.coe_mulLeft]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, e⟩`. Establish `e1 : (σ x - x) * (ϖ * y) = u.1 + x * w.1` using `by rw [e]; field_simp`. Establish `e2` using `congrArg σ e1`. Rewrite `e2` using `[map_mul, map_sub, hσσ, map_mul, hϖ, map_add, map_mul, ((memT _).1 u.2).2, ((memT _).1 w.2).2]`. Establish `e3 : ϖ * (σ y - y) = w.1` using `mul_left_cancel₀ hδ0 (by linear_combination -e1 - e2)`.

Conclude with `⟨⟨_, hu y hy, by linear_combination e1 - x * e3⟩, _, hw y hy, e3⟩`. Introduce and unpack `⟨⟨a, ha, e1⟩, b, hb, e2⟩`. Use `⟨_, (f (⟨a, ha⟩, ⟨b, hb⟩)).2, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, ← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `AddSubgroup.index_comap_of_surjective (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup) hsurj`. Rewrite `h2` using `[hc, AddSubgroup.index_prod, ← pow_two]`. Conclude with `Nat.pow_left_injective two_ne_zero (h2.trans hq)`.
-/
theorem traceZeroIndex_of_intIndex : IntIndex → TraceZeroIndex := by
  intro hI L _ _ ϖ σ q hU
  have hq := hI L ϖ σ q hU
  obtain ⟨hσσ, hv, hϖ, -, ⟨x, hx, hδ⟩, -, -⟩ := hU
  have hσO : ∀ y ∈ intL L, σ y ∈ intL L := fun y hy => by
    show Valued.v (σ y) ≤ 1
    rw [hv]; exact hy
  have hδ0 : σ x - x ≠ 0 := fun h => by rw [h, map_zero] at hδ; exact zero_ne_one hδ
  have hδ1 : x - σ x ≠ 0 := fun h => hδ0 (by linear_combination -h)
  have hδi : (σ x - x)⁻¹ ∈ intL L := by
    show Valued.v (σ x - x)⁻¹ ≤ 1
    rw [map_inv₀, hδ, inv_one]
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y = -y := fun y => by
    rw [hT, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, ← add_eq_zero_iff_eq_neg]
    rfl
  have hw : ∀ y ∈ intL L, σ y - y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (hσO y hy) hy, by rw [map_sub, hσσ]; ring⟩
  have hu : ∀ y ∈ intL L, σ x * y - x * σ y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (mul_mem (hσO x hx) hy) (mul_mem hx (hσO y hy)), by
      rw [map_sub, map_mul, map_mul, hσσ, hσσ]; ring⟩
  let f : T × T →+ (intL L).toAddSubgroup :=
    { toFun := fun p => ⟨(σ x - x)⁻¹ * (p.1.1 + x * p.2.1),
        (intL L).mul_mem hδi ((intL L).add_mem ((memT _).1 p.1.2).1 ((intL L).mul_mem hx ((memT _).1 p.2.2).1))⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp; ring) }
  have hf : ∀ p, (f p : L) = (σ x - x)⁻¹ * (p.1.1 + x * p.2.1) := fun _ => rfl
  have hsurj : Function.Surjective f := fun y =>
    ⟨(⟨_, hu y.1 y.2⟩, ⟨_, hw y.1 y.2⟩), Subtype.ext (by rw [hf]; field_simp; ring)⟩
  have hc : (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup).comap f =
      ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T).prod ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T) := by
    ext ⟨u, w⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map,
      hf, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨y, hy, e⟩
      have e1 : (σ x - x) * (ϖ * y) = u.1 + x * w.1 := by rw [e]; field_simp
      have e2 := congrArg σ e1
      rw [map_mul, map_sub, hσσ, map_mul, hϖ, map_add, map_mul, ((memT _).1 u.2).2, ((memT _).1 w.2).2] at e2
      have e3 : ϖ * (σ y - y) = w.1 := mul_left_cancel₀ hδ0 (by linear_combination -e1 - e2)
      exact ⟨⟨_, hu y hy, by linear_combination e1 - x * e3⟩, _, hw y hy, e3⟩
    · rintro ⟨⟨a, ha, e1⟩, b, hb, e2⟩
      refine ⟨_, (f (⟨a, ha⟩, ⟨b, hb⟩)).2, ?_⟩
      rw [hf, ← e1, ← e2]; ring
  have h2 := AddSubgroup.index_comap_of_surjective
    (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup) hsurj
  rw [hc, AddSubgroup.index_prod, ← pow_two] at h2
  exact Nat.pow_left_injective two_ne_zero (h2.trans hq)

end GlobalTheory.SatakeWeyl
