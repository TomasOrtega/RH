import Formalism.LocalToGlobal.Columns.HeckeInertLemmas
import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Sq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def HiRel (a : 𝓞 E) (X Y : Submodule (𝓞 E) (Sp E n)) : Prop :=
  (∀ x ∈ X, a • x ∈ Y) ∧ ∀ y ∈ Y, a • y ∈ X

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.2, h.1⟩`.
-/
theorem HiRel.symm {a : 𝓞 E} {X Y : Submodule (𝓞 E) (Sp E n)} (h : HiRel a X Y) : HiRel a Y X := ⟨h.2, h.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x hx => h1 (Submodule.smul_mem_smul ha hx), fun y hy => h2 (Submodule.smul_mem_smul ha hy)⟩`.
-/
theorem HiRel.of_ideal {I : Ideal (𝓞 E)} {X Y : Submodule (𝓞 E) (Sp E n)} (h1 : I • X ≤ Y) (h2 : I • Y ≤ X)
    {a : 𝓞 E} (ha : a ∈ I) : HiRel a X Y := ⟨fun x hx => h1 (Submodule.smul_mem_smul ha hx), fun y hy => h2 (Submodule.smul_mem_smul ha hy)⟩

/- English proof (translation)
Set `g : X →ₗ[𝓞 E] X'` to `LinearMap.codRestrict X' ((α • LinearMap.id : Sp E n →ₗ[𝓞 E] Sp E n).comp X.subtype) (fun x => hXX'.1 x.1 x.2)`. Set `f : X →ₗ[𝓞 E] (X' ⧸ (Y' ⊓ X').comap X'.subtype)` to `((Y' ⊓ X').comap X'.subtype).mkQ.comp g`. Establish `key : α * α + β * (1 + α) = 1` using `by linear_combination (1 + α) * hab`. Establish `hker : LinearMap.ker f = (Y ⊓ X).comap X.subtype`. Use extensionality with `x`.

Rewrite using `[LinearMap.mem_ker, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (g x) = 0 ↔ (x : Sp E n) ∈ Y ⊓ X`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_inf]`. Express the relevant statement in the definitionally equal form `(α • (x : Sp E n) ∈ Y' ∧ α • (x : Sp E n) ∈ X') ↔ ((x : Sp E n) ∈ Y ∧ (x : Sp E n) ∈ X)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, -⟩`. Use `⟨?_, x.2⟩` and prove the remaining obligations. Establish `e : (x : Sp E n) = α • (α • (x : Sp E n)) + β • ((1 + α) • (x : Sp E n))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Conclude with `Y.add_mem (hYY'.2 _ h1) (hXY.1 _ (X.smul_mem _ x.2))`. Introduce and unpack `⟨h1, -⟩`. Conclude with `⟨hYY'.1 _ h1, hXX'.1 _ x.2⟩`. Establish `hsurj : Function.Surjective f`. Introduce `q`.

Take `⟨x', rfl⟩` from `Submodule.mkQ_surjective _ q`. Use `⟨⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (g ⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩) = Submodule.Quotient.mk x'`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_inf]`. Express the relevant statement in the definitionally equal form `(α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ Y') ∧ (α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ X')`.

Establish `e : α • (α • (x' : Sp E n)) - (x' : Sp E n) = -(β • ((1 + α) • (x' : Sp E n)))`. Rewrite using `[smul_smul, smul_smul, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_smul, key, one_smul, sub_self]`. Use `⟨?_, X'.sub_mem (X'.smul_mem _ (X'.smul_mem _ x'.2)) x'.2⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Y'.neg_mem (hX'Y'.1 _ (X'.smul_mem _ x'.2))`.

Conclude with `⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩`.
-/
theorem hi_quot {α β : 𝓞 E} (hab : α + β = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel α X X') (hYY' : HiRel α Y Y') (hXY : HiRel β X Y) (hX'Y' : HiRel β X' Y') :
    Nonempty ((X ⧸ (Y ⊓ X).comap X.subtype) ≃ₗ[𝓞 E] (X' ⧸ (Y' ⊓ X').comap X'.subtype)) := by
  let g : X →ₗ[𝓞 E] X' :=
    LinearMap.codRestrict X' ((α • LinearMap.id : Sp E n →ₗ[𝓞 E] Sp E n).comp X.subtype)
      (fun x => hXX'.1 x.1 x.2)
  let f : X →ₗ[𝓞 E] (X' ⧸ (Y' ⊓ X').comap X'.subtype) := ((Y' ⊓ X').comap X'.subtype).mkQ.comp g
  have key : α * α + β * (1 + α) = 1 := by linear_combination (1 + α) * hab
  have hker : LinearMap.ker f = (Y ⊓ X).comap X.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    change Submodule.Quotient.mk (g x) = 0 ↔ (x : Sp E n) ∈ Y ⊓ X
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_inf]
    change (α • (x : Sp E n) ∈ Y' ∧ α • (x : Sp E n) ∈ X') ↔ ((x : Sp E n) ∈ Y ∧ (x : Sp E n) ∈ X)
    constructor
    · rintro ⟨h1, -⟩
      refine ⟨?_, x.2⟩
      have e : (x : Sp E n) = α • (α • (x : Sp E n)) + β • ((1 + α) • (x : Sp E n)) := by
        calc (x : Sp E n) = (1 : 𝓞 E) • (x : Sp E n) := (one_smul _ _).symm
          _ = (α * α + β * (1 + α)) • (x : Sp E n) := by rw [key]
          _ = _ := by simp only [add_smul, mul_smul]
      rw [e]
      exact Y.add_mem (hYY'.2 _ h1) (hXY.1 _ (X.smul_mem _ x.2))
    · rintro ⟨h1, -⟩
      exact ⟨hYY'.1 _ h1, hXX'.1 _ x.2⟩
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩, ?_⟩
    change Submodule.Quotient.mk (g ⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩) = Submodule.Quotient.mk x'
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_inf]
    change (α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ Y') ∧ (α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ X')
    have e : α • (α • (x' : Sp E n)) - (x' : Sp E n) = -(β • ((1 + α) • (x' : Sp E n))) := by
      rw [smul_smul, smul_smul, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_smul, key, one_smul, sub_self]
    refine ⟨?_, X'.sub_mem (X'.smul_mem _ (X'.smul_mem _ x'.2)) x'.2⟩
    rw [e]
    exact Y'.neg_mem (hX'Y'.1 _ (X'.smul_mem _ x'.2))
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x = α • x + β • x` using `by rw [← add_smul, hab, one_smul]`. Rewrite using `[hx']`. Conclude with `Z.add_mem (hN x (Submodule.mem_inf.1 hx).1) (hM x (Submodule.mem_inf.1 hx).2)`.
-/
theorem hi_inf_le {α β : 𝓞 E} (hab : α + β = 1) {N M Z : Submodule (𝓞 E) (Sp E n)}
    (hN : ∀ x ∈ N, α • x ∈ Z) (hM : ∀ x ∈ M, β • x ∈ Z) : N ⊓ M ≤ Z := by
  intro x hx
  have hx' : x = α • x + β • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact Z.add_mem (hN x (Submodule.mem_inf.1 hx).1) (hM x (Submodule.mem_inf.1 hx).2)

/- English proof (translation)
Introduce `x hx`. Establish `hNM : N ⊓ M ≤ X₁` using `hi_inf_le hab h1N.2 h1M.2`. Establish `hc : α • (β • x) ∈ X₁`. Use `hNM (Submodule.mem_inf.2 ⟨hXN.1 _ (X.smul_mem β hx), ?_⟩)` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `hXM.1 _ (X.smul_mem α hx)`. Establish `hd : α • (α • x) ∈ X₁` using `h1N.2 _ (hXN.1 x hx)`. Establish `he : β • (β • x) ∈ X₁` using `h1M.2 _ (hXM.1 x hx)`. Establish `key : α * α + α * β + (α * β + β * β) = 1`. Establish `h2 : (α + β) * (α + β) = 1` using `by rw [hab, one_mul]`.

Take the linear combination `h2`. Establish `hx' : x = α • (α • x) + α • (β • x) + (α • (β • x) + β • (β • x))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx']`. Conclude with `X₁.add_mem (X₁.add_mem hd hc) (X₁.add_mem hc he)`.
-/
theorem hi_le {α β : 𝓞 E} (hab : α + β = 1) {X X₁ N M : Submodule (𝓞 E) (Sp E n)}
    (hXN : HiRel α X N) (hXM : HiRel β X M) (h1N : HiRel α X₁ N) (h1M : HiRel β X₁ M) : X ≤ X₁ := by
  intro x hx
  have hNM : N ⊓ M ≤ X₁ := hi_inf_le hab h1N.2 h1M.2
  have hc : α • (β • x) ∈ X₁ := by
    refine hNM (Submodule.mem_inf.2 ⟨hXN.1 _ (X.smul_mem β hx), ?_⟩)
    rw [smul_comm]
    exact hXM.1 _ (X.smul_mem α hx)
  have hd : α • (α • x) ∈ X₁ := h1N.2 _ (hXN.1 x hx)
  have he : β • (β • x) ∈ X₁ := h1M.2 _ (hXM.1 x hx)
  have key : α * α + α * β + (α * β + β * β) = 1 := by
    have h2 : (α + β) * (α + β) = 1 := by rw [hab, one_mul]
    linear_combination h2
  have hx' : x = α • (α • x) + α • (β • x) + (α • (β • x) + β • (β • x)) := by
    calc x = (1 : 𝓞 E) • x := (one_smul _ _).symm
      _ = (α * α + α * β + (α * β + β * β)) • x := by rw [key]
      _ = _ := by simp only [add_smul, mul_smul]
  rw [hx']
  exact X₁.add_mem (X₁.add_mem hd hc) (X₁.add_mem hc he)

/- English proof (translation)
The claim follows from `le_antisymm (hi_le hab hXN hXM h1N h1M) (hi_le hab h1N h1M hXN hXM)`.
-/
theorem hi_eq {α β : 𝓞 E} (hab : α + β = 1) {X X₁ N M : Submodule (𝓞 E) (Sp E n)}
    (hXN : HiRel α X N) (hXM : HiRel β X M) (h1N : HiRel α X₁ N) (h1M : HiRel β X₁ M) : X = X₁ := le_antisymm (hi_le hab hXN hXM h1N h1M) (hi_le hab h1N h1M hXN hXM)

/- English proof (translation)
Rewrite `h`, the goal using `[Submodule.smul_le]`. Introduce `k hk x hx`. Establish `h1 : γ • (γ • (k • x)) ∈ Y'`. Establish `e : γ • (γ • (k • x)) = γ • (k • (γ • x))` using `by rw [smul_comm γ k x]`. Rewrite using `[e]`.

Conclude with `hYY'.1 _ (h k hk _ (hXX'.2 x hx))`. Establish `h2 : δ • ((1 + γ) • (k • x)) ∈ Y'` using `hX'Y' _ (X'.smul_mem _ (X'.smul_mem _ hx))`. Establish `key : γ * γ + δ * (1 + γ) = 1` using `by linear_combination (1 + γ) * hgd`. Establish `e2 : k • x = γ • (γ • (k • x)) + δ • ((1 + γ) • (k • x))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e2]`. Conclude with `Y'.add_mem h1 h2`.
-/
theorem hi_transport {γ δ : 𝓞 E} (hgd : γ + δ = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel γ X X') (hYY' : HiRel γ Y Y') (hX'Y' : ∀ x ∈ X', δ • x ∈ Y') {K : Ideal (𝓞 E)}
    (h : K • X ≤ Y) : K • X' ≤ Y' := by
  rw [Submodule.smul_le] at h ⊢
  intro k hk x hx
  have h1 : γ • (γ • (k • x)) ∈ Y' := by
    have e : γ • (γ • (k • x)) = γ • (k • (γ • x)) := by rw [smul_comm γ k x]
    rw [e]
    exact hYY'.1 _ (h k hk _ (hXX'.2 x hx))
  have h2 : δ • ((1 + γ) • (k • x)) ∈ Y' := hX'Y' _ (X'.smul_mem _ (X'.smul_mem _ hx))
  have key : γ * γ + δ * (1 + γ) = 1 := by linear_combination (1 + γ) * hgd
  have e2 : k • x = γ • (γ • (k • x)) + δ • ((1 + γ) • (k • x)) := by
    calc k • x = (1 : 𝓞 E) • (k • x) := (one_smul _ _).symm
      _ = (γ * γ + δ * (1 + γ)) • (k • x) := by rw [key]
      _ = _ := by simp only [add_smul, mul_smul]
  rw [e2]
  exact Y'.add_mem h1 h2

def hiCorner (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  α • M ⊔ β • N

/- English proof (translation)
Unfold `hiCorner`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨m, hm, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz`. Conclude with `h1 m hm`.

Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz`. Conclude with `h2 x hx`.
-/
theorem hiCorner_le {α β : 𝓞 E} {M N Z : Submodule (𝓞 E) (Sp E n)} (h1 : ∀ m ∈ M, α • m ∈ Z)
    (h2 : ∀ x ∈ N, β • x ∈ Z) : hiCorner α β M N ≤ Z := by
  unfold hiCorner
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact h1 m hm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact h2 x hx

/- English proof (translation)
The claim follows from `Submodule.mem_sup_left (Submodule.smul_mem_pointwise_smul m α M hm)`.
-/
theorem hiCorner_memL (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) {m : Sp E n} (hm : m ∈ M) :
    α • m ∈ hiCorner α β M N := Submodule.mem_sup_left (Submodule.smul_mem_pointwise_smul m α M hm)

/- English proof (translation)
The claim follows from `Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul x β N hx)`.
-/
theorem hiCorner_memR (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n} (hx : x ∈ N) :
    β • x ∈ hiCorner α β M N := Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul x β N hx)

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x = α • x + β • x` using `by rw [← add_smul, hab, one_smul]`. Rewrite using `[hx']`. Conclude with `Submodule.add_mem_sup (Submodule.smul_mem_pointwise_smul x α M (Submodule.mem_inf.1 hx).1) (Submodule.smul_mem_pointwise_smul x β N (Submodule.mem_inf.1 hx).2)`.
-/
theorem hiCorner_inf {α β : 𝓞 E} (hab : α + β = 1) (M N : Submodule (𝓞 E) (Sp E n)) :
    M ⊓ N ≤ hiCorner α β M N := by
  intro x hx
  have hx' : x = α • x + β • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact Submodule.add_mem_sup (Submodule.smul_mem_pointwise_smul x α M (Submodule.mem_inf.1 hx).1)
    (Submodule.smul_mem_pointwise_smul x β N (Submodule.mem_inf.1 hx).2)

/- English proof (translation)
Establish `hmem : ∀ y ∈ hiCorner α β M N, ∃ m ∈ M, ∃ x ∈ N, α • m + β • x = y`. Introduce `y hy`. Unfold `hiCorner at hy`. Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨m, hm, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1`.

Take `⟨x, hx, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2`. Conclude with `⟨m, hm, x, hx, rfl⟩`. Use `⟨⟨fun x hx => hiCorner_memR α β M N hx, fun y hy => ?_⟩, ⟨fun y hy => ?_, fun m hm => hiCorner_memL α β M N hm⟩⟩` and prove the remaining obligations. Take `⟨m, hm, x, hx, rfl⟩` from `hmem y hy`. Rewrite using `[smul_add, smul_comm β α m]`.

Conclude with `N.add_mem (hNe.2 _ (heM.2 _ hm)) (N.smul_mem _ (N.smul_mem _ hx))`. Take `⟨m, hm, x, hx, rfl⟩` from `hmem y hy`. Rewrite using `[smul_add, smul_comm α β x]`. Conclude with `M.add_mem (M.smul_mem _ (M.smul_mem _ hm)) (heM.1 _ (hNe.1 _ hx))`.
-/
theorem hiCorner_rel {α β : 𝓞 E} {N e M : Submodule (𝓞 E) (Sp E n)} (hNe : HiRel α N e) (heM : HiRel β e M) :
    HiRel β N (hiCorner α β M N) ∧ HiRel α (hiCorner α β M N) M := by
  have hmem : ∀ y ∈ hiCorner α β M N, ∃ m ∈ M, ∃ x ∈ N, α • m + β • x = y := by
    intro y hy
    unfold hiCorner at hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2
    exact ⟨m, hm, x, hx, rfl⟩
  refine ⟨⟨fun x hx => hiCorner_memR α β M N hx, fun y hy => ?_⟩,
    ⟨fun y hy => ?_, fun m hm => hiCorner_memL α β M N hm⟩⟩
  · obtain ⟨m, hm, x, hx, rfl⟩ := hmem y hy
    rw [smul_add, smul_comm β α m]
    exact N.add_mem (hNe.2 _ (heM.2 _ hm)) (N.smul_mem _ (N.smul_mem _ hx))
  · obtain ⟨m, hm, x, hx, rfl⟩ := hmem y hy
    rw [smul_add, smul_comm α β x]
    exact M.add_mem (M.smul_mem _ (M.smul_mem _ hm)) (heM.1 _ (hNe.1 _ hx))

/- English proof (translation)
Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ I ⊔ J by rw [hIJ]; exact Submodule.mem_top)`. Establish `hc1 : cO E a + cO E b = 1` using `by rw [← map_add, hab, map_one]`. Use `⟨a * cO E a, Ideal.mul_mem_right _ _ ha, 1 - a * cO E a, ?_, by ring, ?_, ?_⟩` and prove the remaining obligations. Establish `e : 1 - a * cO E a = a * cO E b + b * cO E a + b * cO E b`. Establish `h1 : (a + b) * (cO E a + cO E b) = 1` using `by rw [hab, hc1, one_mul]`.

Take the linear combination `-h1`. Rewrite using `[e]`. Conclude with `J.add_mem (J.add_mem (Ideal.mul_mem_left _ _ (hJ b hb)) (Ideal.mul_mem_right _ _ hb)) (Ideal.mul_mem_right _ _ hb)`. Rewrite using `[map_mul, cO_cO, mul_comm]`. Rewrite using `[map_sub, map_one, map_mul, cO_cO, mul_comm]`.
-/
theorem hi_exists_conj {I J : Ideal (𝓞 E)} (hJ : ∀ a ∈ J, cO E a ∈ J) (hIJ : I ⊔ J = ⊤) :
    ∃ α ∈ I, ∃ β ∈ J, α + β = 1 ∧ cO E α = α ∧ cO E β = β := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ I ⊔ J by rw [hIJ]; exact Submodule.mem_top)
  have hc1 : cO E a + cO E b = 1 := by rw [← map_add, hab, map_one]
  refine ⟨a * cO E a, Ideal.mul_mem_right _ _ ha, 1 - a * cO E a, ?_, by ring, ?_, ?_⟩
  · have e : 1 - a * cO E a = a * cO E b + b * cO E a + b * cO E b := by
      have h1 : (a + b) * (cO E a + cO E b) = 1 := by rw [hab, hc1, one_mul]
      linear_combination -h1
    rw [e]
    exact J.add_mem (J.add_mem (Ideal.mul_mem_left _ _ (hJ b hb)) (Ideal.mul_mem_right _ _ hb))
      (Ideal.mul_mem_right _ _ hb)
  · rw [map_mul, cO_cO, mul_comm]
  · rw [map_sub, map_one, map_mul, cO_cO, mul_comm]

/- English proof (translation)
Rewrite using `[wmp_hStd_osmul_left, wmp_hStd_osmul_right, ha]`.
-/
theorem hi_hStd_conj {a : 𝓞 E} (ha : cO E a = a) (m x : Sp E n) :
    hStd E n (a • m) x = hStd E n m (a • x) := by
  rw [wmp_hStd_osmul_left, wmp_hStd_osmul_right, ha]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite `hx` using `[mem_dual]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← show dual (hStd E n) M = M from hM, mem_dual]`.

Introduce `m hm`. Rewrite using `[← hi_hStd_conj hα]`. Conclude with `hx _ (hiCorner_memL α β M N hm)`. Rewrite using `[← show dual (hStd E n) N = N from hN, mem_dual]`. Introduce `y hy`.

Rewrite using `[← hi_hStd_conj hβ]`. Conclude with `hx _ (hiCorner_memR α β M N hy)`. Introduce and unpack `⟨h1, h2⟩`. Establish `hM' : α • x ∈ dual (hStd E n) M` using `by rw [show dual (hStd E n) M = M from hM]; exact h1`. Establish `hN' : β • x ∈ dual (hStd E n) N` using `by rw [show dual (hStd E n) N = N from hN]; exact h2`.

Rewrite using `[mem_dual]`. Introduce `y hy`. Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨m, hm, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1`. Take `⟨z, hz, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2`.

Rewrite using `[map_add, LinearMap.add_apply, hi_hStd_conj hα, hi_hStd_conj hβ]`. Conclude with `Submodule.add_mem _ ((mem_dual M _).1 hM' m hm) ((mem_dual N _).1 hN' z hz)`.
-/
theorem hiCorner_mem_dual {α β : 𝓞 E} (hα : cO E α = α) (hβ : cO E β = β) {M N : Submodule (𝓞 E) (Sp E n)}
    (hM : IsUnimodular (hStd E n) M) (hN : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ dual (hStd E n) (hiCorner α β M N) ↔ α • x ∈ M ∧ β • x ∈ N := by
  constructor
  · intro hx
    rw [mem_dual] at hx
    refine ⟨?_, ?_⟩
    · rw [← show dual (hStd E n) M = M from hM, mem_dual]
      intro m hm
      rw [← hi_hStd_conj hα]
      exact hx _ (hiCorner_memL α β M N hm)
    · rw [← show dual (hStd E n) N = N from hN, mem_dual]
      intro y hy
      rw [← hi_hStd_conj hβ]
      exact hx _ (hiCorner_memR α β M N hy)
  · rintro ⟨h1, h2⟩
    have hM' : α • x ∈ dual (hStd E n) M := by rw [show dual (hStd E n) M = M from hM]; exact h1
    have hN' : β • x ∈ dual (hStd E n) N := by rw [show dual (hStd E n) N = N from hN]; exact h2
    rw [mem_dual]
    intro y hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2
    rw [map_add, LinearMap.add_apply, hi_hStd_conj hα, hi_hStd_conj hβ]
    exact Submodule.add_mem _ ((mem_dual M _).1 hM' m hm) ((mem_dual N _).1 hN' z hz)

/- English proof (translation)
Take `⟨hr1, hr2⟩` from `hiCorner_rel hNe heM`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨h1, h2⟩` from `(hiCorner_mem_dual hα hβ hM hN x).1 hx`. Establish `hinf` using `hiCorner_inf hab M N`.

Use `mem_of_smul_mem_of_add_eq_one hab ?_ ?_` and prove the remaining obligations. Use `mem_of_smul_mem_of_add_eq_one hab (hiCorner_memL α β M N h1) (hinf ⟨M.smul_mem β h1, ?_⟩)` and prove the remaining obligations. Rewrite using `[smul_comm β α x]`. Conclude with `N.smul_mem α h2`. Use `mem_of_smul_mem_of_add_eq_one hab (hinf ⟨?_, N.smul_mem α h2⟩) (hiCorner_memR α β M N h2)` and prove the remaining obligations.

Rewrite using `[smul_comm α β x]`. Conclude with `M.smul_mem β h1`. Introduce `x hx`. Conclude with `(hiCorner_mem_dual hα hβ hM hN x).2 ⟨hr2.1 x hx, hr1.2 x hx⟩`.
-/
theorem hiCorner_unimodular {α β : 𝓞 E} (hab : α + β = 1) (hα : cO E α = α) (hβ : cO E β = β)
    {N e M : Submodule (𝓞 E) (Sp E n)} (hN : IsUnimodular (hStd E n) N) (hM : IsUnimodular (hStd E n) M)
    (hNe : HiRel α N e) (heM : HiRel β e M) : IsUnimodular (hStd E n) (hiCorner α β M N) := by
  obtain ⟨hr1, hr2⟩ := hiCorner_rel hNe heM
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := (hiCorner_mem_dual hα hβ hM hN x).1 hx
    have hinf := hiCorner_inf hab M N
    refine mem_of_smul_mem_of_add_eq_one hab ?_ ?_
    · refine mem_of_smul_mem_of_add_eq_one hab (hiCorner_memL α β M N h1) (hinf ⟨M.smul_mem β h1, ?_⟩)
      rw [smul_comm β α x]
      exact N.smul_mem α h2
    · refine mem_of_smul_mem_of_add_eq_one hab (hinf ⟨?_, N.smul_mem α h2⟩) (hiCorner_memR α β M N h2)
      rw [smul_comm α β x]
      exact M.smul_mem β h1
  · intro x hx
    exact (hiCorner_mem_dual hα hβ hM hN x).2 ⟨hr2.1 x hx, hr1.2 x hx⟩

/- English proof (translation)
Establish `hD : Submodule.IsLattice E (M ⊔ N)` using `⟨hM.fg.sup hN.fg, by`. Rewrite using `[eq_top_iff, ← hM.span_eq_top]`. Conclude with `Submodule.span_mono (SetLike.coe_subset_coe.2 (le_sup_left : M ≤ M ⊔ N))⟩`. Use `lattice_of_smul hN hD (hiCorner_le (fun m hm => Submodule.mem_sup_left (M.smul_mem α hm)) (fun x hx => Submodule.mem_sup_right (N.smul_mem β hx))) (mul_ne_zero hj hi) fun x hx => ?_` and prove the remaining obligations. Use `hiCorner_inf hab M N ⟨?_, N.smul_mem _ hx⟩` and prove the remaining obligations.

Rewrite using `[mul_smul]`. Conclude with `hej _ (hNi x hx)`.
-/
theorem hiCorner_lattice {α β : 𝓞 E} (hab : α + β = 1) {N e M : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (hM : Submodule.IsLattice E M) {i j : 𝓞 E} (hi : i ≠ 0) (hj : j ≠ 0)
    (hNi : ∀ x ∈ N, i • x ∈ e) (hej : ∀ y ∈ e, j • y ∈ M) : Submodule.IsLattice E (hiCorner α β M N) := by
  have hD : Submodule.IsLattice E (M ⊔ N) := ⟨hM.fg.sup hN.fg, by
    rw [eq_top_iff, ← hM.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 (le_sup_left : M ≤ M ⊔ N))⟩
  refine lattice_of_smul hN hD (hiCorner_le (fun m hm => Submodule.mem_sup_left (M.smul_mem α hm))
    (fun x hx => Submodule.mem_sup_right (N.smul_mem β hx))) (mul_ne_zero hj hi) fun x hx => ?_
  refine hiCorner_inf hab M N ⟨?_, N.smul_mem _ hx⟩
  rw [mul_smul]
  exact hej _ (hNi x hx)

end Sq

end Formalism.L2.Col
