import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

section Quot

variable {R B G : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing G] [Algebra R G]
  {q : B →+* G} (h : SemiHom (RingHom.id R) q)

/- English proof (translation)
Introduce `ω`. Proceed by induction on `ω using ind1 with`. Consider the case `h g g'`. Take `⟨b, rfl⟩` from `hq g`. Take `⟨b', rfl⟩` from `hq g'`.

Conclude with `⟨b • D R B b', by rw [h.oneFormMap_smul_semilinear, h.m1_D]⟩`. Consider the case `h0 => exact ⟨0, map_zero _⟩`. Consider the case `ha x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`.

Conclude with `⟨a + b, map_add _ _ _⟩`.
-/
theorem SemiHom.oneFormMap_surjective_of_surjective (hq : Function.Surjective q) : Function.Surjective h.m1 := by
  intro ω
  induction ω using ind1 with
  | h g g' =>
    obtain ⟨b, rfl⟩ := hq g
    obtain ⟨b', rfl⟩ := hq g'
    exact ⟨b • D R B b', by rw [h.oneFormMap_smul_semilinear, h.m1_D]⟩
  | h0 => exact ⟨0, map_zero _⟩
  | ha x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.pow_induction_on_left' with`. Consider the case `algebraMap g`. Take `⟨b, rfl⟩` from `hq g`. Use `⟨algebraMap B _ b, ?_, h.mDR_algebraMap b⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ LinearMap.range _ ^ 0`.

Rewrite using `[pow_zero]`. Conclude with `Submodule.algebraMap_mem _`. Consider the case `add x y i _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`.

Conclude with `⟨a + b, add_mem ha hb, map_add _ _ _⟩`. Consider the case `mem_mul m hm i x hx ih`. Take `⟨ω, rfl⟩` from `hm`. Take `⟨ω', rfl⟩` from `h.oneFormMap_surjective_of_surjective hq ω`. Take `⟨y, hy, rfl⟩` from `ih`.

Use `⟨ι1 ω' * y, ?_, by rw [map_mul, h.mDR_ι]⟩` and prove the remaining obligations. Use `mul_mem (ι_mem ω') hy` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis.
-/
theorem SemiHom.exists_mDR_eq (hq : Function.Surjective q) {j : ℕ} {x : DR R G}
    (hx : x ∈ ⋀[G]^j Ω[G⁄R]) : ∃ y ∈ ⋀[B]^j Ω[B⁄R], h.mDR y = x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap g =>
    obtain ⟨b, rfl⟩ := hq g
    refine ⟨algebraMap B _ b, ?_, h.mDR_algebraMap b⟩
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    obtain ⟨ω', rfl⟩ := h.oneFormMap_surjective_of_surjective hq ω
    obtain ⟨y, hy, rfl⟩ := ih
    refine ⟨ι1 ω' * y, ?_, by rw [map_mul, h.mDR_ι]⟩
    have := mul_mem (ι_mem ω') hy
    rwa [add_comm] at this

/- English proof (translation)
Introduce `x`. Take `⟨y, hy, e⟩` from `h.exists_mDR_eq hq x.2`. Conclude with `⟨⟨y, hy⟩, Subtype.ext e⟩`.
-/
theorem SemiHom.mOm_surjective (hq : Function.Surjective q) (j : ℕ) : Function.Surjective (h.mOm j) := by
  intro x
  obtain ⟨y, hy, e⟩ := h.exists_mDR_eq hq x.2
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

/- English proof (translation)
Introduce `x`. Proceed by induction on `x using indDR with`. Consider the case `h g`. Take `⟨b, rfl⟩` from `hq g`. Conclude with `⟨_, h.mDR_algebraMap b⟩`.

Consider the case `hd g`. Take `⟨b, rfl⟩` from `hq g`. Conclude with `⟨ι1 (D R B b), by rw [h.mDR_ι, h.m1_D]⟩`. Consider the case `hm x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, map_mul _ _ _⟩`. Consider the case `ha x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`.

Conclude with `⟨a + b, map_add _ _ _⟩`.
-/
theorem SemiHom.mDR_surjective (hq : Function.Surjective q) : Function.Surjective h.mDR := by
  intro x
  induction x using indDR with
  | h g =>
    obtain ⟨b, rfl⟩ := hq g
    exact ⟨_, h.mDR_algebraMap b⟩
  | hd g =>
    obtain ⟨b, rfl⟩ := hq g
    exact ⟨ι1 (D R B b), by rw [h.mDR_ι, h.m1_D]⟩
  | hm x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩
  | ha x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/- English proof (translation)
Use `haveI : K.IsTwoSided := ⟨fun b ha ↦ hr _ ha b⟩`. Set `π : DR R B →+* DR R B ⧸ K` to `Ideal.Quotient.mk K`. Set `s : G → B` to `Function.surjInv hq`. Establish `hs : Function.RightInverse s q` using `Function.surjInv_eq hq`. Establish `k1 : ∀ a b : B, q a = q b → π (ι1 (D R B a)) = π (ι1 (D R B b))`.

Introduce `a b e`. Rewrite using `[← sub_eq_zero, ← map_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(hk _ (by rw [map_sub, e, sub_self])).2`. Set `φ : G →+* DR R B ⧸ K` to `q.liftOfRightInverse s hs ⟨π.comp (algebraMap B (DR R B)), fun b hb ↦ by`. Rewrite `hb`, the goal using `[RingHom.mem_ker]`.

Conclude with `(Ideal.Quotient.eq_zero_iff_mem).2 (hk b hb).1⟩`. Establish `hφ : ∀ b, φ (q b) = π (algebraMap B _ b)` using `fun b ↦ q.liftOfRightInverse_comp_apply s hs _ b`. Use `letI : Algebra G (DR R B ⧸ K) := φ.toAlgebra' fun g y ↦ by`. Take `⟨b, rfl⟩` from `hq g`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Express the relevant statement in the definitionally equal form `φ (q b) * π y = π y * φ (q b)`. Rewrite using `[hφ, ← map_mul, ← map_mul, Algebra.commutes]`. Establish `hsm : ∀ (g : G) (y : DR R B ⧸ K), g • y = φ g * y` using `fun _ _ ↦ rfl`. Establish `hπr : ∀ (r : R) (z : DR R B), π (r • z) = r • π z` using `fun r z ↦ map_smul (Ideal.Quotient.mkₐ R K) r z`. Use `haveI : IsScalarTower R G (DR R B ⧸ K) := ⟨fun r g y ↦ by`.

Take `⟨b, rfl⟩` from `hq g`. Rewrite using `[hsm, hsm, show r • q b = q (r • b) from (h r b).symm, hφ, hφ, show algebraMap B (DR R B) (r • b) = r • algebraMap B (DR R B) b from map_smul (IsScalarTower.toAlgHom R B (DR R B)) r b, hπr, smul_mul_assoc]⟩`. Set `δ : Derivation R G (DR R B ⧸ K)` to `Derivation.mk' { toFun g := π (ι1 (D R B (s g))) map_add' a b := by`. Rewrite using `[← map_add, ← map_add, ← map_add]`. Conclude with `k1 _ _ (by rw [map_add, hs, hs, hs])`.

Use the proof step `map_smul' r g := by`. Rewrite using `[RingHom.id_apply, ← hπr, ← LinearMap.map_smul_of_tower, ← Derivation.map_smul]`. Conclude with `k1 _ _ (by rw [hs, h r (s g), hs]; rfl) }`. Use `fun a b ↦ by`. Express the relevant statement in the definitionally equal form `π (ι1 (D R B (s (a * b)))) = a • π (ι1 (D R B (s b))) + b • π (ι1 (D R B (s a)))`.

Establish `e : π (ι1 (D R B (s a * s b))) = π (algebraMap B _ (s a)) * π (ι1 (D R B (s b))) + π (algebraMap B _ (s b)) * π (ι1 (D R B (s a)))`. Rewrite using `[Derivation.leibniz, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, map_add, map_mul, map_mul]`. Rewrite `e` using `[← hφ, ← hφ, hs, hs]`. Rewrite using `[hsm, hsm, ← e]`. Conclude with `k1 _ _ (by rw [hs, map_mul, hs, hs])`.

Set `f : Ω[G⁄R] →ₗ[G] DR R B ⧸ K` to `δ.liftKaehlerDifferential`. Establish `hf : ∀ ω : Ω[B⁄R], f (h.m1 ω) = π (ι1 ω)`. Introduce `ω`. Proceed by induction on `ω using ind1 with`. Consider the case `h b c`.

Rewrite using `[h.oneFormMap_smul_semilinear, h.m1_D, map_smul, Derivation.liftKaehlerDifferential_comp_D, hsm, hφ, map_smul, Algebra.smul_def, map_mul]`. Use `congr 1`. Conclude with `k1 _ _ (hs _)`. Consider the case `h0 => simp`. Consider the case `ha x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.

Establish `hsq : ∀ ω, f ω * f ω = 0`. Introduce `ω`. Take `⟨ω', rfl⟩` from `h.oneFormMap_surjective_of_surjective hq ω`. Rewrite using `[hf, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]`. Set `ψ : DR R G →ₐ[G] DR R B ⧸ K` to `ExteriorAlgebra.lift G ⟨f, hsq⟩`.

Establish `key : ∀ y : DR R B, ψ (h.mDR y) = π y`. Introduce `y`. Proceed by induction on `y using indDR with`. Consider the case `h b => rw [h.mDR_algebraMap, AlgHom.commutes]`. Conclude with `hφ b`.

Consider the case `hd b`. Rewrite using `[h.mDR_ι, ExteriorAlgebra.lift_ι_apply]`. Conclude with `hf _`. Consider the case `hm x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]`. Consider the case `ha x y hx hy => rw [map_add, map_add, hx, hy, map_add]`.

Use `key x` as an intermediate fact. Rewrite `this` using `[hx, map_zero]`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem).1 this.symm`.
-/
theorem SemiHom.mem_of_mDR_eq_zero (hq : Function.Surjective q) (K : Ideal (DR R B))
    (hr : ∀ x ∈ K, ∀ y, x * y ∈ K)
    (hk : ∀ b, q b = 0 → algebraMap B (DR R B) b ∈ K ∧ ι1 (D R B b) ∈ K)
    (x : DR R B) (hx : h.mDR x = 0) : x ∈ K := by
  haveI : K.IsTwoSided := ⟨fun b ha ↦ hr _ ha b⟩
  let π : DR R B →+* DR R B ⧸ K := Ideal.Quotient.mk K
  let s : G → B := Function.surjInv hq
  have hs : Function.RightInverse s q := Function.surjInv_eq hq
  have k1 : ∀ a b : B, q a = q b → π (ι1 (D R B a)) = π (ι1 (D R B b)) := by
    intro a b e
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact (hk _ (by rw [map_sub, e, sub_self])).2
  let φ : G →+* DR R B ⧸ K := q.liftOfRightInverse s hs ⟨π.comp (algebraMap B (DR R B)), fun b hb ↦ by
    rw [RingHom.mem_ker] at hb ⊢
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (hk b hb).1⟩
  have hφ : ∀ b, φ (q b) = π (algebraMap B _ b) := fun b ↦
    q.liftOfRightInverse_comp_apply s hs _ b
  letI : Algebra G (DR R B ⧸ K) := φ.toAlgebra' fun g y ↦ by
    obtain ⟨b, rfl⟩ := hq g
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change φ (q b) * π y = π y * φ (q b)
    rw [hφ, ← map_mul, ← map_mul, Algebra.commutes]
  have hsm : ∀ (g : G) (y : DR R B ⧸ K), g • y = φ g * y := fun _ _ ↦ rfl
  have hπr : ∀ (r : R) (z : DR R B), π (r • z) = r • π z := fun r z ↦
    map_smul (Ideal.Quotient.mkₐ R K) r z
  haveI : IsScalarTower R G (DR R B ⧸ K) := ⟨fun r g y ↦ by
    obtain ⟨b, rfl⟩ := hq g
    rw [hsm, hsm, show r • q b = q (r • b) from (h r b).symm, hφ, hφ,
      show algebraMap B (DR R B) (r • b) = r • algebraMap B (DR R B) b from
        map_smul (IsScalarTower.toAlgHom R B (DR R B)) r b, hπr, smul_mul_assoc]⟩

  let δ : Derivation R G (DR R B ⧸ K) := Derivation.mk'
    { toFun g := π (ι1 (D R B (s g)))
      map_add' a b := by
        rw [← map_add, ← map_add, ← map_add]
        exact k1 _ _ (by rw [map_add, hs, hs, hs])
      map_smul' r g := by
        rw [RingHom.id_apply, ← hπr, ← LinearMap.map_smul_of_tower, ← Derivation.map_smul]
        exact k1 _ _ (by rw [hs, h r (s g), hs]; rfl) }
    fun a b ↦ by
      change π (ι1 (D R B (s (a * b)))) = a • π (ι1 (D R B (s b))) + b • π (ι1 (D R B (s a)))
      have e : π (ι1 (D R B (s a * s b))) = π (algebraMap B _ (s a)) * π (ι1 (D R B (s b))) +
          π (algebraMap B _ (s b)) * π (ι1 (D R B (s a))) := by
        rw [Derivation.leibniz, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
          map_add, map_mul, map_mul]
      rw [← hφ, ← hφ, hs, hs] at e
      rw [hsm, hsm, ← e]
      exact k1 _ _ (by rw [hs, map_mul, hs, hs])
  let f : Ω[G⁄R] →ₗ[G] DR R B ⧸ K := δ.liftKaehlerDifferential
  have hf : ∀ ω : Ω[B⁄R], f (h.m1 ω) = π (ι1 ω) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      rw [h.oneFormMap_smul_semilinear, h.m1_D, map_smul, Derivation.liftKaehlerDifferential_comp_D, hsm, hφ, map_smul,
        Algebra.smul_def, map_mul]
      congr 1
      exact k1 _ _ (hs _)
    | h0 => simp
    | ha x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hsq : ∀ ω, f ω * f ω = 0 := by
    intro ω
    obtain ⟨ω', rfl⟩ := h.oneFormMap_surjective_of_surjective hq ω
    rw [hf, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  let ψ : DR R G →ₐ[G] DR R B ⧸ K := ExteriorAlgebra.lift G ⟨f, hsq⟩
  have key : ∀ y : DR R B, ψ (h.mDR y) = π y := by
    intro y
    induction y using indDR with
    | h b => rw [h.mDR_algebraMap, AlgHom.commutes]; exact hφ b
    | hd b =>
      rw [h.mDR_ι, ExteriorAlgebra.lift_ι_apply]
      exact hf _
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]
    | ha x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have := key x
  rw [hx, map_zero] at this
  exact (Ideal.Quotient.eq_zero_iff_mem).1 this.symm

/- English proof (translation)
The claim follows from `fun _ _ _ _ _ _ _ _ _ h hq ↦ ⟨h.oneFormMap_surjective_of_surjective hq, h.mOm_surjective hq, h.mDR_surjective hq, fun K hr hk x hx ↦ h.mem_of_mDR_eq_zero hq K hr hk x hx⟩`.
-/
theorem semiHom_quotient_surjective_ker : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (G : Type) [CommRing G] [Algebra R G] (q : B →+* G) (h : SemiHom (RingHom.id R) q), Function.Surjective q → Function.Surjective h.m1 ∧ (∀ j, Function.Surjective (h.mOm j)) ∧ Function.Surjective h.mDR ∧ ∀ 𝔎 : Ideal (DR R B), (∀ x ∈ 𝔎, ∀ y, x * y ∈ 𝔎) → (∀ b, q b = 0 → algebraMap B (DR R B) b ∈ 𝔎 ∧ ι1 (D R B b) ∈ 𝔎) → ∀ x, h.mDR x = 0 → x ∈ 𝔎 :=
  fun _ _ _ _ _ _ _ _ _ h hq ↦ ⟨h.oneFormMap_surjective_of_surjective hq, h.mOm_surjective hq, h.mDR_surjective hq,
    fun K hr hk x hx ↦ h.mem_of_mDR_eq_zero hq K hr hk x hx⟩

end Quot

end GlobalTheory.CechDR
