import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerClassSum

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Use `set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def`. Use `set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def`. Establish `hT : ν T = ν K` using `measure_preimage_mul ν a⁻¹ K`. Establish `hsum` using `h𝓖.measure_eq_tsum' T`. Establish `hδT : ∀ δ ∈ S, δ • T = T`.

Introduce `δ hδ`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]`. Establish `hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K`.

Use `K.inv_mem hδ` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `K.mul_mem (K.inv_mem hk) hx` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Introduce `hx`. Use `K.mul_mem hk hx` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖)`.

Introduce `δ hδ γ`. Rewrite using `[← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]`. Assume the negation of the conclusion as `hinf`. Choose the witnesses or unpack the hypotheses as in `⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← hT, hsum]`. Simplify using `[hall]`. Establish `hle` using `ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0) (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))`.

Establish `: Infinite S` using `Set.infinite_coe_iff.2 hinf`. Establish `htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤`. Rewrite using `[tsum_congr (fun δ : S => hinv δ δ.2 γ0)]`. Conclude with `ENNReal.tsum_const_eq_top_of_ne_zero hγ0`. Rewrite `hle` using `[htop, ← hsum, hT]`.

Conclude with `h1 (top_le_iff.1 hle)`.
-/
theorem _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (h0 : ν K ≠ 0) (h1 : ν K ≠ ⊤) (a : G) :
    {γ : Γ | a⁻¹ * (γ : G) * a ∈ K}.Finite := by
  set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def
  set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def
  have hT : ν T = ν K := measure_preimage_mul ν a⁻¹ K
  have hsum := h𝓖.measure_eq_tsum' T
  have hδT : ∀ δ ∈ S, δ • T = T := by
    intro δ hδ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul,
      Subgroup.coe_inv]
    have hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K := by
      have := K.inv_mem hδ
      simpa [mul_assoc] using this
    constructor
    · intro hx
      have := K.mul_mem (K.inv_mem hk) hx
      simpa [mul_assoc] using this
    · intro hx
      have := K.mul_mem hk hx
      simpa [mul_assoc] using this
  have hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖) := by
    intro δ hδ γ
    rw [← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]
  by_contra hinf
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← hT, hsum]
    simp [hall]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0)
    (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  have htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤ := by
    rw [tsum_congr (fun δ : S => hinv δ δ.2 γ0)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hγ0
  rw [htop, ← hsum, hT] at hle
  exact h1 (top_le_iff.1 hle)

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Use `set K : Subgroup G := J.comap π with hK_def`. Use `choose a ha using fun i => hπ (y i)`. Establish `hmem : ∀ i (γ : Γ), γ ∈ _root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i) ↔ (a i)⁻¹ * (γ : G) * a i ∈ K`. Introduce `i γ`. Unfold `_root_.Formalism.IndefR.Bridge.stab`.

Simplify using `[hK_def, Subgroup.mem_comap, MulAut.conj_apply, ← ha i, map_mul, map_inv]`. Establish `hK0 : ν K ≠ 0` using `by rw [h1]; exact one_ne_zero`. Establish `hKt : ν K ≠ ⊤` using `by rw [h1]; exact ENNReal.one_ne_top`. Establish `hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ K}.Finite` using `fun i => _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ K h𝓖 hK0 hKt (a i)`. Use `⟨fun i => ((hfin i).subset fun γ hγ => (hmem i γ).1 hγ).to_subtype, ?_⟩` and prove the remaining obligations.

Introduce `f hf f' hf'`. Establish `hf0 : ∀ (γ : Γ) (h : H) (k : J), f (π γ * h * k) = (χ k : ℂ) • ρ γ (f h)`. Unfold `_root_.Formalism.IndefR.Bridge.AdForms at hf`. Conclude with `hf`. Establish `hf0' : ∀ (γ : Γ) (h : H) (k : J), f' (π γ * h * k) = (χ k : ℂ) • ρ γ (f' h)`.

Unfold `_root_.Formalism.IndefR.Bridge.AdForms at hf'`. Conclude with `hf'`. Use `set Fψ : G → ℂ := fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) with hFψ`. Establish `hFψ' : ∀ h, Fψ h = inner ℂ (f (π h)) (f' (π h))` using `fun h => hρ _ _ _`. Establish `hleft : ∀ γ ∈ Γ, ∀ x : G, Fψ (γ * x) = Fψ x`.

Introduce `γ hγ x`. Establish `e` using `hf0 ⟨γ, hγ⟩ (π x) 1`. Establish `e'` using `hf0' ⟨γ, hγ⟩ (π x) 1`. Simplify using `only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at e e'`. Rewrite using `[hFψ', hFψ', map_mul, e, e', hρ]`.

Establish `hright : ∀ k ∈ K, ∀ x : G, Fψ (x * k) = Fψ x`. Introduce `k hk x`. Establish `e` using `hf0 1 (π x) ⟨π k, hk⟩`. Establish `e'` using `hf0' 1 (π x) ⟨π k, hk⟩`. Simplify using `only [OneMemClass.coe_one, map_one, one_mul, Module.End.one_apply] at e e'`.

Rewrite using `[hFψ', hFψ', map_mul, e, e', inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hχ, Complex.ofReal_one, one_pow, one_mul]`. Establish `hreps : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a i * k`. Introduce `x`. Take `⟨i, ⟨γ, k, hk⟩, huniq⟩` from `hy (π x)`. Use `⟨i, ⟨γ, γ.2, (a i)⁻¹ * (γ : G)⁻¹ * x, ?_, by group⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `π ((a i)⁻¹ * (γ : G)⁻¹ * x) ∈ J`. Establish `hk' : π x = π γ * y i * k` using `hk`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, ha i, hk']`. Simplify `k.2` using `[mul_assoc]`. Introduce and unpack `j ⟨γ', hγ', k', hk', hx⟩`.

Use `huniq j ⟨⟨γ', hγ'⟩, ⟨π k', hk'⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π x = π γ' * y j * π k'`. Rewrite using `[hx, map_mul, map_mul, ha j]`. Establish `hmain` using `_root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ K 𝓖 h𝓖 ho hKt I a hreps (fun i => by`. Use `(hfin i).image (fun γ : Γ => (γ : G))` as an intermediate fact.

Use `this.subset ?_` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hzK⟩`. Conclude with `⟨⟨z, hz⟩, hzK, rfl⟩) Fψ hleft hright`. Take `⟨-, hint, heq⟩` from `hmain`. Use `⟨hint, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∫ h in 𝓖, Fψ h ∂ν = _`. Rewrite using `[heq, h1]`. Unfold `_root_.Formalism.IndefR.Bridge.adInner`. Simplify using `only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hcard : {γ | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ K}.ncard = Nat.card (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i))`. Rewrite using `[← Nat.card_coe_set_eq]`. Conclude with `Nat.card_congr { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hmem i _).2 z.2.2⟩ invFun := fun γ => ⟨γ.1.1, γ.1.2, (hmem i _).1 γ.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite using `[hFψ', ha i, hcard]`.
-/
theorem _root_.GlobalTheory.InnerClassSum.integral_inner_eq_adInner {G H W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G)
    [ν.IsMulLeftInvariant]
    (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J.comap π) = 1)
    (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) (χ : J →* ℂˣ)
    (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : _root_.Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    (∀ i, Finite (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i))) ∧
      ∀ f ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν =
          _root_.Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' := by
  set K : Subgroup G := J.comap π with hK_def
  choose a ha using fun i => hπ (y i)
  have hmem : ∀ i (γ : Γ), γ ∈ _root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i) ↔ (a i)⁻¹ * (γ : G) * a i ∈ K := by
    intro i γ
    unfold _root_.Formalism.IndefR.Bridge.stab
    simp [hK_def, Subgroup.mem_comap, MulAut.conj_apply, ← ha i, map_mul, map_inv]
  have hK0 : ν K ≠ 0 := by rw [h1]; exact one_ne_zero
  have hKt : ν K ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ K}.Finite := fun i =>
    _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ K h𝓖 hK0 hKt (a i)
  refine ⟨fun i => ((hfin i).subset fun γ hγ => (hmem i γ).1 hγ).to_subtype, ?_⟩
  intro f hf f' hf'
  have hf0 : ∀ (γ : Γ) (h : H) (k : J), f (π γ * h * k) = (χ k : ℂ) • ρ γ (f h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf
    exact hf
  have hf0' : ∀ (γ : Γ) (h : H) (k : J), f' (π γ * h * k) = (χ k : ℂ) • ρ γ (f' h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf'
    exact hf'
  set Fψ : G → ℂ := fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) with hFψ
  have hFψ' : ∀ h, Fψ h = inner ℂ (f (π h)) (f' (π h)) := fun h => hρ _ _ _
  have hleft : ∀ γ ∈ Γ, ∀ x : G, Fψ (γ * x) = Fψ x := by
    intro γ hγ x
    have e := hf0 ⟨γ, hγ⟩ (π x) 1
    have e' := hf0' ⟨γ, hγ⟩ (π x) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at e e'
    rw [hFψ', hFψ', map_mul, e, e', hρ]
  have hright : ∀ k ∈ K, ∀ x : G, Fψ (x * k) = Fψ x := by
    intro k hk x
    have e := hf0 1 (π x) ⟨π k, hk⟩
    have e' := hf0' 1 (π x) ⟨π k, hk⟩
    simp only [OneMemClass.coe_one, map_one, one_mul, Module.End.one_apply] at e e'
    rw [hFψ', hFψ', map_mul, e, e', inner_smul_left, inner_smul_right, ← mul_assoc,
      Complex.conj_mul', hχ, Complex.ofReal_one, one_pow, one_mul]
  have hreps : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a i * k := by
    intro x
    obtain ⟨i, ⟨γ, k, hk⟩, huniq⟩ := hy (π x)
    refine ⟨i, ⟨γ, γ.2, (a i)⁻¹ * (γ : G)⁻¹ * x, ?_, by group⟩, ?_⟩
    · change π ((a i)⁻¹ * (γ : G)⁻¹ * x) ∈ J
      have hk' : π x = π γ * y i * k := hk
      rw [map_mul, map_mul, map_inv, map_inv, ha i, hk']
      simpa [mul_assoc] using k.2
    · rintro j ⟨γ', hγ', k', hk', hx⟩
      refine huniq j ⟨⟨γ', hγ'⟩, ⟨π k', hk'⟩, ?_⟩
      change π x = π γ' * y j * π k'
      rw [hx, map_mul, map_mul, ha j]
  have hmain := _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ K 𝓖 h𝓖 ho hKt I a hreps
    (fun i => by
      have := (hfin i).image (fun γ : Γ => (γ : G))
      refine this.subset ?_
      rintro z ⟨hz, hzK⟩
      exact ⟨⟨z, hz⟩, hzK, rfl⟩) Fψ hleft hright
  obtain ⟨-, hint, heq⟩ := hmain
  refine ⟨hint, ?_⟩
  change ∫ h in 𝓖, Fψ h ∂ν = _
  rw [heq, h1]
  unfold _root_.Formalism.IndefR.Bridge.adInner
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : {γ | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ K}.ncard =
      Nat.card (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i)) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hmem i _).2 z.2.2⟩
        invFun := fun γ => ⟨γ.1.1, γ.1.2, (hmem i _).1 γ.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hFψ', ha i, hcard]

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
/- English proof (translation)
Apply `Complex.norm_eq_one_of_pow_eq_one (n := Nat.card A) _ Nat.card_pos.ne'` to reduce the goal to its premises. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]`.
-/
private lemma norm_character_eq_one_of_finite {A : Type} [Group A] [Finite A] (φ : A →* ℂˣ) (a : A) :
    ‖((φ a : ℂˣ) : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card A) _ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Unfold `_root_.Formalism.L2.DIV.levFn _root_.Formalism.L2.DIV.ext1`. Simplify using `only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_character_eq_one_of_finite, Finset.prod_const_one, mul_one]`. Use `split_ifs`. Conclude with `norm_character_eq_one_of_finite _ _`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.InnerClassSum.norm_levFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) (L : _root_.Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) :
    ‖(_root_.Formalism.L2.DIV.levFn β L x : ℂ)‖ = 1 := by
  unfold _root_.Formalism.L2.DIV.levFn _root_.Formalism.L2.DIV.ext1
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_character_eq_one_of_finite,
    Finset.prod_const_one, mul_one]
  split_ifs
  · exact norm_character_eq_one_of_finite _ _
  · simp

end GlobalTheory.InnerClassSum
