import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.HighestWeightMap

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun x => x i j map_add' := fun x y => rfl map_smul' := fun c x => rfl }`. Establish `h2` using `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at h2`. Conclude with `h2`.
-/
theorem hasDerivAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end

/- English proof (translation)
Take `⟨D, hD⟩` from `hd`. Set `Φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W` to `{ toFun := fun Z => ∑ a, ∑ b, Z a b • E a b Δ map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun c x => by simp [Finset.smul_sum, mul_smul] }`. Set `Ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W` to `{ toFun := fun Z => D fun i j => Z i j map_add' := fun x y => D.map_add x y map_smul' := fun c x => D.map_smul c x }`. Establish `hskew : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → Φ Z = Ψ Z`. Introduce `Z hZ`.

Establish `h1 : HasDerivAt (fun t : ℝ => fun i j => NormedSpace.exp ((t : ℂ) • Z) i j) (fun i j => Z i j) 0` using `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_exp_line Z i j`. Establish `h2` using `(hD.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 h1 (by simp)`. Conclude with `(hE Z hZ).unique h2`. Establish `hall : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Φ Z = Ψ Z`. Introduce `Z`.

Establish `e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ))`. Establish `: -Complex.I / 2 * Complex.I = 1 / 2`. Take the linear combination `(-1 / 2 : ℂ) * Complex.I_mul_I`. Rewrite using `[smul_smul, this]`. Use `module`.

Establish `s1` using `hskew (Z - Zᴴ) (by simp)`. Establish `s2` using `hskew (Complex.I • (Z + Zᴴ)) (by simp [conjTranspose_smul, add_comm])`. Rewrite using `[e, map_add, map_add, map_smul, map_smul (Ψ), s1, map_smul Φ (-Complex.I / 2), map_smul Ψ (-Complex.I / 2), s2]`. Establish `h3 : Φ (Matrix.single a b 1) = E a b Δ` using `by show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d Δ = _`. Simplify using `[Matrix.single_apply, ite_and, ite_smul]`.

Establish `h4 : HasDerivAt (fun s : ℂ => fun i j => (1 + Matrix.single a b s : Matrix (Fin k) (Fin k) ℂ) i j) (fun i j => Matrix.single a b (1 : ℂ) i j) 0`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.single_apply]`. Use `split_ifs`. Conclude with `(hasDerivAt_id' _).const_add _`.

Conclude with `hasDerivAt_const _ _`. Establish `h5 : HasDerivAt (fun s : ℂ => π (1 + Matrix.single a b s) Δ) (Ψ (Matrix.single a b 1)) 0` using `hD.comp_hasDerivAt_of_eq 0 h4 (by`. Use function extensionality and compare the values at `i j`. Use `show _ = (1 : Matrix (Fin k) (Fin k) ℂ) i j + Matrix.single a b (0 : ℂ) i j`. Use the proof step `simp)`.

Simplify using `only [hab] at h5`. Rewrite using `[← h3, hall, h5.unique (hasDerivAt_const _ _)]`.
-/
theorem raising_eq_zero {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} (E : Fin k → Fin k → Module.End ℂ W) (Δ : W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z →
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) Δ) (∑ a, ∑ b, Z a b • E a b Δ) 0)
    (hd : DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) Δ)
      (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j))
    {a b : Fin k} (hab : ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) : E a b Δ = 0 := by
  obtain ⟨D, hD⟩ := hd
  let Φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => ∑ a, ∑ b, Z a b • E a b Δ
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, mul_smul] }
  let Ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => D fun i j => Z i j
      map_add' := fun x y => D.map_add x y
      map_smul' := fun c x => D.map_smul c x }
  have hskew : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → Φ Z = Ψ Z := by
    intro Z hZ
    have h1 : HasDerivAt (fun t : ℝ => fun i j => NormedSpace.exp ((t : ℂ) • Z) i j) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_exp_line Z i j
    have h2 := (hD.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 h1 (by simp)
    exact (hE Z hZ).unique h2
  have hall : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Φ Z = Ψ Z := by
    intro Z
    have e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ)) := by
      have : -Complex.I / 2 * Complex.I = 1 / 2 := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      rw [smul_smul, this]
      module
    have s1 := hskew (Z - Zᴴ) (by simp)
    have s2 := hskew (Complex.I • (Z + Zᴴ)) (by simp [conjTranspose_smul, add_comm])
    rw [e, map_add, map_add, map_smul, map_smul (Ψ), s1, map_smul Φ (-Complex.I / 2), map_smul Ψ (-Complex.I / 2), s2]
  have h3 : Φ (Matrix.single a b 1) = E a b Δ := by
    show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d Δ = _
    simp [Matrix.single_apply, ite_and, ite_smul]
  have h4 : HasDerivAt (fun s : ℂ => fun i j => (1 + Matrix.single a b s : Matrix (Fin k) (Fin k) ℂ) i j)
      (fun i j => Matrix.single a b (1 : ℂ) i j) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (hasDerivAt_id' _).const_add _
    · exact hasDerivAt_const _ _
  have h5 : HasDerivAt (fun s : ℂ => π (1 + Matrix.single a b s) Δ) (Ψ (Matrix.single a b 1)) 0 :=
    hD.comp_hasDerivAt_of_eq 0 h4 (by
      funext i j
      show _ = (1 : Matrix (Fin k) (Fin k) ℂ) i j + Matrix.single a b (0 : ℂ) i j
      simp)
  simp only [hab] at h5
  rw [← h3, hall, h5.unique (hasDerivAt_const _ _)]

open Formalism.REAL in

/- English proof (translation)
Set `E : Fin n → Fin n → Module.End ℂ (V₁ × V₂)` to `fun a b => (E₁ a b).prodMap (E₂ a b)`. Establish `hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2)` using `fun _ _ _ => rfl`. Establish `hE : GlRel E`. Introduce `a b c d`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hEap]`. Rewrite using `[glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]`. Apply the tactic sequence `split_ifs <;> simp [hEap]`. Apply the tactic sequence `all_goals (constructor <;> abel)`. Establish `hw : IsHW E ν (v₁, v₂)`.

Use `⟨fun a => ?_, fun a b h => ?_⟩` and prove the remaining obligations. Rewrite using `[hEap, hw₁.1, hw₂.1]`. Both sides reduce to the same expression. Rewrite using `[hEap, hw₁.2 a b h, hw₂.2 a b h]`. Both sides reduce to the same expression.

Take `⟨S, hS, hvS, htop⟩` from `exists_stable_submodule_topWeight_line _ n E ν _ hE hw`. Set `K : Submodule ℂ V₂` to `S.comap (LinearMap.inr ℂ V₁ V₂)`. Establish `hK : ∀ a b, ∀ x ∈ K, E₂ a b x ∈ K` using `fun a b x hx => by`. Use `hS a b _ hx` as an intermediate fact. Simplify `this` using `[hEap, K]`.

Establish `hK' : ∀ a b, ∀ x ∈ Kᗮ, E₂ a b x ∈ Kᗮ` using `fun a b x hx => (Submodule.mem_orthogonal _ _).2 fun u hu => by`. Rewrite using `[← hU]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hx _ (hK _ _ _ hu)`. Establish `hv₂ : v₂ ∈ Kᗮ`. Take `⟨y, hy, z, hz, hyz⟩` from `K.exists_add_mem_mem_orthogonal v₂`.

Establish `hyw : ∀ a, E₂ a a y = ν a • y` using `fun a => by`. Establish `e` using `hw₂.1 a`. Rewrite `e` using `[hyz, map_add, smul_add]`. Establish `e' : E₂ a a y - ν a • y = -(E₂ a a z - ν a • z)`. Rewrite using `[neg_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]`.

Rewrite using `[← sub_eq_zero]`. Use `Submodule.disjoint_def.1 K.orthogonal_disjoint _ (K.sub_mem (hK _ _ _ hy) (K.smul_mem _ hy)) ?_` and prove the remaining obligations. Rewrite using `[e']`. Conclude with `Submodule.neg_mem _ (Submodule.sub_mem _ (hK' _ _ _ hz) (Submodule.smul_mem _ _ hz))`. Take `⟨c, hc⟩` from `htop (0, y) hy fun a => by simp [hEap, hyw]`.

Establish `hc1 : (0 : V₁) = c • v₁` using `congrArg Prod.fst hc`. Establish `hc2 : y = c • v₂` using `congrArg Prod.snd hc`. Rewrite `hc2` using `[(smul_eq_zero.1 hc1.symm).resolve_right hv₁, zero_smul]`. Rewrite using `[hyz, hc2, zero_add]`. Conclude with `hz`.

Set `T : Submodule ℂ (V₁ × V₂)` to `S ⊓ Kᗮ.comap (LinearMap.snd ℂ V₁ V₂)`. Establish `hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T` using `fun a b x hx => ⟨hS a b x hx.1, hK' a b _ hx.2⟩`. Establish `hvT : (v₁, v₂) ∈ T` using `⟨hvS, hv₂⟩`. Establish `hb : Function.Bijective ((LinearMap.fst ℂ V₁ V₂).comp T.subtype)`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨⟨x, y⟩, hx⟩ h0`. Take `rfl : x = 0` from `h0`. Take `rfl : y = 0` from `Submodule.disjoint_def.1 K.orthogonal_disjoint y hx.1 hx.2`. Both sides reduce to the same expression.

Break down `h₁ (T.map (LinearMap.fst ℂ V₁ V₂)) (by` into its components or cases. Introduce and unpack `a b _ ⟨x, hx, rfl⟩`. Conclude with `⟨E a b x, hT a b x hx, rfl⟩) with h | h`. Establish `hm : v₁ ∈ T.map (LinearMap.fst ℂ V₁ V₂)` using `⟨_, hvT, rfl⟩`. Rewrite `hm` using `[h]`.

Conclude with `absurd hm hv₁`. Introduce `y`. Establish `hm : y ∈ T.map (LinearMap.fst ℂ V₁ V₂)` using `by rw [h]; trivial`. Take `⟨x, hx, rfl⟩` from `hm`. Conclude with `⟨⟨x, hx⟩, rfl⟩`.

Use `⟨((LinearMap.snd ℂ V₁ V₂).comp T.subtype).comp (LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b x`. Take `⟨y, rfl⟩` from `(LinearEquiv.ofBijective _ hb).surjective x`. Establish `h : E₁ a b (LinearEquiv.ofBijective _ hb y) = LinearEquiv.ofBijective _ hb ⟨E a b y, hT a b y y.2⟩` using `rfl`. Rewrite using `[h]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `h : v₁ = LinearEquiv.ofBijective _ hb ⟨(v₁, v₂), hvT⟩` using `rfl`. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 h]`. Both sides reduce to the same expression.
-/
theorem exists_lie_map {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [NormedAddCommGroup V₂]
    [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] {n : ℕ}
    (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ)
    (v₁ : V₁) (v₂ : V₂) (hE₁ : GlRel E₁) (hE₂ : GlRel E₂)
    (hU : ∀ a b x y, ⟪E₂ a b x, y⟫_ℂ = ⟪x, E₂ b a y⟫_ℂ)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw₁ : IsHW E₁ ν v₁) (hw₂ : IsHW E₂ ν v₂) (hv₁ : v₁ ≠ 0) :
    ∃ L : V₁ →ₗ[ℂ] V₂, (∀ a b x, L (E₁ a b x) = E₂ a b (L x)) ∧ L v₁ = v₂ := by
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  let K : Submodule ℂ V₂ := S.comap (LinearMap.inr ℂ V₁ V₂)
  have hK : ∀ a b, ∀ x ∈ K, E₂ a b x ∈ K := fun a b x hx => by
    have := hS a b _ hx
    simpa [hEap, K] using this
  have hK' : ∀ a b, ∀ x ∈ Kᗮ, E₂ a b x ∈ Kᗮ := fun a b x hx =>
    (Submodule.mem_orthogonal _ _).2 fun u hu => by
      rw [← hU]
      exact (Submodule.mem_orthogonal _ _).1 hx _ (hK _ _ _ hu)
  have hv₂ : v₂ ∈ Kᗮ := by
    obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal v₂
    have hyw : ∀ a, E₂ a a y = ν a • y := fun a => by
      have e := hw₂.1 a
      rw [hyz, map_add, smul_add] at e
      have e' : E₂ a a y - ν a • y = -(E₂ a a z - ν a • z) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
      rw [← sub_eq_zero]
      refine Submodule.disjoint_def.1 K.orthogonal_disjoint _ (K.sub_mem (hK _ _ _ hy) (K.smul_mem _ hy)) ?_
      rw [e']
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (hK' _ _ _ hz) (Submodule.smul_mem _ _ hz))
    obtain ⟨c, hc⟩ := htop (0, y) hy fun a => by simp [hEap, hyw]
    have hc1 : (0 : V₁) = c • v₁ := congrArg Prod.fst hc
    have hc2 : y = c • v₂ := congrArg Prod.snd hc
    rw [(smul_eq_zero.1 hc1.symm).resolve_right hv₁, zero_smul] at hc2
    rw [hyz, hc2, zero_add]
    exact hz
  let T : Submodule ℂ (V₁ × V₂) := S ⊓ Kᗮ.comap (LinearMap.snd ℂ V₁ V₂)
  have hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T := fun a b x hx => ⟨hS a b x hx.1, hK' a b _ hx.2⟩
  have hvT : (v₁, v₂) ∈ T := ⟨hvS, hv₂⟩
  have hb : Function.Bijective ((LinearMap.fst ℂ V₁ V₂).comp T.subtype) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨x, y⟩, hx⟩ h0
      obtain rfl : x = 0 := h0
      obtain rfl : y = 0 := Submodule.disjoint_def.1 K.orthogonal_disjoint y hx.1 hx.2
      rfl
    · rcases h₁ (T.map (LinearMap.fst ℂ V₁ V₂)) (by
        rintro a b _ ⟨x, hx, rfl⟩
        exact ⟨E a b x, hT a b x hx, rfl⟩) with h | h
      · have hm : v₁ ∈ T.map (LinearMap.fst ℂ V₁ V₂) := ⟨_, hvT, rfl⟩
        rw [h] at hm
        exact absurd hm hv₁
      · intro y
        have hm : y ∈ T.map (LinearMap.fst ℂ V₁ V₂) := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := hm
        exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨((LinearMap.snd ℂ V₁ V₂).comp T.subtype).comp (LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_, ?_⟩
  · intro a b x
    obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ hb).surjective x
    have h : E₁ a b (LinearEquiv.ofBijective _ hb y)
        = LinearEquiv.ofBijective _ hb ⟨E a b y, hT a b y y.2⟩ := rfl
    rw [h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  · have h : v₁ = LinearEquiv.ofBijective _ hb ⟨(v₁, v₂), hvT⟩ := rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 h]
    rfl

open Formalism.MainNotions.S in

/- English proof (translation)
Introduce `k Λ H _ _ _ τ E _ _ _ π Δ hτ hK hπ hd _ hup hwt`. Establish `: Nontrivial H`. Take `⟨v, -, hv, -⟩` from `hK.2.2.2.1`. Conclude with `nontrivial_of_ne v 0 hv`. Establish `hτ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) τ` using `hτ`.

Establish `hπ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π` using `hπ`. Take `⟨E₁, g₁, d₁, i₁, x₁, hx₁, w₁⟩` from `GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest (Λ := Λ) hτ' hK`. Take `⟨E₂, g₂, u₂, d₂⟩` from `GlobalTheory.UnitaryDerived.exists_derived_action k E π hπ'`. Establish `w₂ : Formalism.REAL.IsHW E₂ (fun a => (Λ a : ℂ)) Δ` using `⟨GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E₂ d₂ Λ Δ hwt, fun a b hab => raising_eq_zero E₂ Δ (fun Z hZ => d₂ Z hZ Δ) (hd Δ) (hup a b hab)⟩`. Take `⟨L, hL, hLx⟩` from `exists_lie_map E₁ E₂ _ x₁ Δ g₁ g₂ (fun a b x y => by simpa [Formalism.REAL.sgn, PI.UpqRep.allPos] using u₂ a b x y) i₁ w₁ w₂ hx₁`.

Use `⟨L, fun g hg x => ?_, x₁, hLx⟩` and prove the remaining obligations. Take `⟨Y, hY, hg', -⟩` from `Formalism.REAL.compact_exponential_surjective k (PI.UpqRep.allPos k) g ((GlobalTheory.UnitaryHighestWeight.mem_K_iff g).2 hg)`. Establish `hZ : Yᴴ = -Y`. Establish `h : Yᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) + PI.UpqRep.Jm (PI.UpqRep.allPos k) * Y = 0` using `hY.1`. Rewrite `h` using `[GlobalTheory.UnitaryHighestWeight.Jm_allPos, Matrix.mul_one, Matrix.one_mul]`.

Conclude with `eq_neg_of_add_eq_zero_left h`. Establish `h` using `GlobalTheory.UnitaryHighestWeightUnique.intertwine_group (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₁ a b) (GlobalTheory.UnitaryHighestWeight.group_zero hτ' _) (GlobalTheory.UnitaryHighestWeight.group_add hτ' hZ) (fun w => by simpa only [LinearMap.sum_ap …`. Simplify `h` using `[hg']`.
-/
theorem exists_intertwiner : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  intro k Λ H _ _ _ τ E _ _ _ π Δ hτ hK hπ hd _ hup hwt
  have : Nontrivial H := by
    obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact nontrivial_of_ne v 0 hv
  have hτ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) τ := hτ
  have hπ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π := hπ
  obtain ⟨E₁, g₁, d₁, i₁, x₁, hx₁, w₁⟩ :=
    GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest (Λ := Λ) hτ' hK
  obtain ⟨E₂, g₂, u₂, d₂⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k E π hπ'
  have w₂ : Formalism.REAL.IsHW E₂ (fun a => (Λ a : ℂ)) Δ :=
    ⟨GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E₂ d₂ Λ Δ hwt,
      fun a b hab => raising_eq_zero E₂ Δ (fun Z hZ => d₂ Z hZ Δ) (hd Δ) (hup a b hab)⟩
  obtain ⟨L, hL, hLx⟩ := exists_lie_map E₁ E₂ _ x₁ Δ g₁ g₂
    (fun a b x y => by simpa [Formalism.REAL.sgn, PI.UpqRep.allPos] using u₂ a b x y) i₁ w₁ w₂ hx₁
  refine ⟨L, fun g hg x => ?_, x₁, hLx⟩
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (PI.UpqRep.allPos k) g
    ((GlobalTheory.UnitaryHighestWeight.mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) + PI.UpqRep.Jm (PI.UpqRep.allPos k) * Y = 0 := hY.1
    rw [GlobalTheory.UnitaryHighestWeight.Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₁ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hτ' _) (GlobalTheory.UnitaryHighestWeight.group_add hτ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₁ _ hZ w)
    (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₂ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hπ' _) (GlobalTheory.UnitaryHighestWeight.group_add hπ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₂ _ hZ w)
    L (fun w => by simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hL]) x 1
  simpa [hg'] using h

end GlobalTheory.HighestWeightMap
