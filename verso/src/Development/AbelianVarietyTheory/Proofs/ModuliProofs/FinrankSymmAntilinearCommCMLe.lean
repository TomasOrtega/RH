import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.DimPEL

/- English proof (translation)
Set `B` to `canonicalEmbedding.latticeBasis E`. Set `Φ : ((E →+* ℂ) → ℂ) →ₗ[ℂ] Module.End ℂ V` to `B.constr ℂ (fun i => F (RingOfIntegers.basis E i))`. Establish `hB : ∀ i, B i = canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)`. Introduce `i`. Simplify using `[B, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]`.

Establish `h1 : ∀ a : 𝓞 E, Φ (canonicalEmbedding E (a : E)) = F a`. Introduce `a`. Set `L₁ : 𝓞 E →ₗ[ℤ] Module.End ℂ V` to `(Φ.toAddMonoidHom.comp (((canonicalEmbedding E).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)).toIntLinearMap`. Set `L₂ : 𝓞 E →ₗ[ℤ] Module.End ℂ V` to `F.toAddMonoidHom.toIntLinearMap`. Establish `: L₁ = L₂`.

Apply `(RingOfIntegers.basis E).ext` to reduce the goal to its premises. Introduce `i`. Express the relevant statement in the definitionally equal form `Φ (canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)) = F _`. Rewrite using `[← hB]`. Simplify using `[Φ]`.

Conclude with `LinearMap.congr_fun this a`. Establish `h2 : ∀ (a : 𝓞 E) (x : (E →+* ℂ) → ℂ), Φ (canonicalEmbedding E (a : E) * x) = F a * Φ x`. Introduce `a x`. Establish `: Φ ∘ₗ LinearMap.mulLeft ℂ (canonicalEmbedding E (a : E)) = LinearMap.mulLeft ℂ (F a) ∘ₗ Φ`. Apply `B.ext` to reduce the goal to its premises.

Introduce `i`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Rewrite using `[hB, h1, ← map_mul F, ← h1, ← map_mul (canonicalEmbedding E)]`. Both sides reduce to the same expression. Conclude with `LinearMap.congr_fun this x`.

Use `⟨fun τ => Φ (Pi.single τ 1) v, fun τ a => ?_, ?_⟩` and prove the remaining obligations. Establish `: canonicalEmbedding E (a : E) * Pi.single τ 1 = τ (a : E) • (Pi.single τ 1 : (E →+* ℂ) → ℂ)`. Use extensionality with `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality.

Simplify using `[canonicalEmbedding.apply_at]`. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite using `[← Module.End.mul_apply, ← h2, this, map_smul, LinearMap.smul_apply]`. Rewrite using `[← LinearMap.sum_apply, ← map_sum, Finset.univ_sum_single]`. Use `h1 1` as an intermediate fact.

Establish `e : Φ 1 = 1` using `by simpa using this`. Express the relevant statement in the definitionally equal form `v = Φ 1 v`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem exists_sum_eigen {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : 𝓞 E →+* Module.End ℂ V) (v : V) :
    ∃ w : (E →+* ℂ) → V, (∀ τ (a : 𝓞 E), F a (w τ) = τ (a : E) • w τ) ∧ v = ∑ τ, w τ := by
  classical
  let B := canonicalEmbedding.latticeBasis E
  let Φ : ((E →+* ℂ) → ℂ) →ₗ[ℂ] Module.End ℂ V := B.constr ℂ (fun i => F (RingOfIntegers.basis E i))
  have hB : ∀ i, B i = canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    simp [B, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  have h1 : ∀ a : 𝓞 E, Φ (canonicalEmbedding E (a : E)) = F a := by
    intro a
    let L₁ : 𝓞 E →ₗ[ℤ] Module.End ℂ V :=
      (Φ.toAddMonoidHom.comp (((canonicalEmbedding E).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)).toIntLinearMap
    let L₂ : 𝓞 E →ₗ[ℤ] Module.End ℂ V := F.toAddMonoidHom.toIntLinearMap
    have : L₁ = L₂ := by
      apply (RingOfIntegers.basis E).ext
      intro i
      change Φ (canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)) = F _
      rw [← hB]
      simp [Φ]
    exact LinearMap.congr_fun this a
  have h2 : ∀ (a : 𝓞 E) (x : (E →+* ℂ) → ℂ), Φ (canonicalEmbedding E (a : E) * x) = F a * Φ x := by
    intro a x
    have : Φ ∘ₗ LinearMap.mulLeft ℂ (canonicalEmbedding E (a : E)) = LinearMap.mulLeft ℂ (F a) ∘ₗ Φ := by
      apply B.ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hB, h1, ← map_mul F, ← h1, ← map_mul (canonicalEmbedding E)]
      rfl
    exact LinearMap.congr_fun this x
  refine ⟨fun τ => Φ (Pi.single τ 1) v, fun τ a => ?_, ?_⟩
  · have : canonicalEmbedding E (a : E) * Pi.single τ 1 = τ (a : E) • (Pi.single τ 1 : (E →+* ℂ) → ℂ) := by
      ext σ
      by_cases h : σ = τ
      · subst h; simp [canonicalEmbedding.apply_at]
      · simp [Pi.single_eq_of_ne h]
    rw [← Module.End.mul_apply, ← h2, this, map_smul, LinearMap.smul_apply]
  · rw [← LinearMap.sum_apply, ← map_sum, Finset.univ_sum_single]
    have := h1 1
    have e : Φ 1 = 1 := by simpa using this
    change v = Φ 1 v
    rw [e]
    rfl

/- English proof (translation)
Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `[sq] at hre him`. Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `: z.re = 0`.

Establish `h3 : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `h4`. Rewrite `hre` using `[h4]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`.

Apply the tactic sequence `apply Complex.ext <;> simp [this]`.
-/
theorem conj_eq_neg {z : ℂ} {d : ℕ} (h : z ^ 2 = -(d : ℂ)) (hd : 0 < d) : starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : z.re = 0 := by
    have h3 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [this]

abbrev Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) := ⨅ a : 𝓞 E, Module.End.eigenspace (F a) (τ (a : E))

/- English proof (translation)
Simplify using `[Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`.
-/
theorem mem_Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (v : Fin g → ℂ) : v ∈ Eig F τ ↔ ∀ a : 𝓞 E, F a v = τ (a : E) • v := by
  simp [Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_Eig]`. Introduce `a`. Rewrite using `[hΘ a v, hv, star_smul, Matrix.mulVec_smul, ComplexEmbedding.conjugate_coe_eq]`. Both sides reduce to the same expression.
-/
theorem theta_mem {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (Θ : Matrix (Fin g) (Fin g) ℂ) (hΘ : ∀ a, Comm Θ (F a)) (v : Fin g → ℂ) (hv : v ∈ Eig F τ) :
    Θ.mulVec (star v) ∈ Eig F (ComplexEmbedding.conjugate τ) := by
  rw [mem_Eig] at hv ⊢
  intro a
  rw [hΘ a v, hv, star_smul, Matrix.mulVec_smul, ComplexEmbedding.conjugate_coe_eq]
  rfl

/- English proof (translation)
Establish `hd : 0 < H.d` using `H.d_prime.pos`. Establish `hρ0 : ρ₀ ≠ 0`. Introduce `h`. Rewrite `hρ` using `[h]`. Establish `: (H.d : ℂ) = 0` using `by simpa using hρ`.

Conclude with `hd.ne' (by exact_mod_cast this)`. Establish `hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Introduce `τ`. Use `congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Establish `hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E)`. Introduce `τ`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `conj_eq_neg (hsq τ) hd`. Establish `hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀`.

Introduce `τ h h'`. Rewrite `h'` using `[hconj, h]`. Apply `hρ0` to reduce the goal to its premises. Take the linear combination `(-1/2 : ℂ) * h'`. Establish `heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀`.

Introduce `τ h`. Rewrite using `[hconj]`. Establish `: τ (H.rt : E) ^ 2 = ρ₀ ^ 2` using `by rw [hsq, hρ]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1` into its components or cases. Conclude with `absurd h1 h`.

Rewrite using `[h1, neg_neg]`. Establish `hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q` using `fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))`. Set `T` to `{τ : E →+* ℂ // τ (H.rt : E) = ρ₀}`. Establish `hcard : Fintype.card T ≤ Module.finrank ℚ E / 2`. Establish `h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀}`.

Use `Fintype.card_le_of_injective (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_` and prove the remaining obligations. Introduce `σ τ h`. Establish `h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (star_injective h2)`. Rewrite `h1` using `[Fintype.card_subtype_compl, NumberField.Embeddings.card]`.

Establish `h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ)` using `Fintype.card_subtype_le _`. Rewrite `h3` using `[NumberField.Embeddings.card]`. Express the relevant statement in the definitionally equal form `Fintype.card T ≤ _ - Fintype.card T at h1`. Use linear arithmetic over natural numbers and integers. Establish `hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p` using `fun τ => by rw [hdim', if_pos τ.2]`.

Establish `hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q` using `fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]`. Set `b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1)` to `fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)`. Set `Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1))` to `{ toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩ map_add' := fun Θ Θ' => by`. Use function extensionality and compare the values at `τ i`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[Matrix.add_mulVec]`. Use the proof step `map_smul' := fun c Θ => by`. Use function extensionality and compare the values at `τ i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.smul_mulVec] }`.

Establish `hinj : Function.Injective Ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Θ hΘ`. Take `⟨hs, hc⟩` from `hS Θ.1 Θ.2`. Establish `k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0`.

Introduce `τ hτ v hv`. Establish `hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0` using `fun i => congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)`. Establish `e` using `congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e`. Rewrite using `[← e, star_sum, Matrix.mulVec_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, Matrix.mulVec_smul, hb, smul_zero]`. Establish `k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0`. Introduce `τ v hv`. Distinguish the cases in `hτ : τ (H.rt : E) = ρ₀`.

Conclude with `k1 τ hτ v hv`. Assume the negation of the conclusion as `h0`. Establish `h1` using `hpos _ h0`. Rewrite `h1` using `[hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)]`. Simplify using `[hermForm] at h1`.

Establish `k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0`. Introduce `v`. Take `⟨w, hw, rfl⟩` from `exists_sum_eigen F v`. Rewrite using `[star_sum, Matrix.mulVec_sum]`. Conclude with `Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `k3 (star v)` as an intermediate fact.

Rewrite `this` using `[star_star]`. Simplify using `using this`. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hinj`. Rewrite `hle` using `[Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_symm_comm_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ))
    (hρ : ρ₀ ^ 2 = -(H.d : ℂ)) (_hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hdim : ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q)
    (hS : ∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) :
    Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  classical
  have hd : 0 < H.d := H.d_prime.pos
  have hρ0 : ρ₀ ≠ 0 := by
    intro h
    rw [h] at hρ
    have : (H.d : ℂ) = 0 := by simpa using hρ
    exact hd.ne' (by exact_mod_cast this)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    intro τ
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    simpa using this
  have hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E) := by
    intro τ
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg (hsq τ) hd
  have hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀ := by
    intro τ h h'
    rw [hconj, h] at h'
    apply hρ0
    linear_combination (-1/2 : ℂ) * h'
  have heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀ := by
    intro τ h
    rw [hconj]
    have : τ (H.rt : E) ^ 2 = ρ₀ ^ 2 := by rw [hsq, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]
  have hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q :=
    fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))
  let T := {τ : E →+* ℂ // τ (H.rt : E) = ρ₀}
  have hcard : Fintype.card T ≤ Module.finrank ℚ E / 2 := by
    have h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀} := by
      refine Fintype.card_le_of_injective
        (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_
      intro σ τ h
      have h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1 := congrArg Subtype.val h
      exact Subtype.ext (star_injective h2)
    rw [Fintype.card_subtype_compl, NumberField.Embeddings.card] at h1
    have h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ) := Fintype.card_subtype_le _
    rw [NumberField.Embeddings.card] at h3
    change Fintype.card T ≤ _ - Fintype.card T at h1
    omega
  have hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p := fun τ => by rw [hdim', if_pos τ.2]
  have hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q :=
    fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]
  let b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1) := fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)
  let Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1)) :=
    { toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩
      map_add' := fun Θ Θ' => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.add_mulVec]
      map_smul' := fun c Θ => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ
    obtain ⟨hs, hc⟩ := hS Θ.1 Θ.2
    have k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ hτ v hv
      have hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0 := fun i =>
        congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)
      have e := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
      rw [← e, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [star_smul, Matrix.mulVec_smul, hb, smul_zero]
    have k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ v hv
      by_cases hτ : τ (H.rt : E) = ρ₀
      · exact k1 τ hτ v hv
      · by_contra h0
        have h1 := hpos _ h0
        rw [hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)] at h1
        simp [hermForm] at h1
    have k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0 := by
      intro v
      obtain ⟨w, hw, rfl⟩ := exists_sum_eigen F v
      rw [star_sum, Matrix.mulVec_sum]
      exact Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := k3 (star v)
    rw [star_star] at this
    simpa using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Module.finrank ℂ S ≤ Fintype.card T * (p * q) := hle
    _ ≤ Module.finrank ℚ E / 2 * (p * q) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

end GlobalTheory.KS.DimPEL
end
