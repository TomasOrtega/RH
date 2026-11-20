import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualEmbeddingBijective

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

/- English proof (translation)
Take `⟨S, hS⟩` from `F.fg`. Take `⟨d, hd0, hd⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image y ∪ S.biUnion fun g => Finset.univ.image g)`. Establish `hint : ∀ z : K, IsIntegral ℤ z → z ∈ (algebraMap (𝓞 K) K).range` using `fun z hz => ⟨⟨z, hz⟩, rfl⟩`. Use `⟨d * d, mul_ne_zero hd0 hd0, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hS]`. Use `Submodule.span_induction (p := fun x _ => ((d * d) • y) ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce `g hg`. Establish `hsum : ((d * d) • y) ⬝ᵥ g = ∑ j, (d • y j) * (d • g j)`. Simplify using `only [dotProduct, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Use `sum_mem fun j _ => mul_mem (hint _ (hd _ ?_)) (hint _ (hd _ ?_))` and prove the remaining obligations. Conclude with `Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))`.

Conclude with `Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)`. Rewrite using `[dotProduct_zero]`. Conclude with `zero_mem _`. Introduce `x z _ _ hx hz`. Rewrite using `[dotProduct_add]`.

Conclude with `add_mem hx hz`. Introduce `a x _ hx`. Take `⟨c, hc⟩` from `hx`. Conclude with `⟨a * c, by rw [dotProduct_smul, map_mul, hc]; rfl⟩`.
-/
theorem exists_zsmul_mem_dualLattice (F : HermLattice K i) (y : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • y ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image y ∪ S.biUnion fun g => Finset.univ.image g)
  have hint : ∀ z : K, IsIntegral ℤ z → z ∈ (algebraMap (𝓞 K) K).range :=
    fun z hz => ⟨⟨z, hz⟩, rfl⟩
  refine ⟨d * d, mul_ne_zero hd0 hd0, ?_⟩
  intro x hx
  rw [← hS] at hx
  refine Submodule.span_induction
    (p := fun x _ => ((d * d) • y) ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range) ?_ ?_ ?_ ?_ hx
  · intro g hg
    have hsum : ((d * d) • y) ⬝ᵥ g = ∑ j, (d • y j) * (d • g j) := by
      simp only [dotProduct, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    refine sum_mem fun j _ => mul_mem (hint _ (hd _ ?_)) (hint _ (hd _ ?_))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨g, Finset.mem_coe.mp hg, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
  · rw [dotProduct_zero]
    exact zero_mem _
  · intro x z _ _ hx hz
    rw [dotProduct_add]
    exact add_mem hx hz
  · intro a x _ hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [dotProduct_smul, map_mul, hc]; rfl⟩

def pairing (w : (K →+* ℂ) × Fin i → ℂ) : (Fin i → K) →+ ℂ where
  toFun φ := ∑ p, p.1 (φ p.2) * w p
  map_zero' := by simp
  map_add' φ ψ := by simp [add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [pairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[mul_comm]`. Introduce `j' _ hj'`.

Simplify using `[Pi.single_eq_of_ne hj']`. Simplify using the standard rewrite rules.
-/
theorem pairing_single (w : (K →+* ℂ) × Fin i → ℂ) (j : Fin i) (x : K) :
    pairing w (Pi.single j x) = ∑ σ : K →+* ℂ, w (σ, j) * σ x := by
  classical
  simp only [pairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Establish `hb : ∀ t, pairing w (b t : Fin i → K) = 0` using `fun t => by`. Establish `h` using `congrFun hw t`. Simplify `h` using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, pairing]`.

Establish `hL : ∀ φ : dualLattice F, pairing w φ = 0`. Introduce `φ`. Rewrite using `[← b.sum_repr φ, Submodule.coe_sum, map_sum]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, map_zsmul, hb, smul_zero]`.

Establish `hK : ∀ y, pairing w y = 0`. Introduce `y`. Take `⟨N, hN, hy⟩` from `exists_zsmul_mem_dualLattice F y`. Establish `h` using `hL ⟨_, hy⟩`. Rewrite `h` using `[Submodule.coe_mk, map_zsmul]`.

Conclude with `(smul_eq_zero.mp h).resolve_left hN`. Use function extensionality and compare the values at `p`. Take `⟨σ, j⟩` from `p`. Establish `hli` using `(linearIndependent_monoidHom K ℂ).comp (fun σ : K →+* ℂ => σ.toMonoidHom) (fun σ τ h => RingHom.ext fun x => DFunLike.congr_fun h x)`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`.

Use `hli (fun σ => w (σ, j)) ?_ σ` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `h` using `hK (Pi.single j x)`. Rewrite `h` using `[pairing_single]`. Simplify `h` using `[Finset.sum_apply]`.
-/
theorem injective (F : HermLattice K i) {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Function.Injective (Matrix.mulVecLin (dualEmbMatrix b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hb : ∀ t, pairing w (b t : Fin i → K) = 0 := fun t => by
    have h := congrFun hw t
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, pairing] using h
  have hL : ∀ φ : dualLattice F, pairing w φ = 0 := by
    intro φ
    rw [← b.sum_repr φ, Submodule.coe_sum, map_sum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Submodule.coe_smul, map_zsmul, hb, smul_zero]
  have hK : ∀ y, pairing w y = 0 := by
    intro y
    obtain ⟨N, hN, hy⟩ := exists_zsmul_mem_dualLattice F y
    have h := hL ⟨_, hy⟩
    rw [Submodule.coe_mk, map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hN
  funext p
  obtain ⟨σ, j⟩ := p
  have hli := (linearIndependent_monoidHom K ℂ).comp (fun σ : K →+* ℂ => σ.toMonoidHom)
    (fun σ τ h => RingHom.ext fun x => DFunLike.congr_fun h x)
  rw [Fintype.linearIndependent_iff] at hli
  refine hli (fun σ => w (σ, j)) ?_ σ
  funext x
  have h := hK (Pi.single j x)
  rw [pairing_single] at h
  simpa [Finset.sum_apply] using h

/- English proof (translation)
Establish `h1 : LinearIndependent ℤ (fun t => (b t : Fin i → K))` using `b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)`. Establish `h2 : LinearIndependent ℚ (fun t => (b t : Fin i → K))` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp h1`. Establish `h3` using `h2.fintype_card_le_finrank`. Rewrite `h3` using `[Module.finrank_pi_fintype]`. Rewrite using `[Fintype.card_prod, NumberField.Embeddings.card K ℂ, Fintype.card_fin]`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3`. Rewrite using `[mul_comm]`. Conclude with `h3`.
-/
theorem card_le (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Fintype.card T ≤ Fintype.card ((K →+* ℂ) × Fin i) := by
  have h1 : LinearIndependent ℤ (fun t => (b t : Fin i → K)) :=
    b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)
  have h2 : LinearIndependent ℚ (fun t => (b t : Fin i → K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have h3 := h2.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype] at h3
  rw [Fintype.card_prod, NumberField.Embeddings.card K ℂ, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  rw [mul_comm]
  exact h3

end DualEmbeddingBijective

/- English proof (translation)
Introduce `K _ _ i F T _ _ b`. Establish `hinj` using `DualEmbeddingBijective.injective F b`. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hinj`. Establish `hcard` using `DualEmbeddingBijective.card_le F b`. Simplify using `only [Module.finrank_fintype_fun_eq_card] at hle`.

Use `⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩` and prove the remaining obligations. Simplify using `only [Module.finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem DualEmbBijective.proof : DualEmbBijective.Statement := by
  intro K _ _ i F T _ _ b
  have hinj := DualEmbeddingBijective.injective F b
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcard := DualEmbeddingBijective.card_le F b
  simp only [Module.finrank_fintype_fun_eq_card] at hle
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simp only [Module.finrank_fintype_fun_eq_card]
  omega

end

end GroundTheory.Heights₂.Heights
