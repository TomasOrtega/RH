import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Establish `hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g` using `fun g => by`. Rewrite using `[qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]`. Establish `hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) = (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`.

Take `⟨N, hN, g, hg⟩` from `exists_int_mul_eq_qmap f`. Establish `hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)`. Rewrite using `[RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]`. Establish `hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap`. Rewrite using `[hg]`.

Conclude with `Ideal.mem_map_of_mem _ hg0`. Establish `hu : IsUnit (N : MRingOver ℚ ι')`. Rewrite using `[show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]`. Conclude with `(isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C`. Establish `h2` using `Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem`.

Rewrite `h2` using `[← mul_assoc, hu.val_inv_mul, one_mul]`. Then use the resulting hypothesis. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hmap]`. Conclude with `RingHom.mem_ker.mp hg`.

Rewrite using `[hker]`. Take `⟨T, hT, hTe⟩` from `h`. Use `⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hT f hf`.

Conclude with `⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩`.
-/
theorem GenFibreChartDeg.isMultiHomogIdeal_ker_rat {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi`. Establish `: CharZero G.Φ` using `(algebraMap G.Φ G.Φ').charZero`. Establish `hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0` using `fun k => by`. Rewrite using `[G.compat]`. Conclude with `(map_ne_zero _).2 (hc k)`.

Establish `hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0`. Introduce `k'`. Distinguish the cases in `hk : k' ∈ Set.range κ`. Take `⟨k, rfl⟩` from `hk`. Establish `key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0`.

Introduce and unpack `⟨a, j⟩ rfl h`. Conclude with `⟨j, h⟩`. Conclude with `key _ (hv.2.2.1 _) (hx'0 k)`. Conclude with `⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩`. Use `choose i' hi' using hex`.

Set `t : K → G.Φ'` to `fun k => G.x' ⟨κ k, i' (κ k)⟩`. Set `Φ₁` to `(IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange`. Set `F₁` to `blockFnField G.x'`. Set `F₀` to `blockFnField (G.x' ∘ v)`. Set `E` to `IntermediateField.adjoin ℚ (Set.range t)`.

Set `S` to `Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩`. Establish `hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁` using `fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩`. Establish `hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀` using `fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩`. Establish `hF01 : F₀ ≤ F₁` using `IntermediateField.adjoin_le_iff.2 (by`. Introduce and unpack `_ ⟨p, q, h, rfl⟩`.

Conclude with `hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))`. Establish `hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁` using `fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩`. Establish `hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩` using `fun k => by`. Take `⟨p₀, h⟩` from `hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩`. Conclude with `⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩`.

Establish `ht1 : ∀ k, t k ∈ Φ₁` using `fun k => by`. Take `⟨p₀, -, h⟩` from `hchart k`. Use `show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁`. Rewrite using `[← h, G.compat]`. Conclude with `hmem _`.

Establish `hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀` using `fun p => by`. Take `⟨p₀, h1, h⟩` from `hchart p.1`. Use `show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀`. Rewrite using `[← h]`. Conclude with `hF0 p p₀ h1.symm`.

Establish `hΦ₁ : F₀ ⊔ E = Φ₁`. Use `le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, q, -, rfl⟩ show G.x' (v p) / G.x' (v q) ∈ Φ₁`. Rewrite using `[G.compat, G.compat]`. Conclude with `div_mem (hmem _) (hmem _)`.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `ht1 k`. Introduce `z hz`. Take `⟨c, rfl⟩` from `AlgHom.mem_fieldRange.1 hz`. Take `⟨f, g, -, rfl⟩` from `G.gen c`.

Establish `hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]`.

Conclude with `intCast_mem _ a`. Consider the case `add f g hf hg`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem hf hg`. Consider the case `mul_X f q hf`.

Rewrite using `[map_mul, map_mul, aeval_X, ← G.compat]`. Use `mul_mem hf ?_` and prove the remaining obligations. Rewrite using `[← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]`. Conclude with `mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q)) ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))`. Use `show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E`.

Rewrite using `[map_div₀]`. Conclude with `div_mem (hpoly f) (hpoly g)`. Establish `hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E`. Use `le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[← hΦ₁]`.

Conclude with `sup_le_sup_right hF01 E`. Use `(IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `hF _ _ rfl`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩`. Simplify using `only at hab`. Substitute `hab` using the available equality. Distinguish the cases in `ha : a ∈ Set.range κ`. Take `⟨k, rfl⟩` from `ha`.

Take `⟨p, hp⟩` from `hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩`. Take `⟨q, hq⟩` from `hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩`. Establish `hpq : p.1 = q.1` using `hv.1 ((hv.2.2.1 p).symm.trans ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))`. Rewrite using `[← hp, ← hq]`. Conclude with `(le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))`.

Rewrite using `[← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]`. Use `(le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)` and prove the remaining obligations. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩`. Rewrite using `[← hΦ₁]`.

Conclude with `le_sup_right.trans le_sup_left`. Establish `hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁`. Use `le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `hF _ _ rfl`.

Introduce and unpack `_ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩ dsimp only at hab`. Substitute `hab` using the available equality. Rewrite using `[← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]`. Conclude with `div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)`. Establish `hker` using `GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)`.

Establish `hindep : AlgebraicIndependent F₁ t`. Establish `key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t → AlgebraicIndependent F₁ t`. Introduce and unpack `L rfl h`. Conclude with `h`. Conclude with `key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)`.

Use `(GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _`. Rewrite using `[hΦS, ← hΦ₁]`. Conclude with `hC ℚ G.Φ' F₀ F₁ K t hF01 hindep`.
-/
theorem GenFibreChartDeg.proof (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add, map_add]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep

end GroundTheory.Heights₂.Heights.Targets
