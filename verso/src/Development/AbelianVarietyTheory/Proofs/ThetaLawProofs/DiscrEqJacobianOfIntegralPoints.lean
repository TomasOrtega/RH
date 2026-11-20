import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PointMatrixMulLeftMulMatrix
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

/- English proof (translation)
Establish `hfin : Module.Finite O B` using `Module.Finite.of_injective φ hφ`. Establish `hfree : Module.Free O B` using `Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm`. Establish `h1 : Module.finrank O B ≤ Module.finrank O (Ix → O)` using `LinearMap.finrank_le_finrank_of_injective hφ`. Establish `h2 : Module.finrank O (Ix → O) ≤ Module.finrank O (LinearMap.range φ)`. Set `ψ : (Ix → O) →ₗ[O] LinearMap.range φ` to `LinearMap.codRestrict _ (c • LinearMap.id) (fun t => by`.

Take `⟨y, hy⟩` from `hs t`. Conclude with `⟨y, hy⟩)`. Use `LinearMap.finrank_le_finrank_of_injective (f := ψ) ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`.

Establish `h3 : c • t = 0` using `congrArg Subtype.val ht`. Conclude with `(smul_eq_zero.1 h3).resolve_left hc`. Rewrite `h2` using `[← (LinearEquiv.ofInjective φ hφ).finrank_eq]`. Establish `h3 : Module.finrank O B = Fintype.card Ix`. Rewrite using `[le_antisymm h1 h2, Module.finrank_fintype_fun_eq_card]`.

Set `b : Module.Basis Ix O B` to `(Module.finBasisOfFinrankEq O B h3).reindex (Fintype.equivFin Ix).symm`. Use `⟨b, fun h0 => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `h4 : φ (∑ a, v a • b a) = 0`. Use extensionality with `a`.

Use `congrFun hMv a` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this`. Rewrite using `[map_sum, Finset.sum_apply, Pi.zero_apply, ← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.

Establish `h5 : ∑ a, v a • b a = 0` using `hφ (h4.trans (map_zero φ).symm)`. Conclude with `hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h5))`.
-/
theorem exists_basis_det_ne_zero_of_points {O B Ix : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup B] [Module O B] [Fintype Ix] [DecidableEq Ix]
    (φ : B →ₗ[O] (Ix → O)) (hφ : Function.Injective φ) (c : O) (hc : c ≠ 0)
    (hs : ∀ t : Ix → O, ∃ y, φ y = c • t) :
    ∃ b : Module.Basis Ix O B, (Matrix.of fun a a' => φ (b a') a).det ≠ 0 := by
  have hfin : Module.Finite O B := Module.Finite.of_injective φ hφ
  have hfree : Module.Free O B :=
    Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm
  have h1 : Module.finrank O B ≤ Module.finrank O (Ix → O) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have h2 : Module.finrank O (Ix → O) ≤ Module.finrank O (LinearMap.range φ) := by
    let ψ : (Ix → O) →ₗ[O] LinearMap.range φ :=
      LinearMap.codRestrict _ (c • LinearMap.id) (fun t => by
        obtain ⟨y, hy⟩ := hs t
        exact ⟨y, hy⟩)
    refine LinearMap.finrank_le_finrank_of_injective (f := ψ) ?_
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h3 : c • t = 0 := congrArg Subtype.val ht
    exact (smul_eq_zero.1 h3).resolve_left hc
  rw [← (LinearEquiv.ofInjective φ hφ).finrank_eq] at h2
  have h3 : Module.finrank O B = Fintype.card Ix := by
    rw [le_antisymm h1 h2, Module.finrank_fintype_fun_eq_card]
  let b : Module.Basis Ix O B :=
    (Module.finBasisOfFinrankEq O B h3).reindex (Fintype.equivFin Ix).symm
  refine ⟨b, fun h0 => ?_⟩
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h4 : φ (∑ a, v a • b a) = 0 := by
    ext a
    have := congrFun hMv a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h5 : ∑ a, v a • b a = 0 := hφ (h4.trans (map_zero φ).symm)
  exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h5))

/- English proof (translation)
Introduce `O _ _ _ _ g Ix _ _ F e hF hX hker ⟨c, hc, hs⟩`. Set `S` to `MvPowerSeries (Fin g) O`. Set `I : Ideal S` to `Ideal.span (Set.range F)`. Set `eb : Ix → ((S ⧸ I) →ₐ[O] O)` to `fun a => Ideal.Quotient.liftₐ I (e a) (fun s hs => by`. Establish `: I ≤ RingHom.ker (e a)` using `Ideal.span_le.2 (by`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hF a i)`. Conclude with `this hs)`. Establish `heb : ∀ a s, eb a (Ideal.Quotient.mk I s) = e a s` using `fun a s => rfl`. Set `φ : (S ⧸ I) →ₗ[O] (Ix → O)` to `LinearMap.pi fun a => (eb a).toLinearMap`.

Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hker s fun a => congrFun hy a)`.

Take `⟨b, hb⟩` from `exists_basis_det_ne_zero_of_points φ hφ c hc fun t => by`. Take `⟨G, hG⟩` from `hs t`. Conclude with `⟨Ideal.Quotient.mk I G, funext hG⟩`. Use `choose β hβ using fun a => Ideal.Quotient.mk_surjective (b a)`. Establish `hM : (Matrix.of fun a a' => e a (β a')) = Matrix.of fun a a' => eb a (b a')`.

Use extensionality with `a a'`. Rewrite using `[Matrix.of_apply, Matrix.of_apply, ← hβ, heb]`. Establish `hb' : (Matrix.of fun a a' => eb a (b a')).det ≠ 0` using `hb`. Establish `hq : ∀ (G : S) (r : Ix → O), G - ∑ a, r a • β a ∈ I ↔ Ideal.Quotient.mk I G = ∑ a, r a • b a`. Introduce `G r`.

Rewrite using `[← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk O, map_sum]`. Simplify using `only [map_smul, Ideal.Quotient.mkₐ_eq_mk, hβ]`. Use `⟨β, fun G => ⟨b.equivFun (Ideal.Quotient.mk I G), ?_, fun r hr => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hq G _).2 (b.sum_equivFun _).symm`. Rewrite using `[(hq G r).1 hr, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[hM]`. Conclude with `hb'`. Break down `isEmpty_or_nonempty Ix with h | ⟨⟨a⟩⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hf : ∀ i, MvPowerSeries.constantCoeff (F i) ∈ IsLocalRing.maximalIdeal O`.

Introduce `i`. Take `⟨u, hu⟩` from `GlobalTheory.DiscrJacobian.exists_eq_C_add_sum (F i)`. Establish `h1` using `congrArg (e a) hu`. Establish `h2 : e a (MvPowerSeries.C (MvPowerSeries.constantCoeff (F i))) = MvPowerSeries.constantCoeff (F i)` using `(e a).commutes _`. Rewrite `h1` using `[hF, map_add, h2, map_sum]`.

Rewrite using `[eq_neg_of_add_eq_zero_left h1.symm]`. Use `neg_mem (Ideal.sum_mem _ fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_right _ _ (hX a j)`. Establish `h1` using `GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian O g _ F (b.reindex (Fintype.equivFin Ix)) hf`.

Take `⟨h2, h3⟩` from `discr_norm_eq_of_points O (S ⧸ I) Ix b eb hb'`. Rewrite `h1` using `[Module.Basis.coe_reindex, Algebra.discr_reindex, h2, h3]`. Rewrite using `[hM]`. Conclude with `h1`.
-/
theorem discr_jacobian_of_points :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix]
      [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O))
      (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) →
      (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) →
      (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) →
      (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) →
      ∃ β : Ix → (MvPowerSeries (Fin g) O),
        (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧
        (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧
        Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2)
          (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by
  intro O _ _ _ _ g Ix _ _ F e hF hX hker ⟨c, hc, hs⟩
  let S := MvPowerSeries (Fin g) O
  let I : Ideal S := Ideal.span (Set.range F)
  let eb : Ix → ((S ⧸ I) →ₐ[O] O) := fun a => Ideal.Quotient.liftₐ I (e a) (fun s hs => by
    have : I ≤ RingHom.ker (e a) := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hF a i)
    exact this hs)
  have heb : ∀ a s, eb a (Ideal.Quotient.mk I s) = e a s := fun a s => rfl
  let φ : (S ⧸ I) →ₗ[O] (Ix → O) := LinearMap.pi fun a => (eb a).toLinearMap
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker s fun a => congrFun hy a)
  obtain ⟨b, hb⟩ := exists_basis_det_ne_zero_of_points φ hφ c hc fun t => by
    obtain ⟨G, hG⟩ := hs t
    exact ⟨Ideal.Quotient.mk I G, funext hG⟩
  choose β hβ using fun a => Ideal.Quotient.mk_surjective (b a)
  have hM : (Matrix.of fun a a' => e a (β a')) = Matrix.of fun a a' => eb a (b a') := by
    ext a a'
    rw [Matrix.of_apply, Matrix.of_apply, ← hβ, heb]
  have hb' : (Matrix.of fun a a' => eb a (b a')).det ≠ 0 := hb
  have hq : ∀ (G : S) (r : Ix → O), G - ∑ a, r a • β a ∈ I ↔
      Ideal.Quotient.mk I G = ∑ a, r a • b a := by
    intro G r
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk O, map_sum]
    simp only [map_smul, Ideal.Quotient.mkₐ_eq_mk, hβ]
  refine ⟨β, fun G => ⟨b.equivFun (Ideal.Quotient.mk I G), ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · exact (hq G _).2 (b.sum_equivFun _).symm
  · rw [(hq G r).1 hr, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  · rw [hM]; exact hb'
  · rcases isEmpty_or_nonempty Ix with h | ⟨⟨a⟩⟩
    · simp
    · have hf : ∀ i, MvPowerSeries.constantCoeff (F i) ∈ IsLocalRing.maximalIdeal O := by
        intro i
        obtain ⟨u, hu⟩ := GlobalTheory.DiscrJacobian.exists_eq_C_add_sum (F i)
        have h1 := congrArg (e a) hu
        have h2 : e a (MvPowerSeries.C (MvPowerSeries.constantCoeff (F i)))
            = MvPowerSeries.constantCoeff (F i) := (e a).commutes _
        rw [hF, map_add, h2, map_sum] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        refine neg_mem (Ideal.sum_mem _ fun j _ => ?_)
        rw [map_mul]
        exact Ideal.mul_mem_right _ _ (hX a j)
      have h1 := GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian O g _ F
        (b.reindex (Fintype.equivFin Ix)) hf
      obtain ⟨h2, h3⟩ := discr_norm_eq_of_points O (S ⧸ I) Ix b eb hb'
      rw [Module.Basis.coe_reindex, Algebra.discr_reindex, h2, h3] at h1
      rw [hM]
      exact h1

end GlobalTheory.KeyKa
