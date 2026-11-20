import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Introduce `O _ _ _ n _ _ e he hr`. Use `set eK := e.map (algebraMap O (FractionRing O)) with heK`. Establish `hidK : eK * eK = eK`. Rewrite using `[heK, ← Matrix.map_mul, he]`. Establish `hsub : (LinearMap.range (Matrix.toLin' eK)).subtype.comp (Matrix.toLin' eK).rangeRestrict = Matrix.toLin' eK` using `LinearMap.ext fun v => rfl`.

Establish `hid : (Matrix.toLin' eK).rangeRestrict.comp (LinearMap.range (Matrix.toLin' eK)).subtype = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨v, w, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Matrix.toLin' eK (Matrix.toLin' eK w) = Matrix.toLin' eK w`.

Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidK]`. Establish `hfr : Module.finrank (FractionRing O) (LinearMap.range (Matrix.toLin' eK)) = 1`. Rewrite using `[← hr]`. Both sides reduce to the same expression. Take `⟨b⟩ : Nonempty (Module.Basis (Fin 1) (FractionRing O) (LinearMap.range (Matrix.toLin' eK)))` from `⟨Module.finBasisOfFinrankEq _ _ hfr⟩`.

Take `⟨U, W, hUW, hWU⟩ : ∃ (U : Matrix n (Fin 1) (FractionRing O)) (W : Matrix (Fin 1) n (FractionRing O)), U * W = eK ∧ W * U = 1` from `⟨LinearMap.toMatrix b (Pi.basisFun _ n) (LinearMap.range (Matrix.toLin' eK)).subtype, LinearMap.toMatrix (Pi.basisFun _ n) b (Matrix.toLin' eK).rangeRestrict, by rw [← LinearMap.toMatrix_comp, hsub, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'], by rw [← LinearMap. …`. Establish `hfact : ∀ i j, eK i j = U i 0 * W 0 j`. Introduce `i j`. Rewrite using `[← hUW, Matrix.mul_apply, Fin.sum_univ_one]`. Establish `hsum : ∑ i, W 0 i * U i 0 = 1`.

Establish `h` using `congrFun (congrFun hWU 0) 0`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Then use the resulting hypothesis. Establish `inj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O _`. Establish `hmap : ∀ i j, algebraMap O (FractionRing O) (e i j) = eK i j` using `fun i j => rfl`. Establish `htr : ∑ i, e i i = 1`.

Apply `inj` to reduce the goal to its premises. Rewrite using `[map_sum, map_one]`. Simplify using `only [hmap, hfact]`. Rewrite using `[← hsum]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0, IsUnit (e i0 i0) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hmem : ∑ i, e i i ∈ IsLocalRing.maximalIdeal O` using `Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hcon i))`. Rewrite `hmem` using `[htr]`.

Conclude with `mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) isUnit_one`. Establish `hminor : ∀ i j k l, e i j * e k l = e i l * e k j`. Introduce `i j k l`. Apply `inj` to reduce the goal to its premises. Simplify using `only [map_mul, hmap, hfact]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `hi0`. Establish `hfe : ∀ i j, e i j = e i i0 * (↑c⁻¹ * e i0 j)`. Introduce `i j`. Establish `h` using `hminor i j i0 i0`.

Rewrite `h` using `[← hc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hφu : ∑ j, ↑c⁻¹ * e i0 j * e j i0 = 1`. Establish `h` using `congrFun (congrFun he i0) i0`. Rewrite `h` using `[Matrix.mul_apply, ← hc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Simplify using `only [mul_assoc]`. Use `_ = 1 := by rw [h, Units.inv_mul]`. Set `ψ : KO O →ₗ[O] (n → KO O)` to `LinearMap.pi fun i => e i i0 • LinearMap.id`.

Set `χ : (n → KO O) →ₗ[O] KO O` to `∑ j, (↑c⁻¹ * e i0 j) • LinearMap.proj j`. Establish `hχψ : ∀ m, χ (ψ m) = m`. Introduce `m`. Simplify using `only [χ, ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply, smul_smul]`. Rewrite using `[← Finset.sum_smul, hφu, one_smul]`.

Establish `hmat : matEnd O (KO O) n e = ψ.comp χ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use function extensionality and compare the values at `i`. Use `show ∑ j, e i j • v j = _`.

Simplify using `only [χ, ψ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.proj_apply, Finset.smul_sum, smul_smul]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hfe i j]`. Establish `hinj : Function.Injective ψ` using `fun a b h => by rw [← hχψ a, ← hχψ b, h]`. Establish `hχ : LinearMap.range χ = ⊤` using `LinearMap.range_eq_top.2 fun m => ⟨ψ m, hχψ m⟩`. Conclude with `⟨(LinearEquiv.ofEq _ _ (by rw [hmat, LinearMap.range_comp_of_range_eq_top ψ hχ])).trans (LinearEquiv.ofInjective ψ hinj).symm⟩`.
-/
theorem idemKO : StatIdemKO := by
  intro O _ _ _ n _ _ e he hr
  classical
  set eK := e.map (algebraMap O (FractionRing O)) with heK
  have hidK : eK * eK = eK := by
    rw [heK, ← Matrix.map_mul, he]
  have hsub : (LinearMap.range (Matrix.toLin' eK)).subtype.comp (Matrix.toLin' eK).rangeRestrict =
      Matrix.toLin' eK := LinearMap.ext fun v => rfl
  have hid : (Matrix.toLin' eK).rangeRestrict.comp (LinearMap.range (Matrix.toLin' eK)).subtype =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show Matrix.toLin' eK (Matrix.toLin' eK w) = Matrix.toLin' eK w
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidK]
  have hfr : Module.finrank (FractionRing O) (LinearMap.range (Matrix.toLin' eK)) = 1 := by
    rw [← hr]
    rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) (FractionRing O) (LinearMap.range (Matrix.toLin' eK))) :=
    ⟨Module.finBasisOfFinrankEq _ _ hfr⟩
  obtain ⟨U, W, hUW, hWU⟩ : ∃ (U : Matrix n (Fin 1) (FractionRing O))
      (W : Matrix (Fin 1) n (FractionRing O)), U * W = eK ∧ W * U = 1 :=
    ⟨LinearMap.toMatrix b (Pi.basisFun _ n) (LinearMap.range (Matrix.toLin' eK)).subtype,
      LinearMap.toMatrix (Pi.basisFun _ n) b (Matrix.toLin' eK).rangeRestrict,
      by rw [← LinearMap.toMatrix_comp, hsub, LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin'],
      by rw [← LinearMap.toMatrix_comp, hid, LinearMap.toMatrix_id]⟩
  have hfact : ∀ i j, eK i j = U i 0 * W 0 j := by
    intro i j
    rw [← hUW, Matrix.mul_apply, Fin.sum_univ_one]
  have hsum : ∑ i, W 0 i * U i 0 = 1 := by
    have h := congrFun (congrFun hWU 0) 0
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have inj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hmap : ∀ i j, algebraMap O (FractionRing O) (e i j) = eK i j := fun i j => rfl
  have htr : ∑ i, e i i = 1 := by
    apply inj
    rw [map_sum, map_one]
    simp only [hmap, hfact]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨i0, hi0⟩ : ∃ i0, IsUnit (e i0 i0) := by
    by_contra hcon
    push_neg at hcon
    have hmem : ∑ i, e i i ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hcon i))
    rw [htr] at hmem
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) isUnit_one
  have hminor : ∀ i j k l, e i j * e k l = e i l * e k j := by
    intro i j k l
    apply inj
    simp only [map_mul, hmap, hfact]
    ring
  obtain ⟨c, hc⟩ := hi0
  have hfe : ∀ i j, e i j = e i i0 * (↑c⁻¹ * e i0 j) := by
    intro i j
    have h := hminor i j i0 i0
    rw [← hc] at h
    calc e i j = e i j * ↑c * ↑c⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h]; ring
  have hφu : ∑ j, ↑c⁻¹ * e i0 j * e j i0 = 1 := by
    have h := congrFun (congrFun he i0) i0
    rw [Matrix.mul_apply, ← hc] at h
    calc ∑ j, ↑c⁻¹ * e i0 j * e j i0 = ↑c⁻¹ * ∑ j, e i0 j * e j i0 := by
          rw [Finset.mul_sum]
          simp only [mul_assoc]
      _ = 1 := by rw [h, Units.inv_mul]
  let ψ : KO O →ₗ[O] (n → KO O) := LinearMap.pi fun i => e i i0 • LinearMap.id
  let χ : (n → KO O) →ₗ[O] KO O := ∑ j, (↑c⁻¹ * e i0 j) • LinearMap.proj j
  have hχψ : ∀ m, χ (ψ m) = m := by
    intro m
    simp only [χ, ψ, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply, smul_smul]
    rw [← Finset.sum_smul, hφu, one_smul]
  have hmat : matEnd O (KO O) n e = ψ.comp χ := by
    apply LinearMap.ext
    intro v
    funext i
    show ∑ j, e i j • v j = _
    simp only [χ, ψ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.sum_apply, LinearMap.proj_apply,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hfe i j]
  have hinj : Function.Injective ψ := fun a b h => by rw [← hχψ a, ← hχψ b, h]
  have hχ : LinearMap.range χ = ⊤ := LinearMap.range_eq_top.2 fun m => ⟨ψ m, hχψ m⟩
  exact ⟨(LinearEquiv.ofEq _ _ (by rw [hmat, LinearMap.range_comp_of_range_eq_top ψ hχ])).trans
    (LinearEquiv.ofInjective ψ hinj).symm⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
