import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeOfPowFinrankCyclic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OfIntermediateFieldTower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangePropertiesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
/- English proof (translation)
Rewrite using `[← IsCyclic.image_range_orderOf hg, Finset.prod_image]`. Introduce `i hi j hj hij`. Conclude with `pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij`.
-/
private theorem prod_univ_eq_prod_range_orderOf_of_generator {G β : Type} [Group G] [Fintype G] [CommMonoid β]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : G → β) :
    ∏ σ, f σ = ∏ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, Finset.prod_image]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add, map_prod]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← AlgEquiv.mul_apply, ← pow_mul, ← pow_add]`.
-/
private theorem prod_range_pow_pow_prod_range_eq_prod_range_mul {F E : Type} [Field F] [Field E] [Algebra F E]
    (τ : E ≃ₐ[F] E) (y : E) (d n : ℕ) :
    ∏ j ∈ Finset.range n, ((τ ^ d) ^ j) (∏ i ∈ Finset.range d, (τ ^ i) y) =
      ∏ m ∈ Finset.range (d * n), (τ ^ m) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
/- English proof (translation)
Use `haveI : FiniteDimensional M E := FiniteDimensional.right F M E`. Use `haveI : FiniteDimensional F M := FiniteDimensional.left F M E`. Use `haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E`. Use `set n := Module.finrank M E with hn`. Use `set d := Module.finrank F M with hd`.

Establish `hdn : d * n = Module.finrank F E` using `Module.finrank_mul_finrank F M E`. Establish `hn0 : 0 < n` using `Module.finrank_pos`. Establish `hd0 : 0 < d` using `Module.finrank_pos`. Take `⟨τ, hτ⟩` from `hcyc.exists_generator`. Establish `hcomm : ∀ a b : E ≃ₐ[F] E, a * b = b * a`.

Introduce `a b`. Take `⟨i, rfl⟩` from `Subgroup.mem_zpowers_iff.mp (hτ a)`. Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.mp (hτ b)`. Conclude with `((Commute.refl τ).zpow_zpow i j).eq`. Set `ρ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E)` to `{ toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }`.

Establish `hρ : Function.Injective ρ` using `AlgEquiv.restrictScalars_injective F`. Establish `hρapp : ∀ (h : E ≃ₐ[M] E) (y : E), ρ h y = h y` using `fun _ _ => rfl`. Set `K` to `ρ.range`. Use `haveI : K.Normal := ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩`. Establish `hcardK : Nat.card K = n`.

Rewrite using `[← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, IsGalois.card_aut_eq_finrank]`. Establish `hcardG : Nat.card (E ≃ₐ[F] E) = d * n` using `by rw [IsGalois.card_aut_eq_finrank, hdn]`. Establish `hindex : K.index = d`. Establish `h` using `K.index_mul_card`. Rewrite `h` using `[hcardK, hcardG]`.

Conclude with `Nat.eq_of_mul_eq_mul_right hn0 h`. Establish `hτd : τ ^ d ∈ K` using `hindex ▸ K.pow_index_mem τ`. Take `⟨g, hg⟩` from `hτd`. Establish `hordτ : orderOf τ = d * n` using `by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hcardG]`. Establish `hordτd : orderOf (τ ^ d) = n`.

Rewrite using `[orderOf_pow' τ hd0.ne', hordτ, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd0]`. Establish `hKz : Subgroup.zpowers (τ ^ d) = K`. Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Rewrite using `[Subgroup.zpowers_le, ← hg]`. Conclude with `⟨g, rfl⟩`.

Rewrite using `[hcardK, Nat.card_zpowers, hordτd]`. Establish `hgen : ∀ h : E ≃ₐ[M] E, h ∈ Subgroup.zpowers g`. Introduce `h`. Establish `hmem : ρ h ∈ Subgroup.zpowers (τ ^ d)` using `hKz ▸ ⟨h, rfl⟩`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.mp hmem`.

Use `Subgroup.mem_zpowers_iff.mpr ⟨k, hρ ?_⟩` and prove the remaining obligations. Rewrite using `[map_zpow, hg, hk]`. Use `haveI : IsCyclic (E ≃ₐ[M] E) := ⟨⟨g, hgen⟩⟩`. Establish `hordg : orderOf g = n`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]`.

Establish `hnormτ : ∀ y : E, algebraMap M E (Algebra.norm M (τ y)) = τ (algebraMap M E (Algebra.norm M y))`. Introduce `y`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]`. Use `Finset.prod_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← hρapp σ, ← hρapp σ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]`.

Establish `he₀0 : e₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx ((algebraMap F M).injective (by rw [← he₀, Algebra.norm_zero, map_zero]))`. Establish `hxE : algebraMap M E (Algebra.norm M e₀) = algebraMap F E x`. Rewrite using `[he₀, ← IsScalarTower.algebraMap_apply]`.

Establish `hN0 : Algebra.norm M e₀ ≠ 0` using `by rw [he₀]; exact (_root_.map_ne_zero _).mpr hx`. Establish `hu : Algebra.norm M (τ e₀ / e₀) = 1`. Establish `h1 : Algebra.norm M (τ e₀ / e₀) * Algebra.norm M e₀ = Algebra.norm M (τ e₀)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ he₀0]`. Establish `h2 : algebraMap M E (Algebra.norm M (τ e₀)) = algebraMap M E (Algebra.norm M e₀)`.

Rewrite using `[hnormτ, hxE, AlgEquiv.commutes]`. Rewrite `h1` using `[(algebraMap M E).injective h2]`. Conclude with `mul_right_cancel₀ hN0 (h1.trans (one_mul _).symm)`. Take `⟨c, hc⟩` from `groupCohomology.exists_div_of_norm_eq_one hgen hu`. Establish `hgc : g (c : E) = (τ ^ d) (c : E)` using `by rw [← hρapp, hg]`.

Establish `hc0 : (c : E) ≠ 0` using `c.ne_zero`. Establish `hτdc0 : (τ ^ d) (c : E) ≠ 0`. Rewrite using `[← hgc]`. Conclude with `(_root_.map_ne_zero _).mpr hc0`. Use `set P := ∏ i ∈ Finset.range d, (τ ^ i) (c : E) with hPdef`.

Establish `hτP : τ P * c = P * (τ ^ d) (c : E)`. Establish `hs : τ P = ∏ i ∈ Finset.range d, (τ ^ (i + 1)) (c : E)`. Rewrite using `[hPdef, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`.

Rewrite using `[hs]`. Establish `h` using `Finset.prod_range_succ' (fun i => (τ ^ i) (c : E)) d`. Rewrite `h` using `[Finset.prod_range_succ]`. Simplify using `only [pow_zero, AlgEquiv.one_apply] at h`. Conclude with `h.symm`.

Establish `hτe₀ : τ e₀ * (τ ^ d) (c : E) = e₀ * c`. Rewrite using `[← hgc]`. Establish `h` using `hc`. Rewrite `h` using `[div_eq_div_iff ((_root_.map_ne_zero _).mpr hc0) he₀0]`. Take the linear combination `-h`.

Establish `hfix : τ (e₀ * P) = e₀ * P`. Rewrite using `[map_mul]`. Apply `mul_right_cancel₀ (mul_ne_zero hτdc0 hc0)` to reduce the goal to its premises. Take the linear combination `(τ P * c) * hτe₀ + (e₀ * c) * hτP`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b : F, algebraMap F E b = e₀ * P := by`.

Establish `hall : ∀ σ : E ≃ₐ[F] E, σ (e₀ * P) = e₀ * P`. Introduce `σ`. Establish `hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) (e₀ * P)` using `hfix`. Conclude with `(Subgroup.zpowers_le.mpr hst) (hτ σ)`. Conclude with `IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hall)`.

Establish `hnormP : algebraMap M E (Algebra.norm M P) = algebraMap M E (algebraMap F M (Algebra.norm F (c : E)))`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hgen, hordg, ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hτ, hordτ, ← prod_range_pow_pow_prod_range_eq_prod_range_mul]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hρapp, map_pow, hg]`. Establish `hbn : algebraMap F M (b ^ n) = algebraMap F M (x * Algebra.norm F (c : E))`.

Establish `h` using `congrArg (Algebra.norm M) hb`. Rewrite `h` using `[IsScalarTower.algebraMap_apply F M E, Algebra.norm_algebraMap, map_mul, he₀, (algebraMap M E).injective hnormP]`. Rewrite using `[map_pow, map_mul, h]`. Establish `hNc : Algebra.norm F (c : E) ≠ 0` using `(c.isUnit.map (Algebra.norm F)).ne_zero`. Use `⟨b, ((c⁻¹ : Eˣ) : E), Units.ne_zero _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_units_inv (Algebra.norm F) c, (algebraMap F M).injective hbn, mul_inv_cancel_right₀ hNc]`.
-/
private theorem exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic (F M E : Type) [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E]
    [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) (x : F) (hx : x ≠ 0) (e₀ : E)
    (he₀ : Algebra.norm M e₀ = algebraMap F M x) :
    ∃ b : F, ∃ c : E, c ≠ 0 ∧ x = b ^ Module.finrank M E * Algebra.norm F c := by
  classical
  haveI : FiniteDimensional M E := FiniteDimensional.right F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  set n := Module.finrank M E with hn
  set d := Module.finrank F M with hd
  have hdn : d * n = Module.finrank F E := Module.finrank_mul_finrank F M E
  have hn0 : 0 < n := Module.finrank_pos
  have hd0 : 0 < d := Module.finrank_pos
  obtain ⟨τ, hτ⟩ := hcyc.exists_generator
  have hcomm : ∀ a b : E ≃ₐ[F] E, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ b)
    exact ((Commute.refl τ).zpow_zpow i j).eq
  let ρ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := AlgEquiv.restrictScalars_injective F
  have hρapp : ∀ (h : E ≃ₐ[M] E) (y : E), ρ h y = h y := fun _ _ => rfl
  let K := ρ.range
  haveI : K.Normal := ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  have hcardK : Nat.card K = n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcardG : Nat.card (E ≃ₐ[F] E) = d * n := by rw [IsGalois.card_aut_eq_finrank, hdn]
  have hindex : K.index = d := by
    have h := K.index_mul_card
    rw [hcardK, hcardG] at h
    exact Nat.eq_of_mul_eq_mul_right hn0 h
  have hτd : τ ^ d ∈ K := hindex ▸ K.pow_index_mem τ
  obtain ⟨g, hg⟩ := hτd
  have hordτ : orderOf τ = d * n := by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hcardG]
  have hordτd : orderOf (τ ^ d) = n := by
    rw [orderOf_pow' τ hd0.ne', hordτ, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd0]
  have hKz : Subgroup.zpowers (τ ^ d) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, ← hg]
      exact ⟨g, rfl⟩
    · rw [hcardK, Nat.card_zpowers, hordτd]
  have hgen : ∀ h : E ≃ₐ[M] E, h ∈ Subgroup.zpowers g := by
    intro h
    have hmem : ρ h ∈ Subgroup.zpowers (τ ^ d) := hKz ▸ ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hρ ?_⟩
    rw [map_zpow, hg, hk]
  haveI : IsCyclic (E ≃ₐ[M] E) := ⟨⟨g, hgen⟩⟩
  have hordg : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

  have hnormτ : ∀ y : E, algebraMap M E (Algebra.norm M (τ y)) =
      τ (algebraMap M E (Algebra.norm M y)) := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [← hρapp σ, ← hρapp σ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    exact hx ((algebraMap F M).injective (by rw [← he₀, Algebra.norm_zero, map_zero]))
  have hxE : algebraMap M E (Algebra.norm M e₀) = algebraMap F E x := by
    rw [he₀, ← IsScalarTower.algebraMap_apply]
  have hN0 : Algebra.norm M e₀ ≠ 0 := by rw [he₀]; exact (_root_.map_ne_zero _).mpr hx
  have hu : Algebra.norm M (τ e₀ / e₀) = 1 := by
    have h1 : Algebra.norm M (τ e₀ / e₀) * Algebra.norm M e₀ = Algebra.norm M (τ e₀) := by
      rw [← map_mul, div_mul_cancel₀ _ he₀0]
    have h2 : algebraMap M E (Algebra.norm M (τ e₀)) = algebraMap M E (Algebra.norm M e₀) := by
      rw [hnormτ, hxE, AlgEquiv.commutes]
    rw [(algebraMap M E).injective h2] at h1
    exact mul_right_cancel₀ hN0 (h1.trans (one_mul _).symm)
  obtain ⟨c, hc⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hu
  have hgc : g (c : E) = (τ ^ d) (c : E) := by rw [← hρapp, hg]
  have hc0 : (c : E) ≠ 0 := c.ne_zero
  have hτdc0 : (τ ^ d) (c : E) ≠ 0 := by
    rw [← hgc]; exact (_root_.map_ne_zero _).mpr hc0
  set P := ∏ i ∈ Finset.range d, (τ ^ i) (c : E) with hPdef
  have hτP : τ P * c = P * (τ ^ d) (c : E) := by
    have hs : τ P = ∏ i ∈ Finset.range d, (τ ^ (i + 1)) (c : E) := by
      rw [hPdef, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [hs]
    have h := Finset.prod_range_succ' (fun i => (τ ^ i) (c : E)) d
    rw [Finset.prod_range_succ] at h
    simp only [pow_zero, AlgEquiv.one_apply] at h
    exact h.symm
  have hτe₀ : τ e₀ * (τ ^ d) (c : E) = e₀ * c := by
    rw [← hgc]
    have h := hc
    rw [div_eq_div_iff ((_root_.map_ne_zero _).mpr hc0) he₀0] at h
    linear_combination -h
  have hfix : τ (e₀ * P) = e₀ * P := by
    rw [map_mul]
    apply mul_right_cancel₀ (mul_ne_zero hτdc0 hc0)
    linear_combination (τ P * c) * hτe₀ + (e₀ * c) * hτP
  obtain ⟨b, hb⟩ : ∃ b : F, algebraMap F E b = e₀ * P := by
    have hall : ∀ σ : E ≃ₐ[F] E, σ (e₀ * P) = e₀ * P := by
      intro σ
      have hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) (e₀ * P) := hfix
      exact (Subgroup.zpowers_le.mpr hst) (hτ σ)
    exact IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hall)
  have hnormP : algebraMap M E (Algebra.norm M P) =
      algebraMap M E (algebraMap F M (Algebra.norm F (c : E))) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hgen, hordg,
      ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_automorphisms,
      prod_univ_eq_prod_range_orderOf_of_generator hτ, hordτ, ← prod_range_pow_pow_prod_range_eq_prod_range_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hρapp, map_pow, hg]
  have hbn : algebraMap F M (b ^ n) = algebraMap F M (x * Algebra.norm F (c : E)) := by
    have h := congrArg (Algebra.norm M) hb
    rw [IsScalarTower.algebraMap_apply F M E, Algebra.norm_algebraMap, map_mul, he₀,
      (algebraMap M E).injective hnormP] at h
    rw [map_pow, map_mul, h]
  have hNc : Algebra.norm F (c : E) ≠ 0 := (c.isUnit.map (Algebra.norm F)).ne_zero
  refine ⟨b, ((c⁻¹ : Eˣ) : E), Units.ne_zero _, ?_⟩
  rw [map_units_inv (Algebra.norm F) c, (algebraMap F M).injective hbn, mul_inv_cancel_right₀ hNc]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

/- English proof (translation)
Introduce `F M E _ _ _ _ _ _ _ _ _ _ _ hcyc hME hMF x hx0 hloc`. Use `haveI : FiniteDimensional F E := inferInstance`. Use `haveI : FiniteDimensional F M := inferInstance`. Use `haveI : FiniteDimensional M E := inferInstance`. Use `haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E`.

Establish `hprops` using `_root_.GlobalTheory.CNorm.tnorm_baseChange F E`. Establish `hxM : algebraMap F M x ≠ 0` using `(_root_.map_ne_zero _).mpr hx0`. Establish `h1 : _root_.GlobalTheory.CNorm.LocNorm M E (algebraMap F M x)`. Use `⟨fun w => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `_root_.GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F M w`.

Use `letI : Algebra F (w.adicCompletion M) := ((algebraMap M (w.adicCompletion M)).comp (algebraMap F M)).toAlgebra`. Use `haveI : IsScalarTower F M (w.adicCompletion M) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `ψ : (HeightOneSpectrum.under (𝓞 F) w).adicCompletion F →ₐ[F] w.adicCompletion M` to `{ φ with commutes' := fun r => (hφ r).trans rfl }`. Conclude with `_root_.GlobalTheory.CNorm.TNorm.of_tower F M E _ x (hprops.1 _ _ ψ x (hloc.1 _))`. Use `letI : Algebra F ℝ := ((algebraMap M ℝ).comp (algebraMap F M)).toAlgebra haveI : IsScalarTower F M ℝ := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Conclude with `_root_.GlobalTheory.CNorm.TNorm.of_tower F M E ℝ x (hloc.2 _)`. Take `⟨e₀, he₀⟩` from `hME _ hxM h1`. Take `⟨b, c, hc0, hxb⟩` from `exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic F M E hcyc x hx0 e₀ he₀`. Establish `hNc : Algebra.norm F c ≠ 0`. Introduce `h`.

Conclude with `hx0 (by rw [hxb, h, mul_zero])`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx0 (by rw [hxb, zero_pow Module.finrank_pos.ne', zero_mul])`. Establish `hpow : ∀ (K : Type) [Field K] [Algebra F K], _root_.GlobalTheory.CNorm.TNorm F E K x → _root_.GlobalTheory.CNorm.TNorm F M K b`.

Introduce `K _ _ hK`. Use `_root_.GlobalTheory.CNorm.tnorm_of_tnorm_pow F M E K hcyc b hb0 ?_` and prove the remaining obligations. Conclude with `hprops.2.2 K _ _ hNc (hxb ▸ hK) (hprops.2.1 K c)`. Take `⟨m, hm⟩` from `hMF b hb0 ⟨fun v => hpow _ (hloc.1 v), fun a => hpow ℝ (hloc.2 a)⟩`. Use `⟨algebraMap M E m * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hxb, ← Algebra.norm_norm (S := M), Algebra.norm_algebraMap, map_pow, hm]`.
-/
theorem _root_.GlobalTheory.CNorm.np_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → _root_.GlobalTheory.CNorm.NP M E → _root_.GlobalTheory.CNorm.NP F M → _root_.GlobalTheory.CNorm.NP F E := by
  intro F M E _ _ _ _ _ _ _ _ _ _ _ hcyc hME hMF x hx0 hloc
  haveI : FiniteDimensional F E := inferInstance
  haveI : FiniteDimensional F M := inferInstance
  haveI : FiniteDimensional M E := inferInstance
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hprops := _root_.GlobalTheory.CNorm.tnorm_baseChange F E
  have hxM : algebraMap F M x ≠ 0 := (_root_.map_ne_zero _).mpr hx0
  have h1 : _root_.GlobalTheory.CNorm.LocNorm M E (algebraMap F M x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F M w
      letI : Algebra F (w.adicCompletion M) :=
        ((algebraMap M (w.adicCompletion M)).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M (w.adicCompletion M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let ψ : (HeightOneSpectrum.under (𝓞 F) w).adicCompletion F →ₐ[F] w.adicCompletion M :=
        { φ with commutes' := fun r => (hφ r).trans rfl }
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E _ x
        (hprops.1 _ _ ψ x (hloc.1 _))
    · letI : Algebra F ℝ := ((algebraMap M ℝ).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M ℝ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E ℝ x (hloc.2 _)
  obtain ⟨e₀, he₀⟩ := hME _ hxM h1
  obtain ⟨b, c, hc0, hxb⟩ := exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic F M E hcyc x hx0 e₀ he₀
  have hNc : Algebra.norm F c ≠ 0 := by
    intro h
    exact hx0 (by rw [hxb, h, mul_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxb, zero_pow Module.finrank_pos.ne', zero_mul])
  have hpow : ∀ (K : Type) [Field K] [Algebra F K], _root_.GlobalTheory.CNorm.TNorm F E K x →
      _root_.GlobalTheory.CNorm.TNorm F M K b := by
    intro K _ _ hK
    refine _root_.GlobalTheory.CNorm.tnorm_of_tnorm_pow F M E K hcyc b hb0 ?_
    exact hprops.2.2 K _ _ hNc (hxb ▸ hK) (hprops.2.1 K c)
  obtain ⟨m, hm⟩ := hMF b hb0 ⟨fun v => hpow _ (hloc.1 v), fun a => hpow ℝ (hloc.2 a)⟩
  refine ⟨algebraMap M E m * c, ?_⟩
  rw [map_mul, hxb, ← Algebra.norm_norm (S := M), Algebra.norm_algebraMap, map_pow, hm]

end GlobalTheory.CNorm
