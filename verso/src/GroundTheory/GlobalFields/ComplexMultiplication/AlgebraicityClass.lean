import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Algebraicity

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Rewrite using `[Set.image_image]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem image_mul_image_mul (c d : ℂ) (S : Set ℂ) :
    (c * ·) '' ((d * ·) '' S) = ((c * d) * ·) '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  ring

/- English proof (translation)
Rewrite using `[h, image_mul_image_mul, inv_mul_cancel₀ hc]`. Simplify using `only [one_mul, Set.image_id']`.
-/
theorem eq_image_mul_inv {c : ℂ} (hc : c ≠ 0) {A B : Set ℂ} (h : B = (c * ·) '' A) :
    A = (c⁻¹ * ·) '' B := by
  rw [h, image_mul_image_mul, inv_mul_cancel₀ hc]
  simp only [one_mul, Set.image_id']

/- English proof (translation)
Rewrite using `[Set.image_image, Set.image_image]`. Simplify using `only [map_mul]`.
-/
theorem image_ringEquiv_image_mul (σ : ℂ ≃+* ℂ) (c : ℂ) (S : Set ℂ) :
    σ '' ((c * ·) '' S) = (σ c * ·) '' (σ '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [map_mul]

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, (hσ x).symm⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨σ₀ x, ⟨x, hx, rfl⟩, hσ x⟩`.
-/
theorem image_idealLattice (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    σ '' (idealLattice σ₀ I : Set ℂ) = idealLattice σ₀ I := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hσ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ₀ x, ⟨x, hx, rfl⟩, hσ x⟩

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

/- English proof (translation)
Take `⟨I, c, hc, hI⟩` from `exists_idealLattice_of_latticeEnd_eq σ₀ hK L hL`. Establish `hI'` using `idealLattice_mul_homothetic σ₀ (I : FractionalIdeal (𝓞 K)⁰ K) ↑𝔟 hI`. Rewrite `hI'` using `[← h]`. Establish `hmem' : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I), c * σ₀ x = z`. Introduce `z`.

Rewrite using `[← SetLike.mem_coe, hI']`. Simplify using `only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨σ₀ x, ⟨x, hx, rfl⟩, rfl⟩`. Establish `hmemL : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), c * σ₀ x ∈ L.lattice`. Introduce `x hx`. Rewrite using `[← SetLike.mem_coe, hI]`.

Conclude with `⟨σ₀ x, (mem_idealLattice σ₀).2 ⟨x, hx, rfl⟩, rfl⟩`. Use extensionality with `α`. Simplify using `only [SetLike.mem_coe, mem_latticeHom]`. Prove the components needed by the constructor for the conclusion. Introduce `hα`.

Establish `hI0 : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥`. Rewrite using `[Ne, FractionalIdeal.coeToSubmodule_eq_bot]`. Conclude with `I.ne_zero`. Take `⟨i₀, hi₀, hi₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI0`. Take `⟨k₀, -, hk₀⟩` from `(hmem' _).1 (hα _ (hmemL i₀ hi₀))`.

Establish `hσi₀ : σ₀ i₀ ≠ 0` using `(map_ne_zero σ₀).2 hi₀0`. Establish `hy : σ₀ (k₀ / i₀) = α`. Rewrite using `[map_div₀, div_eq_iff hσi₀]`. Conclude with `mul_left_cancel₀ hc (by rw [hk₀]; ring)`. Use `set y := k₀ / i₀`.

Establish `hyI : ∀ i ∈ (I : FractionalIdeal (𝓞 K)⁰ K), y * i ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I`. Introduce `i hi`. Take `⟨k, hk, hke⟩` from `(hmem' _).1 (hα _ (hmemL i hi))`. Establish `: σ₀ k = σ₀ (y * i)`. Rewrite using `[map_mul, hy]`.

Conclude with `mul_left_cancel₀ hc (by rw [hke]; ring)`. Rewrite using `[← σ₀.injective this]` and apply the resulting hypothesis. Establish `hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (I : FractionalIdeal (𝓞 K)⁰ K) ≤ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `a ha b hb`.

Take `⟨r, rfl⟩` from `(FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 ha`. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r (hyI b hb)`. Establish `hle'` using `mul_le_mul_left hle ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)`. Rewrite `hle'` using `[mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, mul_one]`.

Conclude with `(mem_idealLattice σ₀).2 ⟨y, hle' (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y), hy⟩`. Introduce `hα l hl`. Rewrite using `[h]`. Conclude with `Submodule.mul_mem_mul hα hl`.
-/
theorem latticeHom_eq_idealLattice (L L' : PeriodPair) (hL : latticeEnd L = cmRing σ₀)
    (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : L'.lattice = idealLattice σ₀ ↑𝔟 * L.lattice) :
    (latticeHom L L' : Set ℂ) = idealLattice σ₀ ↑𝔟 := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ₀ hK L hL
  have hI' := idealLattice_mul_homothetic σ₀ (I : FractionalIdeal (𝓞 K)⁰ K) ↑𝔟 hI
  rw [← h] at hI'
  have hmem' : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I), c * σ₀ x = z := by
    intro z
    rw [← SetLike.mem_coe, hI']
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ₀ x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemL : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), c * σ₀ x ∈ L.lattice := by
    intro x hx
    rw [← SetLike.mem_coe, hI]
    exact ⟨σ₀ x, (mem_idealLattice σ₀).2 ⟨x, hx, rfl⟩, rfl⟩
  ext α
  simp only [SetLike.mem_coe, mem_latticeHom]
  constructor
  · intro hα
    have hI0 : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact I.ne_zero
    obtain ⟨i₀, hi₀, hi₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨k₀, -, hk₀⟩ := (hmem' _).1 (hα _ (hmemL i₀ hi₀))
    have hσi₀ : σ₀ i₀ ≠ 0 := (map_ne_zero σ₀).2 hi₀0
    have hy : σ₀ (k₀ / i₀) = α := by
      rw [map_div₀, div_eq_iff hσi₀]
      exact mul_left_cancel₀ hc (by rw [hk₀]; ring)
    set y := k₀ / i₀
    have hyI : ∀ i ∈ (I : FractionalIdeal (𝓞 K)⁰ K), y * i ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      intro i hi
      obtain ⟨k, hk, hke⟩ := (hmem' _).1 (hα _ (hmemL i hi))
      have : σ₀ k = σ₀ (y * i) := by
        rw [map_mul, hy]
        exact mul_left_cancel₀ hc (by rw [hke]; ring)
      rwa [← σ₀.injective this]
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r (hyI b hb)
    have hle' := mul_le_mul_left hle ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one,
      mul_one] at hle'
    exact (mem_idealLattice σ₀).2
      ⟨y, hle' (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y), hy⟩
  · intro hα l hl
    rw [h]
    exact Submodule.mul_mem_mul hα hl

/- English proof (translation)
Take `⟨L, C, hL, hC, hE⟩` from `E.exists_lattice σ₀ hK`. Take `⟨L', hL'lat, hL'⟩` from `exists_lattice_mul σ₀ hK L hL 𝔞`. Establish `h1` using `classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat`. Establish `h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll`. Rewrite using `[← h, ← hE]`.

Conclude with `h1`. Take `⟨C', hC'⟩` from `(CMCurve.toEll_eq_iff _ _).1 h2`. Establish `hC'' : C' • E'.curve = weierstrassCurve L'` using `hC'`. Take `⟨d, hd, hset⟩` from `homConstSet_vc C C' hC hC''`. Rewrite `hset` using `[homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat]`.

Conclude with `⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset⟩`.
-/
theorem homConstSet_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧
      (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset⟩ := homConstSet_vc C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset⟩

/- English proof (translation)
Take `⟨b, hb, -⟩` from `existsUnique_smul_eq σ₀ hK E.toEll E'.toEll`. Take `⟨J, rfl⟩` from `classGroup_mk_surjective hK b`. Take `⟨d, hd, h'⟩` from `homConstSet_of_smul σ₀ hK hb`. Establish `e : (idealLattice σ₀ ↑J⁻¹ : Set ℂ) = ((d⁻¹ * c) * ·) '' idealLattice σ₀ ↑𝔞⁻¹`. Rewrite using `[eq_image_mul_inv hd h', h, image_mul_image_mul]`.

Establish `hcls` using `(classGroup_mk_eq_iff σ₀ hK 𝔞⁻¹ J⁻¹).2 ⟨d⁻¹ * c, mul_ne_zero (inv_ne_zero hd) hc, e⟩`. Rewrite `hcls` using `[map_inv, map_inv, inv_inj]`. Rewrite using `[hcls]`. Conclude with `hb`.
-/
theorem smul_toEll_of_homConstSet {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ}
    (hc : c ≠ 0)
    (h : (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll := by
  obtain ⟨b, hb, -⟩ := existsUnique_smul_eq σ₀ hK E.toEll E'.toEll
  obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
  obtain ⟨d, hd, h'⟩ := homConstSet_of_smul σ₀ hK hb
  have e : (idealLattice σ₀ ↑J⁻¹ : Set ℂ) = ((d⁻¹ * c) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [eq_image_mul_inv hd h', h, image_mul_image_mul]
  have hcls := (classGroup_mk_eq_iff σ₀ hK 𝔞⁻¹ J⁻¹).2 ⟨d⁻¹ * c, mul_ne_zero (inv_ne_zero hd) hc, e⟩
  rw [map_inv, map_inv, inv_inj] at hcls
  rw [hcls]
  exact hb

/- English proof (translation)
Take `⟨𝔞, rfl⟩` from `classGroup_mk_surjective hK a`. Take `⟨E, rfl⟩` from `ELL.exists_eq x`. Take `⟨E', hE'⟩` from `ELL.exists_eq ((ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll)`. Rewrite using `[← hE', ELL.map_toEll, ELL.map_toEll]`. Take `⟨c, hc, h⟩` from `homConstSet_of_smul σ₀ hK hE'.symm`.

Use `(smul_toEll_of_homConstSet σ₀ hK (c := σ c) ((map_ne_zero σ).2 hc) ?_).symm` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ELL.map_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (a : ClassGroup (𝓞 K))
    (x : ELL K) :
    ELL.map σ ((ellMulAction σ₀ hK).smul a x) = (ellMulAction σ₀ hK).smul a (ELL.map σ x) := by
  obtain ⟨𝔞, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', hE'⟩ := ELL.exists_eq ((ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll)
  rw [← hE', ELL.map_toEll, ELL.map_toEll]
  obtain ⟨c, hc, h⟩ := homConstSet_of_smul σ₀ hK hE'.symm
  refine (smul_toEll_of_homConstSet σ₀ hK (c := σ c) ((map_ne_zero σ).2 hc) ?_).symm
  calc (homConstSet (E.map σ).curve (E'.map σ).curve : Set ℂ)
      = σ '' homConstSet E.curve E'.curve := homConstSet_map (E := E.curve) (E' := E'.curve) σ
    _ = σ '' ((c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) := by rw [h]
    _ = (σ c * ·) '' (σ '' idealLattice σ₀ ↑𝔞⁻¹) := image_ringEquiv_image_mul σ c _
    _ = (σ c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by rw [image_idealLattice σ₀ σ hσ]

/- English proof (translation)
Rewrite using `[ellMulAction_smul, one_mul, Equiv.apply_symm_apply]`.
-/
theorem ellMulAction_one_smul (x : ELL K) : (ellMulAction σ₀ hK).smul 1 x = x := by
  rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[ellMulAction_smul, ellMulAction_smul, ellMulAction_smul, Equiv.symm_apply_apply, mul_assoc]`.
-/
theorem ellMulAction_mul_smul (a b : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ₀ hK).smul (a * b) x =
      (ellMulAction σ₀ hK).smul a ((ellMulAction σ₀ hK).smul b x) := by
  rw [ellMulAction_smul, ellMulAction_smul, ellMulAction_smul, Equiv.symm_apply_apply, mul_assoc]

def galClass (σ : ℂ ≃+* ℂ) : ClassGroup (𝓞 K) :=
  (ellEquiv σ₀ hK).symm (ELL.map σ (ellEquiv σ₀ hK 1))

/- English proof (translation)
Establish `hx : x = (ellMulAction σ₀ hK).smul ((ellEquiv σ₀ hK).symm x) (ellEquiv σ₀ hK 1)`. Rewrite using `[ellMulAction_smul, Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]`. Rewrite using `[hx, ELL.map_smul σ₀ hK σ hσ]`. Simplify using `only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]`. Conclude with `congrArg (ellEquiv σ₀ hK) (mul_comm _ _)`.
-/
theorem ELL.map_eq_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    ELL.map σ x = (ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x := by
  have hx : x = (ellMulAction σ₀ hK).smul ((ellEquiv σ₀ hK).symm x) (ellEquiv σ₀ hK 1) := by
    rw [ellMulAction_smul, Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
  rw [hx, ELL.map_smul σ₀ hK σ hσ]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]
  exact congrArg (ellEquiv σ₀ hK) (mul_comm _ _)

/- English proof (translation)
Rewrite using `[← ELL.j_map, ELL.map_eq_galClass_smul σ₀ hK σ hσ]`.
-/
theorem apply_j_eq_j_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x) := by
  rw [← ELL.j_map, ELL.map_eq_galClass_smul σ₀ hK σ hσ]

/- English proof (translation)
Rewrite using `[galClass, ELL.map_one, Equiv.symm_apply_apply]`.
-/
theorem galClass_one : galClass σ₀ hK 1 = 1 := by
  rw [galClass, ELL.map_one, Equiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[galClass, ELL.map_mul, ELL.map_eq_galClass_smul σ₀ hK τ hτ, ELL.map_eq_galClass_smul σ₀ hK σ hσ, ← ellMulAction_mul_smul]`. Simplify using `only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]`.
-/
theorem galClass_mul (σ τ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (hτ : ∀ k : K, τ (σ₀ k) = σ₀ k) :
    galClass σ₀ hK (σ * τ) = galClass σ₀ hK σ * galClass σ₀ hK τ := by
  rw [galClass, ELL.map_mul, ELL.map_eq_galClass_smul σ₀ hK τ hτ,
    ELL.map_eq_galClass_smul σ₀ hK σ hσ, ← ellMulAction_mul_smul]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]

/- English proof (translation)
Rewrite using `[apply_j_eq_j_galClass_smul σ₀ hK σ hσ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, ellMulAction_one_smul]`. Introduce `h`.

Conclude with `(ell_smul_eq_self_iff σ₀ hK _ x).1 (ELL.j_injective h)`.
-/
theorem galClass_eq_one_iff (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    galClass σ₀ hK σ = 1 ↔ σ (ELL.j x) = ELL.j x := by
  rw [apply_j_eq_j_galClass_smul σ₀ hK σ hσ]
  constructor
  · intro h
    rw [h, ellMulAction_one_smul]
  · intro h
    exact (ell_smul_eq_self_iff σ₀ hK _ x).1 (ELL.j_injective h)

end Elliptic
end GroundTheory.Global
