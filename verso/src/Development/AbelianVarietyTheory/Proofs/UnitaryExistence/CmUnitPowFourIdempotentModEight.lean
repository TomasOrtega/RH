import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AdaptedDet

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => exact ⟨0, isIntegral_zero, by simp⟩`. Consider the case `cons μ s ih`. Take `⟨y, hy, h⟩` from `ih fun a ha => hs a (Multiset.mem_cons_of_mem ha)`. Establish `hμ` using `hs μ (Multiset.mem_cons_self _ _)`.

Establish `hQ : IsIntegral ℤ s.prod` using `IsIntegral.multiset_prod fun a ha => hs a (Multiset.mem_cons_of_mem ha)`. Use `⟨y * (e * μ + (1 - e)) + t * (μ * s.prod - μ - s.prod + 1), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hy.mul ((hei.mul hμ).add (isIntegral_one.sub hei))).add (hti.mul ((((hμ.mul hQ).sub hμ).sub hQ).add isIntegral_one))`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, h]`. Take the linear combination `(μ * s.prod - μ - s.prod + 1) * he`.
-/
theorem prod_interp {K : Type} [CommRing K] (n e t : K) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (s : Multiset K)
    (hs : ∀ μ ∈ s, IsIntegral ℤ μ) :
    ∃ y, IsIntegral ℤ y ∧ (s.map fun μ => e * μ + (1 - e)).prod = e * s.prod + (1 - e) + n * y := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons μ s ih =>
    obtain ⟨y, hy, h⟩ := ih fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    have hμ := hs μ (Multiset.mem_cons_self _ _)
    have hQ : IsIntegral ℤ s.prod :=
      IsIntegral.multiset_prod fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    refine ⟨y * (e * μ + (1 - e)) + t * (μ * s.prod - μ - s.prod + 1), ?_, ?_⟩
    · exact (hy.mul ((hei.mul hμ).add (isIntegral_one.sub hei))).add
        (hti.mul ((((hμ.mul hQ).sub hμ).sub hQ).add isIntegral_one))
    · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, h]
      linear_combination (μ * s.prod - μ - s.prod + 1) * he

/- English proof (translation)
Establish `h1 : c • A + a • (1 : Matrix (Fin r) (Fin r) K) = (-c) • (Matrix.scalar (Fin r) (-a / c) - A)`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`. Establish `hs : A.charpoly.Splits` using `IsAlgClosed.splits _`. Establish `hcard : A.charpoly.roots.card = r`.

Rewrite using `[← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Rewrite using `[h1, Matrix.det_smul, ← Matrix.eval_charpoly, hs.eval_eq_prod_roots_of_monic A.charpoly_monic, Fintype.card_fin]`. Establish `h2 : (fun μ => c * μ + a) = fun μ => (-c) * (-a / c - μ)`. Use function extensionality and compare the values at `μ`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]`.
-/
theorem det_smul_add {K : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (c a : K) (hc : c ≠ 0) :
    (c • A + a • (1 : Matrix (Fin r) (Fin r) K)).det =
      (A.charpoly.roots.map fun μ => c * μ + a).prod := by
  have h1 : c • A + a • (1 : Matrix (Fin r) (Fin r) K) =
      (-c) • (Matrix.scalar (Fin r) (-a / c) - A) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
      field_simp
      ring
    · simp [h]
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : A.charpoly.roots.card = r := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [h1, Matrix.det_smul, ← Matrix.eval_charpoly, hs.eval_eq_prod_roots_of_monic A.charpoly_monic,
    Fintype.card_fin]
  have h2 : (fun μ => c * μ + a) = fun μ => (-c) * (-a / c - μ) := by
    funext μ
    field_simp
    ring
  rw [h2, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

/- English proof (translation)
Set `K` to `AlgebraicClosure E`. Establish `hinj` using `(algebraMap E K).injective`. Establish `hn' : (n : K) ≠ 0` using `Nat.cast_ne_zero.mpr hn`. Establish `hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E))` using `fun x => x.isIntegral_coe.algebraMap`. Establish `hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ`.

Introduce `μ hμ`. Use `CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ (Polynomial.isRoot_of_mem_roots hμ)` as an intermediate fact. Establish `h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K))` using `isIntegral_trans (A := 𝓞 E) _ this`. Simplify using `using h2.add isIntegral_one`. Take `⟨y, hy, h⟩` from `prod_interp (n : K) (algebraMap E K e) (algebraMap E K t) (by`.

Use `congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he` as an intermediate fact. Simplify using `using this) (hint e) (hint t) _ hroots`. Rewrite `h` using `[← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]`. Use `set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd`. Establish `hd' : algebraMap E K d = 1 + n * y`.

Rewrite using `[hd, RingHom.map_det]`. Establish `: (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)) = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1`. Generalize the expression as in `(e : E) = x`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, -algebraMap_smul]`.

Rewrite using `[this, h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy' : IsIntegral ℤ ((d - 1) / n)`. Rewrite using `[← isIntegral_algebraMap_iff hinj, map_div₀, map_sub, map_one, map_natCast, hd', add_sub_cancel_left, mul_div_cancel_left₀ _ hn']`. Conclude with `hy`.

Take `⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - 1) / n` from `⟨⟨_, hy'⟩, rfl⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hn'' : (n : E) ≠ 0` using `Nat.cast_ne_zero.mpr hn`. Establish `h1 : ((1 + n * z : 𝓞 E) : E) = 1 + n * (z : E)` using `by simp`. Rewrite using `[h1, hz]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_interp {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0) (e t : 𝓞 E)
    (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = 1) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((1 + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = 1 + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h]
    ring
  have hy' : IsIntegral ℤ ((d - 1) / n) := by
    rw [← isIntegral_algebraMap_iff hinj, map_div₀, map_sub, map_one, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - 1) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((1 + n * z : 𝓞 E) : E) = 1 + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add, map_one, ← nsmul_eq_mul, map_nsmul, ← eq_intCast (Int.castRingHom (ZMod n)), RingHom.map_det, map_add, map_one, map_nsmul]`. Establish `: n • (Int.castRingHom (ZMod n)).mapMatrix (Algebra.leftMulMatrix (RingOfIntegers.basis E) y) = 0`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this, add_zero, det_one]`.
-/
theorem norm_one_add {E : Type} [Field E] [NumberField E] (n : ℕ) (y : 𝓞 E) :
    ((Algebra.norm ℤ (1 + n * y : 𝓞 E) : ℤ) : ZMod n) = 1 := by
  classical
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add, map_one, ← nsmul_eq_mul,
    map_nsmul, ← eq_intCast (Int.castRingHom (ZMod n)), RingHom.map_det, map_add, map_one,
    map_nsmul]
  have : n • (Int.castRingHom (ZMod n)).mapMatrix
      (Algebra.leftMulMatrix (RingOfIntegers.basis E) y) = 0 := by
    ext i j
    simp
  rw [this, add_zero, det_one]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7` from `⟨H.d / 16, by have := H.d_mod; omega⟩`. Establish `h1` using `H.rt_sq`. Establish `h2` using `H.two_weight_eq_one_add_root`. Rewrite `h1` using `[hk]`. Move the coercions through the operations in `at h1`.

Establish `hw : H.w0 ^ 2 = H.w0 - (4 * k + 2)`. Apply `mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)` to reduce the goal to its premises. Take the linear combination `h1 + (2 * H.w0 - 1 + H.rt) * h2`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `h` using `[pow_eq_zero_iff (by norm_num)]`. Rewrite `hw` using `[h]`. Establish `: ((4 * k + 2 : ℕ) : 𝓞 E) = 0`. Use `push_cast`. Take the linear combination `hw`.

Rewrite `this` using `[Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers. Establish `h4 : H.w0 ^ 4 = (-8 * k - 3) * H.w0 + (16 * k ^ 2 + 12 * k + 2)`. Take the linear combination `(H.w0 ^ 2 + H.w0 - (4 * k + 2) + 0) * hw + hw`. Use `⟨(-8 * k - 3) * (4 * k ^ 2 + 2 * k) * H.w0 + (4 * k + 2) * (8 * k ^ 3 - 4 * k - 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[h4]`. Use `push_cast`. Take the linear combination `(-8 * k - 3) ^ 2 * hw`.
-/
theorem cmUnit_pow_four_idempotent_mod_eight {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 ^ 4 ≠ 0 ∧ ∃ t : 𝓞 E, H.w0 ^ 4 * H.w0 ^ 4 - H.w0 ^ 4 = (8 : ℕ) * t := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := H.rt_sq
  have h2 := H.two_weight_eq_one_add_root
  rw [hk] at h1
  push_cast at h1
  have hw : H.w0 ^ 2 = H.w0 - (4 * k + 2) := by
    apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
    linear_combination h1 + (2 * H.w0 - 1 + H.rt) * h2
  constructor
  · intro h
    rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h] at hw
    have : ((4 * k + 2 : ℕ) : 𝓞 E) = 0 := by
      push_cast
      linear_combination hw
    rw [Nat.cast_eq_zero] at this
    omega
  · have h4 : H.w0 ^ 4 = (-8 * k - 3) * H.w0 + (16 * k ^ 2 + 12 * k + 2) := by
      linear_combination (H.w0 ^ 2 + H.w0 - (4 * k + 2) + 0) * hw + hw
    refine ⟨(-8 * k - 3) * (4 * k ^ 2 + 2 * k) * H.w0 + (4 * k + 2) * (8 * k ^ 3 - 4 * k - 1), ?_⟩
    rw [h4]
    push_cast
    linear_combination (-8 * k - 3) ^ 2 * hw

section Lattice

variable {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L] {r : ℕ}

/- English proof (translation)
The claim follows from `(isLocalizedModule_id ℤ⁰ (Fin r → E) ℚ).map_units s surj v := by have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E _ v hv rw [← LinearMap.coe_r …`.
-/
theorem isLocalizedModule_int (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) :
    IsLocalizedModule ℤ⁰ (φ.restrictScalars ℤ) where
  map_units s := (isLocalizedModule_id ℤ⁰ (Fin r → E) ℚ).map_units s
  surj v := by
    have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
    obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m, ⟨n, hn⟩), ?_⟩
    change n • v = φ m
    rw [hm, Submonoid.smul_def, algebraMap_smul]
  exists_of_eq h := ⟨1, by rw [hf h]⟩

/- English proof (translation)
Rewrite using `[← isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E]`. Conclude with `{ map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s surj := fun v => by`. Establish `hv : v ∈ Submodule.span E (Set.range φ)` using `by rw [hspan]; trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv`. Rewrite `ht` using `[← LinearMap.coe_range, Submodule.span_eq]`.

Take `⟨m, hm⟩` from `ht`. Conclude with `⟨(m, t), hm.symm⟩`. Use `exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }`.
-/
theorem isBaseChange (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) : IsBaseChange E φ := by
  rw [← isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E]
  exact
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun v => by
        have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
        rw [← LinearMap.coe_range, Submodule.span_eq] at ht
        obtain ⟨m, hm⟩ := ht
        exact ⟨(m, t), hm.symm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }

/- English proof (translation)
Establish `hb` using `isBaseChange φ hf hspan`. Set `A` to `hb.lift (φ ∘ₗ gam.toLinearMap)`. Set `B` to `hb.lift (φ ∘ₗ gam.symm.toLinearMap)`. Establish `hA : ∀ x, A (φ x) = φ (gam x)` using `fun x => hb.lift_eq _ x`. Establish `hB : ∀ x, B (φ x) = φ (gam.symm x)` using `fun x => hb.lift_eq _ x`.

Establish `hAB : A ∘ₗ B = LinearMap.id` using `hb.algHom_ext _ _ fun x => by simp [hA, hB]`. Establish `hBA : B ∘ₗ A = LinearMap.id` using `hb.algHom_ext _ _ fun x => by simp [hA, hB]`. Use `⟨⟨LinearMap.toMatrix' A, LinearMap.toMatrix' B, ?_, ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, hAB, LinearMap.toMatrix'_id]`. Rewrite using `[← LinearMap.toMatrix'_comp, hBA, LinearMap.toMatrix'_id]`.

Simplify using `[hA]`.
-/
theorem exists_gl (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) (gam : L ≃ₗ[𝓞 E] L) :
    ∃ γ : GL (Fin r) E, ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (gam x) := by
  have hb := isBaseChange φ hf hspan
  let A := hb.lift (φ ∘ₗ gam.toLinearMap)
  let B := hb.lift (φ ∘ₗ gam.symm.toLinearMap)
  have hA : ∀ x, A (φ x) = φ (gam x) := fun x => hb.lift_eq _ x
  have hB : ∀ x, B (φ x) = φ (gam.symm x) := fun x => hb.lift_eq _ x
  have hAB : A ∘ₗ B = LinearMap.id := hb.algHom_ext _ _ fun x => by simp [hA, hB]
  have hBA : B ∘ₗ A = LinearMap.id := hb.algHom_ext _ _ fun x => by simp [hA, hB]
  refine ⟨⟨LinearMap.toMatrix' A, LinearMap.toMatrix' B, ?_, ?_⟩, fun x => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hAB, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, hBA, LinearMap.toMatrix'_id]
  · simp [hA]

/- English proof (translation)
Use `haveI := isLocalizedModule_int φ hf hspan`. Set `b'` to `b.ofIsLocalizedModule ℚ ℤ⁰ (φ.restrictScalars ℤ)`. Rewrite using `[← LinearMap.det_toLin' A, ← LinearMap.det_restrictScalars, ← LinearMap.det_toMatrix b', ← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, b', Module.Basis.ofIsLocalizedModule_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply, hA]`. Conclude with `(b.ofIsLocalizedModule_repr_apply ℚ ℤ⁰ (φ.restrictScalars ℤ) _ i).symm`.
-/
theorem det_eq_norm {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) (T : L →ₗ[ℤ] L) (A : Matrix (Fin r) (Fin r) E)
    (hA : ∀ x, A *ᵥ φ x = φ (T x)) :
    (((LinearMap.toMatrix b b T).det : ℤ) : ℚ) = Algebra.norm ℚ A.det := by
  haveI := isLocalizedModule_int φ hf hspan
  let b' := b.ofIsLocalizedModule ℚ ℤ⁰ (φ.restrictScalars ℤ)
  rw [← LinearMap.det_toLin' A, ← LinearMap.det_restrictScalars, ← LinearMap.det_toMatrix b',
    ← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, b',
    Module.Basis.ofIsLocalizedModule_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
    hA]
  exact (b.ofIsLocalizedModule_repr_apply ℚ ℤ⁰ (φ.restrictScalars ℤ) _ i).symm

end Lattice

/- English proof (translation)
Establish `hrt : FD.cc (H.rt : E) = -(H.rt : E) ∧ (H.rt : E) ≠ 0`. Establish `h1 : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Establish `hne : FD.cc (H.rt : E) ≠ (H.rt : E)`. Introduce `h`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2` using `IsCMField.complexEmbedding_complexConj E σ (H.rt : E)`. Rewrite `h2` using `[show IsCMField.complexConj E (H.rt : E) = H.rt from h]`.

Establish `h3 : (σ H.rt).im = 0` using `Complex.conj_eq_iff_im.mp h2.symm`. Establish `h4` using `congrArg (fun x => (σ x).re) h1`. Simplify using `only [map_pow, map_neg, map_natCast, sq, map_mul, Complex.mul_re, h3, Complex.neg_re, Complex.natCast_re] at h4`. Use polynomial arithmetic with `[mul_self_nonneg (σ H.rt).re]`. Prove the components needed by the constructor for the conclusion.

Establish `h2 : FD.cc (H.rt : E) ^ 2 = (H.rt : E) ^ 2`. Rewrite using `[FD.cc, ← map_pow, h1, map_neg, map_natCast]`. Conclude with `(sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hne`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[h, FD.cc, map_zero]`. Take `⟨Gm, φ, hinj, hspan, hherm, hdet, hEF⟩` from `exists_herm_coord_of_datum E H D H.rt hrt.1 hrt.2 _ rfl`. Establish `hfg` using `(HermModel.rank_integral_selfDual E H D _ _ Gm φ hrt.1 ⟨hinj, hspan, hherm, hdet, hEF⟩).2.1`. Take `⟨γ, hγ⟩` from `exists_gl φ hinj hspan gam`. Establish `hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x` using `fun a x => by`.

Rewrite using `[map_smul]`. Both sides reduce to the same expression. Establish `hh : ∀ x y, FD.herm Gm (φ (gam x)) (φ (gam y)) = FD.herm Gm (φ x) (φ y)`. Introduce `x y`. Apply `mul_left_cancel₀ hrt.2` to reduce the goal to its premises.

Apply `DatumCoord.eq_of_trace_int` to reduce the goal to its premises. Introduce `a`. Use `hiso (a • x) y` as an intermediate fact. Establish `h2` using `hEF (a • x) y`. Rewrite `h2` using `[← this, hEF, map_smul, hsm, hsm, HermModel.herm_smul_left, HermModel.herm_smul_left]`.

Rewrite using `[mul_left_comm, h2, mul_left_comm]`. Establish `hadd : ∀ x x' y, FD.herm Gm (x + x') y = FD.herm Gm x y + FD.herm Gm x' y`. Introduce `x x' y`. Simplify using `[FD.herm, add_mul, Finset.sum_add_distrib]`. Establish `hU : FD.IsUStab Gm (LinearMap.range φ) γ`.

Prove the components needed by the constructor for the conclusion. Introduce `x y`. Establish `hx : x ∈ Submodule.span E (Set.range φ)` using `by rw [hspan]; trivial`. Establish `hy : y ∈ Submodule.span E (Set.range φ)` using `by rw [hspan]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨x, rfl⟩` from `hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨y, rfl⟩` from `hy`.

Rewrite using `[hγ, hγ, hh]`. Consider the case `zero => simp [HermModel.herm_zero_right]`. Consider the case `add y z _ _ hy hz`. Rewrite using `[Matrix.mulVec_add, HermModel.herm_add_right, HermModel.herm_add_right, hy, hz]`. Consider the case `smul c y _ hy`.

Rewrite using `[Matrix.mulVec_smul, HermModel.herm_smul_right, HermModel.herm_smul_right, hy]`. Consider the case `zero => simp [FD.herm]`. Consider the case `add x z _ _ hx hz => rw [Matrix.mulVec_add, hadd, hadd, hx, hz]`. Consider the case `smul c x _ hx`. Rewrite using `[Matrix.mulVec_smul, HermModel.herm_smul_left, HermModel.herm_smul_left, hx]`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨gam y, (hγ y).symm⟩`. Introduce and unpack `⟨y, hy⟩`.

Use `⟨gam.symm y, ?_⟩` and prove the remaining obligations. Apply `Matrix.mulVec_injective_of_isUnit γ.isUnit` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ *ᵥ _ = _ *ᵥ _`. Rewrite using `[hγ, LinearEquiv.apply_symm_apply, hy]`. Establish `hdet1` using `CongruenceDet.det_eq_one E _ M Gm (LinearMap.range φ) γ hdet hfg hspan hM hU (by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨e, he⟩` from `hlev x`. Conclude with `⟨φ e, ⟨e, rfl⟩, by rw [hγ, he, map_add, map_nsmul]⟩)`. Take `⟨he0, t, ht⟩` from `cmUnit_pow_four_idempotent_mod_eight H`. Take `⟨y, hy⟩` from `det_interp 8 (by norm_num) _ t he0 ht (LinearMap.range φ) γ hfg hspan (fun v hv => (hU.2 v).1 hv) hdet1`.

Establish `h` using `det_eq_norm b φ hinj hspan T (((H.w0 ^ 4 : 𝓞 E) : E) • (γ : Matrix _ _ E) + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by`. Introduce `x`. Rewrite using `[hT, map_add, map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hγ, Matrix.one_mulVec, sub_smul, one_smul])`. Rewrite `h` using `[hy, ← Algebra.coe_norm_int]`. Rewrite using `[Int.cast_injective h]`.

Conclude with `norm_one_add 8 y`.
-/
theorem det_interp_datum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {M : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (hM : 3 ≤ M) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hlev : ∀ a, ∃ e, gam a = a + M • e) (T : D.La →ₗ[ℤ] D.La)
    (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (((LinearMap.toMatrix b b T).det : ℤ) : ZMod 8) = 1 := by
  have hrt : FD.cc (H.rt : E) = -(H.rt : E) ∧ (H.rt : E) ≠ 0 := by
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hne : FD.cc (H.rt : E) ≠ (H.rt : E) := by
      intro h
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h2 := IsCMField.complexEmbedding_complexConj E σ (H.rt : E)
      rw [show IsCMField.complexConj E (H.rt : E) = H.rt from h] at h2
      have h3 : (σ H.rt).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
      have h4 := congrArg (fun x => (σ x).re) h1
      simp only [map_pow, map_neg, map_natCast, sq, map_mul, Complex.mul_re, h3, Complex.neg_re,
        Complex.natCast_re] at h4
      nlinarith [mul_self_nonneg (σ H.rt).re]
    constructor
    · have h2 : FD.cc (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
        rw [FD.cc, ← map_pow, h1, map_neg, map_natCast]
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hne
    · intro h
      apply hne
      rw [h, FD.cc, map_zero]
  obtain ⟨Gm, φ, hinj, hspan, hherm, hdet, hEF⟩ :=
    exists_herm_coord_of_datum E H D H.rt hrt.1 hrt.2 _ rfl
  have hfg := (HermModel.rank_integral_selfDual E H D _ _ Gm φ hrt.1
    ⟨hinj, hspan, hherm, hdet, hEF⟩).2.1
  obtain ⟨γ, hγ⟩ := exists_gl φ hinj hspan gam
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  have hh : ∀ x y, FD.herm Gm (φ (gam x)) (φ (gam y)) = FD.herm Gm (φ x) (φ y) := by
    intro x y
    apply mul_left_cancel₀ hrt.2
    apply DatumCoord.eq_of_trace_int
    intro a
    have := hiso (a • x) y
    have h2 := hEF (a • x) y
    rw [← this, hEF, map_smul, hsm, hsm, HermModel.herm_smul_left, HermModel.herm_smul_left] at h2
    rw [mul_left_comm, h2, mul_left_comm]
  have hadd : ∀ x x' y, FD.herm Gm (x + x') y = FD.herm Gm x y + FD.herm Gm x' y := by
    intro x x' y
    simp [FD.herm, add_mul, Finset.sum_add_distrib]
  have hU : FD.IsUStab Gm (LinearMap.range φ) γ := by
    constructor
    · intro x y
      have hx : x ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
      have hy : y ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨y, rfl⟩ := hy
          rw [hγ, hγ, hh]
        | zero => simp [HermModel.herm_zero_right]
        | add y z _ _ hy hz =>
          rw [Matrix.mulVec_add, HermModel.herm_add_right, HermModel.herm_add_right, hy, hz]
        | smul c y _ hy =>
          rw [Matrix.mulVec_smul, HermModel.herm_smul_right, HermModel.herm_smul_right, hy]
      | zero => simp [FD.herm]
      | add x z _ _ hx hz => rw [Matrix.mulVec_add, hadd, hadd, hx, hz]
      | smul c x _ hx =>
        rw [Matrix.mulVec_smul, HermModel.herm_smul_left, HermModel.herm_smul_left, hx]
    · intro x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨gam y, (hγ y).symm⟩
      · rintro ⟨y, hy⟩
        refine ⟨gam.symm y, ?_⟩
        apply Matrix.mulVec_injective_of_isUnit γ.isUnit
        change _ *ᵥ _ = _ *ᵥ _
        rw [hγ, LinearEquiv.apply_symm_apply, hy]
  have hdet1 := CongruenceDet.det_eq_one E _ M Gm (LinearMap.range φ) γ hdet hfg hspan hM hU (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hlev x
    exact ⟨φ e, ⟨e, rfl⟩, by rw [hγ, he, map_add, map_nsmul]⟩)
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  obtain ⟨y, hy⟩ := det_interp 8 (by norm_num) _ t he0 ht (LinearMap.range φ) γ hfg hspan
    (fun v hv => (hU.2 v).1 hv) hdet1
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • (γ : Matrix _ _ E) + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add, map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hγ, Matrix.one_mulVec, sub_smul, one_smul])
  rw [hy, ← Algebra.coe_norm_int] at h
  rw [Int.cast_injective h]
  exact norm_one_add 8 y

/- English proof (translation)
Introduce `E _ _ _ H D g M bas gam N ⟨hl, hr⟩ hM hiso hlev hN`. Set `π : D.La →+ (Fin g ⊕ Fin g → ZMod 8)` to `{ toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8) map_zero' := by ext; simp map_add' := fun x y => by ext; simp }`. Establish `hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8)` using `fun _ _ => rfl`. Establish `h8 : ∀ x, π ((8 : ℕ) • x) = 0` using `fun x => by`. Rewrite using `[map_nsmul]`.

Use extensionality with `u`. Rewrite using `[Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]`. Establish `hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0` using `fun v u => by`. Simplify using `[hπ, Pi.single_apply]`. Establish `he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u`.

Introduce `x u`. Take `⟨c, rfl⟩` from `bas.surjective x`. Proceed by induction on `c using Pi.single_induction with`. Consider the case `zero => cases u <;> simp`. Consider the case `add a b ha hb => rw [map_add, smul_add, map_add, map_add, Pi.add_apply, ha, hb]; cases u <;> simp`.

Consider the case `single v n`. Establish `: (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`. Rewrite using `[this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]`. Consider the cases of `v with`.

Consider the case `inl k`. Take `⟨e, h⟩` from `hl k`. Rewrite using `[h, map_add, h8, add_zero]`. Apply the tactic sequence `cases u <;> simp [hπb]`. Consider the case `inr k`.

Take `⟨e, h⟩` from `hr k`. Rewrite using `[h, h8]`. Apply the tactic sequence `cases u <;> simp [hπb]`. Establish `hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u` using `fun u v => by`. Rewrite using `[hN, hπ]`.

Prove the components needed by the constructor for the conclusion. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Apply `(ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp` to reduce the goal to its premises. Take `⟨e, h⟩` from `hr j`.

Establish `h1` using `he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)`. Rewrite `h1` using `[← map_smul, h, map_nsmul, h8]`. Rewrite using `[hN']`. Conclude with `h1.symm`. Apply `(ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp` to reduce the goal to its premises.

Take `⟨e, h⟩` from `hl j`. Establish `h1` using `he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)`. Rewrite `h1` using `[← map_smul, h, map_add, map_nsmul, map_add, h8, add_zero]`. Rewrite using `[hN']`. Conclude with `h1`.

Set `b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La` to `(Pi.basisFun ℤ _).map bas`. Set `T : D.La →ₗ[𝓞 E] D.La` to `H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)`. Establish `hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)` using `fun x => rfl`. Establish `h` using `det_interp_datum D b gam hM hiso hlev (T.restrictScalars ℤ) hT`. Apply `(ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp` to reduce the goal to its premises.

Rewrite using `[Int.cast_sub, Int.cast_one, sub_eq_zero, ← h, ← eq_intCast (Int.castRingHom (ZMod 8)), ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]`. Establish `hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v = π (T.restrictScalars ℤ (bas (Pi.single v 1))) u` using `fun u v => by`. Simplify using `[LinearMap.toMatrix_apply, b, hπ]`. Establish `hblk : (Int.castRingHom (ZMod 8)).mapMatrix (LinearMap.toMatrix b b (T.restrictScalars ℤ)) = Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁) (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) …`. Use extensionality with `u v`.

Apply the tactic sequence `rcases u with i | i <;> rcases v with j | j`. Rewrite using `[hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]`. Simplify using `[Matrix.toBlocks₁₁, hN']`. Both sides reduce to the same expression. Rewrite using `[hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]`.

Simplify using `[hπb]`. Rewrite using `[hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]`. Simplify using `[hπb, Matrix.one_apply]`. Rewrite using `[hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]`.
-/
theorem blocks_det_mod_eight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g M : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → 3 ≤ M → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ a, ∃ e, gam a = a + M • e) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j)) ∧ (8 : ℤ) ∣ N.toBlocks₁₁.det - 1 := by
  intro E _ _ _ H D g M bas gam N ⟨hl, hr⟩ hM hiso hlev hN
  classical
  let π : D.La →+ (Fin g ⊕ Fin g → ZMod 8) :=
    { toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8)
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8) := fun _ _ => rfl
  have h8 : ∀ x, π ((8 : ℕ) • x) = 0 := fun x => by
    rw [map_nsmul]
    ext u
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0 := fun v u => by
    simp [hπ, Pi.single_apply]

  have he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u := by
    intro x u
    obtain ⟨c, rfl⟩ := bas.surjective x
    induction c using Pi.single_induction with
    | zero => cases u <;> simp
    | add a b ha hb => rw [map_add, smul_add, map_add, map_add, Pi.add_apply, ha, hb]; cases u <;> simp
    | single v n =>
      have : (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      cases v with
      | inl k =>
        obtain ⟨e, h⟩ := hl k
        rw [h, map_add, h8, add_zero]
        cases u <;> simp [hπb]
      | inr k =>
        obtain ⟨e, h⟩ := hr k
        rw [h, h8]
        cases u <;> simp [hπb]
  have hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u := fun u v => by
    rw [hN, hπ]
  constructor
  · intro i j
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hr j
      have h1 := he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)
      rw [← map_smul, h, map_nsmul, h8] at h1
      rw [hN']
      exact h1.symm
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hl j
      have h1 := he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)
      rw [← map_smul, h, map_add, map_nsmul, map_add, h8, add_zero] at h1
      rw [hN']
      exact h1
  · let b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La := (Pi.basisFun ℤ _).map bas
    let T : D.La →ₗ[𝓞 E] D.La :=
      H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)
    have hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x) := fun x => rfl
    have h := det_interp_datum D b gam hM hiso hlev (T.restrictScalars ℤ) hT
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero, ← h, ← eq_intCast (Int.castRingHom (ZMod 8)),
      ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]
    have hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v =
        π (T.restrictScalars ℤ (bas (Pi.single v 1))) u := fun u v => by
      simp [LinearMap.toMatrix_apply, b, hπ]
    have hblk : (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) =
        Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁)
          (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix
            (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) (Sum.inr j)) 0 1 := by
      ext u v
      rcases u with i | i <;> rcases v with j | j
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [Matrix.toBlocks₁₁, hN']
      · rfl
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb]
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb, Matrix.one_apply]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]

end GlobalTheory.AdaptedDet
