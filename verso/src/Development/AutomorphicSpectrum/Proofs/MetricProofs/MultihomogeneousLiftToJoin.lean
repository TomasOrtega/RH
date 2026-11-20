import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Set `P : PrimeSpectrum Γ(X, W₀)` to `⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩`. Use `⟨hW₀.fromSpec P, ?_, fun a => ?_⟩` and prove the remaining obligations. Use `hW₀.range_fromSpec` as an intermediate fact. Establish `h2 : hW₀.fromSpec P ∈ Set.range hW₀.fromSpec` using `⟨P, rfl⟩`. Rewrite `h2` using `[this]`.

Conclude with `h2`. Establish `h` using `hW₀.fromSpec_preimage_basicOpen a`. Establish `h2 : hW₀.fromSpec P ∈ X.basicOpen a ↔ P ∈ hW₀.fromSpec ⁻¹ᵁ X.basicOpen a` using `Iff.rfl`. Rewrite using `[h2, h]`. Express the relevant statement in the definitionally equal form `a ∉ RingHom.ker ψ ↔ _`.

Rewrite using `[RingHom.mem_ker]`.
-/
theorem exists_point_of_hom {X : Scheme.{0}} {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) {F : Type} [Field F]
    (ψ : Γ(X, W₀) →+* F) : ∃ t ∈ W₀, ∀ a : Γ(X, W₀), t ∈ X.basicOpen a ↔ ψ a ≠ 0 := by
  let P : PrimeSpectrum Γ(X, W₀) := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  refine ⟨hW₀.fromSpec P, ?_, fun a => ?_⟩
  · have := hW₀.range_fromSpec
    have h2 : hW₀.fromSpec P ∈ Set.range hW₀.fromSpec := ⟨P, rfl⟩
    rw [this] at h2
    exact h2
  · have h := hW₀.fromSpec_preimage_basicOpen a
    have h2 : hW₀.fromSpec P ∈ X.basicOpen a ↔ P ∈ hW₀.fromSpec ⁻¹ᵁ X.basicOpen a := Iff.rfl
    rw [h2, h]
    change a ∉ RingHom.ker ψ ↔ _
    rw [RingHom.mem_ker]

/- English proof (translation)
Use `haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by`. Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`. Establish `hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hU (Set.mem_univ y)`. Set `y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme` to `IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr`. Establish `hy : y ≫ (f ⁻¹ᵁ U).ι = ζ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ` using `by rw [← Category.assoc, hy, hζ]`.

Take `⟨t', ht'⟩` from `(f ∣_ U).surjective ⟨t, htU⟩`. Establish `ht'eq : ((f ⁻¹ᵁ U).ι ≫ f) t' = t`. Rewrite using `[← morphismRestrict_ι]`. Express the relevant statement in the definitionally equal form `U.ι ((f ∣_ U) t') = t`. Rewrite using `[ht']`.

Both sides reduce to the same expression. Set `φ : (f ⁻¹ᵁ U).toScheme ⟶ PSpace ℚ r` to `(f ⁻¹ᵁ U).ι ≫ q`. Establish `hφ : y ≫ φ = point ℚ x' hx'`. Simplify using `only [φ]`. Rewrite using `[← Category.assoc, hy, hq]`.

Take `⟨l, hl⟩` from `exists_mem_chart ℚ r (φ t')`. Set `V : (f ⁻¹ᵁ U).toScheme.Opens` to `φ ⁻¹ᵁ chart ℚ r l`. Set `O : X.Opens` to `((f ⁻¹ᵁ U).ι ≫ f) ''ᵁ V`. Establish `htO : t ∈ O` using `⟨t', hl, ht'eq⟩`. Take `⟨b, hbO, htb⟩` from `hW₀.exists_basicOpen_le (V := O) ⟨t, htO⟩ htW`.

Establish `hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b` using `le_preimage_of_mem ξ htb`. Establish `hyV : ⊤ ≤ y ⁻¹ᵁ V` using `fun u _ => by`. Establish `h1 : ξ u ∈ O` using `hbO (hD (Set.mem_univ u))`. Rewrite `h1` using `[← hyr]`. Establish `h2` using `(((f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq V).le h1`.

Conclude with `h2`. Establish `hl0 : x' l ≠ 0` using `ne_zero_of_le hφ hyV le_rfl`. Set `s : Fin (r + 1) → Γ(X, O)` to `fun i => (((f ⁻¹ᵁ U).ι ≫ f).appIso V).inv.hom (pullRatio φ V l le_rfl i)`. Establish `hs : ∀ i, valR ξ O (s i) = x' i / x' l` using `fun i => by`. Use `valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y V hyV (pullRatio φ V l le_rfl i)` as an intermediate fact.

Rewrite `this` using `[hyr]`. Rewrite using `[this]`. Conclude with `valR_pullRatio hφ hyV le_rfl i`. Establish `hloc` using `hW₀.isLocalization_basicOpen b`. Take `⟨⟨_, n, rfl⟩, hn⟩` from `IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers b) (fun i => (X.presheaf.map (homOfLE hbO).op).hom (s i))`.

Establish `hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) = valR ξ W₀ c` using `fun c => valR_res ξ (X.basicOpen_le b) hD c`. Use `⟨l, hl0, b ^ (n + 1), ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.basicOpen_pow _ _ n.succ_pos]`. Conclude with `htb`. Take `⟨a, ha⟩` from `hn i`.

Use `⟨a * b, ?_⟩` and prove the remaining obligations. Establish `hv` using `congrArg (valR ξ (X.basicOpen b)) ha`. Simplify using `only [Algebra.smul_def] at hv`. Rewrite `hv` using `[valR_mul ξ _ hD, hres, hres, valR_res ξ hbO hD, hs i]`. Rewrite using `[valR_mul ξ _ h₀, hv, pow_succ, valR_mul ξ _ h₀]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_local_quot {Ω : Type} [Field Ω] [CharZero Ω] {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U))
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) {r : ℕ} (q : X' ⟶ PSpace ℚ r)
    (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (hq : ζ ≫ q = point ℚ x' hx') (t : X) (htU : t ∈ U) (htW : t ∈ W₀)
    (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) :
    ∃ l, x' l ≠ 0 ∧ ∃ b : Γ(X, W₀), t ∈ X.basicOpen b ∧
      ∀ i, ∃ a : Γ(X, W₀), x' i / x' l * valR ξ W₀ b = valR ξ W₀ a := by
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  obtain ⟨t', ht'⟩ := (f ∣_ U).surjective ⟨t, htU⟩
  have ht'eq : ((f ⁻¹ᵁ U).ι ≫ f) t' = t := by
    rw [← morphismRestrict_ι]
    change U.ι ((f ∣_ U) t') = t
    rw [ht']
    rfl
  let φ : (f ⁻¹ᵁ U).toScheme ⟶ PSpace ℚ r := (f ⁻¹ᵁ U).ι ≫ q
  have hφ : y ≫ φ = point ℚ x' hx' := by
    simp only [φ]
    rw [← Category.assoc, hy, hq]
  obtain ⟨l, hl⟩ := exists_mem_chart ℚ r (φ t')
  let V : (f ⁻¹ᵁ U).toScheme.Opens := φ ⁻¹ᵁ chart ℚ r l
  let O : X.Opens := ((f ⁻¹ᵁ U).ι ≫ f) ''ᵁ V
  have htO : t ∈ O := ⟨t', hl, ht'eq⟩
  obtain ⟨b, hbO, htb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨t, htO⟩ htW
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := le_preimage_of_mem ξ htb
  have hyV : ⊤ ≤ y ⁻¹ᵁ V := fun u _ => by
    have h1 : ξ u ∈ O := hbO (hD (Set.mem_univ u))
    rw [← hyr] at h1
    have h2 := (((f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq V).le h1
    exact h2
  have hl0 : x' l ≠ 0 := ne_zero_of_le hφ hyV le_rfl
  let s : Fin (r + 1) → Γ(X, O) := fun i => (((f ⁻¹ᵁ U).ι ≫ f).appIso V).inv.hom (pullRatio φ V l le_rfl i)
  have hs : ∀ i, valR ξ O (s i) = x' i / x' l := fun i => by
    have := valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y V hyV (pullRatio φ V l le_rfl i)
    rw [hyr] at this
    rw [this]
    exact valR_pullRatio hφ hyV le_rfl i
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers b)
    (fun i => (X.presheaf.map (homOfLE hbO).op).hom (s i))
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  refine ⟨l, hl0, b ^ (n + 1), ?_, fun i => ?_⟩
  · rw [Scheme.basicOpen_pow _ _ n.succ_pos]
    exact htb
  · obtain ⟨a, ha⟩ := hn i
    refine ⟨a * b, ?_⟩
    have hv := congrArg (valR ξ (X.basicOpen b)) ha
    simp only [Algebra.smul_def] at hv
    rw [valR_mul ξ _ hD, hres, hres, valR_res ξ hbO hD, hs i] at hv
    rw [valR_mul ξ _ h₀, hv, pow_succ, valR_mul ξ _ h₀]
    ring

/- English proof (translation)
Establish `hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ A` using `fun a => by`. Rewrite using `[valR_eq ξ W₀ h₀, ← SetLike.mem_coe, ← hA]`. Conclude with `⟨a, rfl⟩`. Set `v : Γ(X, W₀) →+* A` to `(valMap ξ W₀ h₀).hom.codRestrict A fun a => by`. Rewrite using `[← SetLike.mem_coe, ← hA]`.

Conclude with `⟨a, rfl⟩`. Establish `hv : ∀ a, ((v a : A) : Ω) = valR ξ W₀ a` using `fun a => (valR_eq ξ W₀ h₀ a).symm`. Take `⟨t, htW, ht⟩` from `exists_point_of_hom hW₀ (ψ.comp v)`. Establish `hvσ : v σ₀ = g₀` using `Subtype.ext (by rw [hv, hg])`. Establish `htU : t ∈ U`.

Rewrite using `[← hσ, ht]`. Simplify `hψ` using `[hvσ]`. Take `⟨l, hl, b, hb, hi⟩` from `exists_local_quot ξ f U ζ hζ hU hW₀ q x' hx' hq t htU htW h₀`. Use `⟨l, hl, v b, (ht b).1 hb, fun i => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hi i`.

Conclude with `⟨v a, by rw [hv, hv, ha]⟩`.
-/
theorem local_of_hom {Ω : Type} [Field Ω] [CharZero Ω] {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U))
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) (σ₀ : Γ(X, W₀)) (hσ : X.basicOpen σ₀ = U) (g₀ : A)
    (hg : (g₀ : Ω) = valR ξ W₀ σ₀) {r : ℕ} (q : X' ⟶ PSpace ℚ r)
    (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (hq : ζ ≫ q = point ℚ x' hx') (ψ : A →+* ℂ) (hψ : ψ g₀ ≠ 0) :
    ∃ l, x' l ≠ 0 ∧ ∃ b : A, ψ b ≠ 0 ∧ ∀ i, ∃ a : A, x' i / x' l * (b : Ω) = a := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ A := fun a => by
    rw [valR_eq ξ W₀ h₀, ← SetLike.mem_coe, ← hA]
    exact ⟨a, rfl⟩
  let v : Γ(X, W₀) →+* A := (valMap ξ W₀ h₀).hom.codRestrict A fun a => by
    rw [← SetLike.mem_coe, ← hA]
    exact ⟨a, rfl⟩
  have hv : ∀ a, ((v a : A) : Ω) = valR ξ W₀ a := fun a => (valR_eq ξ W₀ h₀ a).symm
  obtain ⟨t, htW, ht⟩ := exists_point_of_hom hW₀ (ψ.comp v)
  have hvσ : v σ₀ = g₀ := Subtype.ext (by rw [hv, hg])
  have htU : t ∈ U := by
    rw [← hσ, ht]
    simpa [hvσ] using hψ
  obtain ⟨l, hl, b, hb, hi⟩ := exists_local_quot ξ f U ζ hζ hU hW₀ q x' hx' hq t htU htW h₀
  refine ⟨l, hl, v b, (ht b).1 hb, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hi i
  exact ⟨v a, by rw [hv, hv, ha]⟩

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C q`. Use `⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, fun R _ _ v _ => ?_⟩` and prove the remaining obligations. Establish `hd : (q.den : R) ≠ 0` using `by exact_mod_cast q.den_nz`. Simplify using `only [algHom_C, algebraMap_eq, eq_intCast, eq_ratCast, Int.cast_natCast, map_intCast]`.

Rewrite using `[Rat.cast_def]`. Clear the denominators using the available nonvanishing facts. Consider the case `add P Q ihP ihQ`. Take `⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩` from `ihP`. Take `⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩` from `ihQ`.

Use `⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, fun R _ _ v hv => ?_⟩` and prove the remaining obligations. Use `MvPolynomial.IsHomogeneous.add ?_ ?_` and prove the remaining obligations. Use `((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, e₁ R v hv, e₂ R v hv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X P i ih`. Take `⟨m, n, G, hm, hG, e⟩` from `ih`. Use `⟨m, n + 1, G * X i, hm, hG.mul (isHomogeneous_X ℤ i), fun R _ _ v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, aeval_X, e R v hv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_homog_poly {σ : Type} (c₀ : σ) (P : MvPolynomial σ ℚ) :
    ∃ (m : ℤ) (n : ℕ) (H : MvPolynomial σ ℤ), m ≠ 0 ∧ H.IsHomogeneous n ∧
      ∀ (R : Type) [Field R] [CharZero R] (v : σ → R), v c₀ = 1 → aeval v H = (m : R) * aeval v P := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, fun R _ _ v _ => ?_⟩
    have hd : (q.den : R) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [algHom_C, algebraMap_eq, eq_intCast, eq_ratCast, Int.cast_natCast, map_intCast]
    rw [Rat.cast_def]
    field_simp
  | add P Q ihP ihQ =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihP
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihQ
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_,
      fun R _ _ v hv => ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add, map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, e₁ R v hv,
        e₂ R v hv]
      push_cast
      ring
  | mul_X P i ih =>
    obtain ⟨m, n, G, hm, hG, e⟩ := ih
    refine ⟨m, n + 1, G * X i, hm, hG.mul (isHomogeneous_X ℤ i), fun R _ _ v hv => ?_⟩
    simp only [map_mul, aeval_X, e R v hv]
    ring

/- English proof (translation)
Use `choose m₀ n₀ H₀ h1 h2 h3 using fun i => exists_homog_poly c₀ (P i)`. Use `⟨∏ i, m₀ i, ∑ i, n₀ i, fun i => C (∏ j ∈ Finset.univ.erase i, m₀ j) * X c₀ ^ (∑ j, n₀ j - n₀ i) * H₀ i, Finset.prod_ne_zero_iff.2 fun i _ => h1 i, fun i => ?_, fun R _ _ v hv i => ?_⟩` and prove the remaining obligations. Establish `hle : n₀ i ≤ ∑ j, n₀ j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use `((isHomogeneous_C σ (∏ j ∈ Finset.univ.erase i, m₀ j)).mul ((isHomogeneous_X ℤ c₀).pow (∑ j, n₀ j - n₀ i))).mul (h2 i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use linear arithmetic over natural numbers and integers. Establish `e : (∏ j, m₀ j) = (∏ j ∈ Finset.univ.erase i, m₀ j) * m₀ i` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm`. Simplify using `only [map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, h3 i R v hv, e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_homog_family {σ κ : Type} [Fintype κ] (c₀ : σ) (P : κ → MvPolynomial σ ℚ) :
    ∃ (m : ℤ) (n : ℕ) (H : κ → MvPolynomial σ ℤ), m ≠ 0 ∧ (∀ i, (H i).IsHomogeneous n) ∧
      ∀ (R : Type) [Field R] [CharZero R] (v : σ → R), v c₀ = 1 →
        ∀ i, aeval v (H i) = (m : R) * aeval v (P i) := by
  classical
  choose m₀ n₀ H₀ h1 h2 h3 using fun i => exists_homog_poly c₀ (P i)
  refine ⟨∏ i, m₀ i, ∑ i, n₀ i, fun i => C (∏ j ∈ Finset.univ.erase i, m₀ j) * X c₀ ^ (∑ j, n₀ j - n₀ i) * H₀ i,
    Finset.prod_ne_zero_iff.2 fun i _ => h1 i, fun i => ?_, fun R _ _ v hv i => ?_⟩
  · have hle : n₀ i ≤ ∑ j, n₀ j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := ((isHomogeneous_C σ (∏ j ∈ Finset.univ.erase i, m₀ j)).mul
      ((isHomogeneous_X ℤ c₀).pow (∑ j, n₀ j - n₀ i))).mul (h2 i)
    convert this using 1
    omega
  · have e : (∏ j, m₀ j) = (∏ j ∈ Finset.univ.erase i, m₀ j) * m₀ i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    simp only [map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, h3 i R v hv, e]
    push_cast
    ring

/- English proof (translation)
Set `f : MvPolynomial σ ℚ →ₐ[ℚ] Algebra.adjoin ℚ (Set.range r)` to `aeval fun j => ⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩`. Establish `hcoe : ∀ P, ((f P : Algebra.adjoin ℚ (Set.range r)) : Ω) = aeval r P` using `fun P => by`. Use `comp_aeval_apply (R := ℚ) (fun j => (⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ : Algebra.adjoin ℚ (Set.range r))) (Algebra.adjoin ℚ (Set.range r)).val P` as an intermediate fact. Simplify `this` using `[f]`. Establish `hf : Function.Surjective f`.

Introduce and unpack `⟨t, ht⟩`. Rewrite `ht` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨P, rfl⟩` from `ht`. Conclude with `⟨P, Subtype.ext (hcoe P)⟩`. Establish `hle : RingHom.ker f.toRingHom ≤ RingHom.ker (aeval w : MvPolynomial σ ℚ →ₐ[ℚ] ℂ).toRingHom`.

Introduce `P hP`. Establish `h0 : f P = 0` using `hP`. Establish `h1 : aeval r P = 0` using `by rw [← hcoe, h0]; rfl`. Conclude with `hker P h1`. Set `ψ` to `f.toRingHom.liftOfSurjective hf ⟨_, hle⟩`.

Use `⟨ψ, fun P t ht => ?_⟩` and prove the remaining obligations. Establish `e : t = f P` using `Subtype.ext (by rw [ht, hcoe])`. Rewrite using `[e]`. Conclude with `RingHom.liftOfRightInverse_comp_apply _ _ _ _ P`.
-/
theorem exists_adjoin_hom {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (w : σ → ℂ)
    (hker : ∀ P : MvPolynomial σ ℚ, aeval r P = 0 → aeval w P = 0) :
    ∃ ψ : Algebra.adjoin ℚ (Set.range r) →+* ℂ, ∀ (P : MvPolynomial σ ℚ) (t : Algebra.adjoin ℚ (Set.range r)),
      (t : Ω) = aeval r P → ψ t = aeval w P := by
  let f : MvPolynomial σ ℚ →ₐ[ℚ] Algebra.adjoin ℚ (Set.range r) :=
    aeval fun j => ⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  have hcoe : ∀ P, ((f P : Algebra.adjoin ℚ (Set.range r)) : Ω) = aeval r P := fun P => by
    have := comp_aeval_apply (R := ℚ) (fun j => (⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ : Algebra.adjoin ℚ (Set.range r)))
      (Algebra.adjoin ℚ (Set.range r)).val P
    simpa [f] using this
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at ht
    obtain ⟨P, rfl⟩ := ht
    exact ⟨P, Subtype.ext (hcoe P)⟩
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker (aeval w : MvPolynomial σ ℚ →ₐ[ℚ] ℂ).toRingHom := by
    intro P hP
    have h0 : f P = 0 := hP
    have h1 : aeval r P = 0 := by rw [← hcoe, h0]; rfl
    exact hker P h1
  let ψ := f.toRingHom.liftOfSurjective hf ⟨_, hle⟩
  refine ⟨ψ, fun P t ht => ?_⟩
  have e : t = f P := Subtype.ext (by rw [ht, hcoe])
  rw [e]
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ P

/- English proof (translation)
Establish `hx : x ≠ 0` using `fun h => hc₀ (by simp [h])`. Take `⟨hred, hdom⟩` from `closure_facts x hx`. Use `set p := point ℚ x hx with hp`. Establish `hπ : p.toImage ≫ p.imageι = point ℚ x hx` using `Scheme.Hom.toImage_imageι p`. Take `⟨hW₀, h₀, hA₀⟩` from `chart_single p.imageι p.toImage x hx hπ c₀ hc₀`.

Take `⟨σ₀, hσ₀, hb₀⟩` from `form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG`. Establish `hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀`. Take `⟨G', rfl⟩` from `hdiv`. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `inf_le_left`.

Use `set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef`. Establish `hUb : p.image.basicOpen σ₀ = U`. Rewrite using `[hb₀]`. Conclude with `inf_eq_right.2 (p.imageι.preimage_mono hsub)`. Establish `hval : valR p.toImage _ σ₀ = g₀` using `by rw [hσ₀, hg₀]`.

Establish `hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U`. Rewrite using `[← hUb, le_preimage_basicOpen_iff _ h₀, hval]`. Conclude with `isUnit_iff_ne_zero.2 (by simpa using h0)`. Establish `hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N)`. Use `smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm` as an intermediate fact.

Rewrite `this` using `[hUb]`. Then use the resulting hypothesis. Establish `hdense : Dense (U : Set p.image)`. Use `p.toImage.denseRange.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hUtop (Set.mem_univ y)`.

Take `⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩` from `hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩`. Take `⟨ζ, hζ, hdomζ, hζU⟩` from `lift_generic p.toImage f U hd hUtop`. Take `⟨x', hx', hp₂⟩` from `exists_coords (ζ ≫ j ≫ pullback.snd _ _)`. Establish `hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx`. Rewrite using `[← hf, reassoc_of% hζ, hπ]`.

Establish `: Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N)` using `hsm.smooth`. Establish `hredX' : IsReduced X'` using `GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)`. Use `⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_, fun ψ hψ => ?_⟩` and prove the remaining obligations. Establish `hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l)` using `le_preimage_chart (by simpa using hp₂) hl`. Use `val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)` as an intermediate fact.

Rewrite `this` using `[valR_pullRatio (by simpa using hp₂) hW]`. Then use the resulting hypothesis. Take `⟨hWa, hW, hAW⟩` from `prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl`. Take `⟨σ, hσ, hb⟩` from `form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG`. Rewrite using `[← hσ]`. Use `snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_` and prove the remaining obligations.

Rewrite using `[hb]`. Establish `e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t)`. Rewrite using `[← hf]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `h ⟨-, h2⟩`. Conclude with `h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)`. Introduce `h h2`. Conclude with `h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩`. Conclude with `local_of_hom p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ σ₀ hUb g₀ hval.symm (j ≫ pullback.snd _ _) x' hx' hp₂ ψ hψ`.
-/
theorem snc_of_res_local {Ω : Type} [Field Ω] [CharZero Ω] (hR : ResKStatement) (N e d : ℕ) (x : Fin (N + 1) → Ω)
    (c₀ : Fin (N + 1)) (hc₀ : x c₀ ≠ 0)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G.IsHomogeneous (d + 1)) (hdiv : (X c₀ : MvPolynomial _ ℚ) ∣ G)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀))
    (hg₀ : (g₀ : Ω) = aeval (fun j => x j / x c₀) G) (h0 : g₀ ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    ∃ (r : ℕ) (x' : Fin (r + 1) → Ω), x' ≠ 0 ∧
      (∀ i l, x' l ≠ 0 → x' i / x' l ∈
        IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) : Subalgebra ℚ Ω) : Set Ω)) ∧
      (∀ a l, x a ≠ 0 → x' l ≠ 0 →
        SncChart (Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l))) e
          (aeval (fun j => x j / x a) G)) ∧
      ∀ ψ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) →+* ℂ, ψ g₀ ≠ 0 →
        ∃ l, x' l ≠ 0 ∧ ∃ b : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀), ψ b ≠ 0 ∧
          ∀ i, ∃ a : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀), x' i / x' l * (b : Ω) = a := by
  have hx : x ≠ 0 := fun h => hc₀ (by simp [h])
  obtain ⟨hred, hdom⟩ := closure_facts x hx
  set p := point ℚ x hx with hp
  have hπ : p.toImage ≫ p.imageι = point ℚ x hx := Scheme.Hom.toImage_imageι p
  obtain ⟨hW₀, h₀, hA₀⟩ := chart_single p.imageι p.toImage x hx hπ c₀ hc₀
  obtain ⟨σ₀, hσ₀, hb₀⟩ := form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG
  have hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀ := by
    obtain ⟨G', rfl⟩ := hdiv
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef
  have hUb : p.image.basicOpen σ₀ = U := by
    rw [hb₀]
    exact inf_eq_right.2 (p.imageι.preimage_mono hsub)
  have hval : valR p.toImage _ σ₀ = g₀ := by rw [hσ₀, hg₀]
  have hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U := by
    rw [← hUb, le_preimage_basicOpen_iff _ h₀, hval]
    exact isUnit_iff_ne_zero.2 (by simpa using h0)
  have hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N) := by
    have := smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm
    rwa [hUb] at this
  have hdense : Dense (U : Set p.image) := by
    refine p.toImage.denseRange.mono ?_
    rintro _ ⟨y, rfl⟩
    exact hUtop (Set.mem_univ y)
  obtain ⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩ := hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩
  obtain ⟨ζ, hζ, hdomζ, hζU⟩ := lift_generic p.toImage f U hd hUtop
  obtain ⟨x', hx', hp₂⟩ := exists_coords (ζ ≫ j ≫ pullback.snd _ _)
  have hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx := by
    rw [← hf, reassoc_of% hζ, hπ]
  have : Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N) := hsm.smooth
  have hredX' : IsReduced X' := GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)
  refine ⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_, fun ψ hψ => ?_⟩
  · have hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) := le_preimage_chart (by simpa using hp₂) hl
    have := val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW
      (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)
    rwa [valR_pullRatio (by simpa using hp₂) hW] at this
  · obtain ⟨hWa, hW, hAW⟩ := prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl
    obtain ⟨σ, hσ, hb⟩ := form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG
    rw [← hσ]
    refine snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_
    rw [hb]
    have e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t) := by
      rw [← hf]
      rfl
    constructor
    · rintro h ⟨-, h2⟩
      exact h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)
    · intro h h2
      exact h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩
  · exact local_of_hom p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ σ₀ hUb g₀ hval.symm (j ≫ pullback.snd _ _) x' hx' hp₂ ψ hψ

section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.SegreChart (segForm aeval_segForm segForm_multiHomog)
open GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm (aeval_const_mul)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
The claim follows from `funext fun j => (mul_div_cancel₀ _ h0).symm`.
-/
theorem seg_eq_mul {F : Type} [Field F] (v : (Σ k, ι k) → F) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (c₀ : Fin (N + 1)) (h0 : (∏ k, v ⟨k, E c₀ k⟩) ≠ 0) :
    (fun j => ∏ k, v ⟨k, E j k⟩) =
      fun j => (∏ k, v ⟨k, E c₀ k⟩) * ((∏ k, v ⟨k, E j k⟩) / ∏ k, v ⟨k, E c₀ k⟩) :=
  funext fun j => (mul_div_cancel₀ _ h0).symm

/- English proof (translation)
Establish `h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hc k`. Take `⟨m, n, H, hm, hH, e⟩` from `exists_homog_poly c₀ P`. Establish `e₁` using `e Ω (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) (div_self h0)`. Establish `e₂` using `e ℂ (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (div_self hz0)`. Rewrite `e₁` using `[hP, mul_zero]`.

Establish `hy : aeval y (segForm E H) = 0`. Rewrite using `[aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul hH, e₁, mul_zero]`. Establish `hmem : segForm E H ∈ mCoordIdeal y` using `(form_mem_mCoordIdeal_iff y (segForm_multiHomog E hH)).2 hy`. Establish `hZ` using `hz.2 _ hmem`. Rewrite `hZ` using `[GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul hH]`.

Establish `h2` using `(mul_eq_zero.1 hZ).resolve_left (pow_ne_zero _ hz0)`. Rewrite `h2` using `[e₂]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hm)`.
-/
theorem ker_ratio (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hz0 : (∏ k, z ⟨k, E c₀ k⟩) ≠ 0) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (hP : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) P = 0) :
    aeval (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) P = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨m, n, H, hm, hH, e⟩ := exists_homog_poly c₀ P
  have e₁ := e Ω (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) (div_self h0)
  have e₂ := e ℂ (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (div_self hz0)
  rw [hP, mul_zero] at e₁
  have hy : aeval y (segForm E H) = 0 := by
    rw [aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul hH, e₁, mul_zero]
  have hmem : segForm E H ∈ mCoordIdeal y := (form_mem_mCoordIdeal_iff y (segForm_multiHomog E hH)).2 hy
  have hZ := hz.2 _ hmem
  rw [GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul hH] at hZ
  have h2 := (mul_eq_zero.1 hZ).resolve_left (pow_ne_zero _ hz0)
  rw [e₂] at h2
  exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hm)

/- English proof (translation)
Establish `h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hc k`. Establish `hZne : aeval (fun j => ∏ k, z ⟨k, E j k⟩) Gz ≠ 0`. Rewrite `hne` using `[evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm]`. Then use the resulting hypothesis. Establish `hz0 : (∏ k, z ⟨k, E c₀ k⟩) ≠ 0`. Take `⟨G', rfl⟩` from `hdiv`.

Introduce `h`. Apply `hZne` to reduce the goal to its premises. Rewrite using `[map_mul, aeval_X, h, zero_mul]`. Take `⟨ψ, hψ⟩` from `exists_adjoin_hom (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (fun P hP => ker_ratio y E c₀ hc hz hz0 P hP)`. Establish `hψg : ψ g₀ ≠ 0`.

Rewrite using `[hψ (map (algebraMap ℤ ℚ) Gz) g₀ (by rw [hg₀, aeval_map_algebraMap]), aeval_map_algebraMap]`. Introduce `h`. Apply `hZne` to reduce the goal to its premises. Rewrite using `[seg_eq_mul z E c₀ hz0, aeval_const_mul hG, h, mul_zero]`. Take `⟨l, hl, b, hb, hi⟩` from `hloc ψ hψg`.

Use `choose a ha using hi`. Establish `hsurj : ∀ t : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), ∃ P : MvPolynomial (Fin (N + 1)) ℚ, (t : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) P`. Introduce and unpack `⟨t, ht⟩`. Rewrite `ht` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨P, rfl⟩` from `ht`.

Conclude with `⟨P, rfl⟩`. Use `choose P hP using hsurj`. Take `⟨m, n, H, hm, hH, e⟩` from `exists_homog_family c₀ (fun i => P (a i))`. Establish `hv : ∀ i, aeval y (segForm E (H i)) = (∏ k, y ⟨k, E c₀ k⟩) ^ n * ((m : Ω) * (x' i / x' l * (b : Ω)))` using `fun i => by`. Rewrite using `[aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul (hH i), e Ω _ (div_self h0) i, ← hP, ← ha i]`.

Use `⟨fun i => segForm E (H i), fun _ => n, fun i => segForm_multiHomog E (hH i), fun i j => ?_, l, ?_⟩` and prove the remaining obligations. Simplify using `only [hv]`. Clear the denominators using the available nonvanishing facts. Establish `hal : a l = b` using `Subtype.ext (by rw [← ha l, div_self hl, one_mul])`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm`.

Rewrite using `[evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul (hH l), e ℂ _ (div_self hz0) l, ← hψ _ (a l) (hP _), hal]`. Conclude with `mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero hm' hb)`.
-/
theorem exists_forms (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (hG : Gz.IsHomogeneous (d + 1))
    (hdiv : (X c₀ : MvPolynomial _ ℤ) ∣ Gz)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩))
    (hg₀ : (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz) {M : ℕ} (x' : Fin M → Ω)
    (hloc : ∀ ψ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) →+* ℂ, ψ g₀ ≠ 0 →
      ∃ l, x' l ≠ 0 ∧ ∃ b : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), ψ b ≠ 0 ∧
        ∀ i, ∃ a : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩),
          x' i / x' l * (b : Ω) = a)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hne : evC z (segForm E Gz) ≠ 0) :
    ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧
      (∀ i j, x' i * aeval y (G j) = x' j * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0 := by
  classical
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hZne : aeval (fun j => ∏ k, z ⟨k, E j k⟩) Gz ≠ 0 := by
    rwa [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm] at hne
  have hz0 : (∏ k, z ⟨k, E c₀ k⟩) ≠ 0 := by
    obtain ⟨G', rfl⟩ := hdiv
    intro h
    apply hZne
    rw [map_mul, aeval_X, h, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_adjoin_hom (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)
    (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (fun P hP => ker_ratio y E c₀ hc hz hz0 P hP)
  have hψg : ψ g₀ ≠ 0 := by
    rw [hψ (map (algebraMap ℤ ℚ) Gz) g₀ (by rw [hg₀, aeval_map_algebraMap]), aeval_map_algebraMap]
    intro h
    apply hZne
    rw [seg_eq_mul z E c₀ hz0, aeval_const_mul hG, h, mul_zero]
  obtain ⟨l, hl, b, hb, hi⟩ := hloc ψ hψg
  choose a ha using hi
  have hsurj : ∀ t : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩),
      ∃ P : MvPolynomial (Fin (N + 1)) ℚ, (t : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) P := by
    rintro ⟨t, ht⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at ht
    obtain ⟨P, rfl⟩ := ht
    exact ⟨P, rfl⟩
  choose P hP using hsurj
  obtain ⟨m, n, H, hm, hH, e⟩ := exists_homog_family c₀ (fun i => P (a i))
  have hv : ∀ i, aeval y (segForm E (H i)) =
      (∏ k, y ⟨k, E c₀ k⟩) ^ n * ((m : Ω) * (x' i / x' l * (b : Ω))) := fun i => by
    rw [aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul (hH i), e Ω _ (div_self h0) i, ← hP, ← ha i]
  refine ⟨fun i => segForm E (H i), fun _ => n, fun i => segForm_multiHomog E (hH i), fun i j => ?_, l, ?_⟩
  · simp only [hv]
    field_simp
  · have hal : a l = b := Subtype.ext (by rw [← ha l, div_self hl, one_mul])
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul (hH l),
      e ℂ _ (div_self hz0) l, ← hψ _ (a l) (hP _), hal]
    exact mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero hm' hb)

/- English proof (translation)
Introduce `hR K _ ι _ Ω _ _ y e β b hA hb hβ`. Take `⟨-, ⟨-, -, hrel⟩, -, -⟩` from `id hA`. Use `choose c hc using hrel`. Establish `hc' : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hc k (by`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])`.

Establish `: Nonempty ((k : K) → ι k)` using `⟨c⟩`. Take `⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1` from `Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero`. Set `E : Fin (N + 1) ≃ ((k : K) → ι k)` to `(Fintype.equivFinOfCardEq hN).symm`. Set `c₀` to `E.symm c`. Establish `hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0` using `fun k => by simpa [c₀] using hc' k`.

Take `⟨s, hs, hsm⟩` from `exists_smooth y e hA N E c₀ hE`. Take `⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩` from `exists_form y e β b hb hβ N E c₀ hE s hs`. Set `x : Fin (N + 1) → Ω` to `fun j => ∏ k, y ⟨k, E j k⟩`. Establish `hx₀ : x c₀ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hE k`. Set `G` to `map (algebraMap ℤ ℚ) Gz`.

Take `⟨r, x', hx', hF, hch, hloc⟩` from `snc_of_res_local hR N e d x c₀ hx₀ G (hG.map _) (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀ (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0`. Establish `h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0`. Introduce `h`. Establish `h1 : aeval (fun j => x j / x c₀) Gz = 0`. Simplify using `only [div_eq_inv_mul]`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]`. Conclude with `mul_eq_zero_of_right _ h`. Conclude with `hg0 (Subtype.ext (hg₀.trans h1))`. Establish `hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈ Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}` using `Ideal.subset_span rfl`. Establish `hev : ∀ z : (Σ k, ι k) → ℂ, evC z (segForm E Gz) = eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz)` using `fun z => by`.

Rewrite using `[evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm]`. Use `⟨segForm E Gz, fun _ => d + 1, r + 1, fun p => x' p.2, Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, segForm_multiHomog E hG, ?_, fun z hz' hb' => (hev z).trans (hz z hz' hb'), ?_, GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt y x' f …` and prove the remaining obligations. Introduce `hin`. Establish `h1` using `GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem y hin`. Rewrite `h1` using `[aeval_segForm]`.

Conclude with `h0 h1`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hx'`. Conclude with `⟨i, hi⟩`. Use `⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `f rfl`.

Conclude with `⟨_, GlobalTheory.CompanionTheory.Ar.SegreChart.multiHomog_rename_inl (segForm_multiHomog E hG)⟩`. Introduce `hle`. Establish `h1` using `GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem _ (hle hmem)`. Rewrite `h1` using `[aeval_rename, GlobalTheory.CompanionTheory.Ar.SegreChart.joinVec_comp_inl, aeval_segForm]`. Conclude with `h0 h1`.
-/
theorem exists_snc_model_iso : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (β' : MRing ι) (b' : K → ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), IsMultiHomog β' b' ∧ β' ∉ mCoordIdeal y ∧ (∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → evC z β' = 0) ∧ (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β') = 0 → z ∈ mcPts J) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β' ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0 := by
  intro hR K _ ι _ Ω _ _ y e β b hA hb hβ
  classical
  obtain ⟨-, ⟨-, -, hrel⟩, -, -⟩ := id hA
  choose c hc using hrel
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  have : Nonempty ((k : K) → ι k) := ⟨c⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let E : Fin (N + 1) ≃ ((k : K) → ι k) := (Fintype.equivFinOfCardEq hN).symm
  let c₀ := E.symm c
  have hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0 := fun k => by simpa [c₀] using hc' k
  obtain ⟨s, hs, hsm⟩ := exists_smooth y e hA N E c₀ hE
  obtain ⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩ := exists_form y e β b hb hβ N E c₀ hE s hs
  let x : Fin (N + 1) → Ω := fun j => ∏ k, y ⟨k, E j k⟩
  have hx₀ : x c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hE k
  let G := map (algebraMap ℤ ℚ) Gz
  obtain ⟨r, x', hx', hF, hch, hloc⟩ := snc_of_res_local hR N e d x c₀ hx₀ G (hG.map _)
    (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀
    (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0
  have h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0 := by
    intro h
    have h1 : aeval (fun j => x j / x c₀) Gz = 0 := by
      simp only [div_eq_inv_mul]
      rw [GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]
      exact mul_eq_zero_of_right _ h
    exact hg0 (Subtype.ext (hg₀.trans h1))
  have hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈
      Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)} :=
    Ideal.subset_span rfl
  have hev : ∀ z : (Σ k, ι k) → ℂ, evC z (segForm E Gz) =
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) := fun z => by
    rw [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm]
  refine ⟨segForm E Gz, fun _ => d + 1, r + 1, fun p => x' p.2,
    Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, segForm_multiHomog E hG, ?_,
    fun z hz' hb' => (hev z).trans (hz z hz' hb'), ?_,
    GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt y x' fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl), ?_, ?_,
    GlobalTheory.CompanionTheory.Ar.SegreChart.isSncModel_joinPt y x' e E Gz fun a l ha hl => hch a l ha hl,
    fun z hz' hb' => GlobalTheory.CompanionTheory.Ar.SegreChart.mem_mcPts_span y x' (segForm E Gz) E Gz
      (fun w _ hw => (hev w).symm.trans hw) z hz' hb',
    fun z hz' hne => exists_forms y E c₀ hE d Gz hG hdiv g₀ hg₀ x' hloc hz' hne⟩
  · intro hin
    have h1 := GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem y hin
    rw [aeval_segForm] at h1
    exact h0 h1
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
    exact ⟨i, hi⟩
  · refine ⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩
    rintro f rfl
    exact ⟨_, GlobalTheory.CompanionTheory.Ar.SegreChart.multiHomog_rename_inl (segForm_multiHomog E hG)⟩
  · intro hle
    have h1 := GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem _ (hle hmem)
    rw [aeval_rename, GlobalTheory.CompanionTheory.Ar.SegreChart.joinVec_comp_inl, aeval_segForm] at h1
    exact h0 h1
end Top

end GlobalTheory.CompanionTheory.Ar.Giv
