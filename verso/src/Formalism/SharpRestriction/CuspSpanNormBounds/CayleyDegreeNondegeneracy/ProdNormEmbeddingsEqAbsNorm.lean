import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace
import Formalism.ThetaLiftIndependence.Statement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory Module

section Count

variable (K : Type) [Field K] [NumberField K]

/- English proof (translation)
Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ a`. Establish `h2 : ∏ φ : K →+* ℂ, φ a = ∏ σ : K →ₐ[ℚ] ℂ, σ a` using `Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)`. Rewrite using `[← norm_prod, h2, ← h]`. Simplify using the standard rewrite rules.
-/
theorem prod_norm_embeddings_eq_abs_norm_alt (a : K) : ∏ φ : K →+* ℂ, ‖φ a‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have h2 : ∏ φ : K →+* ℂ, φ a = ∏ σ : K →ₐ[ℚ] ℂ, σ a :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [← norm_prod, h2, ← h]
  simp

/- English proof (translation)
Rewrite using `[← Algebra.coe_norm_int a]`. Establish `h0 : Algebra.norm ℤ a ≠ 0`. Rewrite using `[Ne, Algebra.norm_eq_zero_iff]`. Conclude with `ha`. Establish `h1 : (1 : ℤ) ≤ |Algebra.norm ℤ a|` using `Int.one_le_abs h0`.

Conclude with `h1` after adjusting the coercions.
-/
theorem one_le_abs_norm_of_ne_zero_alt (a : 𝓞 K) (ha : a ≠ 0) : (1 : ℝ) ≤ |((Algebra.norm ℚ (a : K) : ℚ) : ℝ)| := by
  rw [← Algebra.coe_norm_int a]
  have h0 : Algebra.norm ℤ a ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact ha
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs h0
  exact_mod_cast h1

def boundedIntegers (B : ℝ) : Set (𝓞 K) := {a | ∀ φ : K →+* ℂ, ‖φ (a : K)‖ ≤ B}

/- English proof (translation)
Set `emb : 𝓞 K →+ ((K →+* ℂ) → ℂ)` to `{ toFun := fun a φ => φ (a : K) map_zero' := by ext; simp map_add' := by intros; ext; simp }`. Establish `hinj : Function.Injective emb`. Introduce `a b hab`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `h1 : φ (a : K) = φ (b : K)` using `congrFun hab φ`.

Conclude with `RingOfIntegers.ext (φ.injective h1)`. Establish `hmin : ∀ x ∈ emb.range, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖`. Introduce and unpack `x ⟨a, rfl⟩ hx`. Establish `ha : a ≠ 0` using `by rintro rfl; exact hx (map_zero _)`. Use `show 1 ≤ ∏ v : K →+* ℂ, ‖v (a : K)‖`.

Rewrite using `[prod_norm_embeddings_eq_abs_norm_alt]`. Conclude with `one_le_abs_norm_of_ne_zero_alt K a ha`. Take `⟨hfin, hcard, -⟩` from `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.boxCountO (K →+* ℂ) emb.range (fun _ => B) (fun _ => hB) hmin`. Establish `himg : emb '' (boundedIntegers K B) = {x | x ∈ emb.range ∧ ∀ v, ‖x v‖ ≤ B}`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, rfl⟩, ha⟩`. Introduce and unpack `⟨⟨a, rfl⟩, ha⟩`. Conclude with `⟨a, ha, rfl⟩`.

Establish `hf : (boundedIntegers K B).Finite` using `Set.Finite.of_finite_image (himg ▸ hfin) hinj.injOn`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite using `[← Set.ncard_image_of_injective _ hinj, himg]`. Use `hcard.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card, ← pow_mul]`.
-/
theorem boundedIntegers_finite_card_le (B : ℝ) (hB : 0 < B) :
    (boundedIntegers K B).Finite ∧ ((boundedIntegers K B).ncard : ℝ) ≤ (1 + 2 * B) ^ (2 * finrank ℚ K) := by
  classical
  let emb : 𝓞 K →+ ((K →+* ℂ) → ℂ) :=
    { toFun := fun a φ => φ (a : K)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hinj : Function.Injective emb := by
    intro a b hab
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 : φ (a : K) = φ (b : K) := congrFun hab φ
    exact RingOfIntegers.ext (φ.injective h1)
  have hmin : ∀ x ∈ emb.range, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖ := by
    rintro x ⟨a, rfl⟩ hx
    have ha : a ≠ 0 := by rintro rfl; exact hx (map_zero _)
    show 1 ≤ ∏ v : K →+* ℂ, ‖v (a : K)‖
    rw [prod_norm_embeddings_eq_abs_norm_alt]; exact one_le_abs_norm_of_ne_zero_alt K a ha
  obtain ⟨hfin, hcard, -⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.boxCountO (K →+* ℂ) emb.range (fun _ => B) (fun _ => hB) hmin
  have himg : emb '' (boundedIntegers K B) = {x | x ∈ emb.range ∧ ∀ v, ‖x v‖ ≤ B} := by
    ext x; constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩; exact ⟨a, ha, rfl⟩
  have hf : (boundedIntegers K B).Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj.injOn
  refine ⟨hf, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj, himg]
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card, ← pow_mul]

abbrev scaledFreeModule (d : 𝓞 K) : Submodule (𝓞 K) (Fin 2 → 𝓞 K) :=
  Ideal.span {d} • (⊤ : Submodule (𝓞 K) (Fin 2 → 𝓞 K))

/- English proof (translation)
Establish `hI : Ideal.span {d} ≠ (⊥ : Ideal (𝓞 K))`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hd`. Establish `hc` using `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K (Fin 2 → 𝓞 K) (Ideal.span {d}) hI`. Rewrite `hc` using `[Module.finrank_fin_fun, Ideal.absNorm_span_singleton]`.

Establish `h0 : Algebra.norm ℤ d ≠ 0`. Rewrite using `[Ne, Algebra.norm_eq_zero_iff]`. Conclude with `hd`. Establish `hpos : Nat.card ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) ≠ 0`. Rewrite using `[hc]`.

Conclude with `pow_ne_zero _ (Int.natAbs_ne_zero.2 h0)`. Establish `: Finite ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)` using `Nat.finite_of_card_ne_zero hpos`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `h1 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤`. Establish `h2` using `(Pi.basisFun (𝓞 K) (Fin 2)).span_eq`.

Establish `h3 : (⇑(Pi.basisFun (𝓞 K) (Fin 2))) = fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K)`. Use function extensionality and compare the values at `i`. Conclude with `Pi.basisFun_apply _ _ i`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Establish `h4 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 => (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤`.

Establish `h5 : Set.range (fun i : Fin 2 => (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K)) = (scaledFreeModule K d).mkQ '' Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K))`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h5, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]`. Establish `h6` using `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2b.1 (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) 2 _ h4`.

Rewrite `h6` using `[hc]`. Then use the resulting hypothesis.
-/
theorem card_submodules_quotient_le (d : 𝓞 K) (hd : d ≠ 0) :
    Finite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ∧
    Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ≤ ((Algebra.norm ℤ d).natAbs ^ 2) ^ 2 := by
  have hI : Ideal.span {d} ≠ (⊥ : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd
  have hc := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K (Fin 2 → 𝓞 K) (Ideal.span {d}) hI
  rw [Module.finrank_fin_fun, Ideal.absNorm_span_singleton] at hc
  have h0 : Algebra.norm ℤ d ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hd
  have hpos : Nat.card ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) ≠ 0 := by
    rw [hc]; exact pow_ne_zero _ (Int.natAbs_ne_zero.2 h0)
  have : Finite ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) := Nat.finite_of_card_ne_zero hpos
  refine ⟨inferInstance, ?_⟩
  have h1 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤ := by
    have h2 := (Pi.basisFun (𝓞 K) (Fin 2)).span_eq
    have h3 : (⇑(Pi.basisFun (𝓞 K) (Fin 2))) = fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K) := by
      funext i; exact Pi.basisFun_apply _ _ i
    rwa [h3] at h2
  have h4 : Submodule.span (𝓞 K) (Set.range (fun i : Fin 2 =>
      (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K))) = ⊤ := by
    have h5 : Set.range (fun i : Fin 2 => (scaledFreeModule K d).mkQ (Pi.single i 1 : Fin 2 → 𝓞 K)) =
        (scaledFreeModule K d).mkQ '' Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → 𝓞 K)) := by
      rw [← Set.range_comp]; rfl
    rw [h5, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have h6 := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2b.1 (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d) 2 _ h4
  rwa [hc] at h6

end Count

section Geo

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)

/- English proof (translation)
Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hxy, hyx, starRingEnd_apply, RingHom.id_apply, mul_zero, add_zero, zero_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_comb_orthogonal_pair (x y : V) (hxy : h x y = 0) (hyx : h y x = 0) (a c a' c' : K) :
    h (a • x + c • y) (a' • x + c' • y) = star a * a' * h x x + star c * c' * h y y := by
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hxy, hyx,
    starRingEnd_apply, RingHom.id_apply, mul_zero, add_zero, zero_add]
  ring

/- English proof (translation)
Take `⟨e, hli, hsp, -, horth⟩` from `hL`. Establish `hv' : v ∈ Submodule.span K (Set.range e)` using `by rw [hsp]; trivial`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hv'`. Rewrite `hv`, the goal using `[Fin.sum_univ_two]`. Establish `h01 : h (e 0) (e 1) = 0` using `by rw [horth]; simp`.

Establish `h10 : h (e 1) (e 0) = 0` using `by rw [horth]; simp`. Rewrite `hv` using `[inner_comb_orthogonal_pair h _ _ h01 h10, horth, horth]`. Simplify using `only [if_true, mul_one] at hv`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `h2` using `congrArg φ hv`.

Rewrite `h2` using `[map_add, map_mul, map_mul, hK.2.1, hK.2.1, map_zero]`. Establish `h3 : ((Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) : ℝ) : ℂ) = 0` using `by push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; exact h2`. Establish `h4 : Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) = 0` using `by exact_mod_cast h3`. Establish `h5` using `Complex.normSq_nonneg (φ (c 0))`. Establish `h6` using `Complex.normSq_nonneg (φ (c 1))`.

Establish `h7 : Complex.normSq (φ (c 0)) = 0` using `by linarith`. Establish `h8 : Complex.normSq (φ (c 1)) = 0` using `by linarith`. Establish `c0 : c 0 = 0` using `(map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h7)`. Establish `c1 : c 1 = 0` using `(map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h8)`. Simplify using `[c0, c1]`.
-/
theorem eq_zero_of_inner_self_eq_zero (hK : IsCMUnram K) (L : Submodule (𝓞 K) V) (hL : IsOrthoLattice h L 2) (v : V)
    (hv : h v v = 0) : v = 0 := by
  obtain ⟨e, hli, hsp, -, horth⟩ := hL
  have hv' : v ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv'
  rw [Fin.sum_univ_two] at hv ⊢
  have h01 : h (e 0) (e 1) = 0 := by rw [horth]; simp
  have h10 : h (e 1) (e 0) = 0 := by rw [horth]; simp
  rw [inner_comb_orthogonal_pair h _ _ h01 h10, horth, horth] at hv
  simp only [if_true, mul_one] at hv
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h2 := congrArg φ hv
  rw [map_add, map_mul, map_mul, hK.2.1, hK.2.1, map_zero] at h2
  have h3 : ((Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) : ℝ) : ℂ) = 0 := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; exact h2
  have h4 : Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) = 0 := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (φ (c 0))
  have h6 := Complex.normSq_nonneg (φ (c 1))
  have h7 : Complex.normSq (φ (c 0)) = 0 := by linarith
  have h8 : Complex.normSq (φ (c 1)) = 0 := by linarith
  have c0 : c 0 = 0 := (map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h7)
  have c1 : c 1 = 0 := (map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h8)
  simp [c0, c1]

/- English proof (translation)
Take `⟨e, hli, hsp, -, -⟩` from `hL`. Use `finrank_eq_card_basis (Basis.mk hli hsp.ge)` as an intermediate fact. Simplify using `using this`.
-/
theorem finrank_orthonormal_plane_eq_two (L : Submodule (𝓞 K) V) (hL : IsOrthoLattice h L 2) : finrank K V = 2 := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  have := finrank_eq_card_basis (Basis.mk hli hsp.ge)
  simpa using this

/- English proof (translation)
Establish `hyx : h y x = 0` using `by rw [← hs.eq x y, hxy, map_zero]`. Establish `hli : LinearIndependent K ![x, y]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h1` using `congrArg (h x) hst`.

Establish `h2` using `congrArg (h y) hst`. Simplify using `only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add, map_zero] at h1 h2`. Conclude with `⟨(mul_eq_zero.1 h1).resolve_right hxx, (mul_eq_zero.1 h2).resolve_right hyy⟩`. Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank (by simp [hfr])`. Establish `hv : v ∈ Submodule.span K (Set.range ![x, y])` using `by rw [hsp]; trivial`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hv`. Rewrite `hc` using `[Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc`. Substitute `hc` using the available equality. Simplify using `only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]`.

Rewrite using `[mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]`.
-/
theorem eq_decomp_orthogonal_pair (hs : h.IsSymm) (hfr : finrank K V = 2) (x y : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (v : V) : v = (h x v / h x x) • x + (h y v / h y y) • y := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  have hli : LinearIndependent K ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (h x) hst
    have h2 := congrArg (h y) hst
    simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add, map_zero] at h1 h2
    exact ⟨(mul_eq_zero.1 h1).resolve_right hxx, (mul_eq_zero.1 h2).resolve_right hyy⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hfr])
  have hv : v ∈ Submodule.span K (Set.range ![x, y]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  subst hc
  simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]
  rw [mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]

def planeMapAlt (x y x' y' : V) : V →ₗ[K] V :=
  ((h x x)⁻¹ • (h x)).smulRight x' + ((h y y)⁻¹ • (h y)).smulRight y'

/- English proof (translation)
Simplify using `[planeMapAlt, div_eq_inv_mul]`.
-/
theorem planeMap_apply_alt (x y x' y' v : V) :
    planeMapAlt h x y x' y' v = (h x v / h x x) • x' + (h y v / h y y) • y' := by
  simp [planeMapAlt, div_eq_inv_mul]

/- English proof (translation)
Establish `hyx : h y x = 0` using `by rw [← hs.eq x y, hxy, map_zero]`. Rewrite using `[planeMap_apply_alt, planeMap_apply_alt]`. Simplify using `only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]`. Rewrite using `[mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]`. Conclude with `(eq_decomp_orthogonal_pair h hs hfr x' y' hxy' hxx' hyy' v).symm`.
-/
theorem planeMapAlt_alt (hs : h.IsSymm) (hfr : finrank K V = 2) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hxx' : h x' x' ≠ 0) (hyy' : h y' y' ≠ 0) (v : V) :
    planeMapAlt h x y x' y' (planeMapAlt h x' y' x y v) = v := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  rw [planeMap_apply_alt, planeMap_apply_alt]
  simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]
  rw [mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]
  exact (eq_decomp_orthogonal_pair h hs hfr x' y' hxy' hxx' hyy' v).symm

/- English proof (translation)
Establish `hyx : h y x = 0` using `by rw [← hs.eq x y, hxy, map_zero]`. Establish `hyx' : h y' x' = 0` using `by rw [← hs.eq x' y', hxy', map_zero]`. Rewrite using `[planeMap_apply_alt, planeMap_apply_alt, inner_comb_orthogonal_pair h x' y' hxy' hyx', hα, hβ]`. Use `conv_rhs => rw [eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy u, eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v]`. Rewrite using `[inner_comb_orthogonal_pair h x y hxy hyx]`.
-/
theorem planeMap_isometry (hs : h.IsSymm) (hfr : finrank K V = 2) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hα : h x' x' = h x x) (hβ : h y' y' = h y y) (u v : V) :
    h (planeMapAlt h x y x' y' u) (planeMapAlt h x y x' y' v) = h u v := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  have hyx' : h y' x' = 0 := by rw [← hs.eq x' y', hxy', map_zero]
  rw [planeMap_apply_alt, planeMap_apply_alt, inner_comb_orthogonal_pair h x' y' hxy' hyx', hα, hβ]
  conv_rhs => rw [eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy u, eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v]
  rw [inner_comb_orthogonal_pair h x y hxy hyx]

def pairCoords (x₁ y₁ : V) : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] V :=
  (LinearMap.proj 0 : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).smulRight x₁ +
    (LinearMap.proj 1 : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).smulRight y₁

/- English proof (translation)
Simplify using `[pairCoords]`.
-/
theorem pairCoords_apply (x₁ y₁ : V) (p : Fin 2 → 𝓞 K) : pairCoords x₁ y₁ p = p 0 • x₁ + p 1 • y₁ := by
  simp [pairCoords]

/- English proof (translation)
Introduce `v hv`. Take `⟨p0, hp0⟩` from `Submodule.mem_one.1 (hint x hx v hv)`. Take `⟨p1, hp1⟩` from `Submodule.mem_one.1 (hint y hy v hv)`. Use `⟨![p0, p1], ?_⟩` and prove the remaining obligations. Rewrite using `[pairCoords_apply]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Rewrite using `[← algebraMap_smul K p0, ← algebraMap_smul K p1, hp0, hp1, smul_smul, smul_smul, ← div_eq_mul_inv, ← div_eq_mul_inv]`. Conclude with `(eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v).symm`.
-/
theorem le_range_of_orthogonal_pair (hs : h.IsSymm) (hfr : finrank K V = 2) (M : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) : M ≤ LinearMap.range (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by
  intro v hv
  obtain ⟨p0, hp0⟩ := Submodule.mem_one.1 (hint x hx v hv)
  obtain ⟨p1, hp1⟩ := Submodule.mem_one.1 (hint y hy v hv)
  refine ⟨![p0, p1], ?_⟩
  rw [pairCoords_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← algebraMap_smul K p0, ← algebraMap_smul K p1, hp0, hp1, smul_smul, smul_smul, ← div_eq_mul_inv,
    ← div_eq_mul_inv]
  exact (eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v).symm

/- English proof (translation)
Rewrite using `[Submodule.smul_le]`. Introduce `r hr p _`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[Submodule.mem_comap, map_smul, pairCoords_apply, mul_smul]`. Use `M.smul_mem c ?_` and prove the remaining obligations.

Rewrite using `[smul_add, smul_comm (a * b) (p 0), smul_comm (a * b) (p 1)]`. Use `M.add_mem (M.smul_mem _ ?_) (M.smul_mem _ ?_)` and prove the remaining obligations. Establish `e : (a * b) • ((h x x)⁻¹ • x) = b • x`. Rewrite using `[← algebraMap_smul K (a * b), ← algebraMap_smul K b, map_mul, ha, smul_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `M.smul_mem _ hx`. Establish `e : (a * b) • ((h y y)⁻¹ • y) = a • y`. Rewrite using `[← algebraMap_smul K (a * b), ← algebraMap_smul K a, map_mul, hb, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `M.smul_mem _ hy`.
-/
theorem scaledFreeModule_le_comap (M : Submodule (𝓞 K) V) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (a b : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = h x x) (hb : algebraMap (𝓞 K) K b = h y y) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) :
    scaledFreeModule K (a * b) ≤ M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by
  rw [Submodule.smul_le]
  intro r hr p _
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [Submodule.mem_comap, map_smul, pairCoords_apply, mul_smul]
  refine M.smul_mem c ?_
  rw [smul_add, smul_comm (a * b) (p 0), smul_comm (a * b) (p 1)]
  refine M.add_mem (M.smul_mem _ ?_) (M.smul_mem _ ?_)
  · have e : (a * b) • ((h x x)⁻¹ • x) = b • x := by
      rw [← algebraMap_smul K (a * b), ← algebraMap_smul K b, map_mul, ha, smul_smul]
      congr 1; field_simp
    rw [e]; exact M.smul_mem _ hx
  · have e : (a * b) • ((h y y)⁻¹ • y) = a • y := by
      rw [← algebraMap_smul K (a * b), ← algebraMap_smul K a, map_mul, hb, smul_smul]
      congr 1; field_simp
    rw [e]; exact M.smul_mem _ hy

end Geo

section Iso

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)

/- English proof (translation)
Establish `hyx : h y x = 0` using `by rw [← hs.eq x y, hxy, map_zero]`. Rewrite using `[planeMap_apply_alt, hyx, div_self hxx, zero_div, one_smul, zero_smul, add_zero]`.
-/
theorem planeMapAlt_alt_alt (hs : h.IsSymm) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0) :
    planeMapAlt h x y x' y' x = x' := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  rw [planeMap_apply_alt, hyx, div_self hxx, zero_div, one_smul, zero_smul, add_zero]

/- English proof (translation)
Rewrite using `[planeMap_apply_alt, hxy, div_self hyy, zero_div, one_smul, zero_smul, zero_add]`.
-/
theorem planeMap_apply_second (x y x' y' : V) (hxy : h x y = 0) (hyy : h y y ≠ 0) :
    planeMapAlt h x y x' y' y = y' := by
  rw [planeMap_apply_alt, hxy, div_self hyy, zero_div, one_smul, zero_smul, zero_add]

/- English proof (translation)
Establish `hxx' : h x' x' ≠ 0` using `by rw [hα]; exact hxx`. Establish `hyy' : h y' y' ≠ 0` using `by rw [hβ]; exact hyy`. Set `g : V ≃ₗ[K] V` to `LinearEquiv.ofLinearMap (planeMapAlt h x y x' y') (planeMapAlt h x' y' x y) (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x y x' y' hxy hxx hyy hxy' hxx' hyy' v) (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x' y' x y hxy' hxx' hyy' hxy hxx hyy v)`. Establish `hg : ∀ v, g v = planeMapAlt h x y x' y' v` using `fun _ => rfl`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u v`. Rewrite using `[hg, hg]`. Apply the tactic sequence `exact planeMap_isometry h hs hfr x y x' y' hxy hxx hyy hxy' hα hβ u v`. Establish `hG : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) ∘ₗ (pairCoords (K` using `K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) = pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y') := by`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `p`. Rewrite using `[LinearMap.comp_apply, pairCoords_apply, pairCoords_apply]`. Use `show g _ = _`. Rewrite using `[← algebraMap_smul K (p 0), ← algebraMap_smul K (p 1), ← algebraMap_smul K (p 0), ← algebraMap_smul K (p 1), map_add, map_smul, map_smul, map_smul, map_smul, hg, hg, planeMapAlt_alt_alt h hs x y x' y' hxy hxx, planeMap_apply_second h x y x' y' hxy hyy, hα, hβ]`. Unfold `gmap`.

Use `conv_lhs => rw [← Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M hint x y hx hy hxy hxx hyy)]`. Rewrite using `[← Submodule.map_comp, hG, hN]`. Conclude with `Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M' hint' x' y' hx' hy' hxy' hxx' hyy')`.
-/
theorem isometric_of_orthogonal_pairs (hs : h.IsSymm) (hfr : finrank K V = 2) (M M' : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (hint' : IsIntegralLat h M') (x y x' y' : V) (hx : x ∈ M) (hy : y ∈ M)
    (hx' : x' ∈ M') (hy' : y' ∈ M') (hxy : h x y = 0) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) (hxy' : h x' y' = 0)
    (hα : h x' x' = h x x) (hβ : h y' y' = h y y)
    (hN : M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) =
      M'.comap (pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y'))) :
    ∃ g ∈ isom h, gmap g M = M' := by
  have hxx' : h x' x' ≠ 0 := by rw [hα]; exact hxx
  have hyy' : h y' y' ≠ 0 := by rw [hβ]; exact hyy
  let g : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (planeMapAlt h x y x' y') (planeMapAlt h x' y' x y)
    (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x y x' y' hxy hxx hyy hxy' hxx' hyy' v)
    (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x' y' x y hxy' hxx' hyy' hxy hxx hyy v)
  have hg : ∀ v, g v = planeMapAlt h x y x' y' v := fun _ => rfl
  refine ⟨g, ?_, ?_⟩
  · intro u v
    rw [hg, hg]
    exact planeMap_isometry h hs hfr x y x' y' hxy hxx hyy hxy' hα hβ u v
  · have hG : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) ∘ₗ
        (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) =
        pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y') := by
      apply LinearMap.ext; intro p
      rw [LinearMap.comp_apply, pairCoords_apply, pairCoords_apply]
      show g _ = _
      rw [← algebraMap_smul K (p 0), ← algebraMap_smul K (p 1), ← algebraMap_smul K (p 0),
        ← algebraMap_smul K (p 1), map_add, map_smul, map_smul, map_smul, map_smul, hg, hg,
        planeMapAlt_alt_alt h hs x y x' y' hxy hxx, planeMap_apply_second h x y x' y' hxy hyy, hα, hβ]
    unfold gmap
    conv_lhs => rw [← Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M hint x y hx hy hxy hxx hyy)]
    rw [← Submodule.map_comp, hG, hN]
    exact Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M' hint' x' y' hx' hy' hxy' hxx' hyy')

end Iso

section Final

/- English proof (translation)
Establish `h1 : ((Algebra.norm ℤ d).natAbs : ℝ) = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)|`. Rewrite using `[← Algebra.coe_norm_int d, Nat.cast_natAbs]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h1, ← prod_norm_embeddings_eq_abs_norm_alt]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem natAbs_norm_le_pow_of_bounded (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (B : ℝ)
    (hd : ∀ φ : K →+* ℂ, ‖φ (d : K)‖ ≤ B) : ((Algebra.norm ℤ d).natAbs : ℝ) ≤ B ^ finrank ℚ K := by
  have h1 : ((Algebra.norm ℤ d).natAbs : ℝ) = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
    rw [← Algebra.coe_norm_int d, Nat.cast_natAbs]
    push_cast
    rfl
  rw [h1, ← prod_norm_embeddings_eq_abs_norm_alt]
  calc ∏ φ : K →+* ℂ, ‖φ (d : K)‖ ≤ ∏ _φ : K →+* ℂ, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => hd φ)
    _ = B ^ finrank ℚ K := by rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]

/- English proof (translation)
Establish `e1 : 0 ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K)` using `by rw [pow_mul]; positivity`. Establish `e2 : 0 ≤ (1 + 2 * B₂) ^ (2 * finrank ℚ K)` using `by rw [pow_mul]; positivity`. Establish `e3 : 0 ≤ (B₁ * B₂) ^ (4 * finrank ℚ K)`. Rewrite using `[show 4 * finrank ℚ K = 2 * (2 * finrank ℚ K) by ring, pow_mul]; positivity`. Break down `s.eq_empty_or_nonempty with rfl | ⟨M₀, hM₀⟩` into its components or cases.

Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Check the signs of the components of the expression. Establish `hfr` using `finrank_orthonormal_plane_eq_two h L hL`. Use `choose! x hx y hy hx0 hy0 hxy hb using hshort`. Establish `hxx : ∀ M ∈ s, h (x M) (x M) ≠ 0` using `fun M hM e => hx0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)`.

Establish `hyy : ∀ M ∈ s, h (y M) (y M) ≠ 0` using `fun M hM e => hy0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)`. Establish `hA : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (x M) (x M)` using `fun M hM => Submodule.mem_one.1 (hint M hM _ (hx M hM) _ (hx M hM))`. Establish `hBe : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (y M) (y M)` using `fun M hM => Submodule.mem_one.1 (hint M hM _ (hy M hM) _ (hy M hM))`. Use `choose! a ha using hA`. Use `choose! b hb' using hBe`.

Take `⟨φ₀⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hB1 : 0 < B₁` using `lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hxx M₀ hM₀))) (hb M₀ hM₀ φ₀).1`. Establish `hB2 : 0 < B₂` using `lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hyy M₀ hM₀))) (hb M₀ hM₀ φ₀).2`. Take `⟨f1, c1⟩` from `boundedIntegers_finite_card_le K B₁ hB1`. Take `⟨f2, c2⟩` from `boundedIntegers_finite_card_le K B₂ hB2`.

Establish `hba : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((a M : 𝓞 K) : K)‖ ≤ B₁` using `fun M hM φ => by`. Establish `e : ((a M : 𝓞 K) : K) = h (x M) (x M)` using `ha M hM`. Rewrite using `[e]`. Conclude with `(hb M hM φ).1`. Establish `hbb : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((b M : 𝓞 K) : K)‖ ≤ B₂` using `fun M hM φ => by`.

Establish `e : ((b M : 𝓞 K) : K) = h (y M) (y M)` using `hb' M hM`. Rewrite using `[e]`. Conclude with `(hb M hM φ).2`. Establish `hmap : ∀ M ∈ s, (a M, b M) ∈ f1.toFinset ×ˢ f2.toFinset`. Introduce `M hM`.

Rewrite using `[Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]`. Conclude with `⟨hba M hM, hbb M hM⟩`. Establish `hfib : ∀ q ∈ f1.toFinset ×ˢ f2.toFinset, ((s.filter (fun M => (a M, b M) = q)).card : ℝ) ≤ (B₁ * B₂) ^ (4 * finrank ℚ K)`. Introduce `q _`. Break down `(s.filter (fun M => (a M, b M) = q)).eq_empty_or_nonempty with he | ⟨M₁, hM₁⟩` into its components or cases.

Rewrite using `[he]`. Simplify using `using e3`. Take `⟨hM₁s, rfl⟩` from `Finset.mem_filter.1 hM₁`. Establish `ha0 : a M₁ ≠ 0`. Introduce `e`.

Apply `hxx M₁ hM₁s` to reduce the goal to its premises. Rewrite using `[← ha M₁ hM₁s, e, map_zero]`. Establish `hb0 : b M₁ ≠ 0`. Introduce `e`. Apply `hyy M₁ hM₁s` to reduce the goal to its premises.

Rewrite using `[← hb' M₁ hM₁s, e, map_zero]`. Take `⟨hfinS, hcardS⟩` from `card_submodules_quotient_le K (a M₁ * b M₁) (mul_ne_zero ha0 hb0)`. Set `Nf : Submodule (𝓞 K) V → Submodule (𝓞 K) (Fin 2 → 𝓞 K)` to `fun M => M.comap (pairCoords (K := K) ((h (x M) (x M))⁻¹ • x M) ((h (y M) (y M))⁻¹ • y M))`. Establish `hQ : ∀ M ∈ s.filter (fun M => (a M, b M) = (a M₁, b M₁)), scaledFreeModule K (a M₁ * b M₁) ≤ Nf M`. Introduce `M hM`.

Take `⟨hMs, hq⟩` from `Finset.mem_filter.1 hM`. Rewrite using `[← (Prod.mk.inj hq).1, ← (Prod.mk.inj hq).2]`. Conclude with `scaledFreeModule_le_comap h M (x M) (y M) (hx M hMs) (hy M hMs) (a M) (b M) (ha M hMs) (hb' M hMs) (hxx M hMs) (hyy M hMs)`. Establish `hinj : Set.InjOn (fun M => (Nf M).map (scaledFreeModule K (a M₁ * b M₁)).mkQ) (s.filter (fun M => (a M, b M) = (a M₁, b M₁)) : Finset (Submodule (𝓞 K) V))`. Introduce `M hM M' hM' hEq`.

Establish `hM2` using `Finset.mem_coe.1 hM`. Establish `hM2'` using `Finset.mem_coe.1 hM'`. Take `⟨hMs, hq⟩` from `Finset.mem_filter.1 hM2`. Take `⟨hMs', hq'⟩` from `Finset.mem_filter.1 hM2'`. Establish `hN : Nf M = Nf M'`.

Establish `h1` using `congrArg (Submodule.comap (scaledFreeModule K (a M₁ * b M₁)).mkQ) hEq`. Simplify using `only [Submodule.comap_map_mkQ] at h1`. Rewrite `h1` using `[sup_eq_right.2 (hQ M hM2), sup_eq_right.2 (hQ M' hM2')]`. Then use the resulting hypothesis. Establish `hα : h (x M') (x M') = h (x M) (x M)`. Rewrite using `[← ha M hMs, ← ha M' hMs', (Prod.mk.inj hq).1, (Prod.mk.inj hq').1]`.

Establish `hβ : h (y M') (y M') = h (y M) (y M)`. Rewrite using `[← hb' M hMs, ← hb' M' hMs', (Prod.mk.inj hq).2, (Prod.mk.inj hq').2]`. Establish `hu` using `hreps.2 M' (hreps.1 M' hMs')`. Establish `u1 : M' ∈ s ∧ ∃ g ∈ isom h, gmap g M' = M'` using `⟨hMs', 1, (isom h).one_mem, by ext v; simp [gmap]⟩`. Establish `u2 : M ∈ s ∧ ∃ g ∈ isom h, gmap g M = M'` using `⟨hMs, isometric_of_orthogonal_pairs h hs hfr M M' (hint M hMs) (hint M' hMs') (x M) (y M) (x M') (y M') (hx M hMs) (hy M hMs) (hx M' hMs') (hy M' hMs') (hxy M hMs) (hxx M hMs) (hyy M hMs) (hxy M' hMs') hα hβ hN⟩`.

Conclude with `hu.unique u2 u1`. Use `Fintype.ofFinite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁)))` as an intermediate fact. Establish `hc1 : (s.filter (fun M => (a M, b M) = (a M₁, b M₁))).card ≤ Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁)))`. Rewrite using `[Nat.card_eq_fintype_card, ← Finset.card_univ]`. Conclude with `Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj`.

Establish `hc2 : ((Algebra.norm ℤ (a M₁ * b M₁)).natAbs : ℝ) ≤ (B₁ * B₂) ^ finrank ℚ K`. Apply `natAbs_norm_le_pow_of_bounded` to reduce the goal to its premises. Introduce `φ`. Establish `e : (((a M₁ * b M₁ : 𝓞 K)) : K) = ((a M₁ : 𝓞 K) : K) * ((b M₁ : 𝓞 K) : K)` using `map_mul _ _ _`. Rewrite using `[e, map_mul, norm_mul]`.

Conclude with `mul_le_mul (hba M₁ hM₁s φ) (hbb M₁ hM₁s φ) (norm_nonneg _) hB1.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum : (s.card : ℝ) = ∑ q ∈ f1.toFinset ×ˢ f2.toFinset, ((s.filter (fun M => (a M, b M) = q)).card : ℝ)`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := fun M => (a M, b M)) (t := f1.toFinset ×ˢ f2.toFinset) (fun M hM => hmap M hM)]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hsum]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_product, nsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Use `_ ≤ ((1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K)) * (B₁ * B₂) ^ (4 * finrank ℚ K) := by`.

Rewrite using `[← Set.ncard_eq_toFinset_card _ f1, ← Set.ncard_eq_toFinset_card _ f2]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul c1 c2 (Nat.cast_nonneg _) e1) e3`.
-/
theorem class_count_plane_bound (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) (V : Type)
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2) (s : Finset (Submodule (𝓞 K) V))
    (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) (B₁ B₂ : ℝ) (hint : ∀ M ∈ s, IsIntegralLat h M)
    (hshort : ∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K) := by
  classical
  have e1 : 0 ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) := by rw [pow_mul]; positivity
  have e2 : 0 ≤ (1 + 2 * B₂) ^ (2 * finrank ℚ K) := by rw [pow_mul]; positivity
  have e3 : 0 ≤ (B₁ * B₂) ^ (4 * finrank ℚ K) := by
    rw [show 4 * finrank ℚ K = 2 * (2 * finrank ℚ K) by ring, pow_mul]; positivity
  rcases s.eq_empty_or_nonempty with rfl | ⟨M₀, hM₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hfr := finrank_orthonormal_plane_eq_two h L hL
  choose! x hx y hy hx0 hy0 hxy hb using hshort
  have hxx : ∀ M ∈ s, h (x M) (x M) ≠ 0 := fun M hM e => hx0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)
  have hyy : ∀ M ∈ s, h (y M) (y M) ≠ 0 := fun M hM e => hy0 M hM (eq_zero_of_inner_self_eq_zero h hK L hL _ e)
  have hA : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (x M) (x M) := fun M hM =>
    Submodule.mem_one.1 (hint M hM _ (hx M hM) _ (hx M hM))
  have hBe : ∀ M ∈ s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = h (y M) (y M) := fun M hM =>
    Submodule.mem_one.1 (hint M hM _ (hy M hM) _ (hy M hM))
  choose! a ha using hA
  choose! b hb' using hBe
  obtain ⟨φ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hB1 : 0 < B₁ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hxx M₀ hM₀))) (hb M₀ hM₀ φ₀).1
  have hB2 : 0 < B₂ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero φ₀).2 (hyy M₀ hM₀))) (hb M₀ hM₀ φ₀).2
  obtain ⟨f1, c1⟩ := boundedIntegers_finite_card_le K B₁ hB1
  obtain ⟨f2, c2⟩ := boundedIntegers_finite_card_le K B₂ hB2
  have hba : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((a M : 𝓞 K) : K)‖ ≤ B₁ := fun M hM φ => by
    have e : ((a M : 𝓞 K) : K) = h (x M) (x M) := ha M hM
    rw [e]; exact (hb M hM φ).1
  have hbb : ∀ M ∈ s, ∀ φ : K →+* ℂ, ‖φ ((b M : 𝓞 K) : K)‖ ≤ B₂ := fun M hM φ => by
    have e : ((b M : 𝓞 K) : K) = h (y M) (y M) := hb' M hM
    rw [e]; exact (hb M hM φ).2
  have hmap : ∀ M ∈ s, (a M, b M) ∈ f1.toFinset ×ˢ f2.toFinset := by
    intro M hM
    rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact ⟨hba M hM, hbb M hM⟩
  have hfib : ∀ q ∈ f1.toFinset ×ˢ f2.toFinset,
      ((s.filter (fun M => (a M, b M) = q)).card : ℝ) ≤ (B₁ * B₂) ^ (4 * finrank ℚ K) := by
    intro q _
    rcases (s.filter (fun M => (a M, b M) = q)).eq_empty_or_nonempty with he | ⟨M₁, hM₁⟩
    · rw [he]; simpa using e3
    obtain ⟨hM₁s, rfl⟩ := Finset.mem_filter.1 hM₁
    have ha0 : a M₁ ≠ 0 := by
      intro e; apply hxx M₁ hM₁s; rw [← ha M₁ hM₁s, e, map_zero]
    have hb0 : b M₁ ≠ 0 := by
      intro e; apply hyy M₁ hM₁s; rw [← hb' M₁ hM₁s, e, map_zero]
    obtain ⟨hfinS, hcardS⟩ := card_submodules_quotient_le K (a M₁ * b M₁) (mul_ne_zero ha0 hb0)
    let Nf : Submodule (𝓞 K) V → Submodule (𝓞 K) (Fin 2 → 𝓞 K) := fun M =>
      M.comap (pairCoords (K := K) ((h (x M) (x M))⁻¹ • x M) ((h (y M) (y M))⁻¹ • y M))
    have hQ : ∀ M ∈ s.filter (fun M => (a M, b M) = (a M₁, b M₁)), scaledFreeModule K (a M₁ * b M₁) ≤ Nf M := by
      intro M hM
      obtain ⟨hMs, hq⟩ := Finset.mem_filter.1 hM
      rw [← (Prod.mk.inj hq).1, ← (Prod.mk.inj hq).2]
      exact scaledFreeModule_le_comap h M (x M) (y M) (hx M hMs) (hy M hMs) (a M) (b M) (ha M hMs) (hb' M hMs) (hxx M hMs)
        (hyy M hMs)
    have hinj : Set.InjOn (fun M => (Nf M).map (scaledFreeModule K (a M₁ * b M₁)).mkQ)
        (s.filter (fun M => (a M, b M) = (a M₁, b M₁)) : Finset (Submodule (𝓞 K) V)) := by
      intro M hM M' hM' hEq
      have hM2 := Finset.mem_coe.1 hM
      have hM2' := Finset.mem_coe.1 hM'
      obtain ⟨hMs, hq⟩ := Finset.mem_filter.1 hM2
      obtain ⟨hMs', hq'⟩ := Finset.mem_filter.1 hM2'
      have hN : Nf M = Nf M' := by
        have h1 := congrArg (Submodule.comap (scaledFreeModule K (a M₁ * b M₁)).mkQ) hEq
        simp only [Submodule.comap_map_mkQ] at h1
        rwa [sup_eq_right.2 (hQ M hM2), sup_eq_right.2 (hQ M' hM2')] at h1
      have hα : h (x M') (x M') = h (x M) (x M) := by
        rw [← ha M hMs, ← ha M' hMs', (Prod.mk.inj hq).1, (Prod.mk.inj hq').1]
      have hβ : h (y M') (y M') = h (y M) (y M) := by
        rw [← hb' M hMs, ← hb' M' hMs', (Prod.mk.inj hq).2, (Prod.mk.inj hq').2]
      have hu := hreps.2 M' (hreps.1 M' hMs')
      have u1 : M' ∈ s ∧ ∃ g ∈ isom h, gmap g M' = M' :=
        ⟨hMs', 1, (isom h).one_mem, by ext v; simp [gmap]⟩
      have u2 : M ∈ s ∧ ∃ g ∈ isom h, gmap g M = M' :=
        ⟨hMs, isometric_of_orthogonal_pairs h hs hfr M M' (hint M hMs) (hint M' hMs') (x M) (y M) (x M') (y M') (hx M hMs)
          (hy M hMs) (hx M' hMs') (hy M' hMs') (hxy M hMs) (hxx M hMs) (hyy M hMs) (hxy M' hMs') hα hβ hN⟩
      exact hu.unique u2 u1
    have := Fintype.ofFinite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁)))
    have hc1 : (s.filter (fun M => (a M, b M) = (a M₁, b M₁))).card ≤
        Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K (a M₁ * b M₁))) := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    have hc2 : ((Algebra.norm ℤ (a M₁ * b M₁)).natAbs : ℝ) ≤ (B₁ * B₂) ^ finrank ℚ K := by
      apply natAbs_norm_le_pow_of_bounded
      intro φ
      have e : (((a M₁ * b M₁ : 𝓞 K)) : K) = ((a M₁ : 𝓞 K) : K) * ((b M₁ : 𝓞 K) : K) := map_mul _ _ _
      rw [e, map_mul, norm_mul]
      exact mul_le_mul (hba M₁ hM₁s φ) (hbb M₁ hM₁s φ) (norm_nonneg _) hB1.le
    calc ((s.filter (fun M => (a M, b M) = (a M₁, b M₁))).card : ℝ)
        ≤ (((((Algebra.norm ℤ (a M₁ * b M₁)).natAbs ^ 2) ^ 2 : ℕ)) : ℝ) := by exact_mod_cast hc1.trans hcardS
      _ = (((Algebra.norm ℤ (a M₁ * b M₁)).natAbs : ℝ) ^ 2) ^ 2 := by push_cast; rfl
      _ ≤ (((B₁ * B₂) ^ finrank ℚ K) ^ 2) ^ 2 := by gcongr
      _ = (B₁ * B₂) ^ (4 * finrank ℚ K) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
  have hsum : (s.card : ℝ) = ∑ q ∈ f1.toFinset ×ˢ f2.toFinset,
      ((s.filter (fun M => (a M, b M) = q)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun M => (a M, b M)) (t := f1.toFinset ×ˢ f2.toFinset)
      (fun M hM => hmap M hM)]
    push_cast; rfl
  rw [hsum]
  calc ∑ q ∈ f1.toFinset ×ˢ f2.toFinset, ((s.filter (fun M => (a M, b M) = q)).card : ℝ)
      ≤ ∑ _q ∈ f1.toFinset ×ˢ f2.toFinset, (B₁ * B₂) ^ (4 * finrank ℚ K) := Finset.sum_le_sum hfib
    _ = ((f1.toFinset.card : ℝ) * (f2.toFinset.card : ℝ)) * (B₁ * B₂) ^ (4 * finrank ℚ K) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; rfl
    _ ≤ ((1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K)) *
          (B₁ * B₂) ^ (4 * finrank ℚ K) := by
        rw [← Set.ncard_eq_toFinset_card _ f1, ← Set.ncard_eq_toFinset_card _ f2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul c1 c2 (Nat.cast_nonneg _) e1) e3

end Final

end Formalism.MainNotions.BridgeLemma₂

end
