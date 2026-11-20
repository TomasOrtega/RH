import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun ij : Fin k × Fin k => g ij.1 ij.2)`. Take `⟨a, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ`. Use `choose y hy using hd`. Use `⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Establish `h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R)` using `by rw [hu]; simp`. Rewrite using `[Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul, Algebra.smul_def, mul_assoc]`.
-/
theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]

/- English proof (translation)
Take `⟨a, g0, h0⟩` from `exists_pow_smul (K := K) hπ g`. Take `⟨b, h, h1⟩` from `exists_pow_smul (K := K) hπ g⁻¹`. Use `choose x z hx using fun i j => hd (g0 i j) (a + b + 1)`. Establish `hp0 : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero`. Use `⟨Matrix.of fun i j => (t ^ a)⁻¹ * x i j, 1 + π • (h * Matrix.of z), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Establish `hr : IsLocalRing.residue R π = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `hπ.not_isUnit`. Establish `: (IsLocalRing.residue R).mapMatrix (1 + π • (h * Matrix.of z)) = 1`.

Rewrite using `[map_add, map_one]`. Establish `: (IsLocalRing.residue R).mapMatrix (π • (h * Matrix.of z)) = 0`. Use extensionality with `i j`. Simplify using `[hr]`. Rewrite using `[this, add_zero]`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `e1 : (1 + π • (h * Matrix.of z)).map (algebraMap R K) = 1 + algebraMap R K π • (h.map (algebraMap R K) * (Matrix.of z).map (algebraMap R K))`. Rewrite using `[← Matrix.map_mul]`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply, apply_ite (algebraMap R K), map_one, map_zero]`. Rewrite using `[e1, ← h1, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]`. Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun h0 i) j`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_pow, ht, hx, map_add, ← h2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_approx {E : Type} [Field E] (f : E →+* K) {π : R} (hπ : Irreducible π) (t : E)
    (ht : f t = algebraMap R K π)
    (hd : ∀ (y : R) (N : ℕ), ∃ (x : E) (z : R), f x = algebraMap R K (y + π ^ N * z))
    {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) :
    ∃ (B : Matrix (Fin k) (Fin k) E) (u : Matrix (Fin k) (Fin k) R), IsUnit u.det ∧
      B.map f = g * u.map (algebraMap R K) := by
  obtain ⟨a, g0, h0⟩ := exists_pow_smul (K := K) hπ g
  obtain ⟨b, h, h1⟩ := exists_pow_smul (K := K) hπ g⁻¹
  choose x z hx using fun i j => hd (g0 i j) (a + b + 1)
  have hp0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  refine ⟨Matrix.of fun i j => (t ^ a)⁻¹ * x i j, 1 + π • (h * Matrix.of z), ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue R π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
    have : (IsLocalRing.residue R).mapMatrix (1 + π • (h * Matrix.of z)) = 1 := by
      rw [map_add, map_one]
      have : (IsLocalRing.residue R).mapMatrix (π • (h * Matrix.of z)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π • (h * Matrix.of z)).map (algebraMap R K) =
        1 + algebraMap R K π • (h.map (algebraMap R K) * (Matrix.of z).map (algebraMap R K)) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply,
        apply_ite (algebraMap R K), map_one, map_zero]
    rw [e1, ← h1, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun h0 i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀,
      map_pow, ht, hx, map_add, ← h2]
    field_simp
    ring

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/- English proof (translation)
Rewrite using `[colSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Establish `: (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mul_apply, Algebra.smul_def, mul_comm]`.

Express the relevant statement in the definitionally equal form `(fun i => (g * u.map (algebraMap R K)) i c) ∈ colSpan R g`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem colSpan_mul_le {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) :
    colSpan R (g * u.map (algebraMap R K)) ≤ colSpan R g := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/- English proof (translation)
Use `le_antisymm (colSpan_mul_le g u) ?_` and prove the remaining obligations. Use `colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem colSpan_mul_eq {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    colSpan R (g * u.map (algebraMap R K)) = colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[colSpan, Submodule.span_span_of_tower, eq_top_iff]`. Introduce `w _`. Establish `: w = ∑ j, (B⁻¹.mulVec w) j • fun i => B i j`. Use function extensionality and compare the values at `i`.

Establish `h : B.mulVec (B⁻¹.mulVec w) = w`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]`. Use `conv_lhs => rw [← h]`. Generalize the expression as in `B⁻¹.mulVec w = y`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem isLattice_colSpan {A E : Type} [CommRing A] [Field E] [Algebra A E] {k : ℕ} (B : Matrix (Fin k) (Fin k) E)
    (hB : IsUnit B.det) : Submodule.IsLattice E (colSpan A B) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [colSpan, Submodule.span_span_of_tower, eq_top_iff]
  intro w _
  have : w = ∑ j, (B⁻¹.mulVec w) j • fun i => B i j := by
    funext i
    have h : B.mulVec (B⁻¹.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    conv_lhs => rw [← h]
    generalize B⁻¹.mulVec w = y
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `(fun i => f (x i)) ∈ colSpan R (B.map f)`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨c, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨c, rfl⟩`. Consider the case `zero`. Establish `: (fun i => f ((0 : Fin k → E) i)) = 0` using `by funext i; simp`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun i => f ((x + y) i)) = (fun i => f (x i)) + fun i => f (y i)` using `by funext i; simp`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Take `⟨s, hs⟩` from `hf a`. Establish `: (fun i => f ((a • x) i)) = s • fun i => f (x i)`. Use function extensionality and compare the values at `i`.

Simplify using `[Algebra.smul_def, hs]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[colSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`.

Conclude with `Submodule.subset_span ⟨fun i => B i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩`.
-/
theorem span_image {A E R K : Type} [CommRing A] [Field E] [Algebra A E] [CommRing R] [Field K] [Algebra R K]
    (f : E →+* K) (hf : ∀ r : A, f (algebraMap A E r) ∈ Set.range (algebraMap R K)) {k : ℕ}
    (B : Matrix (Fin k) (Fin k) E) :
    Submodule.span R ((fun (x : Fin k → E) i => f (x i)) '' (colSpan A B : Set (Fin k → E))) = colSpan R (B.map f) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change (fun i => f (x i)) ∈ colSpan R (B.map f)
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero =>
      have : (fun i => f ((0 : Fin k → E) i)) = 0 := by funext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => f ((x + y) i)) = (fun i => f (x i)) + fun i => f (y i) := by funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨s, hs⟩ := hf a
      have : (fun i => f ((a • x) i)) = s • fun i => f (x i) := by
        funext i; simp [Algebra.smul_def, hs]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => B i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

end TupApx

/- English proof (translation)
Introduce `p O Kf _ _ _ _ _ X P T n hn v L hL`. Substitute `hn` using the available equality. Take `⟨g, hg, rfl⟩` from `hL`. Establish `hS` using `P.setting v`. Use `haveI := hS.frac_alt`.

Take `⟨B, u, hu, hB⟩` from `TupApx.exists_approx (T.iw v) hS.p_unif (p : X.E) (by simp) (fun y N => by obtain ⟨x, z, h⟩ := T.iw_dense v y N; exact ⟨x, z, h⟩) g hg`. Establish `hdet : IsUnit B.det`. Establish `h1 : T.iw v B.det = g.det * algebraMap _ _ u.det`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]`. Conclude with `congrArg Matrix.det hB`.

Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Rewrite `h1` using `[h0, map_zero]`. Conclude with `(hg.mul (hu.map _)).ne_zero h1.symm`. Use `⟨colSpan (𝓞 X.E) B, TupApx.isLattice_colSpan B hdet, ?_⟩` and prove the remaining obligations. Rewrite using `[← TupApx.colSpan_mul_eq g u hu, ← hB, ← TupApx.span_image (T.iw v) (fun r => (T.iw_int v _).1 (IntAt.coe _ r)) B]`.

Both sides reduce to the same expression.
-/
theorem exists_tup_eq : ∀ (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] (X : Fields) (P : Places p O Kf) (T : PlTie X P) (n : ℕ) (hn : n = P.m + 1) (v : Fin P.nV) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)), Formalism.MainNotions.G.IsLattice (P.W v) L → ∃ M : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E M ∧ T.tup hn M v = L := by
  intro p O Kf _ _ _ _ _ X P T n hn v L hL
  subst hn
  obtain ⟨g, hg, rfl⟩ := hL
  have hS := P.setting v
  haveI := hS.frac_alt
  obtain ⟨B, u, hu, hB⟩ := TupApx.exists_approx (T.iw v) hS.p_unif (p : X.E) (by simp)
    (fun y N => by obtain ⟨x, z, h⟩ := T.iw_dense v y N; exact ⟨x, z, h⟩) g hg
  have hdet : IsUnit B.det := by
    have h1 : T.iw v B.det = g.det * algebraMap _ _ u.det := by
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
      exact congrArg Matrix.det hB
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact (hg.mul (hu.map _)).ne_zero h1.symm
  refine ⟨colSpan (𝓞 X.E) B, TupApx.isLattice_colSpan B hdet, ?_⟩
  rw [← TupApx.colSpan_mul_eq g u hu, ← hB,
    ← TupApx.span_image (T.iw v) (fun r => (T.iw_int v _).1 (IntAt.coe _ r)) B]
  rfl

end GlobalTheory.GO
