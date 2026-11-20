import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L`. Take `⟨σ, hσ⟩` from `minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic a) h`. Rewrite using `[← hσ]`. Conclude with `spectralNorm_eq_of_equiv (K := ℚ_[l]) (L := PadicAlgCl l) (σ.restrictScalars ℚ_[l]) μ`.
-/
private theorem norm_eq_of_aeval_minpoly_eq_zero' {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) (a μ : Om l)
    (h : Polynomial.aeval μ (minpoly L a) = 0) : ‖μ‖ = ‖a‖ := by
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic a) h
  rw [← hσ]
  exact spectralNorm_eq_of_equiv (K := ℚ_[l]) (L := PadicAlgCl l) (σ.restrictScalars ℚ_[l]) μ

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]`. Consider the case `monomial n c`. Establish `hpow : ∀ m : ℕ, F ^ m * Y = Y * F' ^ m`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]`.

Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hpow]`.
-/
private theorem aeval_mul_eq_mul_aeval_of_semiconj {K : Type} [Field K] {d r : ℕ} (F : Matrix (Fin d) (Fin d) K)
    (Y : Matrix (Fin d) (Fin r) K) (F' : Matrix (Fin r) (Fin r) K) (h : F * Y = Y * F')
    (q : Polynomial K) : Polynomial.aeval F q * Y = Y * Polynomial.aeval F' q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    have hpow : ∀ m : ℕ, F ^ m * Y = Y * F' ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hpow]

/- English proof (translation)
Use `set M : Matrix (Fin r) (Fin r) (Om l) := A.map (algebraMap ↥L (Om l)) with hMdef`. Establish `hdet : ((A.det : ↥L) : Om l) = M.det`. Rewrite using `[hMdef]`. Conclude with `RingHom.map_det (algebraMap ↥L (Om l)) A`. Establish `hMp : Polynomial.aeval M (minpoly L a) = 0`.

Establish `e` using `Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin r)) A (minpoly L a)`. Rewrite `e` using `[hA, map_zero]`. Conclude with `e`. Establish `hroot : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = ‖a‖`. Introduce `μ hμ`.

Establish `hr : Polynomial.IsRoot M.charpoly μ` using `(Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hμ`. Establish `hs : μ ∈ spectrum (Om l) M` using `Matrix.mem_spectrum_of_isRoot_charpoly hr`. Establish `hs2` using `spectrum.subset_polynomial_aeval M ((minpoly L a).map (algebraMap ↥L (Om l))) ⟨μ, hs, rfl⟩`. Rewrite `hs2` using `[Polynomial.aeval_map_algebraMap, hMp]`. Establish `hz : Polynomial.eval μ ((minpoly L a).map (algebraMap ↥L (Om l))) = 0`.

Assume the negation of the conclusion as `hx`. Rewrite `hs2` using `[spectrum.mem_iff, sub_zero]`. Conclude with `hs2 ((Units.mk0 _ hx).isUnit.map (algebraMap (Om l) (Matrix (Fin r) (Fin r) (Om l))))`. Rewrite `hz` using `[Polynomial.eval_map_algebraMap]`. Conclude with `norm_eq_of_aeval_minpoly_eq_zero' L a μ hz`.

Rewrite using `[hdet, Matrix.det_eq_prod_roots_charpoly]`. Establish `hn` using `map_multiset_prod (normHom : Om l →*₀ ℝ) M.charpoly.roots`. Simplify using `only [normHom_apply] at hn`. Rewrite using `[hn, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate, IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.
-/
private theorem norm_det_eq_pow_of_aeval_minpoly_eq_zero {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ↥L) (a : Om l) (hA : Polynomial.aeval A (minpoly L a) = 0) :
    ‖((A.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  set M : Matrix (Fin r) (Fin r) (Om l) := A.map (algebraMap ↥L (Om l)) with hMdef
  have hdet : ((A.det : ↥L) : Om l) = M.det := by
    rw [hMdef]
    exact RingHom.map_det (algebraMap ↥L (Om l)) A
  have hMp : Polynomial.aeval M (minpoly L a) = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin r)) A (minpoly L a)
    rw [hA, map_zero] at e
    exact e
  have hroot : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = ‖a‖ := by
    intro μ hμ
    have hr : Polynomial.IsRoot M.charpoly μ := (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hμ
    have hs : μ ∈ spectrum (Om l) M := Matrix.mem_spectrum_of_isRoot_charpoly hr
    have hs2 := spectrum.subset_polynomial_aeval M ((minpoly L a).map (algebraMap ↥L (Om l))) ⟨μ, hs, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hMp] at hs2
    have hz : Polynomial.eval μ ((minpoly L a).map (algebraMap ↥L (Om l))) = 0 := by
      by_contra hx
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Units.mk0 _ hx).isUnit.map (algebraMap (Om l) (Matrix (Fin r) (Fin r) (Om l))))
    rw [Polynomial.eval_map_algebraMap] at hz
    exact norm_eq_of_aeval_minpoly_eq_zero' L a μ hz
  rw [hdet, Matrix.det_eq_prod_roots_charpoly]
  have hn := map_multiset_prod (normHom : Om l →*₀ ℝ) M.charpoly.roots
  simp only [normHom_apply] at hn
  rw [hn, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/- English proof (translation)
Use `set W := LinearMap.ker (Matrix.toLin' P) with hWdef`. Establish `hW : W ≠ ⊥`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hP`. Introduce `h`. Establish `hvW : v ∈ W`.

Rewrite using `[hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]`. Conclude with `hv`. Rewrite `hvW` using `[h, Submodule.mem_bot]`. Conclude with `hv0 hvW`. Establish `hr : 0 < Module.finrank K W` using `Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))`.

Establish `hinv : ∀ w ∈ W, Matrix.toLin' F w ∈ W`. Introduce `w hw`. Rewrite `hw`, the goal using `[hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]`. Use `set e := (Module.finBasis K W).equivFun`.

Use `set ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ e.symm.toLinearMap with hι`. Establish `hιker : LinearMap.ker ι = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `Subtype.val_injective.comp e.symm.injective`. Take `⟨g, hg⟩` from `ι.exists_leftInverse_of_injective hιker`.

Use `set G := e.toLinearMap ∘ₗ (Matrix.toLin' F).restrict hinv ∘ₗ e.symm.toLinearMap with hG`. Use `⟨Module.finrank K W, LinearMap.toMatrix' ι, LinearMap.toMatrix' g, LinearMap.toMatrix' G, hr, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Establish `hcomp : ι ∘ₗ G = Matrix.toLin' F ∘ₗ ι`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Simplify using `[hι, hG, LinearMap.restrict_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[LinearMap.toMatrix'_toLin']`. Use `_ = LinearMap.toMatrix' (Matrix.toLin' F ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm`.

Use `_ = LinearMap.toMatrix' (ι ∘ₗ G) := by rw [hcomp]`. Use `_ = _ := LinearMap.toMatrix'_comp _ _`. Establish `hzero : Matrix.toLin' P ∘ₗ ι = 0`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[LinearMap.comp_apply, LinearMap.zero_apply]`. Conclude with `(e.symm x).2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[LinearMap.toMatrix'_toLin']`. Use `_ = LinearMap.toMatrix' (Matrix.toLin' P ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm`.

Use `_ = 0 := by rw [hzero, map_zero]`.
-/
private theorem exists_invariant_subspace_in_ker_of_det_zero {K : Type} [Field K] {d : ℕ} (F P : Matrix (Fin d) (Fin d) K)
    (hP : P.det = 0) (hc : F * P = P * F) :
    ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) K) (Z : Matrix (Fin r) (Fin d) K) (F' : Matrix (Fin r) (Fin r) K),
      0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ P * Y = 0 := by
  classical
  set W := LinearMap.ker (Matrix.toLin' P) with hWdef
  have hW : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hP
    intro h
    have hvW : v ∈ W := by
      rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hv
    rw [h, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hr : 0 < Module.finrank K W := Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hinv : ∀ w ∈ W, Matrix.toLin' F w ∈ W := by
    intro w hw
    rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  set e := (Module.finBasis K W).equivFun
  set ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ e.symm.toLinearMap with hι
  have hιker : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hιker
  set G := e.toLinearMap ∘ₗ (Matrix.toLin' F).restrict hinv ∘ₗ e.symm.toLinearMap with hG
  refine ⟨Module.finrank K W, LinearMap.toMatrix' ι, LinearMap.toMatrix' g, LinearMap.toMatrix' G, hr, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · have hcomp : ι ∘ₗ G = Matrix.toLin' F ∘ₗ ι := by
      apply LinearMap.ext
      intro x
      simp [hι, hG, LinearMap.restrict_apply]
    calc F * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' F) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' F ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = LinearMap.toMatrix' (ι ∘ₗ G) := by rw [hcomp]
      _ = _ := LinearMap.toMatrix'_comp _ _
  · have hzero : Matrix.toLin' P ∘ₗ ι = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact (e.symm x).2
    calc P * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' P) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' P ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 0 := by rw [hzero, map_zero]

/- English proof (translation)
Introduce `l _ L d F a ha`. Use `set p := minpoly (↥L) a with hp`. Establish `hPdet : (Polynomial.aeval F p).det = 0`. Establish `hs2` using `spectrum.subset_polynomial_aeval (F.map (algebraMap ↥L (Om l))) (p.map (algebraMap ↥L (Om l))) ⟨a, ha, rfl⟩`. Use `beta_reduce at hs2`.

Rewrite `hs2` using `[Polynomial.eval_map_algebraMap, hp, minpoly.aeval, Polynomial.aeval_map_algebraMap]`. Establish `e` using `Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F (minpoly (↥L) a)`. Rewrite `e` using `[show ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F = F.map (algebraMap ↥L (Om l)) from rfl]`. Rewrite `hs2` using `[e, spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]`. Establish `h3 : algebraMap ↥L (Om l) (Polynomial.aeval F (minpoly (↥L) a)).det = 0`.

Rewrite using `[RingHom.map_det]`. Conclude with `hs2`. Conclude with `(map_eq_zero_iff _ (algebraMap ↥L (Om l)).injective).mp h3`. Establish `hcomm : F * Polynomial.aeval F p = Polynomial.aeval F p * F` using `(aeval_mul_eq_mul_aeval_of_semiconj F F F rfl p).symm`. Take `⟨r, Y, Z, F', hr, hZY, hFY, hPY⟩` from `exists_invariant_subspace_in_ker_of_det_zero F (Polynomial.aeval F p) hPdet hcomm`.

Establish `hF' : Polynomial.aeval F' p = 0`. Establish `h1` using `aeval_mul_eq_mul_aeval_of_semiconj F Y F' hFY p`. Rewrite `h1` using `[hPY]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨r, Y, Z, F', hr, hZY, hFY, norm_det_eq_pow_of_aeval_minpoly_eq_zero L F' a hF'⟩`.
-/
theorem UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) ↥L) (Z : Matrix (Fin r) (Fin d) ↥L) (F' : Matrix (Fin r) (Fin r) ↥L), 0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ ‖((F'.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  intro l _ L d F a ha
  set p := minpoly (↥L) a with hp
  have hPdet : (Polynomial.aeval F p).det = 0 := by
    have hs2 := spectrum.subset_polynomial_aeval (F.map (algebraMap ↥L (Om l)))
      (p.map (algebraMap ↥L (Om l))) ⟨a, ha, rfl⟩
    beta_reduce at hs2
    rw [Polynomial.eval_map_algebraMap, hp, minpoly.aeval, Polynomial.aeval_map_algebraMap] at hs2
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F (minpoly (↥L) a)
    rw [show ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F = F.map (algebraMap ↥L (Om l)) from rfl] at e
    rw [e, spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hs2
    have h3 : algebraMap ↥L (Om l) (Polynomial.aeval F (minpoly (↥L) a)).det = 0 := by
      rw [RingHom.map_det]
      exact hs2
    exact (map_eq_zero_iff _ (algebraMap ↥L (Om l)).injective).mp h3
  have hcomm : F * Polynomial.aeval F p = Polynomial.aeval F p * F := (aeval_mul_eq_mul_aeval_of_semiconj F F F rfl p).symm
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hPY⟩ := exists_invariant_subspace_in_ker_of_det_zero F (Polynomial.aeval F p) hPdet hcomm
  have hF' : Polynomial.aeval F' p = 0 := by
    have h1 := aeval_mul_eq_mul_aeval_of_semiconj F Y F' hFY p
    rw [hPY] at h1
    calc Polynomial.aeval F' p = (Z * Y) * Polynomial.aeval F' p := by rw [hZY, Matrix.one_mul]
      _ = Z * (Y * Polynomial.aeval F' p) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← h1, Matrix.mul_zero]
  exact ⟨r, Y, Z, F', hr, hZY, hFY, norm_det_eq_pow_of_aeval_minpoly_eq_zero L F' a hF'⟩
