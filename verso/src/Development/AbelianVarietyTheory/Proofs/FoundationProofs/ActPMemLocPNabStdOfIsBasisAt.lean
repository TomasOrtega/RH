import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.NabStab

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Unfold `colLat at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨j, rfl⟩` from `h`. Distinguish the cases in `h : a = j`.

Conclude with `⟨1, by simp [h]⟩`. Conclude with `⟨0, by simp [Matrix.one_apply, h]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, hu⟩` from `hx`.

Take `⟨v, hv⟩` from `hy`. Conclude with `⟨u + v, by rw [map_add, hu, hv]; rfl⟩`. Consider the case `smul r x _ hx`. Take `⟨u, hu⟩` from `hx`. Conclude with `⟨r * u, by rw [map_mul, hu, Pi.smul_apply, Algebra.smul_def]⟩`.
-/
theorem int_of_mem_colLat_one {x : Fin n → K} (hx : x ∈ colLat (1 : GL (Fin n) K)) (a : Fin n) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, rfl⟩ := h
    by_cases h : a = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [Matrix.one_apply, h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
  | smul r x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨r * u, by rw [map_mul, hu, Pi.smul_apply, Algebra.smul_def]⟩

/- English proof (translation)
Establish `h1 : ∀ j : Fin n, (fun a : Fin n => (g : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat (1 : GL (Fin n) K))`. Introduce `j`. Unfold `IsBasisAt at h`. Rewrite using `[h]`. Conclude with `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩`.

Use `choose s hs hs' using h1`. Establish `h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * (g : Matrix (Fin n) (Fin n) K) a j`. Introduce `a j`. Take `⟨y, hy⟩` from `int_of_mem_colLat_one (hs' j) a`. Use `⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, Pi.smul_apply, Algebra.smul_def, mul_assoc]`. Use `choose A hA using h2`. Use `⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩` and prove the remaining obligations. Use extensionality with `a j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]`.
-/
theorem exists_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K) := by
  classical
  have h1 : ∀ j : Fin n, (fun a : Fin n => (g : Matrix (Fin n) (Fin n) K) a j) ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat (1 : GL (Fin n) K)) := by
    intro j
    unfold IsBasisAt at h
    rw [h]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  choose s hs hs' using h1
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * (g : Matrix (Fin n) (Fin n) K) a j := by
    intro a j
    obtain ⟨y, hy⟩ := int_of_mem_colLat_one (hs' j) a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, Pi.smul_apply, Algebra.smul_def,
      mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

/- English proof (translation)
Rewrite using `[← isBasisAt_gLat w g, ← colLat_mul, mul_one, mul_inv_cancel]`. Conclude with `h.symm`.
-/
theorem isBasisAt_inv (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    IsBasisAt w (colLat 1) g⁻¹ := by
  rw [← isBasisAt_gLat w g, ← colLat_mul, mul_one, mul_inv_cancel]
  exact h.symm

/- English proof (translation)
Take `⟨t, ht, A, hA⟩` from `exists_int w g h`. Use `⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]`. Simplify using the standard rewrite rules.
-/
theorem det_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `e.eq_nat_or_neg`. Take `⟨t, ht, y, hy⟩` from `det_int w g h`. Use `⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hy, map_pow, mul_pow, detPow, zpow_natCast, Units.val_pow_eq_pow_val]`. Take `⟨t, ht, y, hy⟩` from `det_int w g⁻¹ (isBasisAt_inv w g h)`.

Use `⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hy, map_pow, mul_pow, detPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, map_inv]`.
-/
theorem detPow_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) (e : ℤ) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * detPow K n g e := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := det_int w g h
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_natCast, Units.val_pow_eq_pow_val]
  · obtain ⟨t, ht, y, hy⟩ := det_int w g⁻¹ (isBasisAt_inv w g h)
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, map_inv]

/- English proof (translation)
Rewrite using `[← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]`. Simplify using `only [Finset.sum_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW, Pi.single_apply]`.
-/
theorem degree_of_weight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[← degree_of_weight m (hf (mem_support_iff.mp hm))]`.

Establish `h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) = C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2)`. Introduce `v`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowAct_smul {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_weight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [Formalism.GradedWeylDivisibility.rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, hp]`.

Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`.
-/
theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hf`. Take `⟨t, ht, A, hA⟩` from `exists_int w g h`. Take `⟨u, hu, y, hy⟩` from `detPow_int w g h lam.detShift`. Use `⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _), y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f, Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩` and prove the remaining obligations. Establish `hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW` using `Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf`.

Establish `hT : Aᵀ.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K)ᵀ`. Rewrite using `[Matrix.transpose_map, hA, Matrix.transpose_smul]`. Rewrite using `[map_smul, toK_apply, toK_apply, map_rowAct, hT, rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, map_mul, map_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqAct_mem (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g)
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • sqAct K n lam g f ∈ (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  obtain ⟨u, hu, y, hy⟩ := detPow_int w g h lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul]
  rw [map_smul, toK_apply, toK_apply, map_rowAct, hT, rowAct_smul _ _ _ hK.1, sqAct,
    ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, map_mul, map_pow]
  congr 1
  ring

/- English proof (translation)
Establish `key : ∀ F ∈ nabStd K lam, actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)`. Introduce `F hF`. Unfold `nabStd Formalism.GradedWeylDivisibility.tensorLat at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨f, hf, rfl⟩` from `hx`. Use `choose s hs hs' using fun τ => sqAct_mem w (g τ) (h τ) (lam τ) (f τ) (hf τ)`. Use `⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `actTen K ι n lam g f`. Unfold `ten at h1`.

Rewrite using `[h1, ← IsScalarTower.algebraMap_smul K, map_prod]`. Simplify using `only [map_smul]`. Conclude with `(Finset.prod_smul _ _ _).symm`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ hx`.

Introduce and unpack `F ⟨s, hs, hF⟩`. Take `⟨t, ht, h2⟩` from `key _ hF`. Use `⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[LinearMap.map_smul_of_tower]`. Rewrite using `[mul_smul]`.

Conclude with `h2`.
-/
theorem polyAction_mem_locP_nabStd (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (h : ∀ τ, IsBasisAt w (colLat 1) (g τ)) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_mem w (g τ) (h τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod]
      simp only [map_smul]
      exact (Finset.prod_smul _ _ _).symm
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul]
  exact h2

end GlobalTheory.NabStab
