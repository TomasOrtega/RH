import Mathlib
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
open NumberField

noncomputable section

namespace GlobalTheory.NabScale

open MvPolynomial IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def IntAt (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
    A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • m

/- English proof (translation)
Take `⟨t, ht, A, hA⟩` from `h`. Use `⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]`. Simplify using the standard rewrite rules.
-/
theorem IntAt.det {w : HeightOneSpectrum (𝓞 K)} {m : Matrix (Fin n) (Fin n) K} (h : IntAt w m) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m.det := by
  obtain ⟨t, ht, A, hA⟩ := h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `e.eq_nat_or_neg`. Take `⟨t, ht, y, hy⟩` from `hc.det`. Use `⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_natCast, detPow, zpow_natCast, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]`. Simplify using `only [Fintype.card_fin]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht, y, hy⟩` from `hc'.det`. Use `⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_neg, Int.natAbs_natCast, detPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]`. Simplify using `only [Fintype.card_fin]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem detPow_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (e : ℤ) :
    ∃ u ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K u * (c ^ (n * e.natAbs) * detPow K n g e) := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := hc.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_natCast, detPow, zpow_natCast, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring
  · obtain ⟨t, ht, y, hy⟩ := hc'.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_neg, Int.natAbs_natCast, detPow, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hf`. Take `⟨t, ht, A, hA⟩` from `hc`. Take `⟨u, hu, y, hy⟩` from `detPow_scaled w g c ⟨t, ht, A, hA⟩ hc' lam.detShift`. Use `⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _), y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f, Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩` and prove the remaining obligations. Establish `hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW` using `Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf`.

Establish `hT : Aᵀ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K t * c) • (g : Matrix (Fin n) (Fin n) K)ᵀ`. Rewrite using `[Matrix.transpose_map, hA, Matrix.transpose_smul, Matrix.transpose_smul, smul_smul]`. Rewrite using `[map_smul, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.map_rowAct, hT, GlobalTheory.NabStab.rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, smul_smul, map_mul, map_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqAct_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • (c ^ (∑ j, lam.natW j + n * lam.detShift.natAbs) • sqAct K n lam g f) ∈
        (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := hc
  obtain ⟨u, hu, y, hy⟩ := detPow_scaled w g c ⟨t, ht, A, hA⟩ hc' lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K t * c) • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul, Matrix.transpose_smul, smul_smul]
  rw [map_smul, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.map_rowAct, hT,
    GlobalTheory.NabStab.rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, smul_smul,
    map_mul, map_pow]
  congr 1
  ring

def scaleExp {ι : Type} [Fintype ι] (lam : ι → DomWeight n) : ℕ :=
  ∑ τ, (∑ j, (lam τ).natW j + n * (lam τ).detShift.natAbs)

/- English proof (translation)
Establish `key : ∀ F ∈ nabStd K lam, c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)`. Introduce `F hF`. Unfold `nabStd Formalism.GradedWeylDivisibility.tensorLat at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨f, hf, rfl⟩` from `hx`. Use `choose s hs hs' using fun τ => sqAct_scaled w (g τ) c (hc τ) (hc' τ) (lam τ) (f τ) (hf τ)`. Use `⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `actTen K ι n lam g f`. Unfold `ten at h1`.

Rewrite using `[h1, ← IsScalarTower.algebraMap_smul K, map_prod, scaleExp, ← Finset.prod_pow_eq_pow_sum, smul_smul, ← Finset.prod_mul_distrib]`. Simplify using `only [map_smul, smul_smul]`. Rewrite using `[Finset.prod_smul]`. Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[LinearMap.map_smul_of_tower, smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.

Introduce and unpack `F ⟨s, hs, hF⟩`. Take `⟨t, ht, h2⟩` from `key _ hF`. Use `⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[LinearMap.map_smul_of_tower]`. Rewrite using `[mul_smul, smul_comm s (c ^ scaleExp lam)]`.

Conclude with `h2`.
-/
theorem polyAction_scaled_mem_locP_nabStd {ι : Type} [Fintype ι] (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (c : K)
    (hc : ∀ τ, IntAt w (c • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hc' : ∀ τ, IntAt w (c • (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_scaled w (g τ) c (hc τ) (hc' τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod, scaleExp, ← Finset.prod_pow_eq_pow_sum, smul_smul,
        ← Finset.prod_mul_distrib]
      simp only [map_smul, smul_smul]
      rw [Finset.prod_smul]
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, smul_comm]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul, smul_comm s (c ^ scaleExp lam)]
  exact h2

/- English proof (translation)
Use `choose s hs hs' using h`. Establish `h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * m a j`. Introduce `a j`. Take `⟨y, hy⟩` from `hs' j a`. Use `⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, mul_assoc]`. Use `choose A hA using h2`. Use `⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩` and prove the remaining obligations. Use extensionality with `a j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]`.
-/
theorem intAt_of_cols (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, ∃ t ∈ w.asIdeal.primeCompl, ∀ a, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m a j) :
    IntAt w m := by
  classical
  choose s hs hs' using h
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * m a j := by
    intro a j
    obtain ⟨y, hy⟩ := hs' j a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

/- English proof (translation)
Apply `intAt_of_cols` to reduce the goal to its premises. Introduce `j`. Establish `h1 : (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L`. Unfold `IsBasisAt at hB`. Rewrite using `[hB]`.

Conclude with `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩`. Take `⟨s, hs, hx⟩` from `h1`. Establish `h2 : c • (s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B')`. Unfold `IsBasisAt at hB'`. Rewrite using `[← hB']`.

Conclude with `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h _ hx⟩`. Take `⟨s', hs', hx'⟩` from `h2`. Establish `h3 : colLat B' = gLat B' (colLat 1)` using `by rw [← colLat_mul, mul_one]`. Rewrite `hx'` using `[h3]`. Take `⟨z, hz, hzx⟩` from `hx'`.

Use `⟨s' * s, Submonoid.mul_mem _ hs' hs, fun a => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `GlobalTheory.NabStab.int_of_mem_colLat_one hz a`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hz' : z = ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j)`. Establish `hzx' : (B' : Matrix (Fin n) (Fin n) K) *ᵥ z = s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j` using `hzx`.

Rewrite using `[← hzx', Matrix.mulVec_mulVec]`. Simplify using the standard rewrite rules. Rewrite using `[hy, hz']`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, Units.val_mul, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, Finset.mul_sum, map_mul]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intAt_transition (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w L B) (hB' : IsBasisAt w L' B') (c : K) (h : ∀ x ∈ L, c • x ∈ L') :
    IntAt w (c • ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  apply intAt_of_cols
  intro j
  have h1 : (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
    unfold IsBasisAt at hB
    rw [hB]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  obtain ⟨s, hs, hx⟩ := h1
  have h2 : c • (s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B') := by
    unfold IsBasisAt at hB'
    rw [← hB']
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h _ hx⟩
  obtain ⟨s', hs', hx'⟩ := h2
  have h3 : colLat B' = gLat B' (colLat 1) := by rw [← colLat_mul, mul_one]
  rw [h3] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, fun a => ?_⟩
  obtain ⟨y, hy⟩ := GlobalTheory.NabStab.int_of_mem_colLat_one hz a
  refine ⟨y, ?_⟩
  have hz' : z = ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) := by
    have hzx' : (B' : Matrix (Fin n) (Fin n) K) *ᵥ z = s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j := hzx
    rw [← hzx', Matrix.mulVec_mulVec]
    simp
  rw [hy, hz']
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Units.val_mul, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section ESide

variable {E : Type} [Field E] [NumberField E] {ι : Type}

/- English proof (translation)
Introduce `x hx`. Unfold `tauLat at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`.

Use `Submodule.subset_span ⟨(N : 𝓞 E) • m, h m hm, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `[Algebra.smul_def]`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M, (N : 𝓞 E) • x ∈ M') : ∀ x ∈ tauLat emb τ M, (N : 𝓞 K) • x ∈ tauLat emb τ M' := by
  intro x hx
  unfold tauLat at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • m, h m hm, ?_⟩
    funext a
    simp [Algebra.smul_def]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `φ hφ x hx`. Establish `h1` using `hφ _ (tauLat_smul_mem emb τ N h x hx)`. Use `show ((N : K) • φ) ⬝ᵥ x ∈ _`. Rewrite using `[smul_dotProduct]`. Rewrite `h1` using `[dotProduct_smul]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `[Algebra.smul_def]`.
-/
theorem dualFr_tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M', (N : 𝓞 E) • x ∈ M) :
    ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') := by
  intro φ hφ x hx
  have h1 := hφ _ (tauLat_smul_mem emb τ N h x hx)
  show ((N : K) • φ) ⬝ᵥ x ∈ _
  rw [smul_dotProduct]
  rw [dotProduct_smul] at h1
  convert h1 using 1
  simp [Algebra.smul_def]

end ESide

/- English proof (translation)
Introduce `E K _ _ _ _ ι _ n emb lam M M' N _ hM _ h1 h2`. Use `⟨scaleExp lam, fun F hF => ?_⟩` and prove the remaining obligations. Establish `hL : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M))` using `fun τ => dualFr_tauLat_isLattice emb τ M hM`. Establish `hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M')` using `fun τ => dualFr_tauLat_smul_mem emb τ N h2`. Establish `hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M)` using `fun τ => dualFr_tauLat_smul_mem emb τ N h1`.

Unfold `nabAtr nabK at hF ⊢`. Rewrite `hF`, the goal using `[Submodule.mem_comap]`. Simplify using `only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.coe_subtype] at hF ⊢`. Introduce `w B' hB'`. Use `choose B hB using fun τ => basisAtEx K n _ (hL τ) w`.

Establish `hF'` using `hF w B hB`. Establish `e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹` using `by rw [mul_assoc, mul_inv_cancel, mul_one]`. Rewrite using `[SetLike.val_smul, map_smul, e, polyAction_mul]`. Use `polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'` and prove the remaining obligations. Conclude with `intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)`.

Establish `h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ` using `by simp [mul_inv_rev]`. Rewrite using `[h3]`. Conclude with `intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)`.
-/
theorem nabAtr_smul_pow_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ),
    N ≠ 0 → Submodule.IsLattice E M → Submodule.IsLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') →
    (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) →
    ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  intro E K _ _ _ _ ι _ n emb lam M M' N _ hM _ h1 h2
  refine ⟨scaleExp lam, fun F hF => ?_⟩
  have hL : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M)) := fun τ => dualFr_tauLat_isLattice emb τ M hM
  have hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h2
  have hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M) :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h1
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at hF ⊢
  intro w B' hB'
  choose B hB using fun τ => basisAtEx K n _ (hL τ) w
  have hF' := hF w B hB
  have e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [SetLike.val_smul, map_smul, e, polyAction_mul]
  refine polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'
  · exact intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)
  · have h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ := by simp [mul_inv_rev]
    rw [h3]
    exact intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)

end GlobalTheory.NabScale
