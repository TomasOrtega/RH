import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b', hb', v, hv, rfl⟩` from `hz`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩`.

Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hu hw`. Consider the case `smul c u _ hu`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ c hu`.
-/
private lemma omB_smul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hu

/- English proof (translation)
Rewrite using `[rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Establish `h : x j / x i ∈ rA ℂ x {i}` using `Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩`. Conclude with `isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))`.
-/
private lemma ratio_mem_rB {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (i j : Fin (d + 1)) :
    algebraMap F K (x j / x i) ∈ rB ℂ K x {i} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have h : x j / x i ∈ rA ℂ x {i} := Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  exact isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))

/- English proof (translation)
Establish `hi : (x i : F) ≠ 0` using `(x i).ne_zero`. Establish `hj : (x j : F) ≠ 0` using `(x j).ne_zero`. Establish `h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1)`. Simplify using `only [omG]`. Rewrite using `[show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow], ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Rewrite using `[h, ← inv_div (x j : F) (x i : F)]`. Establish `ha : (x j : F) / x i ≠ 0` using `div_ne_zero hj hi`. Generalize the expression as in `(x j : F) / x i = a at ha ⊢`.

Rewrite using `[inv_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma omG_ratio {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) (N : ℕ) :
    ((x j : F) / x i) ^ (N + d + 1) * ((x i : F) / x j) ^ N * omG x j = omG x i := by
  have hi : (x i : F) ≠ 0 := (x i).ne_zero
  have hj : (x j : F) ≠ 0 := (x j).ne_zero
  have h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1) := by
    simp only [omG]
    rw [show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    field_simp
  rw [h, ← inv_div (x j : F) (x i : F)]
  have ha : (x j : F) / x i ≠ 0 := div_ne_zero hj hi
  generalize (x j : F) / x i = a at ha ⊢
  rw [inv_pow, inv_pow]
  field_simp
  ring

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_pair h, div_self (x i).ne_zero, one_mul]`.
-/
private lemma pair_prod {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) :
    (∏ l ∈ ({i, j} : Finset (Fin (d + 1))), (x l : F) / x i) = (x j : F) / x i := by
  by_cases h : i = j
  · subst h
    simp
  · rw [Finset.prod_pair h, div_self (x i).ne_zero, one_mul]

/- English proof (translation)
Simplify using `[actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]`.
-/
private theorem key_lemma' {K : Type} [Field K] [Algebra ℂ K] (s t : K) (y z : DR ℂ K) :
    actZ K (s ⊗ₜ[ℂ] t) (y ⊗ₜ[ℂ] z) = (s • y) ⊗ₜ[ℂ] (t • z) := by
  simp [actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]

/- English proof (translation)
Establish `hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i}` using `ratio_mem_rB K (xv x) i j`. Establish `hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j}` using `ratio_mem_rB K (xv x) j i`. Establish `gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a, ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈ MZ F K (xv x) a {i} {j …`. Introduce `y hy z hz`. Establish `hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a)` using `hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr (by simp)) hy`.

Take `⟨N1, hN1⟩` from `(GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'`. Establish `hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a)`. Rewrite using `[← pair_prod x i j]`. Conclude with `hN1`. Use `⟨N1, fun N hN => ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.mk_apply, key_lemma']`. Establish `h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a)`. Establish `e : N + d + 1 = (N + d + 1 - N1) + N1` using `by omega`. Rewrite using `[e, pow_add, ← smul_smul]`. Conclude with `omB_smul_mem _ _ (pow_mem hu _) hN1'`.

Establish `h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a` using `omB_smul_mem _ _ (pow_mem hv _) hz`. Conclude with `Submodule.apply_mem_map₂ _ h1 h2`. Unfold `MZ at hm`. Rewrite `hm` using `[Submodule.map₂_eq_span_image2]`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨y, hy, z, hz, rfl⟩` from `hw`. Conclude with `gen y hy z hz`. Consider the case `zero => exact ⟨0, fun N _ => by simp⟩`. Consider the case `add w w' _ _ h1 h2`.

Take `⟨N1, h1⟩` from `h1`. Take `⟨N2, h2⟩` from `h2`. Conclude with `⟨max N1 N2, fun N hN => by`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩`.

Consider the case `smul c w _ h`. Take `⟨N1, h⟩` from `h`. Conclude with `⟨N1, fun N hN => by`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ c (h N hN)⟩`.
-/
private lemma key {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q) (a : ℕ) (i j : Fin (d + 1))
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) (hm : m ∈ MZ F K (xv x) a {j} {j}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
      (algebraMap F K ((x i : F) / x j) ^ N)) m ∈ MZ F K (xv x) a {i} {j} := by
  have hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := ratio_mem_rB K (xv x) i j
  have hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j} := ratio_mem_rB K (xv x) j i
  have gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a,
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
        (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈
          MZ F K (xv x) a {i} {j} := by
    intro y hy z hz
    have hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a) :=
      hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j)
        (Finset.singleton_subset_iff.mpr (by simp)) hy
    obtain ⟨N1, hN1⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'
    have hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      rw [← pair_prod x i j]
      exact hN1
    refine ⟨N1, fun N hN => ?_⟩
    rw [TensorProduct.mk_apply, key_lemma']
    have h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈
        omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      have e : N + d + 1 = (N + d + 1 - N1) + N1 := by omega
      rw [e, pow_add, ← smul_smul]
      exact omB_smul_mem _ _ (pow_mem hu _) hN1'
    have h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a :=
      omB_smul_mem _ _ (pow_mem hv _) hz
    exact Submodule.apply_mem_map₂ _ h1 h2
  unfold MZ at hm
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    exact gen y hy z hz
  | zero => exact ⟨0, fun N _ => by simp⟩
  | add w w' _ _ h1 h2 =>
    obtain ⟨N1, h1⟩ := h1
    obtain ⟨N2, h2⟩ := h2
    exact ⟨max N1 N2, fun N hN => by
      rw [map_add]
      exact Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩
  | smul c w _ h =>
    obtain ⟨N1, h⟩ := h
    exact ⟨N1, fun N hN => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h N hN)⟩

/- English proof (translation)
Introduce `hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j`. Take `⟨m, hm, hact⟩` from `hJ F K d x hc τ hτ a ha j`. Establish `hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t → omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q` using `fun q => (hG F K d x hc q).2.2`. Take `⟨N0, hN0⟩` from `key x hc hmono a i j m hm`. Use `⟨_, hN0 N0 le_rfl, ?_⟩` and prove the remaining obligations.

Establish `h2` using `(hL F K d x hc τ hτ a).2.1 m _ ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact`. Rewrite `h2` using `[Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul, omG_ratio]`. Simplify `h2` using `only [map_pow]`.
-/
theorem UpperTheory.Gal.productCup_of_system.idIJ_of :
    IdJ → ActsLin → GoodZ → IdIJ := by
  intro hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j
  obtain ⟨m, hm, hact⟩ := hJ F K d x hc τ hτ a ha j
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q :=
    fun q => (hG F K d x hc q).2.2
  obtain ⟨N0, hN0⟩ := key x hc hmono a i j m hm
  refine ⟨_, hN0 N0 le_rfl, ?_⟩
  have h2 := (hL F K d x hc τ hτ a).2.1 m _
    ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact
  rw [Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    omG_ratio] at h2
  simpa only [map_pow] using h2
