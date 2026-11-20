import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → Fˣ}

/- English proof (translation)
Establish `hm : ((x j : F) / x i) ∈ rA ℂ (xv x) {i}` using `Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩`. Rewrite using `[rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Conclude with `isIntegral_algebraMap (R := rA ℂ (xv x) {i}) (x := ⟨_, hm⟩)`.
-/
private lemma ratio_mem (i j : Fin (d + 1)) :
    algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := by
  have hm : ((x j : F) / x i) ∈ rA ℂ (xv x) {i} :=
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := rA ℂ (xv x) {i}) (x := ⟨_, hm⟩)

/- English proof (translation)
Distinguish the cases in `hne : i = i'`. Substitute `hne` using the available equality. Use `⟨0, fun N _ => ?_⟩` and prove the remaining obligations. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i i) N) hb`. Establish `hb' : b ∈ rB ℂ K (xv x) {i, i'}` using `(GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i} i (by simp)).1 {i, i'} (by simp) hb`.

Take `⟨N0, hN0⟩` from `((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i, i'} i' (by simp)).2 b).mp hb'`. Rewrite `hN0` using `[Finset.prod_pair hne, div_self (Units.ne_zero (x i')), mul_one]`. Use `⟨N0, fun N hN => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Establish `e : algebraMap F K ((x i : F) / x i') ^ (N0 + k) * b = algebraMap F K ((x i : F) / x i') ^ k * (b * algebraMap F K ((x i : F) / x i') ^ N0)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i' i) k) hN0`.
-/
private lemma pow_mul_mem (h : IsFinCover ℂ K (xv x)) (i i' : Fin (d + 1)) (b : K)
    (hb : b ∈ rB ℂ K (xv x) {i}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} := by
  by_cases hne : i = i'
  · subst hne
    refine ⟨0, fun N _ => ?_⟩
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i i) N) hb
  have hb' : b ∈ rB ℂ K (xv x) {i, i'} :=
    (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i} i (by simp)).1 {i, i'} (by simp) hb
  obtain ⟨N0, hN0⟩ :=
    ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i, i'} i' (by simp)).2 b).mp hb'
  rw [Finset.prod_pair hne, div_self (Units.ne_zero (x i')), mul_one] at hN0
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have e : algebraMap F K ((x i : F) / x i') ^ (N0 + k) * b =
      algebraMap F K ((x i : F) / x i') ^ k * (b * algebraMap F K ((x i : F) / x i') ^ N0) := by
    ring
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i' i) k) hN0

/- English proof (translation)
Use `haveI := h.smooth i`. Conclude with `(Subalgebra.fg_iff_finiteType _).mpr inferInstance`.
-/
private lemma gens (h : IsFinCover ℂ K (xv x)) (i : Fin (d + 1)) :
    ∃ G : Finset K, Algebra.adjoin ℂ (G : Set K) = rB ℂ K (xv x) {i} := by
  haveI := h.smooth i
  exact (Subalgebra.fg_iff_finiteType _).mpr inferInstance

/- English proof (translation)
Establish `e1 : (a / a') ^ N * a' ^ N = a ^ N` using `by rw [← mul_pow, div_mul_cancel₀ a ha']`. Establish `e2 : (a / a'') ^ N * a'' ^ N = a ^ N` using `by rw [← mul_pow, div_mul_cancel₀ a ha'']`. Establish `e3 : (a / a') ^ N * b * a' ^ N = a ^ N * b` using `by rw [mul_right_comm, e1]`. Establish `e4 : (a / a'') ^ N * b * a'' ^ N = a ^ N * b` using `by rw [mul_right_comm, e2]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, sub_mul, mul_sub, mul_one, one_mul, e1, e2, e3, e4]`.

Use `done`.
-/
private lemma tensor_id (a a' a'' b : K) (ha' : a' ≠ 0) (ha'' : a'' ≠ 0) (N : ℕ) :
    (((a ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a ^ N))) * (b ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] b) =
      ((((a / a') ^ N * b) ⊗ₜ[ℂ] ((a / a'') ^ N)) - (((a / a') ^ N) ⊗ₜ[ℂ] ((a / a'') ^ N * b))) *
        (((a' ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a'' ^ N))) := by
  have e1 : (a / a') ^ N * a' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha']
  have e2 : (a / a'') ^ N * a'' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha'']
  have e3 : (a / a') ^ N * b * a' ^ N = a ^ N * b := by rw [mul_right_comm, e1]
  have e4 : (a / a'') ^ N * b * a'' ^ N = a ^ N * b := by rw [mul_right_comm, e2]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, sub_mul, mul_sub, mul_one, one_mul, e1, e2, e3, e4]
  done

/- English proof (translation)
Simplify using `[sysZ, Units.val_pow_eq_pow_val, Algebra.TensorProduct.tmul_pow]`.
-/
private lemma coe_XY (i j : Fin (d + 1)) (N : ℕ) :
    (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y j ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      (((algebraMap F K (x i)) ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] ((algebraMap F K (x j)) ^ N)) := by
  simp [sysZ, Units.val_pow_eq_pow_val, Algebra.TensorProduct.tmul_pow]

end

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x h`. Use `choose G hG using fun i => gens (x := x) h i`. Establish `hGm : ∀ i, ∀ b ∈ G i, b ∈ rB ℂ K (xv x) {i}` using `fun i b hb => hG i ▸ Algebra.subset_adjoin hb`. Establish `hP : ∀ i b, b ∈ G i → ∀ i', ∃ N0 : ℕ, ∀ N, N0 ≤ N → (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'}` using `fun i b hb i' => pow_mul_mem h i i' b (hGm i b hb)`. Use `choose! Nb hNb using hP`.

Set `Nq : Fin (d + 1) × K → ℕ` to `fun q => Finset.univ.sup (fun i' => Nb q.1 q.2 i')`. Set `P : Finset (Fin (d + 1) × K)` to `Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))`. Establish `hPm : ∀ q ∈ P, q.2 ∈ G q.1`. Introduce `q hq`. Simplify using `only [P, Finset.mem_biUnion, Finset.mem_image] at hq`.

Take `⟨i, _, b, hb, rfl⟩` from `hq`. Conclude with `hb`. Set `e` to `P.equivFin.symm`. Set `zz : Fin (d + 1) × K → K ⊗[ℂ] K` to `fun q => (((sysZ K x 0).X q.1 ^ Nq q * (sysZ K x 0).Y q.1 ^ Nq q : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (q.2 ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] q.2)`. Use `⟨P.card, fun l => (Nq (e l).1, Nq (e l).1), fun l => zz (e l).1, ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `i' j' l show zz (e l).1 * ↑((sysZ K x 0).X i' ^ Nq (e l).1 * (sysZ K x 0).Y j' ^ Nq (e l).1)⁻¹ ∈ _`. Establish `hb` using `hPm _ (e l).2`. Generalize the expression as in `(e l).1 = q at hb ⊢`. Take `⟨i, b⟩` from `q`. Simplify using `only [zz] at hb ⊢`.

Establish `hN1 : Nb i b i' ≤ Nq (i, b)` using `Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ i')`. Establish `hN2 : Nb i b j' ≤ Nq (i, b)` using `Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ j')`. Establish `hA` using `hNb i b hb i' _ hN1`. Establish `hD` using `hNb i b hb j' _ hN2`. Establish `hB` using `Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) j' i) (Nq (i, b))`.

Establish `hC` using `Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) i' i) (Nq (i, b))`. Rewrite using `[coe_XY, tensor_id (algebraMap F K (x i)) (algebraMap F K (x i')) (algebraMap F K (x j')) b (by simp) (by simp) _, ← coe_XY i' j' _, Units.mul_inv_cancel_right]`. Simplify using `only [map_div₀] at hA hB hC hD`. Conclude with `Subalgebra.sub_mem _ ((AlgHom.mem_range _).mpr ⟨⟨_, hA⟩ ⊗ₜ ⟨_, hB⟩, by simp⟩) ((AlgHom.mem_range _).mpr ⟨⟨_, hC⟩ ⊗ₜ ⟨_, hD⟩, by simp⟩)`. Introduce `l`.

Simplify using `[zz, Algebra.TensorProduct.lmul'_apply_tmul]`. Introduce `i`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Algebra.adjoin_le (fun b hb => hb.1)`. Use `(hG i).symm.le.trans (Algebra.adjoin_mono ?_)` and prove the remaining obligations.

Introduce `b hb`. Establish `hq : (i, b) ∈ P`. Simplify using `only [P, Finset.mem_biUnion, Finset.mem_image]`. Conclude with `⟨i, Finset.mem_univ _, b, hb, rfl⟩`. Apply the tactic sequence `refine ⟨hGm i b hb, e.symm ⟨(i, b), hq⟩, Nq (i, b), ?_, ?_⟩ <;> simp [e, zz]`.
-/
theorem UpperTheory.Gal.productCup_of_system.zFam_of :
    ZFam := by
  classical
  intro F K _ _ _ _ _ _ d x h
  choose G hG using fun i => gens (x := x) h i
  have hGm : ∀ i, ∀ b ∈ G i, b ∈ rB ℂ K (xv x) {i} := fun i b hb =>
    hG i ▸ Algebra.subset_adjoin hb
  have hP : ∀ i b, b ∈ G i → ∀ i', ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} :=
    fun i b hb i' => pow_mul_mem h i i' b (hGm i b hb)
  choose! Nb hNb using hP
  let Nq : Fin (d + 1) × K → ℕ := fun q => Finset.univ.sup (fun i' => Nb q.1 q.2 i')
  let P : Finset (Fin (d + 1) × K) :=
    Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))
  have hPm : ∀ q ∈ P, q.2 ∈ G q.1 := by
    intro q hq
    simp only [P, Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨i, _, b, hb, rfl⟩ := hq
    exact hb
  let e := P.equivFin.symm
  let zz : Fin (d + 1) × K → K ⊗[ℂ] K := fun q =>
    (((sysZ K x 0).X q.1 ^ Nq q * (sysZ K x 0).Y q.1 ^ Nq q : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) *
      (q.2 ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] q.2)
  refine ⟨P.card, fun l => (Nq (e l).1, Nq (e l).1), fun l => zz (e l).1, ⟨?_, ?_, ?_⟩⟩
  · intro i' j' l
    show zz (e l).1 * ↑((sysZ K x 0).X i' ^ Nq (e l).1 * (sysZ K x 0).Y j' ^ Nq (e l).1)⁻¹ ∈ _
    have hb := hPm _ (e l).2
    generalize (e l).1 = q at hb ⊢
    obtain ⟨i, b⟩ := q
    dsimp only [zz] at hb ⊢
    have hN1 : Nb i b i' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ i')
    have hN2 : Nb i b j' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ j')
    have hA := hNb i b hb i' _ hN1
    have hD := hNb i b hb j' _ hN2
    have hB := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) j' i) (Nq (i, b))
    have hC := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) i' i) (Nq (i, b))
    rw [coe_XY, tensor_id (algebraMap F K (x i)) (algebraMap F K (x i')) (algebraMap F K (x j')) b
      (by simp) (by simp) _, ← coe_XY i' j' _, Units.mul_inv_cancel_right]
    simp only [map_div₀] at hA hB hC hD
    exact Subalgebra.sub_mem _ ((AlgHom.mem_range _).mpr ⟨⟨_, hA⟩ ⊗ₜ ⟨_, hB⟩, by simp⟩)
      ((AlgHom.mem_range _).mpr ⟨⟨_, hC⟩ ⊗ₜ ⟨_, hD⟩, by simp⟩)
  · intro l
    simp [zz, Algebra.TensorProduct.lmul'_apply_tmul]
  · intro i
    apply le_antisymm
    · exact Algebra.adjoin_le (fun b hb => hb.1)
    · refine (hG i).symm.le.trans (Algebra.adjoin_mono ?_)
      intro b hb
      have hq : (i, b) ∈ P := by
        simp only [P, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨i, Finset.mem_univ _, b, hb, rfl⟩
      refine ⟨hGm i b hb, e.symm ⟨(i, b), hq⟩, Nq (i, b), ?_, ?_⟩ <;> simp [e, zz]
