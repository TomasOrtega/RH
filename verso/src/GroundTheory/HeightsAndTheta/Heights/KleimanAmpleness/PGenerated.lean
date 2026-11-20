import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x Q`. Take `⟨M, hMgam, hMtilde⟩` from `hE S Ω N x Ω Q.toSubFamily Q.fg`. Take `⟨n, deg, gen, hgen, hM⟩` from `M.fg`. Use `⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Conclude with `(Submodule.mem_iInf _).mp hz I`. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT`.

Establish `hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' → s.IsHomogeneous e → (e' : ℤ) + deg j = e → x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T`. Introduce `j f s e e' hs hf hse hee`. Establish `hd : deg j ≤ c` using `(le_abs_self (deg j)).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j` from `⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩`. Establish `hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs`.

Establish `h1` using `M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)`. Establish `h2 : deg j + (k : ℤ) = c` using `by omega`. Rewrite `h1` using `[h2]`. Establish `h3` using `hMgam c h1`. Rewrite `h3` using `[map_pow, aeval_X, smul_eq_mul]`. Then use the resulting hypothesis.

Establish `hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I` using `Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩`. Rewrite `hα` using `[twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton]`. Take `⟨b, hb⟩` from `hα`. Rewrite `hb` using `[chartRing_smul_def]`. Establish `e1 : x i ^ c * x i ^ (-deg j) = x i ^ k`.

Rewrite using `[← zpow_add₀ hxi, ← zpow_natCast, hk]`. Use `congr 1`. Establish `e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j)`. Rewrite using `[chartRing_smul_def, ← e1]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e2]`. Conclude with `T.smul_mem b (Submodule.subset_span hsec)`. Establish `key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T`. Introduce `y hy`. Use `Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations.

Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Use `Submodule.span_induction (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, f, e', hf, hee, rfl⟩`. Rewrite using `[smul_eq_mul, smul_eq_mul]`. Conclude with `hgenT j f s e e' hs hf hse (by omega)`.

Rewrite using `[smul_zero, mul_zero]`. Conclude with `T.zero_mem`. Introduce `m m' _ _ h h'`. Rewrite using `[smul_add, mul_add]`. Conclude with `T.add_mem h h'`.

Introduce `r m _ h`. Establish `: x i ^ c * ((aeval x s)⁻¹ • (r • m)) = (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m))`. Rewrite using `[chartRing_smul_def]`. Simplify using `only [smul_eq_mul, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = algebraMap S Ω r * _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `T.smul_mem _ h`. Rewrite using `[mul_zero]`. Conclude with `T.zero_mem`.

Introduce `y y' _ _ h h'`. Rewrite using `[mul_add]`. Conclude with `T.add_mem h h'`. Introduce `b y _ h`. Establish `: x i ^ c * (b • y) = b • (x i ^ c * y)`.

Rewrite using `[chartRing_smul_def, chartRing_smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `T.smul_mem b h`. Express the relevant statement in the definitionally equal form `Submodule.span _ _ ≤ T`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `q ∈ twistMod S x c I at hq`. Rewrite `hq` using `[twistMod_eq_span c I hi, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hq`.

Establish `hy' : y ∈ M.tilde 0 I` using `by rw [hMtilde I]; exact hy`. Establish `: (a • x i ^ c) • y = a • (x i ^ c * y)`. Rewrite using `[smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]`. Rewrite using `[SetLike.mem_coe, this]`. Conclude with `T.smul_mem a (key y hy')`.
-/
theorem Generated.proof (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      refine Submodule.span_induction
        (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)
      · rintro _ ⟨j, f, e', hf, hee, rfl⟩
        rw [smul_eq_mul, smul_eq_mul]
        exact hgenT j f s e e' hs hf hse (by omega)
      · rw [smul_zero, mul_zero]; exact T.zero_mem
      · intro m m' _ _ h h'
        rw [smul_add, mul_add]; exact T.add_mem h h'
      · intro r m _ h
        have : x i ^ c * ((aeval x s)⁻¹ • (r • m)) =
            (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m)) := by
          rw [chartRing_smul_def]
          simp only [smul_eq_mul, Algebra.smul_def]
          change _ = algebraMap S Ω r * _
          ring
        rw [this]; exact T.smul_mem _ h
    · rw [mul_zero]; exact T.zero_mem
    · intro y y' _ _ h h'
      rw [mul_add]; exact T.add_mem h h'
    · intro b y _ h
      have : x i ^ c * (b • y) = b • (x i ^ c * y) := by
        rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem b h
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')

end

end GroundTheory.Heights₂.Heights.Kleiman
