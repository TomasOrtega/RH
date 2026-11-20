import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

/- English proof (translation)
Take `⟨m, hm, h⟩` from `hx`. Take `⟨n, hn, h'⟩` from `hy`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Establish `: ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y)`. Simplify using `only [nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (nsmul_mem h n) (nsmul_mem h' m)`.
-/
theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨n, hn, h'⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (nsmul_mem h n) (nsmul_mem h' m)

/- English proof (translation)
Take `⟨m, hm, h⟩` from `hx`. Conclude with `⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩`.
-/
theorem rationalLatticePoint_neg {Λ : AddSubgroup ℂ} {x : ℂ} (hx : InRationalLattice Λ x) : InRationalLattice Λ (-x) := by
  obtain ⟨m, hm, h⟩ := hx
  exact ⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩

/- English proof (translation)
Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Establish `: (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hm.ne'`. Rewrite using `[mul_div_cancel₀ _ this]`. Conclude with `hw`.
-/
theorem rationalLatticePoint_div_natCast {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {m : ℕ} (hm : 0 < m) : InRationalLattice Λ (w / m) := by
  refine ⟨m, hm, ?_⟩
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel₀ _ this]; exact hw

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `map_nsmul (h.embHom N N') k A`.
-/
theorem Good.embV_nsmul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (k : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : embV D T (k • A) = (k : ℂ) • embV D T A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (h.embHom N N') k A

/- English proof (translation)
Use `map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ` as an intermediate fact. Use `this.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Conclude with `h.embV_smul _ _`.
-/
theorem Good.embV_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ} (a : Fin r → D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (∑ j, a j • b j) = ∑ j, D.host.φ₀ (a j : D.host.E) • embV D T (b j) := by
  have := map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact h.embV_smul _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `w • h.embHom N N' y ∈ _`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩`. Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg, smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem Good.smul_embV_mem {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {w : ℂ} (hw : w ∈ T.abelian₂)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ AddSubgroup.closure Y) :
    w • embV D T y ∈ LaS D T Y := by
  change w • h.embHom N N' y ∈ _
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC`. Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hn.ne'`. Establish `hk0 : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hk.ne'`. Establish `hS0 : S 0 0`. Take `⟨t', ht'⟩` from `hex 0 ⟨1, one_pos, by simp⟩`.

Simplify using `using hmul 0 _ _ ht'`. Establish `hneg : ∀ t t', S t t' → S (-t) (-t')` using `fun t t' h => by`. Simplify using `using hmul (-1) _ _ h`. Establish `first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y`. Introduce `x hx`.

Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, y, hy, rfl⟩` from `hx`. Take `⟨a, ha⟩` from `hC.1 y hy`. Take `⟨u', hu'⟩` from `hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))`.

Establish `hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂`. Use `hint _ _ _ hu' ?_` and prove the remaining obligations. Rewrite using `[mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw`. Establish `e1` using `hT.embV_sum (fun j => (a j : D.host.K)) b`. Establish `e2` using `hT'.embV_sum (fun j => (a j : D.host.K)) b`.

Rewrite `e1` using `[← ha, hT.embV_nsmul]`. Rewrite `e2` using `[← ha, hT'.embV_nsmul]`. Use `⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k, fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'), fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `: w • embV D T y = (w / k) • ((k : ℂ) • embV D T y)`. Rewrite using `[smul_smul, div_mul_cancel₀ _ hk0]`.

Rewrite using `[this, e1, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `hmul (a j) _ _ hu'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts.

Establish `: ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j) = (((n * k : ℕ) : ℂ) * u') • embV D T' y`. Establish `h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y)`. Rewrite using `[smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, e2, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩`. Consider the case `zero`. Use `⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Take `⟨c, c', h1, h2, h3, h4⟩` from `hx`. Take `⟨d, d', g1, g2, g3, g4⟩` from `hy`. Use `⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, g2, ← Finset.sum_add_distrib]`. Simplify using `only [Pi.add_apply, add_smul]`. Simplify using `only [Pi.add_apply, add_div]`. Conclude with `hadd _ _ _ _ (h3 j) (g3 j)`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`.

Conclude with `add_mem h4 g4`. Consider the case `neg x _ hx`. Take `⟨c, c', h1, h2, h3, h4⟩` from `hx`. Use `⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ← Finset.sum_neg_distrib]`.

Simplify using `only [Pi.neg_apply, neg_smul]`. Simplify using `only [Pi.neg_apply, neg_div]`. Conclude with `hneg _ _ (h3 j)`. Simplify using `only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]`. Conclude with `neg_mem h4`.

Use `⟨first, fun c c' hS hc => ?_⟩` and prove the remaining obligations. Take `⟨d, d', -, h2, h3, h4⟩` from `first _ hc`. Establish `hcd : c = d`. Use function extensionality and compare the values at `j`. Rewrite using `[← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]`.

Substitute `hcd` using the available equality. Take `⟨m, hm⟩` from `hkn`. Establish `key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y` using `fun j => by`. Establish `h5` using `nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m`. Establish `h6` using `hT'.smul_embV_mem h5 (hC.2 j)`.

Rewrite `h6` using `[hT'.embV_nsmul, smul_smul]`. Use `h6 using 2` and compare the differences between its conclusion and the goal. Establish `hm' : (n : ℂ) = k * m` using `by rw [hm]; push_cast; rfl`. Rewrite using `[nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]`. Establish `: ∑ j, c' j • embV D T' (b j) = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j)`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `add_mem h4 (sum_mem fun j _ => key j)`.
-/
theorem corr_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  intro D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hS0 : S 0 0 := by
    obtain ⟨t', ht'⟩ := hex 0 ⟨1, one_pos, by simp⟩
    simpa using hmul 0 _ _ ht'
  have hneg : ∀ t t', S t t' → S (-t) (-t') := fun t t' h => by
    simpa using hmul (-1) _ _ h
  have first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
      x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧
      ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hC.1 y hy
      obtain ⟨u', hu'⟩ := hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))
      have hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂ := by
        refine hint _ _ _ hu' ?_
        rw [mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw
      have e1 := hT.embV_sum (fun j => (a j : D.host.K)) b
      have e2 := hT'.embV_sum (fun j => (a j : D.host.K)) b
      rw [← ha, hT.embV_nsmul] at e1
      rw [← ha, hT'.embV_nsmul] at e2
      refine ⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k,
        fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'),
        fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩
      · have : w • embV D T y = (w / k) • ((k : ℂ) • embV D T y) := by
          rw [smul_smul, div_mul_cancel₀ _ hk0]
        rw [this, e1, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]; congr 1; ring
      · have := hmul (a j) _ _ hu'
        convert this using 1
        · push_cast; field_simp
        · field_simp
      · have : ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j)
            = (((n * k : ℕ) : ℂ) * u') • embV D T' y := by
          have h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y
              = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y) := by
            rw [smul_smul]; congr 1; push_cast; ring
          rw [h2, e2, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; ring
        rw [this]
        exact AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩
    | zero =>
      refine ⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      obtain ⟨d, d', g1, g2, g3, g4⟩ := hy
      refine ⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, g2, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]
      · simp only [Pi.add_apply, add_div]; exact hadd _ _ _ _ (h3 j) (g3 j)
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; exact add_mem h4 g4
    | neg x _ hx =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      refine ⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, ← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]
      · simp only [Pi.neg_apply, neg_div]; exact hneg _ _ (h3 j)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]; exact neg_mem h4
  refine ⟨first, fun c c' hS hc => ?_⟩
  obtain ⟨d, d', -, h2, h3, h4⟩ := first _ hc
  have hcd : c = d := by
    funext j
    rw [← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]
  subst hcd
  obtain ⟨m, hm⟩ := hkn
  have key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y := fun j => by
    have h5 := nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m
    have h6 := hT'.smul_embV_mem h5 (hC.2 j)
    rw [hT'.embV_nsmul, smul_smul] at h6
    convert h6 using 2
    have hm' : (n : ℂ) = k * m := by rw [hm]; push_cast; rfl
    rw [nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]
  have : ∑ j, c' j • embV D T' (b j)
      = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [this]
  exact add_mem h4 (sum_mem fun j _ => key j)

end GlobalTheory.ThetaConj
