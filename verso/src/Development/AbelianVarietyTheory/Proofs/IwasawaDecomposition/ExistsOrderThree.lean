import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeanSquareEvenThetaTwelfthRootInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasRationalTorsionIffMemRange
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI

noncomputable section

namespace GlobalTheory.Mem.PeriodTie

section Lattice

open PeriodPair GlobalTheory.ConjPoint

/- English proof (translation)
Rewrite `h2`, `h3` using `[map_pow]`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ σ L.g₂ = u * L.g₂ := by`. Distinguish the cases in `h0 : L.g₂ = 0`. Conclude with `⟨1, one_pow _, by simp [h0]⟩`. Conclude with `⟨σ L.g₂ / L.g₂, by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨η, hη, e2, e3⟩ : ∃ η : ℂ, η ≠ 0 ∧ σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ := by`. Establish `hu0 : u ≠ 0` using `by rintro rfl; simp at hu`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e` into its components or cases. Conclude with `⟨u ^ 2, pow_ne_zero _ hu0, by rw [hu2]; linear_combination -u * L.g₂ * hu, by rw [e]; linear_combination -(u ^ 3 + 1) * L.g₃ * hu⟩`. Conclude with `⟨-u ^ 2, neg_ne_zero.2 (pow_ne_zero _ hu0), by rw [hu2]; linear_combination -u * L.g₂ * hu, by rw [e]; linear_combination (u ^ 3 + 1) * L.g₃ * hu⟩`.

Take `⟨m, hm⟩` from `IsAlgClosed.exists_pow_nat_eq η⁻¹ (n := 2) (by norm_num)`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hη (by simpa using hm.symm)`. Establish `hmu : (m ^ 2)⁻¹ = η` using `by rw [hm, inv_inv]`.

Establish `H` using `isHomothetic_scalePeriods L m hm0`. Generalize the expression as in `scalePeriods L m hm0 = L' at H`. Establish `f2 : L'.g₂ = σ L.g₂` using `by rw [H.g₂_eq, e2, ← hmu]; ring`. Establish `f3 : L'.g₃ = σ L.g₃` using `by rw [H.g₃_eq, e3, ← hmu]; ring`. Use `⟨η, e2, e3, fun t => ?_⟩` and prove the remaining obligations.

Take `⟨s, -, hc⟩` from `exists_conjEquiv f2 f3`. Take `⟨w, hw⟩` from `latticePoint_surjective L' (s (latticePoint L t))`. Take `⟨t', rfl⟩ : ∃ t', w = m * t'` from `⟨m⁻¹ * w, by field_simp⟩`. Use `⟨t', fun c hσ hc' => ?_⟩` and prove the remaining obligations. Use `IsConj.mul f2 f3 hc' ((hc _ _).2 hw.symm)` as an intermediate fact.

Rewrite `this` using `[hσ, mul_left_comm]`. Break down `this with ⟨a, b⟩ | ⟨a, b, e, -⟩` into its components or cases. Conclude with `⟨iff_of_true a ((H _).1 b), fun h => absurd a h⟩`. Conclude with `⟨iff_of_false a fun h => b ((H _).2 h), fun _ => by rw [← e, H.weierstrassP_mul, hmu]⟩`.
-/
theorem exists_action (L : PeriodPair) (σ : ℂ ≃+* ℂ) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3) (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) :
    ∃ η : ℂ, σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ ∧ ∀ t, ∃ t', ∀ c : ℂ, σ c = c →
      (∀ l ∈ L.lattice, c * l ∈ L.lattice) → (c * t ∈ L.lattice ↔ c * t' ∈ L.lattice) ∧
        (c * t ∉ L.lattice → σ (℘[L] (c * t)) = η * ℘[L] (c * t')) := by
  rw [map_pow] at h2 h3
  obtain ⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ σ L.g₂ = u * L.g₂ := by
    by_cases h0 : L.g₂ = 0
    · exact ⟨1, one_pow _, by simp [h0]⟩
    · exact ⟨σ L.g₂ / L.g₂, by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩
  obtain ⟨η, hη, e2, e3⟩ : ∃ η : ℂ, η ≠ 0 ∧ σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e
    · exact ⟨u ^ 2, pow_ne_zero _ hu0, by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination -(u ^ 3 + 1) * L.g₃ * hu⟩
    · exact ⟨-u ^ 2, neg_ne_zero.2 (pow_ne_zero _ hu0), by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination (u ^ 3 + 1) * L.g₃ * hu⟩
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq η⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hη (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = η := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  generalize scalePeriods L m hm0 = L' at H
  have f2 : L'.g₂ = σ L.g₂ := by rw [H.g₂_eq, e2, ← hmu]; ring
  have f3 : L'.g₃ = σ L.g₃ := by rw [H.g₃_eq, e3, ← hmu]; ring
  refine ⟨η, e2, e3, fun t => ?_⟩
  obtain ⟨s, -, hc⟩ := exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L t))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  refine ⟨t', fun c hσ hc' => ?_⟩
  have := IsConj.mul f2 f3 hc' ((hc _ _).2 hw.symm)
  rw [hσ, mul_left_comm] at this
  rcases this with ⟨a, b⟩ | ⟨a, b, e, -⟩
  · exact ⟨iff_of_true a ((H _).1 b), fun h => absurd a h⟩
  · exact ⟨iff_of_false a fun h => b ((H _).2 h), fun _ => by rw [← e, H.weierstrassP_mul, hmu]⟩

/- English proof (translation)
Rewrite using `[← L.derivWeierstrassP_sq t ht, (derivWeierstrassP_eq_zero_iff L ht).2 h]`. Simplify using the standard rewrite rules.
-/
theorem cubic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : t + t ∈ L.lattice) :
    4 * ℘[L] t ^ 3 - L.g₂ * ℘[L] t - L.g₃ = 0 := by
  rw [← L.derivWeierstrassP_sq t ht, (derivWeierstrassP_eq_zero_iff L ht).2 h]; simp

/- English proof (translation)
Establish `h0 : 3 • latticePoint L t = 0`. Rewrite using `[← latticePointHom_apply, ← map_nsmul, latticePointHom_apply, latticePoint_eq_zero_iff]`. Simplify using `using h`. Rewrite `h0` using `[latticePoint_of_notMem L ht, three_nsmul_eq_zero_iff]`. Simplify using `only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, latticeCurve, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] at h0`.

Take the linear combination `h0`.
-/
theorem quartic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : 3 * t ∈ L.lattice) :
    3 * ℘[L] t ^ 4 - 3 / 2 * L.g₂ * ℘[L] t ^ 2 - 3 * L.g₃ * ℘[L] t - L.g₂ ^ 2 / 16 = 0 := by
  have h0 : 3 • latticePoint L t = 0 := by
    rw [← latticePointHom_apply, ← map_nsmul, latticePointHom_apply, latticePoint_eq_zero_iff]
    simpa using h
  rw [latticePoint_of_notMem L ht, three_nsmul_eq_zero_iff] at h0
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, latticeCurve, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] at h0
  linear_combination h0

/- English proof (translation)
Establish `h1 : G = 4 * (x ^ 2 + x * y + y ^ 2)` using `mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination hy - hx)`. Establish `h2 : T = 4 * x ^ 3 - G * x` using `by linear_combination -hx`. Rewrite using `[h2, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cubic_discr {G T x y : ℂ} (hx : 4 * x ^ 3 - G * x - T = 0) (hy : 4 * y ^ 3 - G * y - T = 0) (hxy : x ≠ y) :
    (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) ^ 2 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : G = 4 * (x ^ 2 + x * y + y ^ 2) :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination hy - hx)
  have h2 : T = 4 * x ^ 3 - G * x := by linear_combination -hx
  rw [h2, h1]; ring

/- English proof (translation)
Establish `h1 : T = (x + y) * (x ^ 2 + y ^ 2) - G * (x + y) / 2` using `mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination (hy - hx) / 3)`. Establish `h2 : -3 * (x * y) * ((x + y) ^ 2 - x * y) + 3 / 2 * G * (x * y) - G ^ 2 / 16 = 0` using `mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination x * hy - y * hx)`. Rewrite using `[h1]`. Take the linear combination `36 * (x + y) ^ 2 * h2`.
-/
theorem quartic_discr {G T x y : ℂ} (hx : 3 * x ^ 4 - 3 / 2 * G * x ^ 2 - 3 * T * x - G ^ 2 / 16 = 0)
    (hy : 3 * y ^ 4 - 3 / 2 * G * y ^ 2 - 3 * T * y - G ^ 2 / 16 = 0) (hxy : x ≠ y) :
    (G - 3 * (x + y) ^ 2) ^ 3 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : T = (x + y) * (x ^ 2 + y ^ 2) - G * (x + y) / 2 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination (hy - hx) / 3)
  have h2 : -3 * (x * y) * ((x + y) ^ 2 - x * y) + 3 / 2 * G * (x * y) - G ^ 2 / 16 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination x * hy - y * hx)
  rw [h1]
  linear_combination 36 * (x + y) ^ 2 * h2

/- English proof (translation)
Establish `k : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u → 3 * (x ^ 3 + x ^ 2 * u + x * u ^ 2 + u ^ 3) - A * (x + u) - B = 0` using `fun u hu h => mul_left_cancel₀ (sub_ne_zero.2 h) (by linear_combination hx - hu)`. Establish `k' : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u → y ≠ u → 3 * (x ^ 2 + x * (y + u) + (y ^ 2 + y * u + u ^ 2)) - A = 0` using `fun u hu h h' => mul_left_cancel₀ (sub_ne_zero.2 h') (by linear_combination k y hy hxy - k u hu h)`. Conclude with `mul_left_cancel₀ (sub_ne_zero.2 hzw) (by linear_combination (k' z hz hxz hyz - k' w hw hxw hyw) / 3)`.
-/
theorem quartic_sum {A B C x y z w : ℂ} (hx : 3 * x ^ 4 - A * x ^ 2 - B * x - C = 0)
    (hy : 3 * y ^ 4 - A * y ^ 2 - B * y - C = 0) (hz : 3 * z ^ 4 - A * z ^ 2 - B * z - C = 0)
    (hw : 3 * w ^ 4 - A * w ^ 2 - B * w - C = 0) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : z + w = -(x + y) := by
  have k : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u →
      3 * (x ^ 3 + x ^ 2 * u + x * u ^ 2 + u ^ 3) - A * (x + u) - B = 0 := fun u hu h =>
    mul_left_cancel₀ (sub_ne_zero.2 h) (by linear_combination hx - hu)
  have k' : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u → y ≠ u →
      3 * (x ^ 2 + x * (y + u) + (y ^ 2 + y * u + u ^ 2)) - A = 0 := fun u hu h h' =>
    mul_left_cancel₀ (sub_ne_zero.2 h') (by linear_combination k y hy hxy - k u hu h)
  exact mul_left_cancel₀ (sub_ne_zero.2 hzw) (by linear_combination (k' z hz hxz hyz - k' w hw hxw hyw) / 3)

/- English proof (translation)
Establish `uniq : ∀ a b : ℤ, (a : ℂ) * L.ω₁ + b * L.ω₂ = 0 → a = 0 ∧ b = 0` using `fun a b h => by`. Use `LinearIndependent.pair_iff.1 L.indep (a : ℝ) (b : ℝ) (by simpa using h)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Take `⟨a, b, h1⟩` from `mem_lattice.1 (hL _ L.ω₁_mem_lattice)`. Take `⟨c, e, h2⟩` from `mem_lattice.1 (hL _ L.ω₂_mem_lattice)`.

Take `⟨q1, q2⟩` from `uniq (a ^ 2 + b * c + d) (b * (a + e)) (by`. Use `push_cast`. Take the linear combination `(a + β) * h1 + b * h2 + L.ω₁ * hβ)`. Establish `hb : b ≠ 0` using `by rintro rfl; nlinarith [sq_nonneg a]`. Take `rfl : e = -a` from `by have := (mul_eq_zero.1 q2).resolve_left hb; omega`.

Establish `key : ∀ x y ε : ℤ, (β - ε) * ((x * L.ω₁ + y * L.ω₂) / 3) ∈ L.lattice → (x * a + y * c - ε * x) % 3 = 0 ∧ (x * b - y * a - ε * y) % 3 = 0` using `fun x y ε h => by`. Take `⟨m, n, h⟩` from `mem_lattice.1 h`. Take `⟨r1, r2⟩` from `uniq (x * a + y * c - ε * x - 3 * m) (x * b - y * a - ε * y - 3 * n) (by`. Move the coercions through the operations in `at h2 ⊢`. Take the linear combination `x * h1 + y * h2 - 3 * h)`.

Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hcon`. Establish `k : ∀ x y : ℤ, ((x * a + y * c - 1 * x) % 3 = 0 ∧ (x * b - y * a - 1 * y) % 3 = 0) ∨ ((x * a + y * c - (-1) * x) % 3 = 0 ∧ (x * b - y * a - (-1) * y) % 3 = 0)` using `fun x y => by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_or]`.

Use `hcon ⟨(x * L.ω₁ + y * L.ω₂) / 3, mem_lattice.2 ⟨x, y, by ring⟩, fun h' => h.1 (key x y 1 ?_), fun h' => h.2 (key x y (-1) ?_)⟩` and prove the remaining obligations. Simplify using `using h'`. Simplify using `using h'`. Establish `k1` using `k 1 0`. Establish `k2` using `k 0 1`.

Establish `k3` using `k 1 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_order_three (L : PeriodPair) {β : ℂ} {d : ℕ} (hd : 0 < d) (hβ : β ^ 2 = -d)
    (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ t, 3 * t ∈ L.lattice ∧ (β - 1) * t ∉ L.lattice ∧ (β + 1) * t ∉ L.lattice := by
  have uniq : ∀ a b : ℤ, (a : ℂ) * L.ω₁ + b * L.ω₂ = 0 → a = 0 ∧ b = 0 := fun a b h => by
    have := LinearIndependent.pair_iff.1 L.indep (a : ℝ) (b : ℝ) (by simpa using h)
    exact_mod_cast this
  obtain ⟨a, b, h1⟩ := mem_lattice.1 (hL _ L.ω₁_mem_lattice)
  obtain ⟨c, e, h2⟩ := mem_lattice.1 (hL _ L.ω₂_mem_lattice)
  obtain ⟨q1, q2⟩ := uniq (a ^ 2 + b * c + d) (b * (a + e)) (by
    push_cast
    linear_combination (a + β) * h1 + b * h2 + L.ω₁ * hβ)
  have hb : b ≠ 0 := by rintro rfl; nlinarith [sq_nonneg a]
  obtain rfl : e = -a := by have := (mul_eq_zero.1 q2).resolve_left hb; omega
  have key : ∀ x y ε : ℤ, (β - ε) * ((x * L.ω₁ + y * L.ω₂) / 3) ∈ L.lattice →
      (x * a + y * c - ε * x) % 3 = 0 ∧ (x * b - y * a - ε * y) % 3 = 0 := fun x y ε h => by
    obtain ⟨m, n, h⟩ := mem_lattice.1 h
    obtain ⟨r1, r2⟩ := uniq (x * a + y * c - ε * x - 3 * m) (x * b - y * a - ε * y - 3 * n) (by
      push_cast at h2 ⊢
      linear_combination x * h1 + y * h2 - 3 * h)
    omega
  by_contra hcon
  have k : ∀ x y : ℤ, ((x * a + y * c - 1 * x) % 3 = 0 ∧ (x * b - y * a - 1 * y) % 3 = 0) ∨
      ((x * a + y * c - (-1) * x) % 3 = 0 ∧ (x * b - y * a - (-1) * y) % 3 = 0) := fun x y => by
    by_contra h
    rw [not_or] at h
    refine hcon ⟨(x * L.ω₁ + y * L.ω₂) / 3, mem_lattice.2 ⟨x, y, by ring⟩, fun h' => h.1 (key x y 1 ?_),
      fun h' => h.2 (key x y (-1) ?_)⟩
    · simpa using h'
    · simpa using h'
  have k1 := k 1 0
  have k2 := k 0 1
  have k3 := k 1 1
  omega

/- English proof (translation)
Take `⟨η, -, e3, h⟩` from `exists_action L σ h2 h3`. Take `⟨t', h⟩` from `h t`. Establish `hs' : ∀ l ∈ L.lattice, (1 - w) * l ∈ L.lattice` using `fun l hl => by`. Rewrite using `[sub_mul, one_mul]`. Conclude with `sub_mem hl (hs l hl)`.

Take `⟨a1, a2⟩` from `h w hσ hs`. Take `⟨b1, b2⟩` from `h (1 - w) (by rw [map_sub, map_one, hσ]) hs'`. Take `⟨c1, -⟩` from `h 2 (map_ofNat σ 2) fun l hl => by rw [two_mul]; exact add_mem hl hl`. Establish `hlat : GlobalTheory.ThetaConj.IsLat L.lattice.toAddSubgroup`. Use `⟨L.ω₁, L.ω₂, L.indep, ?_⟩` and prove the remaining obligations.

Use extensionality with `z`. Rewrite using `[AddSubgroup.mem_closure_pair, Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice]`. Simplify using `only [zsmul_eq_mul]`. Establish `hu : t - t' ∈ L.lattice` using `GlobalTheory.ThetaConj.two_torsion_unique hlat w k hw t2 ta tb (c1.1 t2) (mt a1.2 ta) (mt b1.2 tb) hs`. Establish `ea : ℘[L] (w * t) = ℘[L] (w * t')` using `(weierstrassP_eq_iff L ta (mt a1.2 ta)).2 (.inl (by rw [← mul_sub]; exact hs _ hu))`.

Establish `eb : ℘[L] ((1 - w) * t) = ℘[L] ((1 - w) * t')` using `(weierstrassP_eq_iff L tb (mt b1.2 tb)).2 (.inl (by rw [← mul_sub]; exact hs' _ hu))`. Establish `fa` using `a2 ta`. Establish `fb` using `b2 tb`. Rewrite `fa` using `[← ea]`. Rewrite `fb` using `[← eb]`.

Establish `ha2 : w * t + w * t ∈ L.lattice` using `by convert hs _ t2 using 1; ring`. Establish `hb2 : (1 - w) * t + (1 - w) * t ∈ L.lattice` using `by convert hs' _ t2 using 1; ring`. Establish `hne : ℘[L] (w * t) ≠ ℘[L] ((1 - w) * t)` using `fun e => by`. Establish `ht : t ∈ L.lattice`. Break down `(weierstrassP_eq_iff L ta tb).1 e with e | e` into its components or cases.

Use `add_mem e hb2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `e using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `ta (hs _ ht)`.

Establish `hd` using `cubic_discr (cubic_eq_zero L ta ha2) (cubic_eq_zero L tb hb2) hne`. Rewrite `hd` using `[hΔ]`. Generalize the expression as in `℘[L] (w * t) = x at *`. Generalize the expression as in `℘[L] ((1 - w) * t) = y at *`. Establish `hP : σ (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) = η ^ 3 * (4 * ((x - y) * (2 * x + y) * (x + 2 * y)))`.

Simplify using `only [map_mul, map_add, map_sub, map_ofNat, fa, fb]`. Expand and normalize the polynomial expressions, which then agree. Establish `: η ^ 3 = 1`. Apply the tactic sequence `rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hd.trans (one_pow 2).symm) with e | e <;> rw [e] at hP`. Simplify using `using hP.symm`.

Simplify using `using hP.symm`. Rewrite using `[e3, this, one_mul]`.
-/
theorem map_g₃ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {w : ℂ} {k : ℤ} (hw : w * (1 - w) = 2 * k)
    (hs : ∀ l ∈ L.lattice, w * l ∈ L.lattice) {t : ℂ} (t2 : 2 * t ∈ L.lattice) (ta : w * t ∉ L.lattice)
    (tb : (1 - w) * t ∉ L.lattice) (σ : ℂ ≃+* ℂ) (hσ : σ w = w) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3)
    (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) : σ L.g₃ = L.g₃ := by
  obtain ⟨η, -, e3, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have hs' : ∀ l ∈ L.lattice, (1 - w) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hs l hl)
  obtain ⟨a1, a2⟩ := h w hσ hs
  obtain ⟨b1, b2⟩ := h (1 - w) (by rw [map_sub, map_one, hσ]) hs'
  obtain ⟨c1, -⟩ := h 2 (map_ofNat σ 2) fun l hl => by rw [two_mul]; exact add_mem hl hl
  have hlat : GlobalTheory.ThetaConj.IsLat L.lattice.toAddSubgroup := by
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [AddSubgroup.mem_closure_pair, Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice]
    simp only [zsmul_eq_mul]
  have hu : t - t' ∈ L.lattice := GlobalTheory.ThetaConj.two_torsion_unique hlat w k hw t2 ta tb (c1.1 t2)
    (mt a1.2 ta) (mt b1.2 tb) hs
  have ea : ℘[L] (w * t) = ℘[L] (w * t') :=
    (weierstrassP_eq_iff L ta (mt a1.2 ta)).2 (.inl (by rw [← mul_sub]; exact hs _ hu))
  have eb : ℘[L] ((1 - w) * t) = ℘[L] ((1 - w) * t') :=
    (weierstrassP_eq_iff L tb (mt b1.2 tb)).2 (.inl (by rw [← mul_sub]; exact hs' _ hu))
  have fa := a2 ta
  have fb := b2 tb
  rw [← ea] at fa
  rw [← eb] at fb
  have ha2 : w * t + w * t ∈ L.lattice := by convert hs _ t2 using 1; ring
  have hb2 : (1 - w) * t + (1 - w) * t ∈ L.lattice := by convert hs' _ t2 using 1; ring
  have hne : ℘[L] (w * t) ≠ ℘[L] ((1 - w) * t) := fun e => by
    have ht : t ∈ L.lattice := by
      rcases (weierstrassP_eq_iff L ta tb).1 e with e | e
      · convert add_mem e hb2 using 1; ring
      · convert e using 1; ring
    exact ta (hs _ ht)
  have hd := cubic_discr (cubic_eq_zero L ta ha2) (cubic_eq_zero L tb hb2) hne
  rw [hΔ] at hd
  generalize ℘[L] (w * t) = x at *
  generalize ℘[L] ((1 - w) * t) = y at *
  have hP : σ (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) = η ^ 3 * (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) := by
    simp only [map_mul, map_add, map_sub, map_ofNat, fa, fb]; ring
  have : η ^ 3 = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hd.trans (one_pow 2).symm) with e | e <;> rw [e] at hP
    · simpa using hP.symm
    · simpa using hP.symm
  rw [e3, this, one_mul]

/- English proof (translation)
Establish `hββ : ∀ t, 3 * t ∈ L.lattice → β * (β * t) - t ∈ L.lattice ∨ β * (β * t) + t ∈ L.lattice` using `fun t ht => by`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn | hn⟩ : ∃ n : ℕ, d + 1 = 3 * n ∨ d = 3 * n + 1 := by`. Break down `(show d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h` into its components or cases. Conclude with `⟨d / 3, .inr (by omega)⟩`. Conclude with `⟨d / 3 + 1, .inl (by omega)⟩`.

Establish `hn' : (d : ℂ) + 1 = 3 * n` using `by exact_mod_cast hn left`. Use `neg_mem (nsmul_mem ht n) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[nsmul_eq_mul]`. Take the linear combination `t * hβ - t * hn'`. Establish `hn' : (d : ℂ) = 3 * n + 1` using `by exact_mod_cast hn right`.

Use `neg_mem (nsmul_mem ht n) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[nsmul_eq_mul]`. Take the linear combination `t * hβ - t * hn'`. Establish `h3β : ∀ t, 3 * t ∈ L.lattice → 3 * (β * t) ∈ L.lattice` using `fun t ht => by`. Rewrite using `[mul_left_comm]`.

Conclude with `hs _ ht`. Establish `hnβ : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → β * t ∉ L.lattice` using `fun t ht hn h => hn <| by`. Break down `hββ t ht with e | e` into its components or cases. Simplify using `using sub_mem (hs _ h) e`. Simplify using `using sub_mem e (hs _ h)`.

Establish `hA : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] (β * (β * t)) = ℘[L] t` using `fun t ht hn => (weierstrassP_eq_iff L (hnβ _ (h3β t ht) (hnβ t ht hn)) hn).2 (hββ t ht)`. Establish `hB : ∀ s t, 3 * s ∈ L.lattice → s ∉ L.lattice → 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] s = ℘[L] t → ℘[L] (β * s) = ℘[L] (β * t)` using `fun s t s3 sn t3 tn e => by`. Rewrite using `[weierstrassP_eq_iff L (hnβ s s3 sn) (hnβ t t3 tn), ← mul_sub, ← mul_add]`. Conclude with `((weierstrassP_eq_iff L sn tn).1 e).imp (hs _) (hs _)`. Establish `hs1 : ∀ l ∈ L.lattice, (β - 1) * l ∈ L.lattice` using `fun l hl => by`.

Rewrite using `[sub_mul, one_mul]`. Conclude with `sub_mem (hs l hl) hl`. Establish `hs2 : ∀ l ∈ L.lattice, (β + 1) * l ∈ L.lattice` using `fun l hl => by`. Rewrite using `[add_mul, one_mul]`. Conclude with `add_mem (hs l hl) hl`.

Establish `hne : ∀ t, 3 * t ∈ L.lattice → (β - 1) * t ∉ L.lattice → (β + 1) * t ∉ L.lattice → ℘[L] t ≠ ℘[L] (β * t)` using `fun t ht a b e => by`. Establish `tn : t ∉ L.lattice` using `fun h => a (hs1 _ h)`. Break down `(weierstrassP_eq_iff L (hnβ t ht tn) tn).1 e.symm with e | e` into its components or cases. Conclude with `a (by convert e using 1; ring)`. Conclude with `b (by convert e using 1; ring)`.

Take `⟨t, t3, ta, tb⟩` from `exists_order_three L (Nat.pos_of_ne_zero (by rintro rfl; simp at hd)) hβ hs`. Establish `tn : t ∉ L.lattice` using `fun h => ta (hs1 _ h)`. Establish `hx` using `quartic_eq_zero L tn t3`. Establish `hy` using `quartic_eq_zero L (hnβ t t3 tn) (h3β t t3)`. Establish `hv` using `quartic_discr hx hy (hne t t3 ta tb)`.

Rewrite `hv` using `[hΔ]`. Use `⟨(L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2)⁻¹, by rw [inv_pow, hv, inv_one], fun σ hσ h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨η, e2, -, h⟩` from `exists_action L σ h2 h3`. Take `⟨t', h⟩` from `h t`. Establish `t3'` using `(h 3 (map_ofNat σ 3) fun l hl => by simpa using nsmul_mem hl 3).1.1 t3`.

Establish `ta'` using `mt (h (β - 1) (by rw [map_sub, map_one, hσ]) hs1).1.2 ta`. Establish `tb'` using `mt (h (β + 1) (by rw [map_add, map_one, hσ]) hs2).1.2 tb`. Establish `tn' : t' ∉ L.lattice` using `fun h => ta' (hs1 _ h)`. Establish `fx` using `(h 1 (map_one σ) fun l hl => by simpa using hl).2 (by simpa using tn)`. Rewrite `fx` using `[one_mul, one_mul]`.

Establish `fy` using `(h β hσ hs).2 (hnβ t t3 tn)`. Establish `hsq : (℘[L] t' + ℘[L] (β * t')) ^ 2 = (℘[L] t + ℘[L] (β * t)) ^ 2`. Distinguish the cases in `c1 : ℘[L] t = ℘[L] t'`. Rewrite using `[hB _ _ t3 tn t3' tn' c1, c1]`. Distinguish the cases in `c2 : ℘[L] t = ℘[L] (β * t')`.

Rewrite using `[hB _ _ t3 tn (h3β _ t3') (hnβ _ t3' tn') c2, hA _ t3' tn', c2, add_comm]`. Establish `c3 : ℘[L] (β * t) ≠ ℘[L] t'` using `fun e => c2 (by`. Rewrite using `[← hB _ _ (h3β _ t3) (hnβ _ t3 tn) t3' tn' e, hA _ t3 tn])`. Establish `c4 : ℘[L] (β * t) ≠ ℘[L] (β * t')` using `fun e => c1 (by`. Rewrite using `[← hA _ t3 tn, hB _ _ (h3β _ t3) (hnβ _ t3 tn) (h3β _ t3') (hnβ _ t3' tn') e, hA _ t3' tn'])`.

Rewrite using `[quartic_sum hx hy (quartic_eq_zero L tn' t3') (quartic_eq_zero L (hnβ _ t3' tn') (h3β _ t3')) (hne t t3 ta tb) c1 c2 c3 c4 (hne t' t3' ta' tb'), neg_sq]`. Establish `hσv : σ (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) = η ^ 2 * (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2)`. Rewrite using `[map_sub, map_mul, map_pow, map_add, map_ofNat, fx, fy, e2, ← hsq]`. Expand and normalize the polynomial expressions, which then agree. Generalize the expression as in `L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2 = v at hv hσv`.

Establish `hv0 : v ≠ 0` using `by rintro rfl; simp at hv`. Establish `hη : η ^ 2 ≠ 0` using `left_ne_zero_of_mul (hσv ▸ (map_ne_zero σ).2 hv0)`. Rewrite using `[map_mul, map_inv₀, hσv, e2, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hη, one_mul]`.
-/
theorem exists_map_g₂ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {β : ℂ} {d : ℕ} (hd : d % 3 ≠ 0)
    (hβ : β ^ 2 = -d) (hs : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ u : ℂ, u ^ 3 = 1 ∧ ∀ σ : ℂ ≃+* ℂ, σ β = β → σ (L.g₂ ^ 3) = L.g₂ ^ 3 → σ (L.g₃ ^ 2) = L.g₃ ^ 2 →
      σ (u * L.g₂) = u * L.g₂ := by
  have hββ : ∀ t, 3 * t ∈ L.lattice → β * (β * t) - t ∈ L.lattice ∨ β * (β * t) + t ∈ L.lattice := fun t ht => by
    obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, d + 1 = 3 * n ∨ d = 3 * n + 1 := by
      rcases (show d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h
      · exact ⟨d / 3, .inr (by omega)⟩
      · exact ⟨d / 3 + 1, .inl (by omega)⟩
    · have hn' : (d : ℂ) + 1 = 3 * n := by exact_mod_cast hn
      left
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
    · have hn' : (d : ℂ) = 3 * n + 1 := by exact_mod_cast hn
      right
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
  have h3β : ∀ t, 3 * t ∈ L.lattice → 3 * (β * t) ∈ L.lattice := fun t ht => by
    rw [mul_left_comm]; exact hs _ ht
  have hnβ : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → β * t ∉ L.lattice := fun t ht hn h => hn <| by
    rcases hββ t ht with e | e
    · simpa using sub_mem (hs _ h) e
    · simpa using sub_mem e (hs _ h)
  have hA : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] (β * (β * t)) = ℘[L] t := fun t ht hn =>
    (weierstrassP_eq_iff L (hnβ _ (h3β t ht) (hnβ t ht hn)) hn).2 (hββ t ht)
  have hB : ∀ s t, 3 * s ∈ L.lattice → s ∉ L.lattice → 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] s = ℘[L] t →
      ℘[L] (β * s) = ℘[L] (β * t) := fun s t s3 sn t3 tn e => by
    rw [weierstrassP_eq_iff L (hnβ s s3 sn) (hnβ t t3 tn), ← mul_sub, ← mul_add]
    exact ((weierstrassP_eq_iff L sn tn).1 e).imp (hs _) (hs _)
  have hs1 : ∀ l ∈ L.lattice, (β - 1) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem (hs l hl) hl
  have hs2 : ∀ l ∈ L.lattice, (β + 1) * l ∈ L.lattice := fun l hl => by
    rw [add_mul, one_mul]; exact add_mem (hs l hl) hl
  have hne : ∀ t, 3 * t ∈ L.lattice → (β - 1) * t ∉ L.lattice → (β + 1) * t ∉ L.lattice →
      ℘[L] t ≠ ℘[L] (β * t) := fun t ht a b e => by
    have tn : t ∉ L.lattice := fun h => a (hs1 _ h)
    rcases (weierstrassP_eq_iff L (hnβ t ht tn) tn).1 e.symm with e | e
    · exact a (by convert e using 1; ring)
    · exact b (by convert e using 1; ring)
  obtain ⟨t, t3, ta, tb⟩ := exists_order_three L (Nat.pos_of_ne_zero (by rintro rfl; simp at hd)) hβ hs
  have tn : t ∉ L.lattice := fun h => ta (hs1 _ h)
  have hx := quartic_eq_zero L tn t3
  have hy := quartic_eq_zero L (hnβ t t3 tn) (h3β t t3)
  have hv := quartic_discr hx hy (hne t t3 ta tb)
  rw [hΔ] at hv
  refine ⟨(L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2)⁻¹, by rw [inv_pow, hv, inv_one], fun σ hσ h2 h3 => ?_⟩
  obtain ⟨η, e2, -, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have t3' := (h 3 (map_ofNat σ 3) fun l hl => by simpa using nsmul_mem hl 3).1.1 t3
  have ta' := mt (h (β - 1) (by rw [map_sub, map_one, hσ]) hs1).1.2 ta
  have tb' := mt (h (β + 1) (by rw [map_add, map_one, hσ]) hs2).1.2 tb
  have tn' : t' ∉ L.lattice := fun h => ta' (hs1 _ h)
  have fx := (h 1 (map_one σ) fun l hl => by simpa using hl).2 (by simpa using tn)
  rw [one_mul, one_mul] at fx
  have fy := (h β hσ hs).2 (hnβ t t3 tn)
  have hsq : (℘[L] t' + ℘[L] (β * t')) ^ 2 = (℘[L] t + ℘[L] (β * t)) ^ 2 := by
    by_cases c1 : ℘[L] t = ℘[L] t'
    · rw [hB _ _ t3 tn t3' tn' c1, c1]
    by_cases c2 : ℘[L] t = ℘[L] (β * t')
    · rw [hB _ _ t3 tn (h3β _ t3') (hnβ _ t3' tn') c2, hA _ t3' tn', c2, add_comm]
    have c3 : ℘[L] (β * t) ≠ ℘[L] t' := fun e => c2 (by
      rw [← hB _ _ (h3β _ t3) (hnβ _ t3 tn) t3' tn' e, hA _ t3 tn])
    have c4 : ℘[L] (β * t) ≠ ℘[L] (β * t') := fun e => c1 (by
      rw [← hA _ t3 tn, hB _ _ (h3β _ t3) (hnβ _ t3 tn) (h3β _ t3') (hnβ _ t3' tn') e, hA _ t3' tn'])
    rw [quartic_sum hx hy (quartic_eq_zero L tn' t3') (quartic_eq_zero L (hnβ _ t3' tn') (h3β _ t3'))
      (hne t t3 ta tb) c1 c2 c3 c4 (hne t' t3' ta' tb'), neg_sq]
  have hσv : σ (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) = η ^ 2 * (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) := by
    rw [map_sub, map_mul, map_pow, map_add, map_ofNat, fx, fy, e2, ← hsq]; ring
  generalize L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2 = v at hv hσv
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hη : η ^ 2 ≠ 0 := left_ne_zero_of_mul (hσv ▸ (map_ne_zero σ).2 hv0)
  rw [map_mul, map_inv₀, hσv, e2, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hη, one_mul]

end Lattice

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods

/- English proof (translation)
Take `⟨δ, h⟩` from `exists_discriminantTwelfthRoot_of_ideal D`. Establish `hc : Crv D D.host.ccK δ` using `⟨isCurveIdeal_ccK D, h⟩`. Take `⟨-, m2, m3⟩` from `data_of_fieldOK (M := coefM D) hF h fun x => ⟨x, rfl⟩`. Take `⟨hlat, -, hΔ, -, hO⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 _ δ hc`. Take `⟨L, hL⟩` from `GlobalTheory.ThetaConj.IsLat.exists_periodPair hlat`.

Take `⟨e2, e3, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL`. Rewrite `hΔ` using `[TaylorLogMetric.discr, e2, e3]`. Rewrite `m2` using `[e2]`. Rewrite `m3` using `[e3]`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`.

Establish `mw : w0 D ∈ coefM D` using `⟨D.embE _, by rw [← ha, ← D.embE_φ₀]; rfl⟩`. Establish `hs : ∀ l ∈ L.lattice, w0 D * l ∈ L.lattice` using `fun l hl => (hL _).1 (ha ▸ hO a l ((hL l).2 hl))`. Establish `key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ coefM D, σ y = y) → σ x = x) → x ∈ coefM D` using `fun x hx => by`. Take `⟨y, rfl⟩` from `GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := coefM D) x fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩`. Conclude with `y.2`.

Take `⟨k, hk⟩` from `GlobalTheory.ThetaConj.weylMatrix_mul_apply D`. Take `⟨t, ht⟩` from `(GlobalTheory.TwoTorsionPt.exists_point D _ δ hc).1`. Rewrite `ht` using `[GlobalTheory.ThetaConj.twoTorsionCMPoint_iff, hL, hL, hL]`. Establish `n3 : L.g₃ ∈ coefM D` using `key _ fun σ hσ => map_g₃ L hΔ hk hs ht.1 ht.2.1 ht.2.2 σ (hσ _ mw) (hσ _ m2) (hσ _ m3)`. Establish `hd : D.host.d % 3 ≠ 0` using `fun h3 => by`.

Use `(Nat.prime_dvd_prime_iff_eq Nat.prime_three D.host.hyp.2.1).1 (Nat.dvd_of_mod_eq_zero h3)` as an intermediate fact. Use `D.host.hyp.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`.

Simplify using the standard rewrite rules. Take `⟨u, hu, hσu⟩` from `exists_map_g₂ L hΔ (β := 2 * w0 D - 1) hd (by unfold w0; linear_combination ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hsq) fun l hl => by`. Use `sub_mem (add_mem (hs l hl) (hs l hl)) hl using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `n2 : u * L.g₂ ∈ coefM D` using `key _ fun σ hσ => hσu σ (by rw [map_sub, map_mul, map_ofNat, map_one, hσ _ mw]) (hσ _ m2) (hσ _ m3)`.

Establish `hu0 : u ^ 2 ≠ 0`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hu`. Establish `hmap : lamOf D D.host.ccK (u ^ 2 * δ) = (lamOf D D.host.ccK δ).map (AddMonoidHom.mulLeft (u ^ 2))`.

Rewrite using `[lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]`. Use `congr 1`. Use `ext`. Simplify using `[mul_assoc]`. Use `⟨u ^ 2 * δ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsDiscriminantTwelfthRootOfIdealLattice at h ⊢`. Rewrite using `[mul_pow, h, show (u ^ 2) ^ 12 = (u ^ 3) ^ 8 by ring, hu, one_pow, one_mul]`. Rewrite `n2` using `[← e2]`. Use `n2 using 1` and compare the differences between its conclusion and the goal. Unfold `g2`.

Rewrite using `[hmap, Model.eisG_map _ _ hu0, inv_eq_of_mul_eq_one_right (b := u) (by rw [show (u ^ 2) ^ (2 * 2) * u = (u ^ 3) ^ 3 by ring, hu, one_pow])]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `n3` using `[← e3]`. Use `n3 using 1` and compare the differences between its conclusion and the goal. Unfold `g3`.

Rewrite using `[hmap, Model.eisG_map _ _ hu0, show (u ^ 2) ^ (2 * 3) = (u ^ 3) ^ 4 by ring, hu]`. Simplify using the standard rewrite rules.
-/
theorem exists_delta_data (D : D7) (hF : FieldOK D.host D.what₂.embLL D.embE) :
    ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ g2 (lamOf D D.host.ccK δ) ∈ coefM D ∧ g3 (lamOf D D.host.ccK δ) ∈ coefM D := by
  obtain ⟨δ, h⟩ := exists_discriminantTwelfthRoot_of_ideal D
  have hc : Crv D D.host.ccK δ := ⟨isCurveIdeal_ccK D, h⟩
  obtain ⟨-, m2, m3⟩ := data_of_fieldOK (M := coefM D) hF h fun x => ⟨x, rfl⟩
  obtain ⟨hlat, -, hΔ, -, hO⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 _ δ hc
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaConj.IsLat.exists_periodPair hlat
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  rw [TaylorLogMetric.discr, e2, e3] at hΔ
  rw [e2] at m2
  rw [e3] at m3
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have mw : w0 D ∈ coefM D := ⟨D.embE _, by rw [← ha, ← D.embE_φ₀]; rfl⟩
  have hs : ∀ l ∈ L.lattice, w0 D * l ∈ L.lattice := fun l hl => (hL _).1 (ha ▸ hO a l ((hL l).2 hl))
  have key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ coefM D, σ y = y) → σ x = x) → x ∈ coefM D := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := coefM D) x
      fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩
    exact y.2
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  obtain ⟨t, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ δ hc).1
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff, hL, hL, hL] at ht
  have n3 : L.g₃ ∈ coefM D := key _ fun σ hσ =>
    map_g₃ L hΔ hk hs ht.1 ht.2.1 ht.2.2 σ (hσ _ mw) (hσ _ m2) (hσ _ m3)
  have hd : D.host.d % 3 ≠ 0 := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three D.host.hyp.2.1).1 (Nat.dvd_of_mod_eq_zero h3)
    have := D.host.hyp.2.2.2.1
    omega
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  obtain ⟨u, hu, hσu⟩ := exists_map_g₂ L hΔ (β := 2 * w0 D - 1) hd
    (by unfold w0; linear_combination ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hsq)
    fun l hl => by
      convert sub_mem (add_mem (hs l hl) (hs l hl)) hl using 1; ring
  have n2 : u * L.g₂ ∈ coefM D := key _ fun σ hσ =>
    hσu σ (by rw [map_sub, map_mul, map_ofNat, map_one, hσ _ mw]) (hσ _ m2) (hσ _ m3)
  have hu0 : u ^ 2 ≠ 0 := by
    refine pow_ne_zero _ ?_
    rintro rfl; simp at hu
  have hmap : lamOf D D.host.ccK (u ^ 2 * δ) = (lamOf D D.host.ccK δ).map (AddMonoidHom.mulLeft (u ^ 2)) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [mul_assoc]
  refine ⟨u ^ 2 * δ, ?_, ?_, ?_⟩
  · unfold IsDiscriminantTwelfthRootOfIdealLattice at h ⊢
    rw [mul_pow, h, show (u ^ 2) ^ 12 = (u ^ 3) ^ 8 by ring, hu, one_pow, one_mul]
  · rw [← e2] at n2
    convert n2 using 1
    unfold g2
    rw [hmap, Model.eisG_map _ _ hu0, inv_eq_of_mul_eq_one_right (b := u)
      (by rw [show (u ^ 2) ^ (2 * 2) * u = (u ^ 3) ^ 3 by ring, hu, one_pow])]
    ring
  · rw [← e3] at n3
    convert n3 using 1
    unfold g3
    rw [hmap, Model.eisG_map _ _ hu0, show (u ^ 2) ^ (2 * 3) = (u ^ 3) ^ 4 by ring, hu]
    simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.HalfPeriodTheta.theta_signed_translation D (GlobalTheory.InducedType.induced_type D).1 cc δ h t ht`. Use `⟨h1, fun x hx z => ?_, div_self fun h0 => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, e⟩` from `h2 x hx`. Establish `: Real.sqrt D.host.d / 2 * (GL3Theta.hf1 (lamOf D cc δ) x x).re = m`. Rewrite using `[← hm, q1, GL3Theta.hf1, Complex.mul_conj, Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.

Rewrite using `[GL3Theta.al1, this, round_intCast, e]`. Apply `GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t h ht` to reduce the goal to its premises. Unfold `GL3Theta.th0`. Rewrite using `[h0]`. Simplify using `[nrm1Sq]`.
-/
theorem isTheta0_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} (h : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) : GL3Theta.IsTheta0 D.host.d (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HalfPeriodTheta.theta_signed_translation D (GlobalTheory.InducedType.induced_type D).1 cc δ h t ht
  refine ⟨h1, fun x hx z => ?_, div_self fun h0 => ?_⟩
  · obtain ⟨m, hm, e⟩ := h2 x hx
    have : Real.sqrt D.host.d / 2 * (GL3Theta.hf1 (lamOf D cc δ) x x).re = m := by
      rw [← hm, q1, GL3Theta.hf1, Complex.mul_conj, Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [GL3Theta.al1, this, round_intCast, e]
  · apply GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t h ht
    unfold GL3Theta.th0
    rw [h0]
    simp [nrm1Sq]

/- English proof (translation)
Use `⟨fun z => differentiableAt_conj_conj_iff.mpr (h.1 _), ?_, by simp [h.2.2]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ z`. Establish `e : (starRingEnd ℂ).toAddMonoidHom x = starRingEnd ℂ x` using `rfl`. Establish `e' : GL3Theta.al1 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ x) = starRingEnd ℂ (GL3Theta.al1 d Λ x)`. Unfold `GL3Theta.al1 GL3Theta.hf1`.

Rewrite using `[GlobalTheory.ThetaConj.area_conj, Complex.conj_conj, mul_comm ((starRingEnd ℂ) x) x, map_zpow₀, map_neg, map_one]`. Rewrite using `[e, e', GlobalTheory.ThetaConj.thetaTranslate_conjugateLattice]`. Simplify using `only [Function.comp]`. Rewrite using `[← map_mul, h.2.1 x hx]`.
-/
theorem isTheta0_conj {d : ℕ} {Λ : AddSubgroup ℂ} {G : ℂ → ℂ} (h : GL3Theta.IsTheta0 d Λ G) :
    GL3Theta.IsTheta0 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) := by
  refine ⟨fun z => differentiableAt_conj_conj_iff.mpr (h.1 _), ?_, by simp [h.2.2]⟩
  rintro _ ⟨x, hx, rfl⟩ z
  have e : (starRingEnd ℂ).toAddMonoidHom x = starRingEnd ℂ x := rfl
  have e' : GL3Theta.al1 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ x) =
      starRingEnd ℂ (GL3Theta.al1 d Λ x) := by
    unfold GL3Theta.al1 GL3Theta.hf1
    rw [GlobalTheory.ThetaConj.area_conj, Complex.conj_conj, mul_comm ((starRingEnd ℂ) x) x, map_zpow₀, map_neg, map_one]
  rw [e, e', GlobalTheory.ThetaConj.thetaTranslate_conjugateLattice]
  simp only [Function.comp]
  rw [← map_mul, h.2.1 x hx]

/- English proof (translation)
Take `⟨cc', δ', h', e | e⟩` from `lamConj_cases h hM ρ`. Rewrite `ht`, the goal using `[e]`. Conclude with `isTheta0_lamOf h' ht`. Establish `h1` using `GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht`. Rewrite `h1` using `[e]`.

Establish `h2` using `isTheta0_conj (isTheta0_lamOf h' h1)`. Rewrite `h2` using `[← GlobalTheory.ThetaConj.evenTheta_conjugateLattice (GlobalTheory.ThetaConj.isLat_lamOf h'), ← e, GlobalTheory.ThetaConj.conj_conj_lat, Complex.conj_conj]`. Conclude with `h2`.
-/
theorem isTheta0_lamConj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} {M : IntermediateField ℚ ℂ} (h : Crv D cc δ)
    (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ⊢; exact isTheta0_lamOf h' ht
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    rw [e] at h1
    have h2 := isTheta0_conj (isTheta0_lamOf h' h1)
    rw [← GlobalTheory.ThetaConj.evenTheta_conjugateLattice (GlobalTheory.ThetaConj.isLat_lamOf h'), ← e, GlobalTheory.ThetaConj.conj_conj_lat,
      Complex.conj_conj] at h2
    exact h2

open Formalism.L2.GlobalTheoryTheory in

/- English proof (translation)
Take `⟨hc, hM, -, hth⟩` from `perTie_retie hF h h2 h3`. Use `⟨⟨coefM D, inferInstance, (imEquiv D.what₂.embLL).toRingEquiv, fun _ => rfl, hM, fun τ => ?_⟩, hM, fun s => ?_⟩` and prove the remaining obligations. Establish `hL : ∀ x, D.what₂.embLL x ∈ coefM D` using `fun x => ⟨x, rfl⟩`. Use `⟨_, (span_gen hF hL τ).symm, fun s : D.what₂.LL →+* ℂ => ?_⟩` and prove the remaining obligations. Establish `hs : ∀ x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x)` using `fun x => (rhoOf_imEquiv D.what₂.embLL s x).symm`.

Take `⟨ζ, hζ, e⟩` from `conjLat_eq hF h hL hM _ s hs`. Establish `h1 : (retie D).gx.Om τ s = _` using `Model.om_eq D.host hF D.eTau τ s`. Rewrite `h1` using `[e, area_map_unit _ (norm_eq_one_of_pow hζ), hs]`. Rewrite using `[h1, inv_div]`. Both sides reduce to the same expression.

Take `⟨t, ht⟩` from `exists_isThetaZero hc hM (rhoOf D.what₂.embLL s)`. Conclude with `⟨_, (is_theta_zero_iff _ _ _).1 (isTheta0_lamConj hc hM _ ht), hth s t ht⟩`.
-/
theorem ties_of_data {D : D7} {δ : ℂ} (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (h2 : g2 (lamOf D D.host.ccK δ) ∈ coefM D) (h3 : g3 (lamOf D D.host.ccK δ) ∈ coefM D) :
    OmegaCompatible (retie D) δ ∧ DataIn D (tor0 D D.host.ccK δ) (coefM D) ∧ ∀ s : D.what₂.LL →+* ℂ,
      ∃ G, IsTheta0 D.host.d (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G ∧
        (retie D).gx.thOne s ^ 2 = normSq1 (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G := by
  obtain ⟨hc, hM, -, hth⟩ := perTie_retie hF h h2 h3
  refine ⟨⟨coefM D, inferInstance, (imEquiv D.what₂.embLL).toRingEquiv, fun _ => rfl, hM, fun τ => ?_⟩, hM,
    fun s => ?_⟩
  · have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
    refine ⟨_, (span_gen hF hL τ).symm, fun s : D.what₂.LL →+* ℂ => ?_⟩
    have hs : ∀ x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x) := fun x =>
      (rhoOf_imEquiv D.what₂.embLL s x).symm
    obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM _ s hs
    have h1 : (retie D).gx.Om τ s = _ := Model.om_eq D.host hF D.eTau τ s
    rw [e, area_map_unit _ (norm_eq_one_of_pow hζ), hs] at h1
    rw [h1, inv_div]
    rfl
  · obtain ⟨t, ht⟩ := exists_isThetaZero hc hM (rhoOf D.what₂.embLL s)
    exact ⟨_, (is_theta_zero_iff _ _ _).1 (isTheta0_lamConj hc hM _ ht), hth s t ht⟩

end GlobalTheory.Mem.PeriodTie
