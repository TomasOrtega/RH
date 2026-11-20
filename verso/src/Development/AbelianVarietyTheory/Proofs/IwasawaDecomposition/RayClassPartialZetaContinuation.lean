import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEpsteinZetaContinuationStatement

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hc` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)`. Establish `hr` using `InfinitePlace.card_add_two_mul_card_eq_rank (K := K)`. Rewrite `hr` using `[IsTotallyComplex.nrRealPlaces_eq_zero, h2]`. Rewrite `hc` using `[IsTotallyComplex.nrRealPlaces_eq_zero]`. Establish `h1 : Fintype.card (InfinitePlace K) = 1` using `by omega`.

Conclude with `Fintype.card_le_one_iff.1 h1.le v w`.
-/
theorem place_unique [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

/- English proof (translation)
Use `haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩`. Establish `hprod` using `InfinitePlace.prod_eq_abs_norm (x : K)`. Rewrite `hprod` using `[Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _))]`. Rewrite using `[hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, ← Algebra.coe_norm_int]`. Use `norm_cast`.
-/
theorem normSq_eq [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

/- English proof (translation)
Establish `hfin` using `Embeddings.finite_of_norm_le K ℂ 1`. Establish `hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1`. Introduce `u ψ`. Establish `h` using `normSq_eq h2 ψ (u : 𝓞 K)`. Rewrite `h` using `[Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h`. Use `haveI := hfin.to_subtype`. Use `Finite.of_injective (fun u : (𝓞 K)ˣ => (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ : {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_` and prove the remaining obligations. Introduce `u v huv`. Conclude with `Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))`.
-/
theorem finite_units [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by
  have hfin := Embeddings.finite_of_norm_le K ℂ 1
  have hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1 := by
    intro u ψ
    have h := normSq_eq h2 ψ (u : 𝓞 K)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun u : (𝓞 K)ˣ =>
    (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ :
      {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_
  intro u v huv
  exact Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))

/- English proof (translation)
Introduce `him`. Establish `h2 : Module.finrank ℚ K = 2`. Rewrite using `[← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `hb0 : (b 0 : K) ≠ 0`. Introduce `h`.

Conclude with `b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))`. Establish `ha0 : φ (b 0 : K) ≠ 0` using `(map_ne_zero φ).2 hb0`. Establish `hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0` using `(map_ne_zero _).2 ha0`. Use `set y : K := (b 1 : K) / (b 0 : K) with hy`. Establish `hφy : (φ y).im = 0`.

Establish `hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) / (Complex.normSq (φ (b 0 : K)) : ℂ)`. Rewrite using `[Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]`. Rewrite using `[hq, Complex.div_ofReal_im, him, zero_div]`. Distinguish the cases in `hyq : y ∈ Set.range (algebraMap ℚ K)`. Take `⟨q, hq⟩` from `hyq`.

Establish `hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K)`. Establish `hd : (q.den : K) ≠ 0` using `by exact_mod_cast q.den_nz`. Establish `h1 : (b 1 : K) = (q : K) * (b 0 : K)`. Rewrite using `[← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]`. Rewrite using `[h1, Rat.cast_def]`.

Clear the denominators using the available nonvanishing facts. Establish `hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢`. Simplify using `only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]`.

Move the coercions through the operations in `at hK ⊢`. Take the linear combination `hK`. Use `Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)] (by simpa [Fin.sum_univ_two] using hz) 1` as an intermediate fact. Simplify using `at this`. Establish `hli : LinearIndependent ℚ ![(1 : K), y]`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg`. Establish `hg1 : g 1 = 0`. Assume the negation of the conclusion as `hne`.

Apply `hyq` to reduce the goal to its premises. Use `⟨-(g 0) / g 1, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_ratCast]`. Use `push_cast`. Rewrite `hg` using `[Rat.smul_def, Rat.smul_def, mul_one]`.

Rewrite using `[div_eq_iff (by exact_mod_cast hne)]`. Take the linear combination `-hg`. Establish `hg0 : g 0 = 0`. Rewrite `hg` using `[hg1, zero_smul, add_zero, smul_eq_zero]`. Simplify using `using hg`.

Introduce `i`. Use `fin_cases i`. Conclude with `hg0`. Conclude with `hg1`. Establish `htop` using `hli.span_eq_top_of_card_eq_finrank' (by simp [h2])`.

Establish `hreal : ∀ x : K, (φ x).im = 0`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y])` using `htop ▸ Submodule.mem_top`. Take `⟨g, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℚ).1 hx`. Simplify using `[Fin.sum_univ_two, Rat.smul_def, hφy]`.

Establish `hR : ComplexEmbedding.IsReal φ`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.2 (hreal x)`.

Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)`.
-/
theorem im_ne_zero [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by
  intro him
  have h2 : Module.finrank ℚ K = 2 := by
    rw [← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))
  have ha0 : φ (b 0 : K) ≠ 0 := (map_ne_zero φ).2 hb0
  have hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0 := (map_ne_zero _).2 ha0
  set y : K := (b 1 : K) / (b 0 : K) with hy
  have hφy : (φ y).im = 0 := by
    have hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) /
        (Complex.normSq (φ (b 0 : K)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]
    rw [hq, Complex.div_ofReal_im, him, zero_div]
  by_cases hyq : y ∈ Set.range (algebraMap ℚ K)
  · obtain ⟨q, hq⟩ := hyq
    have hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K) := by
      have hd : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
      have h1 : (b 1 : K) = (q : K) * (b 0 : K) := by
        rw [← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]
      rw [h1, Rat.cast_def]
      field_simp
    have hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0 := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢
      simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]
      push_cast at hK ⊢
      linear_combination hK
    have := Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)]
      (by simpa [Fin.sum_univ_two] using hz) 1
    simp at this
  · have hli : LinearIndependent ℚ ![(1 : K), y] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have hg1 : g 1 = 0 := by
        by_contra hne
        apply hyq
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [eq_ratCast]
        push_cast
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hg
        rw [div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hg
      have hg0 : g 0 = 0 := by
        rw [hg1, zero_smul, add_zero, smul_eq_zero] at hg
        simpa using hg
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
    have hreal : ∀ x : K, (φ x).im = 0 := by
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y]) := htop ▸ Submodule.mem_top
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
      simp [Fin.sum_univ_two, Rat.smul_def, hφy]
    have hR : ComplexEmbedding.IsReal φ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.2 (hreal x)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex
      (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)

/- English proof (translation)
The claim follows from `|(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| = Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by classical set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl have he : ∀ j, ψ …`.
-/
theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]
    simp [map_sum, Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hIB : D.cls (I * B) = 1`. Rewrite using `[D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]`. Take `⟨a, b', ha, hb, ha1, hb1, hab⟩` from `(D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB`.

Establish `hmem : b' ∈ Ideal.span {a}`. Establish `: b' ∈ Ideal.span {a} * (I * B)`. Rewrite using `[hab]`. Conclude with `Ideal.mem_span_singleton_self b'`. Conclude with `Ideal.mul_le_left this`.

Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.1 hmem`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Establish `hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)}` using `by rw [mul_comm, hx]; exact hb1`. Establish `: x - 1 = (a * x - 1) - (a - 1) * x` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)`. Establish `hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x}`. Rewrite using `[hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]`. Establish `ha' : Ideal.span {a} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `ha`. Conclude with `(mul_left_cancel₀ ha' hspan).symm`. Introduce and unpack `⟨x, hx1, hx⟩`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx` using `[Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `mul_ne_zero hI0 hB0 hx.symm`. Establish `h1 : D.cls (I * B) = 1` using `by rw [← hx]; exact D.cls_span hx0 hx1`. Rewrite `h1` using `[D.cls_mul I B hI hB hI0 hB0, hc]`. Conclude with `mul_inv_eq_one.1 h1`.
-/
theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨a, b', ha, hb, ha1, hb1, hab⟩ :=
      (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB
    have hmem : b' ∈ Ideal.span {a} := by
      have : b' ∈ Ideal.span {a} * (I * B) := by
        rw [hab]; exact Ideal.mem_span_singleton_self b'
      exact Ideal.mul_le_left this
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_, ?_⟩
    · have hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [mul_comm, hx]; exact hb1
      have : x - 1 = (a * x - 1) - (a - 1) * x := by ring
      rw [this]
      exact Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)
    · have hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x} := by
        rw [hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
      have ha' : Ideal.span {a} ≠ 0 := by
        rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact ha
      exact (mul_left_cancel₀ ha' hspan).symm
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

/- English proof (translation)
Establish `hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N` using `fun y => ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩`. Set `g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N}` to `{ toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by`. Rewrite using `[add_sub_right_comm]`. Conclude with `N.add_mem h1 (hmemNB y).2⟩`. Use `invFun := fun x => ⟨x.1 - x₀, by`.

Rewrite using `[← Ideal.inf_eq_mul_of_isCoprime hB.symm]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: x.1 - x₀ = (x.1 - 1) - (x₀ - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `N.sub_mem x.2.2 h1`.

Conclude with `B.sub_mem x.2.1 h0⟩`. Use `left_inv := fun y => by ext; simp`. Use `right_inv := fun x => by ext; simp }`. Use `⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩` and prove the remaining obligations. Simplify using `[g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]`.
-/
theorem lattice_bij (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [← Ideal.inf_eq_mul_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `hI` using `[Ideal.isCoprime_iff_sup_eq, bot_sup_eq]`. Conclude with `hM hI`.
-/
theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

/- English proof (translation)
Establish `hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}, ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B` using `fun I => (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2`. Use `choose g hg1 hg using hgen`. Establish `hgB : ∀ I, g I ∈ B` using `fun I => by`. Establish `: g I ∈ Ideal.span {g I}` using `Ideal.mem_span_singleton_self _`. Rewrite `this` using `[hg I]`.

Conclude with `Ideal.mul_le_right this`. Establish `hg0 : ∀ I, g I ≠ 0` using `fun I h => by`. Use `hg I` as an intermediate fact. Rewrite `this` using `[h, Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm`.

Set `F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} × {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} → {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}}` to `fun p => ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by`. Establish `: (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩`.

Establish `hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B` using `fun p => by show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _`. Rewrite using `[Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]`. Establish `hinj : Function.Injective F`. Introduce and unpack `⟨I, u⟩ ⟨I', u'⟩ h`. Establish `h1` using `hspanF (I, u)`.

Rewrite `h1` using `[h, hspanF (I', u')]`. Establish `hII : I = I'` using `Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)`. Substitute `hII` using the available equality. Establish `h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I` using `congrArg Subtype.val h`. Establish `h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K)` using `mul_right_cancel₀ (hg0 I) h2`.

Rewrite using `[Subtype.ext (Units.ext h3)]`. Establish `hsurj : Function.Surjective F`. Introduce and unpack `⟨x, hxB, hx1⟩`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Apply `hM` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `(Ideal.neg_mem_iff _).2 hx1` as an intermediate fact. Simplify using `using this`. Establish `hle : Ideal.span {x} ≤ B` using `(Ideal.span_singleton_le_iff_mem _).2 hxB`.

Take `⟨I, hI⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)})`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]`. Establish `: (1 : 𝓞 K) = x - (x - 1)` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)) (Ideal.mem_sup_right hx1)`. Establish `hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)})`. Rewrite `hxc` using `[hI]`. Conclude with `hxc.of_mul_left_right`. Establish `hIB : Ideal.span {x} = I * B` using `by rw [hI, mul_comm]`.

Establish `hIcls : D.cls I = c` using `(cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩`. Set `I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}` to `⟨I, hIc, hIcls⟩`. Establish `hass : Associated (g I') x`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton, hg I', hIB]`. Take `⟨u, hu⟩` from `hass`.

Establish `hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}`. Establish `hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)}` using `by rw [hu]; exact hx1`. Establish `: (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))`.

Use `⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (u : 𝓞 K) * g I' = x`. Rewrite using `[mul_comm, hu]`. Conclude with `⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩`.
-/
theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
        {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} ≃
        {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}},
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1 * B := by
  classical
  have hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c},
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B := fun I =>
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2
  choose g hg1 hg using hgen
  have hgB : ∀ I, g I ∈ B := fun I => by
    have : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at this
    exact Ideal.mul_le_right this
  have hg0 : ∀ I, g I ≠ 0 := fun I h => by
    have := hg I
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm
  let F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
      {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} →
      {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} := fun p =>
    ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by
      have : (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B := fun p => by
    show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]
  have hinj : Function.Injective F := by
    rintro ⟨I, u⟩ ⟨I', u'⟩ h
    have h1 := hspanF (I, u)
    rw [h, hspanF (I', u')] at h1
    have hII : I = I' := Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)
    subst hII
    have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := congrArg Subtype.val h
    have h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K) := mul_right_cancel₀ (hg0 I) h2
    rw [Subtype.ext (Units.ext h3)]
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hxB, hx1⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hM
      rw [Ideal.eq_top_iff_one]
      have := (Ideal.neg_mem_iff _).2 hx1
      simpa using this
    have hle : Ideal.span {x} ≤ B := (Ideal.span_singleton_le_iff_mem _).2 hxB
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
    have hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = x - (x - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
        (Ideal.mem_sup_right hx1)
    have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      rw [hI] at hxc; exact hxc.of_mul_left_right
    have hIB : Ideal.span {x} = I * B := by rw [hI, mul_comm]
    have hIcls : D.cls I = c :=
      (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩
    let I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} :=
      ⟨I, hIc, hIcls⟩
    have hass : Associated (g I') x := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I', hIB]
    obtain ⟨u, hu⟩ := hass
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [hu]; exact hx1
      have : (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u := by ring
      rw [this]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))
    refine ⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩
    show (u : 𝓞 K) * g I' = x
    rw [mul_comm, hu]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩

/- English proof (translation)
Set `C` to `{I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}`. Set `Nm : C → ℕ` to `fun I => Ideal.absNorm I.1`. Establish `h' : HasSum (fun x : (Σ n : ℕ, {I : C // Nm I = n}) => (Ideal.absNorm x.2.1.1 : ℂ) ^ (-s)) a` using `(Equiv.sigmaFiberEquiv Nm).hasSum_iff.2 h`. Use `h'.sigma (fun n => ?_)` and prove the remaining obligations. Set `en : {I : C // Nm I = n} ≃ {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c}` to `{ toFun := fun x => ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩ invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.2⟩, y.2.2.1⟩ left_inv := fun x => rfl right_inv := fun y => rfl }`.

Use `haveI : Finite {I : C // Nm I = n} := by haveI := D.finite_cnt c n`. Conclude with `Finite.of_equiv _ en.symm`. Use `haveI : Fintype {I : C // Nm I = n} := Fintype.ofFinite _`. Establish `hconst : (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) = fun _ => (n : ℂ) ^ (-s)`. Use function extensionality and compare the values at `x`.

Rewrite using `[show Ideal.absNorm x.1.1 = n from x.2]`. Use `show HasSum (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) _`. Rewrite using `[hconst]`. Distinguish the cases in `hn : n = 0`. Substitute `hn haveI : IsEmpty {I : C // Nm I = 0} := ⟨fun x => by` using the available equality.

Establish `hx : x.1.1 = ⊥` using `Ideal.absNorm_eq_zero_iff.1 x.2`. Conclude with `ne_bot_of_coprime hM x.1.2.1 hx⟩`. Rewrite using `[LSeries.term_zero]`. Conclude with `hasSum_empty`. Rewrite using `[LSeries.term_of_ne_zero hn]`.

Establish `hs` using `hasSum_fintype (fun _ : {I : C // Nm I = n} => (n : ℂ) ^ (-s))`. Use `hs using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RayData.cnt, ← Nat.card_congr en, Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]`.
-/
theorem hasSum_cnt {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G) (s a : ℂ)
    (h : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} =>
      (Ideal.absNorm I.1 : ℂ) ^ (-s)) a) : LSeriesHasSum (D.cnt c) s a := by
  classical
  let C := {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}
  let Nm : C → ℕ := fun I => Ideal.absNorm I.1
  have h' : HasSum (fun x : (Σ n : ℕ, {I : C // Nm I = n}) =>
      (Ideal.absNorm x.2.1.1 : ℂ) ^ (-s)) a :=
    (Equiv.sigmaFiberEquiv Nm).hasSum_iff.2 h
  refine h'.sigma (fun n => ?_)
  let en : {I : C // Nm I = n} ≃
      {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.2⟩, y.2.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  haveI : Finite {I : C // Nm I = n} := by
    haveI := D.finite_cnt c n
    exact Finite.of_equiv _ en.symm
  haveI : Fintype {I : C // Nm I = n} := Fintype.ofFinite _
  have hconst : (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) =
      fun _ => (n : ℂ) ^ (-s) := by
    funext x
    rw [show Ideal.absNorm x.1.1 = n from x.2]
  show HasSum (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) _
  rw [hconst]
  by_cases hn : n = 0
  · subst hn
    haveI : IsEmpty {I : C // Nm I = 0} := ⟨fun x => by
      have hx : x.1.1 = ⊥ := Ideal.absNorm_eq_zero_iff.1 x.2
      exact ne_bot_of_coprime hM x.1.2.1 hx⟩
    rw [LSeries.term_zero]
    exact hasSum_empty
  · rw [LSeries.term_of_ne_zero hn]
    have hs := hasSum_fintype (fun _ : {I : C // Nm I = n} => (n : ℂ) ^ (-s))
    convert hs using 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RayData.cnt,
      ← Nat.card_congr en, Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]

/- English proof (translation)
Introduce `K _ _ _ h2 M hM2 D`. Establish `hrk : Module.finrank ℤ (𝓞 K) = 2` using `by rw [RingOfIntegers.rank, h2]`. Establish `hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2`. Rewrite using `[Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) (M : ℤ) by simp, Algebra.norm_algebraMap, hrk]`. Simplify using `[Int.natAbs_pow]`.

Establish `hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤`. Introduce `h`. Use `hNnorm` as an intermediate fact. Rewrite `this` using `[h, Ideal.absNorm_top]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥`. Introduce `h`. Use `hNnorm` as an intermediate fact. Rewrite `this` using `[h, Ideal.absNorm_bot]`. Use the polynomial consequences of the given equalities and inequalities.

Set `b : Module.Basis (Fin 2) ℤ (𝓞 K)` to `Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk`. Set `φ : K →+* ℂ` to `Classical.choice inferInstance`. Set `ψ : 𝓞 K →+* ℂ` to `φ.comp (algebraMap (𝓞 K) K)`. Use `haveI : Finite (𝓞 K)ˣ := finite_units h2`. Set `U` to `{u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}`.

Use `haveI : Fintype U := Fintype.ofFinite _`. Establish `hw : 0 < Fintype.card U` using `Fintype.card_pos_iff.2 ⟨⟨1, by simp⟩⟩`. Use `set ib := |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| with hib`. Establish `hib0 : 0 < ib` using `abs_pos.2 (im_ne_zero φ b)`. Use `⟨Real.pi / (Fintype.card U * (M : ℝ) ^ 2 * ib), by positivity, fun c => ?_⟩` and prove the remaining obligations.

Take `⟨B, hBc, hB0, hcB⟩` from `D.cls_surj c⁻¹`. Take `⟨x₀, hx₀B, z, hz, hxz⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hBc))`. Establish `hx₀1 : x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)}`. Establish `: x₀ - 1 = -z` using `by rw [← hxz]; ring`. Rewrite using `[this]`.

Conclude with `(Ideal.neg_mem_iff _).2 hz`. Establish `hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥` using `mul_ne_zero hN0 hB0`. Set `e : Module.Basis (Fin 2) ℤ ↥(Ideal.span {(M : 𝓞 K)} * B)` to `Ideal.selfBasis b _ hNB0`. Take `⟨fL, hfL⟩` from `lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc e x₀ hx₀B hx₀1`. Take `⟨fG, hfG⟩` from `gen_bij hM D c B hBc hB0 hcB`.

Establish `hBn0 : Ideal.absNorm B ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]` and apply the resulting hypothesis. Establish `hIm` using `abs_im_eq φ b (Ideal.span {(M : 𝓞 K)} * B) e`. Rewrite `hIm` using `[map_mul, hNnorm]`. Establish `him : (starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im ≠ 0`.

Introduce `h0`. Rewrite `hIm` using `[h0, abs_zero]`. Establish `: (0 : ℝ) < ((M ^ 2 * Ideal.absNorm B : ℕ) : ℝ) * ib`. Establish `: 0 < M ^ 2 * Ideal.absNorm B` using `by positivity`. Check the signs of the components of the expression.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hψL : ∀ p : ℤ × ℤ, ψ (fL p : 𝓞 K) = φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K)`. Introduce `p`. Rewrite using `[hfL p]`. Simplify using `[ψ, map_add, map_mul, map_intCast]`.

Establish `hnz : ∀ m n : ℤ, φ (x₀ : K) + m * φ ((e 0 : 𝓞 K) : K) + n * φ ((e 1 : 𝓞 K) : K) ≠ 0`. Introduce `m n h0`. Establish `hx` using `(fL (m, n)).2.2`. Establish `hzero : (fL (m, n) : 𝓞 K) = 0`. Use `hψL (m, n)` as an intermediate fact.

Rewrite `this` using `[h0]`. Establish `hinj : Function.Injective ψ` using `φ.injective.comp (IsFractionRing.injective (𝓞 K) K)`. Conclude with `hinj (by rw [this, map_zero])`. Rewrite `hx` using `[hzero, zero_sub]`. Apply `hM` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using (Ideal.neg_mem_iff _).2 hx`. Take `⟨Z0, hZd, hZ1, hZm1, hZs⟩` from `GlobalTheory.T.lattice_epstein_zeta_continuation _ _ _ him hnz`. Establish `hBc0 : (Ideal.absNorm B : ℂ) ≠ 0` using `by exact_mod_cast hBn0`. Establish `hwc : (Fintype.card U : ℂ) ≠ 0` using `by exact_mod_cast hw.ne'`.

Use `⟨fun s => (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((differentiable_id.const_cpow (Or.inl hBc0)).div_const _).mul hZd`. Simplify using `only [Complex.cpow_one]`. Rewrite using `[hZ1, hIm]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[← hib]`. Conclude with `div_self (by exact_mod_cast hib0.ne')`. Simplify using `[hZm1]`. Introduce `s hs`.

Take `⟨hsum, hZeq⟩` from `hZs s hs`. Use `set S := ∑' p : ℤ × ℤ, ((‖φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) with hS`. Set `G : {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} → ℂ` to `fun x => ((‖ψ (x : 𝓞 K)‖ ^ 2 : ℝ) : ℂ) ^ (-s)`. Establish `hG : HasSum G S`. Rewrite using `[← fL.hasSum_iff]`.

Use `hsum.hasSum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, G, hψL p]`. Establish `hGG` using `fG.hasSum_iff.2 hG`. Establish `hterm : ∀ p, (G ∘ fG) p = (Ideal.absNorm p.1.1 : ℂ) ^ (-s) * (Ideal.absNorm B : ℂ) ^ (-s)`.

Introduce `p`. Simplify using `only [Function.comp_apply, G]`. Establish `hn` using `normSq_eq h2 φ (fG p : 𝓞 K)`. Rewrite `hn` using `[hfG p, map_mul]`. Use `show ((‖φ ((fG p : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) = _`.

Rewrite using `[hn]`. Use `push_cast`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_natCast (Ideal.absNorm B), ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]`. Establish `hfib` using `hGG.prod_fiberwise (fun I => hasSum_fintype (fun u : U => (G ∘ fG) (I, u)))`. Simplify using `only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfib`.

Establish `hcnt : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} => (Ideal.absNorm I.1 : ℂ) ^ (-s)) ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U * S)`. Establish `hBs : (Ideal.absNorm B : ℂ) ^ s ≠ 0`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. The claim follows by propositional logic. Use `(hfib.mul_left ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U)).congr_fun (fun I => ?_)` and prove the remaining obligations.

Rewrite using `[Complex.cpow_neg (Ideal.absNorm B : ℂ)]`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Establish `hL` using `hasSum_cnt hM D c s _ hcnt`.

Use `⟨hL.LSeriesSummable, ?_⟩` and prove the remaining obligations. Rewrite using `[hL.LSeries_eq]`. Use `show (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s = _`. Rewrite using `[hZeq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem partial_zeta_continuation : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  intro K _ _ _ h2 M hM2 D
  classical
  have hrk : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, h2]
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton,
      show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) (M : ℤ) by simp, Algebra.norm_algebraMap, hrk]
    simp [Int.natAbs_pow]
  have hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_top] at this
    nlinarith
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_bot] at this
    nlinarith
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K)
  haveI : Finite (𝓞 K)ˣ := finite_units h2
  let U := {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}
  haveI : Fintype U := Fintype.ofFinite _
  have hw : 0 < Fintype.card U := Fintype.card_pos_iff.2 ⟨⟨1, by simp⟩⟩
  set ib := |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| with hib
  have hib0 : 0 < ib := abs_pos.2 (im_ne_zero φ b)
  refine ⟨Real.pi / (Fintype.card U * (M : ℝ) ^ 2 * ib), by positivity, fun c => ?_⟩
  obtain ⟨B, hBc, hB0, hcB⟩ := D.cls_surj c⁻¹
  obtain ⟨x₀, hx₀B, z, hz, hxz⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hBc))
  have hx₀1 : x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    have : x₀ - 1 = -z := by rw [← hxz]; ring
    rw [this]; exact (Ideal.neg_mem_iff _).2 hz
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := mul_ne_zero hN0 hB0
  let e : Module.Basis (Fin 2) ℤ ↥(Ideal.span {(M : 𝓞 K)} * B) := Ideal.selfBasis b _ hNB0
  obtain ⟨fL, hfL⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc e x₀ hx₀B hx₀1
  obtain ⟨fG, hfG⟩ := gen_bij hM D c B hBc hB0 hcB
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIm := abs_im_eq φ b (Ideal.span {(M : 𝓞 K)} * B) e
  rw [map_mul, hNnorm] at hIm
  have him : (starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hIm
    have : (0 : ℝ) < ((M ^ 2 * Ideal.absNorm B : ℕ) : ℝ) * ib := by
      have : 0 < M ^ 2 * Ideal.absNorm B := by positivity
      positivity
    linarith
  have hψL : ∀ p : ℤ × ℤ, ψ (fL p : 𝓞 K) =
      φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K) := by
    intro p
    rw [hfL p]
    simp [ψ, map_add, map_mul, map_intCast]
  have hnz : ∀ m n : ℤ, φ (x₀ : K) + m * φ ((e 0 : 𝓞 K) : K) + n * φ ((e 1 : 𝓞 K) : K) ≠ 0 := by
    intro m n h0
    have hx := (fL (m, n)).2.2
    have hzero : (fL (m, n) : 𝓞 K) = 0 := by
      have := hψL (m, n)
      rw [h0] at this
      have hinj : Function.Injective ψ :=
        φ.injective.comp (IsFractionRing.injective (𝓞 K) K)
      exact hinj (by rw [this, map_zero])
    rw [hzero, zero_sub] at hx
    apply hM
    rw [Ideal.eq_top_iff_one]
    simpa using (Ideal.neg_mem_iff _).2 hx
  obtain ⟨Z0, hZd, hZ1, hZm1, hZs⟩ := GlobalTheory.T.lattice_epstein_zeta_continuation _ _ _ him hnz
  have hBc0 : (Ideal.absNorm B : ℂ) ≠ 0 := by exact_mod_cast hBn0
  have hwc : (Fintype.card U : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  refine ⟨fun s => (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s, ?_, ?_, ?_, ?_⟩
  · exact ((differentiable_id.const_cpow (Or.inl hBc0)).div_const _).mul hZd
  · simp only [Complex.cpow_one]
    rw [hZ1, hIm]
    push_cast
    field_simp
    rw [← hib]
    exact div_self (by exact_mod_cast hib0.ne')
  · simp [hZm1]
  · intro s hs
    obtain ⟨hsum, hZeq⟩ := hZs s hs
    set S := ∑' p : ℤ × ℤ, ((‖φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) +
      p.2 * φ ((e 1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) with hS
    let G : {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} → ℂ := fun x =>
      ((‖ψ (x : 𝓞 K)‖ ^ 2 : ℝ) : ℂ) ^ (-s)
    have hG : HasSum G S := by
      rw [← fL.hasSum_iff]
      convert hsum.hasSum using 1
      funext p
      simp only [Function.comp_apply, G, hψL p]
    have hGG := fG.hasSum_iff.2 hG
    have hterm : ∀ p, (G ∘ fG) p = (Ideal.absNorm p.1.1 : ℂ) ^ (-s) *
        (Ideal.absNorm B : ℂ) ^ (-s) := by
      intro p
      simp only [Function.comp_apply, G]
      have hn := normSq_eq h2 φ (fG p : 𝓞 K)
      rw [hfG p, map_mul] at hn
      show ((‖φ ((fG p : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) = _
      rw [hn]
      push_cast
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (Ideal.absNorm B),
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    have hfib := hGG.prod_fiberwise (fun I => hasSum_fintype (fun u : U => (G ∘ fG) (I, u)))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfib
    have hcnt : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        D.cls I = c} => (Ideal.absNorm I.1 : ℂ) ^ (-s))
        ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U * S) := by
      have hBs : (Ideal.absNorm B : ℂ) ^ s ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      refine (hfib.mul_left ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U)).congr_fun (fun I => ?_)
      rw [Complex.cpow_neg (Ideal.absNorm B : ℂ)]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have hL := hasSum_cnt hM D c s _ hcnt
    refine ⟨hL.LSeriesSummable, ?_⟩
    rw [hL.LSeries_eq]
    show (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s = _
    rw [hZeq]
    ring

end GlobalTheory.Mem.PartialZeta

end
