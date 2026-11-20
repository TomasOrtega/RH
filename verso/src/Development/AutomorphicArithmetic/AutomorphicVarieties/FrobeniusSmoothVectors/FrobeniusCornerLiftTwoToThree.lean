import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
import Mathlib.RingTheory.GradedAlgebra.Radical

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `key : ∀ x ∈ Ideal.map (algebraMap B A) p, ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c`. Introduce `x hx`. Establish `hx' : x ∈ (p • (⊤ : Submodule B A))`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hx`.

Use `Submodule.smul_induction_on (p := fun x => ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c) hx' ?_ ?_` and prove the remaining obligations. Introduce `b hb y _`. Establish `hy : GradedAlgebra.proj 𝒜 0 y ∈ 𝒜 0`. Rewrite using `[GradedAlgebra.proj_apply]`. Conclude with `SetLike.coe_mem _`.

Rewrite `hy` using `[h0]`. Take `⟨c, hc⟩` from `Submodule.mem_one.mp hy`. Use `⟨b * c, p.mul_mem_right c hb, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, ← hc, Algebra.smul_def, map_mul]`. Introduce `x y hx hy`.

Take `⟨c, hc, hxc⟩` from `hx`. Take `⟨d, hd, hyd⟩` from `hy`. Conclude with `⟨c + d, p.add_mem hc hd, by rw [map_add, hxc, hyd, map_add]⟩`. Establish `hdisj : Disjoint ((Ideal.map (algebraMap B A) p : Ideal A) : Set A) (Algebra.algebraMapSubmonoid A p.primeCompl : Set A)`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `x hxJ ⟨s, hs, rfl⟩`. Take `⟨c, hc, he⟩` from `key _ hxJ`. Rewrite `he` using `[GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 s)]`. Conclude with `hs (by rw [hinj he]; exact hc)`. Take `⟨P, hP, hJP, hPd⟩` from `Ideal.exists_le_prime_disjoint _ _ hdisj`.

Use `⟨(P.homogeneousCore 𝒜).toIdeal, Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hP, (P.homogeneousCore 𝒜).isHomogeneous, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce `b hb`. Rewrite `hb` using `[Ideal.mem_comap]`. Establish `hbP : algebraMap B A b ∈ P` using `Ideal.toIdeal_homogeneousCore_le 𝒜 P hb`.

Assume the negation of the conclusion as `hnb`. Conclude with `Set.disjoint_left.mp hPd hbP ⟨b, hnb, rfl⟩`. Introduce `b hb`. Rewrite using `[Ideal.mem_comap]`. Conclude with `Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨0, SetLike.algebraMap_mem_graded 𝒜 b⟩ (hJP (Ideal.mem_map_of_mem _ hb))`.
-/
private theorem ex_core {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = 1) (hinj : Function.Injective (algebraMap B A)) (p : Ideal B) [p.IsPrime] :
    ∃ η : Ideal A, η.IsPrime ∧ η.IsHomogeneous 𝒜 ∧ η.comap (algebraMap B A) = p := by
  classical
  have key : ∀ x ∈ Ideal.map (algebraMap B A) p, ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c := by
    intro x hx
    have hx' : x ∈ (p • (⊤ : Submodule B A)) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    refine Submodule.smul_induction_on (p := fun x => ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c)
      hx' ?_ ?_
    · intro b hb y _
      have hy : GradedAlgebra.proj 𝒜 0 y ∈ 𝒜 0 := by
        rw [GradedAlgebra.proj_apply]
        exact SetLike.coe_mem _
      rw [h0] at hy
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hy
      refine ⟨b * c, p.mul_mem_right c hb, ?_⟩
      rw [LinearMap.map_smul, ← hc, Algebra.smul_def, map_mul]
    · intro x y hx hy
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, p.add_mem hc hd, by rw [map_add, hxc, hyd, map_add]⟩
  have hdisj : Disjoint ((Ideal.map (algebraMap B A) p : Ideal A) : Set A)
      (Algebra.algebraMapSubmonoid A p.primeCompl : Set A) := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨s, hs, rfl⟩
    obtain ⟨c, hc, he⟩ := key _ hxJ
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 s)] at he
    exact hs (by rw [hinj he]; exact hc)
  obtain ⟨P, hP, hJP, hPd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  refine ⟨(P.homogeneousCore 𝒜).toIdeal, Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hP,
    (P.homogeneousCore 𝒜).isHomogeneous, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_comap] at hb
    have hbP : algebraMap B A b ∈ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P hb
    by_contra hnb
    exact Set.disjoint_left.mp hPd hbP ⟨b, hnb, rfl⟩
  · intro b hb
    rw [Ideal.mem_comap]
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨0, SetLike.algebraMap_mem_graded 𝒜 b⟩
      (hJP (Ideal.mem_map_of_mem _ hb))

/- English proof (translation)
Establish `key : ∀ Q : Polynomial B, Polynomial.aeval a Q ∈ η → ∀ k, Q.coeff k ∈ η.comap (algebraMap B A)`. Introduce `Q hQ k`. Establish `hn : Q.natDegree < Q.natDegree + k + 1` using `by omega`. Rewrite `hQ` using `[Polynomial.aeval_eq_sum_range' hn]`. Establish `hmem : ∀ i : ℕ, Q.coeff i • a ^ i ∈ 𝒜 (i • α)` using `fun i => Submodule.smul_mem _ _ (SetLike.pow_mem_graded i ha)`.

Establish `h2 : GradedAlgebra.proj 𝒜 (k • α) (∑ i ∈ Finset.range (Q.natDegree + k + 1), Q.coeff i • a ^ i) ∈ η`. Rewrite using `[GradedAlgebra.proj_apply]`. Conclude with `(Ideal.IsHomogeneous.mem_iff 𝒜 hh).1 hQ _`. Rewrite `h2` using `[map_sum, Finset.sum_eq_single k]`. Rewrite `h2` using `[GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hmem k), Algebra.smul_def]`.

Break down `hη.mem_or_mem h2 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (hη.mem_of_pow_mem _ h) ha'`. Introduce `i _ hik`. Rewrite using `[GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hmem i)]`.

Introduce `he`. Apply `hik` to reduce the goal to its premises. Establish `he' : (i : ℤ) * α = (k : ℤ) * α` using `by simpa [nsmul_eq_mul] using he`. Conclude with `mul_right_cancel₀ hα he'` after adjusting the coercions. Introduce `hk`.

Conclude with `absurd (Finset.mem_range.2 (by omega)) hk`. Establish `htr : Transcendental (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a)`. Rewrite using `[transcendental_iff]`. Introduce `P hP`. Take `⟨Q, rfl⟩` from `Polynomial.map_surjective (Ideal.Quotient.mk (η.comap (algebraMap B A))) Ideal.Quotient.mk_surjective P`.

Establish `e : Polynomial.aeval (Ideal.Quotient.mk η a) (Q.map (Ideal.Quotient.mk (η.comap (algebraMap B A)))) = Ideal.Quotient.mk η (Polynomial.aeval a Q)`. Establish `e1` using `Polynomial.aeval_map_algebraMap (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) Q`. Rewrite `e1` using `[Ideal.Quotient.algebraMap_eq]`. Rewrite using `[e1, ← Ideal.Quotient.mkₐ_eq_mk B η, Polynomial.aeval_algHom_apply]`. Rewrite `hP` using `[e, Ideal.Quotient.eq_zero_iff_mem]`.

Use extensionality with `k`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `key Q hP k`. Use `haveI : Algebra.Transcendental (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := ⟨⟨_, htr⟩⟩`. Conclude with `Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)`.
-/
private theorem one_le_td {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [GradedAlgebra 𝒜] (η : Ideal A) (hη : η.IsPrime) (hh : η.IsHomogeneous 𝒜) {a : A} {α : ℤ} (ha : a ∈ 𝒜 α)
    (hα : α ≠ 0) (ha' : a ∉ η) : 1 ≤ Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  classical
  have key : ∀ Q : Polynomial B, Polynomial.aeval a Q ∈ η → ∀ k, Q.coeff k ∈ η.comap (algebraMap B A) := by
    intro Q hQ k
    have hn : Q.natDegree < Q.natDegree + k + 1 := by omega
    rw [Polynomial.aeval_eq_sum_range' hn] at hQ
    have hmem : ∀ i : ℕ, Q.coeff i • a ^ i ∈ 𝒜 (i • α) := fun i =>
      Submodule.smul_mem _ _ (SetLike.pow_mem_graded i ha)
    have h2 : GradedAlgebra.proj 𝒜 (k • α)
        (∑ i ∈ Finset.range (Q.natDegree + k + 1), Q.coeff i • a ^ i) ∈ η := by
      rw [GradedAlgebra.proj_apply]
      exact (Ideal.IsHomogeneous.mem_iff 𝒜 hh).1 hQ _
    rw [map_sum, Finset.sum_eq_single k] at h2
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hmem k), Algebra.smul_def] at h2
      rcases hη.mem_or_mem h2 with h | h
      · exact h
      · exact absurd (hη.mem_of_pow_mem _ h) ha'
    · intro i _ hik
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hmem i)]
      intro he
      apply hik
      have he' : (i : ℤ) * α = (k : ℤ) * α := by simpa [nsmul_eq_mul] using he
      exact_mod_cast mul_right_cancel₀ hα he'
    · intro hk
      exact absurd (Finset.mem_range.2 (by omega)) hk
  have htr : Transcendental (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) := by
    rw [transcendental_iff]
    intro P hP
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (η.comap (algebraMap B A)))
      Ideal.Quotient.mk_surjective P
    have e : Polynomial.aeval (Ideal.Quotient.mk η a) (Q.map (Ideal.Quotient.mk (η.comap (algebraMap B A))))
        = Ideal.Quotient.mk η (Polynomial.aeval a Q) := by
      have e1 := Polynomial.aeval_map_algebraMap (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) Q
      rw [Ideal.Quotient.algebraMap_eq] at e1
      rw [e1, ← Ideal.Quotient.mkₐ_eq_mk B η, Polynomial.aeval_algHom_apply]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at hP
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact key Q hP k
  haveI : Algebra.Transcendental (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := ⟨⟨_, htr⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = α` from `⟨α.toNat, Int.toNat_of_nonneg hα.le⟩`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -β` from `⟨(-β).toNat, Int.toNat_of_nonneg (by omega)⟩`. Establish `hm0 : 0 < m` using `by omega`. Establish `hk0 : 0 < k` using `by omega`. Establish `hmem : a ^ k * b ^ m ∈ 𝒜 0`.

Establish `h1` using `SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) (SetLike.pow_mem_graded m hb)`. Establish `he : k • α + m • β = 0`. Rewrite using `[nsmul_eq_mul, nsmul_eq_mul, hk, hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[he]`. Then use the resulting hypothesis.

Rewrite `hmem` using `[h0]`. Take `⟨x, hx⟩` from `Submodule.mem_one.mp hmem`. Establish `hc : a ^ k * b ^ m ∉ ξ`. Introduce `hin`. Break down `hξ.mem_or_mem hin with h | h` into its components or cases.

Conclude with `ha' (hξ.mem_of_pow_mem _ h)`. Conclude with `hb' (hξ.mem_of_pow_mem _ h)`. Establish `hxξ : x ∉ ξ.comap (algebraMap B A)`. Rewrite using `[Ideal.mem_comap, hx]`. Conclude with `hc`.

Establish `hxη : x ∉ η.comap (algebraMap B A)` using `fun hin => hxξ (hle hin)`. Rewrite `hxη` using `[Ideal.mem_comap, hx]`. Prove the components needed by the constructor for the conclusion. Introduce `hin`. Conclude with `hxη (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hin _ hk0))`.

Introduce `hin`. Conclude with `hxη (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hin _ hm0))`.
-/
private theorem pair {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [SetLike.GradedMonoid 𝒜] (h0 : 𝒜 0 = 1) {ξ η : Ideal A} (hξ : ξ.IsPrime)
    (hle : η.comap (algebraMap B A) ≤ ξ.comap (algebraMap B A)) {a b : A} {α β : ℤ} (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β)
    (hα : 0 < α) (hβ : β < 0) (ha' : a ∉ ξ) (hb' : b ∉ ξ) : a ∉ η ∧ b ∉ η := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = α := ⟨α.toNat, Int.toNat_of_nonneg hα.le⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -β := ⟨(-β).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hmem : a ^ k * b ^ m ∈ 𝒜 0 := by
    have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) (SetLike.pow_mem_graded m hb)
    have he : k • α + m • β = 0 := by
      rw [nsmul_eq_mul, nsmul_eq_mul, hk, hm]
      ring
    rwa [he] at h1
  rw [h0] at hmem
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hmem
  have hc : a ^ k * b ^ m ∉ ξ := by
    intro hin
    rcases hξ.mem_or_mem hin with h | h
    · exact ha' (hξ.mem_of_pow_mem _ h)
    · exact hb' (hξ.mem_of_pow_mem _ h)
  have hxξ : x ∉ ξ.comap (algebraMap B A) := by
    rw [Ideal.mem_comap, hx]
    exact hc
  have hxη : x ∉ η.comap (algebraMap B A) := fun hin => hxξ (hle hin)
  rw [Ideal.mem_comap, hx] at hxη
  constructor
  · intro hin
    exact hxη (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hin _ hk0))
  · intro hin
    exact hxη (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hin _ hm0))

/- English proof (translation)
Establish `: (i : ℕ) < j` using `h`. Unfold `w`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hle`. Take `⟨hint, hgm, h0, -, -, -, hr⟩` from `gr_A hF hn S`. Use `letI : GradedAlgebra S.gr := { hgm, hint.chooseDecomposition with }`. Establish `hinj : Function.Injective (algebraMap S.B S.A)`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : S.A => (z : S.R)) hxy`. Take `⟨η, hηp, hηh, hηc⟩` from `ex_core S.gr h0 hinj p`. Establish `hP` using `hTI.1.1`. Establish `hM` using `hTI.1.2`.

Simplify using `only [NRep.triP, NRep.triM, Ideal.span_le, Set.not_subset] at hP hM`. Take `⟨_, ⟨g, i, j, hji, rfl⟩, hb⟩` from `hP`. Take `⟨_, ⟨g', i', j', hij', rfl⟩, ha⟩` from `hM`. Establish `hbd : w n i - w n j < 0` using `by have := w_lt hji; omega`. Establish `had : 0 < w n i' - w n j'` using `by have := w_lt hij'; omega`.

Establish `hle' : η.comap (algebraMap S.B S.A) ≤ ξ.comap (algebraMap S.B S.A)`. Rewrite using `[hηc]`. Conclude with `hle`. Establish `hab` using `pair S.gr h0 hξ hle' (hr g' i' j') (hr g i j) had hbd ha hb`. Use `⟨η, hηp, ?_, hηc, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Establish `e` using `(Ideal.IsHomogeneous.iff_eq S.gr η).mp hηh`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `_ ⟨⟨x, hxh⟩, hx, rfl⟩`. Conclude with `⟨hx, hxh⟩`.

Conclude with `Ideal.span_le.2 fun x hx => hx.1`. Introduce `h`. Conclude with `hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩))`. Introduce `h`. Conclude with `hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))`.

Introduce `h3 h`. Establish `hE` using `hTI.2 h3`. Simplify using `only [NRep.ee, Ideal.span_le, Set.not_subset] at hE`. Take `⟨_, ⟨g'', i'', j'', hodd, rfl⟩, hc⟩` from `hE`. Establish `hne : w n i'' - w n j'' ≠ 0`.

Introduce and unpack `h0'`. Rewrite `hodd` using `[h0']`. Conclude with `(Int.not_odd_iff_even.2 ⟨0, by norm_num⟩) hodd`. Establish `hcη : S.u.r g'' i'' j'' ∉ η`. Break down `lt_or_gt_of_ne hne with hneg | hpos` into its components or cases.

Conclude with `(pair S.gr h0 hξ hle' (hr g' i' j') (hr g'' i'' j'') had hneg ha hc).2`. Conclude with `(pair S.gr h0 hξ hle' (hr g'' i'' j'') (hr g i j) hpos hbd hc hb).1`. Conclude with `hcη (h (Ideal.subset_span ⟨g'', i'', j'', hodd, rfl⟩))`. Conclude with `le_antisymm (fibre hF hn S η hηp ⟨fun h => hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)), fun h => hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))⟩) (one_le_td S.gr η hηp hηh (hr g' i' j') had.ne' hab.1)`.
-/
theorem UpperTheory.V.Fr.frobenius_corner_lift_two_to_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ η : Ideal S.A, η.IsPrime ∧ S.IsHom η ∧ S.π η = p ∧ S.u.TI η ∧ S.td η = 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hle
  obtain ⟨hint, hgm, h0, -, -, -, hr⟩ := gr_A hF hn S
  letI : GradedAlgebra S.gr := { hgm, hint.chooseDecomposition with }
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  obtain ⟨η, hηp, hηh, hηc⟩ := ex_core S.gr h0 hinj p
  have hP := hTI.1.1
  have hM := hTI.1.2
  simp only [NRep.triP, NRep.triM, Ideal.span_le, Set.not_subset] at hP hM
  obtain ⟨_, ⟨g, i, j, hji, rfl⟩, hb⟩ := hP
  obtain ⟨_, ⟨g', i', j', hij', rfl⟩, ha⟩ := hM
  have hbd : w n i - w n j < 0 := by have := w_lt hji; omega
  have had : 0 < w n i' - w n j' := by have := w_lt hij'; omega
  have hle' : η.comap (algebraMap S.B S.A) ≤ ξ.comap (algebraMap S.B S.A) := by
    rw [hηc]; exact hle
  have hab := pair S.gr h0 hξ hle' (hr g' i' j') (hr g i j) had hbd ha hb
  refine ⟨η, hηp, ?_, hηc, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply le_antisymm
    · have e := (Ideal.IsHomogeneous.iff_eq S.gr η).mp hηh
      calc η = _ := e.symm
        _ ≤ _ := Ideal.span_mono ?_
      rintro _ ⟨⟨x, hxh⟩, hx, rfl⟩
      exact ⟨hx, hxh⟩
    · exact Ideal.span_le.2 fun x hx => hx.1
  · intro h
    exact hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩))
  · intro h
    exact hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))
  · intro h3 h
    have hE := hTI.2 h3
    simp only [NRep.ee, Ideal.span_le, Set.not_subset] at hE
    obtain ⟨_, ⟨g'', i'', j'', hodd, rfl⟩, hc⟩ := hE
    have hne : w n i'' - w n j'' ≠ 0 := by
      rintro h0'
      rw [h0'] at hodd
      exact (Int.not_odd_iff_even.2 ⟨0, by norm_num⟩) hodd
    have hcη : S.u.r g'' i'' j'' ∉ η := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact (pair S.gr h0 hξ hle' (hr g' i' j') (hr g'' i'' j'') had hneg ha hc).2
      · exact (pair S.gr h0 hξ hle' (hr g'' i'' j'') (hr g i j) hpos hbd hc hb).1
    exact hcη (h (Ideal.subset_span ⟨g'', i'', j'', hodd, rfl⟩))
  · exact le_antisymm (fibre hF hn S η hηp ⟨fun h => hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)),
      fun h => hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))⟩)
      (one_le_td S.gr η hηp hηh (hr g' i' j') had.ne' hab.1)
