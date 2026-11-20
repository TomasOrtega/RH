import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Use `set y : ∀ c, E c := fun c => ∑ l, v l • b l c with hy`. Establish `hk : ∀ k, ∑ c, Algebra.trace F (E c) (b k c * y c) = 0`. Introduce `k`.

Establish `h1` using `congrFun hv k`. Establish `h2 : ∑ c, Algebra.trace F (E c) (b k c * y c) = ∑ l, (∑ c, Algebra.trace F (E c) (b k c * b l c)) * v l`. Simplify using `only [hy, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Simplify `h1` using `[Matrix.mulVec, dotProduct]`. Establish `hall : ∀ x : ∀ c, E c, ∑ c, Algebra.trace F (E c) (x c * y c) = 0`. Introduce `x`.

Take `⟨μ, hμ⟩` from `hspan x`. Establish `hx : ∀ c, x c * y c = ∑ k, μ k • (b k c * y c)`. Introduce `c`. Rewrite using `[hμ c, Finset.sum_mul]`. Simplify using `[smul_mul_assoc]`.

Simplify using `only [hx, map_sum, map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `[← Finset.mul_sum, hk]`. Establish `hy0 : y = 0`. Assume the negation of the conclusion as `hne`.

Take `⟨c0, hc0⟩` from `Function.ne_iff.mp hne`. Establish `hc0' : y c0 ≠ 0` using `by simpa using hc0`. Establish `ht` using `hall (Pi.single c0 (y c0)⁻¹)`. Rewrite `ht` using `[Finset.sum_eq_single c0]`. Establish `h1 : (1 : E c0) = algebraMap F (E c0) 1` using `(map_one _).symm`.

Rewrite `ht` using `[Pi.single_eq_same, inv_mul_cancel₀ hc0', h1, Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]`. Conclude with `(Nat.cast_ne_zero.mpr (Module.finrank_pos (R := F) (M := E c0)).ne') ht`. Introduce `c _ hc`. Simplify using `[Pi.single_apply, hc]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ c0) h`. Conclude with `hv0 (hind v fun c => by simpa [hy] using congrFun hy0 c)`.
-/
theorem trace_gram_det_ne_zero {F : Type} [Field F] [CharZero F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {E : κ → Type} [∀ c, Field (E c)] [∀ c, Algebra F (E c)] [∀ c, FiniteDimensional F (E c)]
    {n : ℕ} (b : Fin n → ∀ c, E c)
    (hind : ∀ v : Fin n → F, (∀ c, ∑ l, v l • b l c = 0) → v = 0)
    (hspan : ∀ y : ∀ c, E c, ∃ μ : Fin n → F, ∀ c, y c = ∑ k, μ k • b k c) :
    (Matrix.of fun k l : Fin n => ∑ c, Algebra.trace F (E c) (b k c * b l c)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y : ∀ c, E c := fun c => ∑ l, v l • b l c with hy
  have hk : ∀ k, ∑ c, Algebra.trace F (E c) (b k c * y c) = 0 := by
    intro k
    have h1 := congrFun hv k
    have h2 : ∑ c, Algebra.trace F (E c) (b k c * y c) =
        ∑ l, (∑ c, Algebra.trace F (E c) (b k c * b l c)) * v l := by
      simp only [hy, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [h2]
    simpa [Matrix.mulVec, dotProduct] using h1
  have hall : ∀ x : ∀ c, E c, ∑ c, Algebra.trace F (E c) (x c * y c) = 0 := by
    intro x
    obtain ⟨μ, hμ⟩ := hspan x
    have hx : ∀ c, x c * y c = ∑ k, μ k • (b k c * y c) := by
      intro c
      rw [hμ c, Finset.sum_mul]
      simp [smul_mul_assoc]
    simp only [hx, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hk]
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨c0, hc0⟩ := Function.ne_iff.mp hne
    have hc0' : y c0 ≠ 0 := by simpa using hc0
    have ht := hall (Pi.single c0 (y c0)⁻¹)
    rw [Finset.sum_eq_single c0] at ht
    · have h1 : (1 : E c0) = algebraMap F (E c0) 1 := (map_one _).symm
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc0', h1, Algebra.trace_algebraMap, nsmul_eq_mul,
        mul_one] at ht
      exact (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := F) (M := E c0)).ne') ht
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · intro h
      exact absurd (Finset.mem_univ c0) h
  exact hv0 (hind v fun c => by simpa [hy] using congrFun hy0 c)

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Use `letI alg : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra`. Use `haveI : CharZero (KTf K d.D d.N) := charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective`. Take `⟨_, hli, hsp⟩` from `hd.a4.choose_spec`. Establish `hS : ∀ c (p : KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) = d.sH c p`. Introduce `c p`.

Unfold `Data.KTtoS`. Conclude with `IsFractionRing.lift_algebraMap _ _`. Establish `hsm : ∀ c (a : KTf K d.D d.N) (x : OmS (Ω c) d.D d.N), a • x = d.KTtoS h c a * x`. Introduce `c a x`. Both sides reduce to the same expression.

Establish `hspan : ∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ μ : Fin d.del → KTf K d.D d.N, ∀ c, y c = ∑ k, μ k • d.bvecG hd.sel hd.a4.choose k c`. Introduce `y`. Take `⟨q, hq, p, hp⟩` from `hsp y`. Use `⟨fun k => algebraMap _ (KTf K d.D d.N) (p k) / algebraMap _ (KTf K d.D d.N) q, fun c => ?_⟩` and prove the remaining obligations. Simplify using `only [hsm, map_div₀, hS]`.

Establish `hq'` using `hq c`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hq', one_mul]`. Use `_ = (d.sH c q)⁻¹ * ∑ k, d.sH c (p k) * d.bvecG hd.sel hd.a4.choose k c := congrArg (fun t => (d.sH c q)⁻¹ * t) (hp c)`. Use `_ = ∑ k, d.sH c (p k) / d.sH c q * d.bvecG hd.sel hd.a4.choose k c := by`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hind : ∀ v : Fin d.del → KTf K d.D d.N, (∀ c, ∑ l, v l • d.bvecG hd.sel hd.a4.choose l c = 0) → v = 0`. Introduce `v hv`.

Take `⟨⟨q, hq⟩, hqv⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (KTp K d.D d.N)) v`. Establish `hqv' : ∀ l, ∃ pl : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) pl = q • v l` using `fun l => hqv l`. Use `choose p hp using hqv'`. Establish `hp0` using `hli p (fun c => by`. Establish `key` using `congrArg (fun t => d.KTtoS h c (algebraMap _ (KTf K d.D d.N) q) * t) (hv c)`.

Simplify using `only [mul_zero, Finset.mul_sum] at key`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, ← mul_assoc, ← map_mul, ← Algebra.smul_def, ← hp l, hS]`. Apply the tactic sequence `all_goals rfl)`.

Use function extensionality and compare the values at `l`. Establish `h1 : q • v l = 0` using `by rw [← hp l, hp0 l, map_zero]`. Rewrite `h1` using `[Algebra.smul_def]`. Establish `hq0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq`. Conclude with `(mul_eq_zero.mp h1).resolve_left hq0`.

Use `haveI hfd : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by`. Introduce `c`. Use `Module.finite_def.mpr ⟨Finset.univ.image (fun k => d.bvecG hd.sel hd.a4.choose k c), eq_top_iff.mpr fun y _ => ?_⟩` and prove the remaining obligations. Take `⟨μ, hμ⟩` from `hspan (Pi.single c y)`. Establish `hy` using `hμ c`.

Rewrite `hy` using `[Pi.single_eq_same]`. Rewrite using `[hy]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`. Unfold `Data.De`. Conclude with `trace_gram_det_ne_zero (fun k c => d.bvecG hd.sel hd.a4.choose k c) hind hspan`.
-/
theorem de_ne_zero (hd : d.AxH 𝒜) (h : d.S1) : d.De hd h ≠ 0 := by
  classical
  letI alg : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  obtain ⟨_, hli, hsp⟩ := hd.a4.choose_spec
  have hS : ∀ c (p : KTp K d.D d.N),
      d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) = d.sH c p := by
    intro c p
    unfold Data.KTtoS
    exact IsFractionRing.lift_algebraMap _ _
  have hsm : ∀ c (a : KTf K d.D d.N) (x : OmS (Ω c) d.D d.N), a • x = d.KTtoS h c a * x := by
    intro c a x
    rfl
  have hspan : ∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ μ : Fin d.del → KTf K d.D d.N,
      ∀ c, y c = ∑ k, μ k • d.bvecG hd.sel hd.a4.choose k c := by
    intro y
    obtain ⟨q, hq, p, hp⟩ := hsp y
    refine ⟨fun k => algebraMap _ (KTf K d.D d.N) (p k) / algebraMap _ (KTf K d.D d.N) q,
      fun c => ?_⟩
    simp only [hsm, map_div₀, hS]
    have hq' := hq c
    calc y c = (d.sH c q)⁻¹ * (d.sH c q * y c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hq', one_mul]
      _ = (d.sH c q)⁻¹ * ∑ k, d.sH c (p k) * d.bvecG hd.sel hd.a4.choose k c :=
          congrArg (fun t => (d.sH c q)⁻¹ * t) (hp c)
      _ = ∑ k, d.sH c (p k) / d.sH c q * d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hind : ∀ v : Fin d.del → KTf K d.D d.N,
      (∀ c, ∑ l, v l • d.bvecG hd.sel hd.a4.choose l c = 0) → v = 0 := by
    intro v hv
    obtain ⟨⟨q, hq⟩, hqv⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (KTp K d.D d.N)) v
    have hqv' : ∀ l, ∃ pl : KTp K d.D d.N,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) pl = q • v l := fun l => hqv l
    choose p hp using hqv'
    have hp0 := hli p (fun c => by
      have key := congrArg (fun t => d.KTtoS h c (algebraMap _ (KTf K d.D d.N) q) * t) (hv c)
      simp only [mul_zero, Finset.mul_sum] at key
      refine Eq.trans ?_ key
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsm, ← mul_assoc, ← map_mul, ← Algebra.smul_def, ← hp l, hS]
      all_goals rfl)
    funext l
    have h1 : q • v l = 0 := by rw [← hp l, hp0 l, map_zero]
    rw [Algebra.smul_def] at h1
    have hq0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    exact (mul_eq_zero.mp h1).resolve_left hq0
  haveI hfd : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    intro c
    refine Module.finite_def.mpr ⟨Finset.univ.image (fun k => d.bvecG hd.sel hd.a4.choose k c),
      eq_top_iff.mpr fun y _ => ?_⟩
    obtain ⟨μ, hμ⟩ := hspan (Pi.single c y)
    have hy := hμ c
    rw [Pi.single_eq_same] at hy
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  unfold Data.De
  exact trace_gram_det_ne_zero (fun k c => d.bvecG hd.sel hd.a4.choose k c) hind hspan

end Data

end ReciprocityTheory.ChartRestriction.G.T0
