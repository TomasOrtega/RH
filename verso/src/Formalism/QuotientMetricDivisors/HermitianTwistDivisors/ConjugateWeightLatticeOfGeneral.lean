import Mathlib
import Formalism.QuotientMetricDivisors.RatHermLcvTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsChain
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.JwConj
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

open RationalHermitianForm

/- English proof (translation)
Introduce `K _ _ _ d H hherm hdetH T hT w f hf`. Establish `hs` using `hform_isSymm H hherm`. Establish `hnd` using `hform_nondeg H hs hdetH`. Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `fun r => ⟨cO K r, rfl⟩`. Use `set h := hform H with hh`.

Use `set M : Matrix (Fin d) (Fin d) K := Matrix.of fun a b => h (f a) (f b) with hMdef`. Establish `hM : M.det = gramR H f`. Unfold `gramR`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[M, h, hform_eq_dot]`. Establish `hG : gramR H f ≠ 0`. Rewrite using `[gramR_eq_std]`. Use `det_of_ne_zero hf.1` as an intermediate fact. Conclude with `mul_ne_zero (mul_ne_zero (star_ne_zero.mpr this) this) hdetH`.

Establish `hMu : IsUnit M.det` using `isUnit_iff_ne_zero.mpr (hM ▸ hG)`. Use `set fs : Fin d → Fin d → K := fun b => ∑ k, M⁻¹ k b • f k with hfs`. Establish `hpair : ∀ a b, h (f a) (fs b) = if a = b then 1 else 0`. Introduce `a b`. Establish `hmul : M * M⁻¹ = 1` using `Matrix.mul_nonsing_inv M hMu`.

Use `congrFun (congrFun hmul a) b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← this, hfs, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.

Both sides reduce to the same expression. Establish `hfsli : LinearIndependent K fs`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `congrArg (h (f i)) hg` as an intermediate fact.

Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this`. Conclude with `this`. Establish `hspK : Submodule.span K (Set.range f) = ⊤` using `hf.1.span_eq_top_of_card_eq_finrank' (by simp)`. Establish `hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f))` using `⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩`.

Establish `hone : ∀ c : K, c ∈ (1 : Submodule (𝓞 K) K) → ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) * c ∈ (1 : Submodule (𝓞 K) K)`. Introduce `c hc r`. Conclude with `Formalism.HermitianLatticesTheory.locDual_one_mul (Submodule.mem_one.mpr ⟨cO K r, rfl⟩) hc`. Establish `hdual_span : Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f)) = Submodule.span (𝓞 K) (Set.range fs)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Establish `hc : ∀ a, h (f a) x ∈ (1 : Submodule (𝓞 K) K)` using `fun a => hx _ (Submodule.subset_span ⟨a, rfl⟩)`. Use `set b : Basis (Fin d) K (Fin d → K) := Basis.mk hf.1 (by rw [hspK]) with hb`. Establish `hbf : ∀ i, b i = f i` using `fun i => by simp [b]`.

Establish `hexp` using `Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b fs (by simpa [hbf] using hpair) x`. Rewrite using `[hexp]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hc j)`. Rewrite using `[hbf, ← hr, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Express the relevant statement in the definitionally equal form `fs b ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))`. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[hpair]`.

Use `split_ifs`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => rw [map_zero, LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_h_smul_left]`. Conclude with `hone _ hx r`.

Establish `hdualT : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h T)` using `(Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) h hs hnd hstar T hT).1`. Establish `hLD` using `Formalism.HermitianLatticesTheory.locDual (𝓞 K) K (Fin d → K) h hs hstar`. Establish `A` using `(hLD _ hspan_f.fg).1 w.asIdeal w.isPrime`. Establish `B` using `(hLD _ hT.fg).1 w.asIdeal w.isPrime`. Establish `hlocfs : IsLocBasis (Formalism.HermitianLatticesTheory.dual h T) w fs`.

Use `⟨hfsli, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdual_span]`. Use `_ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f))) := by`. Rewrite using `[A.1, A.2]`.

Use `_ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal T) := by rw [hf.2]`. Use `_ = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h T) := by rw [B.1, B.2]`. Establish `hone_f : (fun i => ∑ k, (1 : Matrix (Fin d) (Fin d) K) k i • f k) = f`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.one_apply]`.

Establish `i1` using `(hIC K d T hT f hf.1 w 1 (by rw [hone_f]; exact hf)).1`. Establish `i2` using `(hIC K d (Formalism.HermitianLatticesTheory.dual h T) hdualT f hf.1 w M⁻¹ hlocfs).1`. Establish `: w.asIdeal.IsMaximal` using `w.isMaximal`. Establish `hIB` using `Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin d → K) h hs hnd hstar w.asIdeal T (Submodule.span (𝓞 K) (Set.range f)) (Formalism.HermitianLatticesTheory.dual h T) hT hspan_f hdualT`. Unfold `jw Formalism.HermitianLatticesTheory.jIdx`.

Unfold `idx at i1 i2`. Rewrite using `[hIB.2.2.1, hIB.2.1, i1, i2, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ValuationRepresentative.vw_inv, hM, Matrix.det_one, ValuationRepresentative.vw_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jwGramW_of (hIC : IdxChange) : JwGramW := by
  intro K _ _ _ d H hherm hdetH T hT w f hf
  classical
  have hs := hform_isSymm H hherm
  have hnd := hform_nondeg H hs hdetH
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨cO K r, rfl⟩
  set h := hform H with hh
  set M : Matrix (Fin d) (Fin d) K := Matrix.of fun a b => h (f a) (f b) with hMdef
  have hM : M.det = gramR H f := by
    unfold gramR
    congr 1
    ext a b
    simp [M, h, hform_eq_dot]
  have hG : gramR H f ≠ 0 := by
    rw [gramR_eq_std]
    have := det_of_ne_zero hf.1
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr this) this) hdetH
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr (hM ▸ hG)
  set fs : Fin d → Fin d → K := fun b => ∑ k, M⁻¹ k b • f k with hfs
  have hpair : ∀ a b, h (f a) (fs b) = if a = b then 1 else 0 := by
    intro a b
    have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
    have := congrFun (congrFun hmul a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, hfs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have hfsli : LinearIndependent K fs := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (h (f i)) hg
    rw [map_sum, map_zero] at this
    simp only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  have hspK : Submodule.span K (Set.range f) = ⊤ :=
    hf.1.span_eq_top_of_card_eq_finrank' (by simp)
  have hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f)) :=
    ⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩
  have hone : ∀ c : K, c ∈ (1 : Submodule (𝓞 K) K) → ∀ r : 𝓞 K,
      star (algebraMap (𝓞 K) K r) * c ∈ (1 : Submodule (𝓞 K) K) := by
    intro c hc r
    exact Formalism.HermitianLatticesTheory.locDual_one_mul (Submodule.mem_one.mpr ⟨cO K r, rfl⟩) hc
  have hdual_span : Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f)) =
      Submodule.span (𝓞 K) (Set.range fs) := by
    apply le_antisymm
    · intro x hx
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
      have hc : ∀ a, h (f a) x ∈ (1 : Submodule (𝓞 K) K) :=
        fun a => hx _ (Submodule.subset_span ⟨a, rfl⟩)
      set b : Basis (Fin d) K (Fin d → K) := Basis.mk hf.1 (by rw [hspK]) with hb
      have hbf : ∀ i, b i = f i := fun i => by simp [b]
      have hexp := Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b fs (by simpa [hbf] using hpair) x
      rw [hexp]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hc j)
      rw [hbf, ← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      change fs b ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [hpair]
        split_ifs
        · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
        · exact Submodule.zero_mem _
      | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left]
        exact hone _ hx r
  have hdualT : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h T) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) h hs hnd hstar T hT).1
  have hLD := Formalism.HermitianLatticesTheory.locDual (𝓞 K) K (Fin d → K) h hs hstar
  have A := (hLD _ hspan_f.fg).1 w.asIdeal w.isPrime
  have B := (hLD _ hT.fg).1 w.asIdeal w.isPrime
  have hlocfs : IsLocBasis (Formalism.HermitianLatticesTheory.dual h T) w fs := by
    refine ⟨hfsli, ?_⟩
    calc Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range fs))
        = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))) := by
          rw [hdual_span]
      _ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal
            (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f))) := by
          rw [A.1, A.2]
      _ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal T) := by rw [hf.2]
      _ = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h T) := by rw [B.1, B.2]
  have hone_f : (fun i => ∑ k, (1 : Matrix (Fin d) (Fin d) K) k i • f k) = f := by
    funext i
    simp [Matrix.one_apply]
  have i1 := (hIC K d T hT f hf.1 w 1 (by rw [hone_f]; exact hf)).1
  have i2 := (hIC K d (Formalism.HermitianLatticesTheory.dual h T) hdualT f hf.1 w M⁻¹ hlocfs).1
  have : w.asIdeal.IsMaximal := w.isMaximal
  have hIB := Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin d → K) h hs hnd hstar w.asIdeal T
    (Submodule.span (𝓞 K) (Set.range f)) (Formalism.HermitianLatticesTheory.dual h T) hT hspan_f hdualT
  unfold jw Formalism.HermitianLatticesTheory.jIdx
  unfold idx at i1 i2
  rw [hIB.2.2.1, hIB.2.1, i1, i2, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ValuationRepresentative.vw_inv,
    hM, Matrix.det_one, ValuationRepresentative.vw_one]
  ring

/- English proof (translation)
The claim follows from `jwGramW_of index_change_formula`.
-/
theorem conjugate_weight_gram_general : JwGramW := jwGramW_of index_change_formula

namespace ConjugateWeightGram

open StepBAux

section LocalW

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v => (h.2 v).1, (h.2 v0).2⟩`.
-/
theorem isHermAt_of_ratHerm {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (h : IsRatHerm K0 H X) (v0 : InfinitePlace K) :
    IsHermAt v0 H X :=
  ⟨fun v => (h.2 v).1, (h.2 v0).2⟩

/- English proof (translation)
Establish `h1` using `hR.2`. Establish `h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding`. Rewrite using `[← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Establish `h3` using `congrFun (congrFun h2 j) i`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3`.

Apply `v0.embedding.injective` to reduce the goal to its premises. Rewrite using `[hv0, ← h3, starRingEnd_apply]`.
-/
theorem herm_of_hermAt {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) (i j : Fin n) : H j i = star (H i j) := by
  have h1 := hR.2
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := by
    rw [← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h3 := congrFun (congrFun h2 j) i
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3
  apply v0.embedding.injective
  rw [hv0, ← h3, starRingEnd_apply]

/- English proof (translation)
Introduce `h0`. Establish `h1 : v0.embedding H.det = star ((X v0)⁻¹.det) * (X v0)⁻¹.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← hR.2, Matrix.det_mul, Matrix.det_conjTranspose]`. Rewrite `h1` using `[h0, map_zero]`. Establish `hz : (X v0)⁻¹.det ≠ 0` using `(Matrix.isUnit_nonsing_inv_det _ (hR.1 v0)).ne_zero`.

Conclude with `mul_ne_zero (star_ne_zero.mpr hz) hz h1.symm`.
-/
theorem det_ne_of_hermAt {v0 : InfinitePlace K} {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) : H.det ≠ 0 := by
  intro h0
  have h1 : v0.embedding H.det = star ((X v0)⁻¹.det) * (X v0)⁻¹.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hR.2, Matrix.det_mul,
      Matrix.det_conjTranspose]
  rw [h0, map_zero] at h1
  have hz : (X v0)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hR.1 v0)).ne_zero
  exact mul_ne_zero (star_ne_zero.mpr hz) hz h1.symm

/- English proof (translation)
Establish `hm : met X v0 = H.map v0.embedding` using `hH.2`. Rewrite using `[gramR, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [gram, Formalism.HN.gramPl, Matrix.of_apply, StepBAux.majAt_eq, hm, RingHom.mapMatrix_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, cvec, Pi.star_apply, map_sum, map_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hv0, Complex.star_def]`.
-/
theorem gram_hermAt {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (hH : IsHermAt v0 H X) (f : Fin d → Fin d → K) :
    (gram X v0 f).det = v0.embedding (gramR H f) := by
  have hm : met X v0 = H.map v0.embedding := hH.2
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, StepBAux.majAt_eq, hm, RingHom.mapMatrix_apply,
    Matrix.map_apply, dotProduct, Matrix.mulVec, cvec, Pi.star_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0, Complex.star_def]

/- English proof (translation)
Take `⟨hmul, hstar, -, -, -, -, -⟩` from `hV K w`. Take `⟨γ, hγ, hy1, hy2⟩` from `idx_change_img hIC ι0 ι1 hι0 hι1 Lam0 Lam1 hL1 w e0 e1 he0 he1`. Use `choose δ hδ hz1 hz2 using fun j => idx_change_img hIC (θ0 j) (θ1 j) (hθ0 j) (hθ1 j) (T0 j) (T1 j) (hT1 j) w (f0 j) (f1 j) (hf0 j) (hf1 j)`. Establish `hc : ∀ j (u : HeightOneSpectrum (𝓞 K)), idx u (M j) (matLat (θ1 j) (T1 j)) = idx u (M j) (matLat (θ0 j) (T0 j)) + idx u (matLat (θ0 j) (T0 j)) (matLat (θ1 j) (T1 j))` using `fun j u => lidx_add (K := K) u.asIdeal _ _ _ (hM j) (matLat_lattice _ (hθ0 j) _ (hT0 j)) (matLat_lattice _ (hθ1 j) _ (hT1 j))`. Establish `hj0 : ∀ j, jw (HT0 j) w (T0 j) = - vw w (gramR (HT0 j) (f0 j))` using `fun j => hJw K (d j) (HT0 j) (herm_of_hermAt hv0 (hHT0 j)) (det_ne_of_hermAt (hHT0 j)) (T0 j) (hT0 j) w (f0 j) (hf0 j)`.

Establish `hj1 : ∀ j, jw (HT1 j) w (T1 j) = - vw w (gramR (HT1 j) (f1 j))` using `fun j => hJw K (d j) (HT1 j) (herm_of_hermAt hv0 (hHT1 j)) (det_ne_of_hermAt (hHT1 j)) (T1 j) (hT1 j) w (f1 j) (hf1 j)`. Establish `hXT0 : ∀ j v, IsUnit (XT0 j v).det` using `fun j v => (hHT0 j).1 v`. Establish `hXT1 : ∀ j v, IsUnit (XT1 j v).det` using `fun j v => (hHT1 j).1 v`. Establish `h1 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det = star (v0.embedding γ.det) * v0.embedding γ.det * (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det`. Rewrite using `[hγ]`.

Conclude with `gram_change _ _ _ _`. Establish `h21 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det = (detRatio XQ1 XE ι1 v0 : ℂ) * v0.embedding G1`. Rewrite using `[hG1]`. Conclude with `gram_image XQ1 XE hXQ1 ι1 e1 v0`. Establish `h20 : (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det = (detRatio XQ0 XE ι0 v0 : ℂ) * v0.embedding G0`.

Rewrite using `[hG0]`. Conclude with `gram_image XQ0 XE hXQ0 ι0 e0 v0`. Establish `h4 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det = star (v0.embedding (δ j).det) * v0.embedding (δ j).det * (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det` using `fun j => by`. Rewrite using `[hδ j]`. Conclude with `gram_change _ _ _ _`.

Establish `h51 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det = (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ) * v0.embedding (gramR (HT1 j) (f1 j))` using `fun j => by`. Rewrite using `[← gram_hermAt (HT1 j) (XT1 j) v0 hv0 (hHT1 j)]`. Conclude with `gram_image (XT1 j) (XW j) (hXT1 j) (θ1 j) (f1 j) v0`. Establish `h50 : ∀ j, (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det = (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) * v0.embedding (gramR (HT0 j) (f0 j))` using `fun j => by`. Rewrite using `[← gram_hermAt (HT0 j) (XT0 j) v0 hv0 (hHT0 j)]`.

Conclude with `gram_image (XT0 j) (XW j) (hXT0 j) (θ0 j) (f0 j) v0`. Establish `hθne : ∀ j, (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) ≠ 0` using `fun j => by`. Conclude with `detRatio_ne (XT0 j) (XW j) (hXT0 j) (hXW j) (θ0 j) (hθ0 j) v0` after adjusting the coercions. Establish `hC` using `key_alg (J := J) D (gE0 := (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det) (gE1 := (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det) (dR0 := (detRatio XQ0 XE ι0 v0 : ℂ)) (dR1 := (detRatio XQ1 XE ι1 v0 : ℂ)) (G0 := v0.embedding G0) (G1 := v0.embedding G1) (Ny := star (v0.embedding γ.det) * v0.embed …`. Establish `hK : ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j)) = star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j)`.

Establish `hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a)` using `hv0`. Apply `v0.embedding.injective` to reduce the goal to its premises. Simplify using `only [map_mul, map_pow, map_prod, hv0', hρ]`. Simplify using `only [Complex.star_def] at hC`. Conclude with `hC`.

Establish `hG0ne : G0 ≠ 0` using `fun h => gram_ne XQ0 hXQ0 e0 he0.1 v0 (by rw [← hG0, h, map_zero])`. Establish `hG1ne : G1 ≠ 0` using `fun h => gram_ne XQ1 hXQ1 e1 he1.1 v0 (by rw [← hG1, h, map_zero])`. Establish `hγne : γ.det ≠ 0`. Introduce `h`. Apply `gram_ne XE hXE _ (image_li ι1 hι1 e1 he1.1) v0` to reduce the goal to its premises.

Rewrite using `[h1, h, map_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hδne : ∀ j, (δ j).det ≠ 0`. Introduce `j h`. Apply `gram_ne (XW j) (hXW j) _ (image_li (θ1 j) (hθ1 j) (f1 j) (hf1 j).1) v0` to reduce the goal to its premises.

Rewrite using `[h4 j, h, map_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgT0ne : ∀ j, gramR (HT0 j) (f0 j) ≠ 0` using `fun j h => gram_ne (XT0 j) (hXT0 j) (f0 j) (hf0 j).1 v0 (by rw [gram_hermAt (HT0 j) (XT0 j) v0 hv0 (hHT0 j), h, map_zero])`. Establish `hgT1ne : ∀ j, gramR (HT1 j) (f1 j) ≠ 0` using `fun j h => gram_ne (XT1 j) (hXT1 j) (f1 j) (hf1 j).1 v0 (by rw [gram_hermAt (HT1 j) (XT1 j) v0 hv0 (hHT1 j), h, map_zero])`. Establish `hρne : ρ ≠ 0`.

Introduce `h`. Rewrite `hρ` using `[h, map_zero]`. Conclude with `hρpos.ne' (by exact_mod_cast hρ.symm)`. Establish `hv` using `congrArg (vw w) hK`. Establish `hL : vw w (ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j))) = vw w G1 + ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j)))`.

Establish `hne : ∀ j, star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j) ≠ 0` using `fun j => mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j)`. Rewrite using `[hmul _ _ (mul_ne_zero (pow_ne_zero _ hρne) hG1ne) (Finset.prod_ne_zero_iff.mpr fun j _ => hne j), hmul _ _ (pow_ne_zero _ hρne) hG1ne, vw_pow hV w ρ hρne, hρv, vw_prod hV w _ _ hne]`. Simplify using `only [mul_zero, zero_add]`. Use `congrArg _ (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j), hmul _ _ (star_ne_zero.mpr (hδne j)) (hδne j), hstar]`.

Establish `hR : vw w (star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j)) = vw (conjPl w) γ.det + vw w γ.det + vw w G0 + ∑ j, vw w (gramR (HT1 j) (f1 j))`. Rewrite using `[hmul _ _ (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne) (Finset.prod_ne_zero_iff.mpr fun j _ => hgT1ne j), hmul _ _ (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne, hmul _ _ (star_ne_zero.mpr hγne) hγne, hstar, vw_prod hV w _ _ hgT1ne]`. Establish `hsum : ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) - idx w (M j) (matLat (θ0 j) (T0 j))) + (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) - idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) + (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) = ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + v …`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hc j w, hc j (conjPl w), hz1 j, hz2 j, hj0 j, hj1 j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, hy1, hy2]`. Rewrite `hv` using `[hL, hR]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem local_idW (hV : ValBasic) (hIC : IdxChange) (hJw : JwGramW) [IsTotallyComplex K]
    (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (XQ0 XQ1 : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ0 : ∀ v, IsUnit (XQ0 v).det)
    (hXQ1 : ∀ v, IsUnit (XQ1 v).det)
    (Lam0 Lam1 : Submodule (𝓞 K) (Fin D → K)) (hL1 : Submodule.IsLattice K Lam1)
    (ι0 ι1 : Matrix (Fin D) (Fin D) K) (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det)
    (J : Type) [Fintype J] (d : J → ℕ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hXW : ∀ j v, IsUnit (XW j v).det)
    (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)) (hM : ∀ j, Submodule.IsLattice K (M j))
    (HT0 HT1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K)
    (XT0 XT1 : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hHT0 : ∀ j, IsHermAt v0 (HT0 j) (XT0 j)) (hHT1 : ∀ j, IsHermAt v0 (HT1 j) (XT1 j))
    (T0 T1 : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (hT0 : ∀ j, Submodule.IsLattice K (T0 j)) (hT1 : ∀ j, Submodule.IsLattice K (T1 j))
    (θ0 θ1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K) (hθ0 : ∀ j, IsUnit (θ0 j).det)
    (hθ1 : ∀ j, IsUnit (θ1 j).det)
    (κ0 ρr : ℝ) (hκ : 0 < κ0) (ρ : K) (hρ : v0.embedding ρ = (ρr : ℂ)) (hρpos : 0 < ρr)
    (w : HeightOneSpectrum (𝓞 K)) (hρv : vw w ρ = 0)
    (hdet0 : detRatio XQ0 XE ι0 v0 = κ0 ^ D * ∏ j, detRatio (XT0 j) (XW j) (θ0 j) v0)
    (hdet1 : detRatio XQ1 XE ι1 v0 = (κ0 * ρr) ^ D * ∏ j, detRatio (XT1 j) (XW j) (θ1 j) v0)
    (G0 G1 : K) (e0 e1 : Fin D → Fin D → K) (he0 : IsLocBasis Lam0 w e0)
    (he1 : IsLocBasis Lam1 w e1)
    (hG0 : v0.embedding G0 = (gram XQ0 v0 e0).det) (hG1 : v0.embedding G1 = (gram XQ1 v0 e1).det)
    (f0 f1 : ∀ j, Fin (d j) → Fin (d j) → K) (hf0 : ∀ j, IsLocBasis (T0 j) w (f0 j))
    (hf1 : ∀ j, IsLocBasis (T1 j) w (f1 j)) :
    idx w (matLat ι0 Lam0) (matLat ι1 Lam1) + idx (conjPl w) (matLat ι0 Lam0) (matLat ι1 Lam1) =
      vw w G1 - vw w G0 + ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) := by
  classical
  obtain ⟨hmul, hstar, -, -, -, -, -⟩ := hV K w
  obtain ⟨γ, hγ, hy1, hy2⟩ := idx_change_img hIC ι0 ι1 hι0 hι1 Lam0 Lam1 hL1 w e0 e1 he0 he1
  choose δ hδ hz1 hz2 using fun j => idx_change_img hIC (θ0 j) (θ1 j) (hθ0 j) (hθ1 j) (T0 j)
    (T1 j) (hT1 j) w (f0 j) (f1 j) (hf0 j) (hf1 j)
  have hc : ∀ j (u : HeightOneSpectrum (𝓞 K)), idx u (M j) (matLat (θ1 j) (T1 j)) =
      idx u (M j) (matLat (θ0 j) (T0 j)) + idx u (matLat (θ0 j) (T0 j)) (matLat (θ1 j) (T1 j)) :=
    fun j u => lidx_add (K := K) u.asIdeal _ _ _ (hM j) (matLat_lattice _ (hθ0 j) _ (hT0 j))
      (matLat_lattice _ (hθ1 j) _ (hT1 j))
  have hj0 : ∀ j, jw (HT0 j) w (T0 j) = - vw w (gramR (HT0 j) (f0 j)) := fun j =>
    hJw K (d j) (HT0 j) (herm_of_hermAt hv0 (hHT0 j)) (det_ne_of_hermAt (hHT0 j)) (T0 j) (hT0 j) w (f0 j) (hf0 j)
  have hj1 : ∀ j, jw (HT1 j) w (T1 j) = - vw w (gramR (HT1 j) (f1 j)) := fun j =>
    hJw K (d j) (HT1 j) (herm_of_hermAt hv0 (hHT1 j)) (det_ne_of_hermAt (hHT1 j)) (T1 j) (hT1 j) w (f1 j) (hf1 j)
  have hXT0 : ∀ j v, IsUnit (XT0 j v).det := fun j v => (hHT0 j).1 v
  have hXT1 : ∀ j v, IsUnit (XT1 j v).det := fun j v => (hHT1 j).1 v
  have h1 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det = star (v0.embedding γ.det) *
      v0.embedding γ.det * (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det := by
    rw [hγ]; exact gram_change _ _ _ _
  have h21 : (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det =
      (detRatio XQ1 XE ι1 v0 : ℂ) * v0.embedding G1 := by
    rw [hG1]; exact gram_image XQ1 XE hXQ1 ι1 e1 v0
  have h20 : (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det =
      (detRatio XQ0 XE ι0 v0 : ℂ) * v0.embedding G0 := by
    rw [hG0]; exact gram_image XQ0 XE hXQ0 ι0 e0 v0
  have h4 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      star (v0.embedding (δ j).det) * v0.embedding (δ j).det *
        (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det := fun j => by
    rw [hδ j]; exact gram_change _ _ _ _
  have h51 : ∀ j, (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det =
      (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ) * v0.embedding (gramR (HT1 j) (f1 j)) := fun j => by
    rw [← gram_hermAt (HT1 j) (XT1 j) v0 hv0 (hHT1 j)]
    exact gram_image (XT1 j) (XW j) (hXT1 j) (θ1 j) (f1 j) v0
  have h50 : ∀ j, (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det =
      (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) * v0.embedding (gramR (HT0 j) (f0 j)) := fun j => by
    rw [← gram_hermAt (HT0 j) (XT0 j) v0 hv0 (hHT0 j)]
    exact gram_image (XT0 j) (XW j) (hXT0 j) (θ0 j) (f0 j) v0
  have hθne : ∀ j, (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ) ≠ 0 := fun j => by
    exact_mod_cast detRatio_ne (XT0 j) (XW j) (hXT0 j) (hXW j) (θ0 j) (hθ0 j) v0
  have hC := key_alg (J := J) D
    (gE0 := (gram XE v0 (fun i => ι0 *ᵥ e0 i)).det) (gE1 := (gram XE v0 (fun i => ι1 *ᵥ e1 i)).det)
    (dR0 := (detRatio XQ0 XE ι0 v0 : ℂ)) (dR1 := (detRatio XQ1 XE ι1 v0 : ℂ))
    (G0 := v0.embedding G0) (G1 := v0.embedding G1)
    (Ny := star (v0.embedding γ.det) * v0.embedding γ.det) (κ := (κ0 : ℂ)) (ρ := (ρr : ℂ))
    (gW0 := fun j => (gram (XW j) v0 (fun i => θ0 j *ᵥ f0 j i)).det)
    (gW1 := fun j => (gram (XW j) v0 (fun i => θ1 j *ᵥ f1 j i)).det)
    (dθ0 := fun j => (detRatio (XT0 j) (XW j) (θ0 j) v0 : ℂ))
    (dθ1 := fun j => (detRatio (XT1 j) (XW j) (θ1 j) v0 : ℂ))
    (gT0 := fun j => v0.embedding (gramR (HT0 j) (f0 j)))
    (gT1 := fun j => v0.embedding (gramR (HT1 j) (f1 j)))
    (Nz := fun j => star (v0.embedding (δ j).det) * v0.embedding (δ j).det)
    h1 h21 h20 (by rw [hdet1]; push_cast; ring) (by rw [hdet0]; push_cast; ring) h4 h51 h50
    (by exact_mod_cast hκ.ne') hθne
  have hK : ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j)) =
      star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j) := by
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    apply v0.embedding.injective
    simp only [map_mul, map_pow, map_prod, hv0', hρ]
    simp only [Complex.star_def] at hC
    exact hC
  have hG0ne : G0 ≠ 0 := fun h => gram_ne XQ0 hXQ0 e0 he0.1 v0 (by rw [← hG0, h, map_zero])
  have hG1ne : G1 ≠ 0 := fun h => gram_ne XQ1 hXQ1 e1 he1.1 v0 (by rw [← hG1, h, map_zero])
  have hγne : γ.det ≠ 0 := by
    intro h
    apply gram_ne XE hXE _ (image_li ι1 hι1 e1 he1.1) v0
    rw [h1, h, map_zero]; ring
  have hδne : ∀ j, (δ j).det ≠ 0 := by
    intro j h
    apply gram_ne (XW j) (hXW j) _ (image_li (θ1 j) (hθ1 j) (f1 j) (hf1 j).1) v0
    rw [h4 j, h, map_zero]; ring
  have hgT0ne : ∀ j, gramR (HT0 j) (f0 j) ≠ 0 := fun j h =>
    gram_ne (XT0 j) (hXT0 j) (f0 j) (hf0 j).1 v0
      (by rw [gram_hermAt (HT0 j) (XT0 j) v0 hv0 (hHT0 j), h, map_zero])
  have hgT1ne : ∀ j, gramR (HT1 j) (f1 j) ≠ 0 := fun j h =>
    gram_ne (XT1 j) (hXT1 j) (f1 j) (hf1 j).1 v0
      (by rw [gram_hermAt (HT1 j) (XT1 j) v0 hv0 (hHT1 j), h, map_zero])
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact hρpos.ne' (by exact_mod_cast hρ.symm)
  have hv := congrArg (vw w) hK
  have hL : vw w (ρ ^ D * G1 * ∏ j, (star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j))) =
      vw w G1 + ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) := by
    have hne : ∀ j, star (δ j).det * (δ j).det * gramR (HT0 j) (f0 j) ≠ 0 := fun j =>
      mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j)
    rw [hmul _ _ (mul_ne_zero (pow_ne_zero _ hρne) hG1ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hne j),
      hmul _ _ (pow_ne_zero _ hρne) hG1ne, vw_pow hV w ρ hρne, hρv, vw_prod hV w _ _ hne]
    simp only [mul_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hmul _ _ (mul_ne_zero (star_ne_zero.mpr (hδne j)) (hδne j)) (hgT0ne j),
      hmul _ _ (star_ne_zero.mpr (hδne j)) (hδne j), hstar]
  have hR : vw w (star γ.det * γ.det * G0 * ∏ j, gramR (HT1 j) (f1 j)) =
      vw (conjPl w) γ.det + vw w γ.det + vw w G0 + ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hgT1ne j),
      hmul _ _ (mul_ne_zero (star_ne_zero.mpr hγne) hγne) hG0ne,
      hmul _ _ (star_ne_zero.mpr hγne) hγne, hstar, vw_prod hV w _ _ hgT1ne]
  have hsum : ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) =
      ∑ j, (vw (conjPl w) (δ j).det + vw w (δ j).det + vw w (gramR (HT0 j) (f0 j))) -
        ∑ j, vw w (gramR (HT1 j) (f1 j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j w, hc j (conjPl w), hz1 j, hz2 j, hj0 j, hj1 j]
    ring
  rw [hsum, hy1, hy2]
  rw [hL, hR] at hv
  linarith

end LocalW

end ConjugateWeightGram

open StepBAux ConjugateWeightGram in
/- English proof (translation)
Introduce `K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρ hρ1 hρpos hρv hdetAll hdetV0 G e he hG hR R hRlat hRloc`. Establish `hlw : ∀ w : HeightOneSpectrum (𝓞 K), lw (conjPl w) = lw w` using `fun w => (hV K w).2.2.1`. Establish `hΛ0 : Submodule.IsLattice K (matLat (ι μ0) (abelian₂ μ0))` using `matLat_lattice _ (hι μ0) _ (hLam μ0)`. Establish `hA0 : ∀ j, Submodule.IsLattice K (matLat (θ j μ0) (T j μ0))` using `fun j => matLat_lattice _ (hθ j μ0) _ (hT j μ0)`. Establish `hXT : ∀ j t v, IsUnit (XT j t v).det` using `fun j t v => (hHTw j t).1 v`.

Use `choose f hf using fun j t w => hLoc K (d j) (T j t) (hT j t) w`. Establish `hloc : ∀ w : HeightOneSpectrum (𝓞 K), idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R = vw w (G (μ w) w) - vw w (G μ0 w) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) - idx w (M j) (matLat (θ j μ0) (T j μ0))) + (idx (conjPl w) (M j) …`. Introduce `w`. Establish `hRc` using `hRloc (conjPl w)`. Rewrite `hRc` using `[hμc]`.

Establish `hx1 : idx w (matLat (ι μ0) (abelian₂ μ0)) R = idx w (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w)))` using `lidx_congr _ _ _ _ _ rfl (hRloc w)`. Establish `hx2 : idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R = idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w)))` using `lidx_congr _ _ _ _ _ rfl hRc`. Rewrite using `[hx1, hx2]`. Conclude with `local_idW hV hIC hJw v0 hv0 D XE hXE (XQ μ0) (XQ (μ w)) (hXQ μ0) (hXQ (μ w)) (abelian₂ μ0) (abelian₂ (μ w)) (hLam (μ w)) (ι μ0) (ι (μ w)) (hι μ0) (hι (μ w)) J d XW hXW M hM (fun j => HT j μ0) (fun j => HT j (μ w)) (fun j => XT j μ0) (fun j => XT j (μ w)) (fun j => hHTw j μ0) (fun …`. Establish `hFeq : ∀ w : HeightOneSpectrum (𝓞 K), lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) = lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : …`.

Introduce `w`. Establish `hZ : vw w (G (μ w) w) + ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) + idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) + jw (HT j (μ w)) w (T j (μ w))) = idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R + vw w (G μ0 w) + ∑ j, (idx …`. Establish `h` using `hloc w`. Establish `hs : ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) + idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) + jw (HT j (μ w)) w (T j (μ w))) = ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) - idx w (M j) (matLat (θ j μ0) (T j μ0))) + (idx (conjPl w) (M j) (matLat (θ j (μ …`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hZR : ((vw w (G (μ w) w) : ℤ) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) = (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) + (idx (conjPl w) (matLat (ι μ0) (abeli …`. Conclude with `hZ` after adjusting the coercions. Rewrite using `[hlw w, hZR]`.

Simplify using `only [mul_add, Finset.mul_sum]`. Establish `sx` using `(hIL K D XE hXE _ R hΛ0 hRlat).1`. Establish `sx'` using `supp_conj hV _ sx`. Establish `sa` using `G_finite hV hIC hLB hPF v0 hv0 D (XQ μ0) (hXQ μ0) (abelian₂ μ0) (hLam μ0) (G μ0) (e μ0) (he μ0) (hG μ0)`. Establish `sb : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite` using `fun j => (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).1`.

Establish `sb' : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite` using `fun j => supp_conj hV _ (sb j)`. Establish `sc : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite` using `fun j => (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).1`. Establish `sin : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite` using `fun j => supp_add _ _ (supp_add _ _ (sb j) (sb' j)) (sc j)`. Establish `sJ` using `supp_sum (fun j (w : HeightOneSpectrum (𝓞 K)) => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) sin`. Establish `s12` using `supp_add _ _ sx sx'`.

Establish `s123` using `supp_add _ _ s12 sa`. Establish `sAll` using `supp_add _ _ s123 sJ`. Use `⟨sAll.subset ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Function.mem_support] at hw ⊢`.

Rewrite `hw` using `[hFeq w]`. Then use the resulting hypothesis. Establish `hsumF` using `finsum_congr hFeq`. Rewrite `hsumF` using `[finsum_add_distrib s123 sJ, finsum_add_distrib s12 sa, finsum_add_distrib sx sx', finsum_sum_comm _ _ (fun j _ => sin j)]`. Establish `hcx : (∑ᶠ w, lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ)) = ∑ᶠ w, lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ)` using `hFC K (fun w => lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ))`. Establish `hcb : ∑ j, (∑ᶠ w, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + lw w * (jw (HT j μ0) w (T j μ0) : ℝ))) = ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + ∑ᶠ w, lw w * (jw (HT j μ …`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_add_distrib (supp_add _ _ (sb j) (sb' j)) (sc j), finsum_add_distrib (sb j) (sb' j), hFC K (fun w => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ))]`. Expand and normalize the polynomial expressions, which then agree. Establish `hI1` using `(hIL K D XE hXE _ R hΛ0 hRlat).2`. Establish `hI2` using `hIm K D (XQ μ0) XE (hXQ μ0) hXE (ι μ0) (hι μ0) (abelian₂ μ0) (hLam μ0)`.

Establish `hθne : ∀ j v, detRatio (XT j μ0) (XW j) (θ j μ0) v ≠ 0` using `fun j v => detRatio_ne (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) v`. Establish `hlogv : ∀ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) = (D : ℝ) * Real.log (κ v) + ∑ j, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v)`. Introduce `v`. Rewrite using `[hdetAll v, Real.log_mul (pow_ne_zero _ (hκ v).ne') (Finset.prod_ne_zero_iff.mpr fun j _ => hθne j v), Real.log_pow, Real.log_prod (fun j _ => hθne j v)]`. Establish `hlogsum : ∑ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) = (D : ℝ) * ∑ v, Real.log (κ v) + ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v)`.

Rewrite using `[Finset.sum_congr rfl (fun v _ => hlogv v), Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]`. Establish `hN : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ)`. Rewrite using `[IsTotallyComplex.finrank, Formalism.HN.nPl, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmean : (2 / (finrank ℚ K : ℝ)) * ((D : ℝ) * ∑ v, Real.log (κ v)) = (D : ℝ) * meanLog κ`. Rewrite using `[meanLog, hN]`. Break down `eq_or_ne (Formalism.HN.nPl K : ℝ) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Establish `hθj : ∀ j, (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) = lcv (XW j) (M j) + (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ))`. Introduce `j`. Establish `e1` using `hIm K (d j) (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) (T j μ0) (hT j μ0)`. Establish `e2` using `(hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).2`.

Establish `e3` using `(hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hθsum : (2 / (finrank ℚ K : ℝ)) * ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) = ∑ j, lcv (XW j) (M j) + ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) + ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ))`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => hθj j`.

Rewrite `hI2` using `[hlogsum, mul_add]`. Rewrite using `[hsumF, hcx, hcb]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem stepBW_of (hPF : ProdFormula) (hLB : LcvBasis) (hIC : IdxChange) (hV : ValBasic)
    (hIm : ImageLcv) (hIL : IdxLcv) (hRH : RatHermLcv) (hJw : JwGramW) (hFC : FinsumConj)
    (hLoc : LocBasisEx) : StepBW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM
    HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρ hρ1 hρpos hρv hdetAll hdetV0 G e he hG hR R hRlat hRloc
  classical
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), lw (conjPl w) = lw w := fun w => (hV K w).2.2.1
  have hΛ0 : Submodule.IsLattice K (matLat (ι μ0) (abelian₂ μ0)) :=
    matLat_lattice _ (hι μ0) _ (hLam μ0)
  have hA0 : ∀ j, Submodule.IsLattice K (matLat (θ j μ0) (T j μ0)) := fun j =>
    matLat_lattice _ (hθ j μ0) _ (hT j μ0)
  have hXT : ∀ j t v, IsUnit (XT j t v).det := fun j t v => (hHTw j t).1 v
  choose f hf using fun j t w => hLoc K (d j) (T j t) (hT j t) w

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        vw w (G (μ w) w) - vw w (G μ0 w) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx w (M j) (matLat (θ j μ0) (T j μ0))) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
          (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) := by
    intro w
    have hRc := hRloc (conjPl w)
    rw [hμc] at hRc
    have hx1 : idx w (matLat (ι μ0) (abelian₂ μ0)) R =
        idx w (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl (hRloc w)
    have hx2 : idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl hRc
    rw [hx1, hx2]
    exact local_idW hV hIC hJw v0 hv0 D XE hXE (XQ μ0) (XQ (μ w)) (hXQ μ0) (hXQ (μ w))
      (abelian₂ μ0) (abelian₂ (μ w)) (hLam (μ w)) (ι μ0) (ι (μ w)) (hι μ0) (hι (μ w)) J d XW hXW M hM
      (fun j => HT j μ0) (fun j => HT j (μ w)) (fun j => XT j μ0) (fun j => XT j (μ w))
      (fun j => hHTw j μ0) (fun j => hHTw j (μ w)) (fun j => T j μ0) (fun j => T j (μ w))
      (fun j => hT j μ0) (fun j => hT j (μ w)) (fun j => θ j μ0) (fun j => θ j (μ w))
      (fun j => hθ j μ0) (fun j => hθ j (μ w)) (κ v0) (ρr (μ w)) (hκ v0) (ρ (μ w)) (hρ (μ w))
      (hρpos (μ w)) w (hρv w) (hdetAll v0) (hdetV0 (μ w)) (G μ0 w) (G (μ w) w) (e μ0 w)
      (e (μ w) w) (he μ0 w) (he (μ w) w) (hG μ0 w) (hG (μ w) w) (fun j => f j μ0 w)
      (fun j => f j (μ w) w) (fun j => hf j μ0 w) (fun j => hf j (μ w) w)

  have hFeq : ∀ w : HeightOneSpectrum (𝓞 K),
      lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) =
      lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw w * (vw w (G μ0 w) : ℝ) +
        ∑ j, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro w
    have hZ : vw w (G (μ w) w) + ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
          idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) + jw (HT j (μ w)) w (T j (μ w))) =
        idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R +
          vw w (G μ0 w) + ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
      have h := hloc w
      have hs : ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            jw (HT j (μ w)) w (T j (μ w))) =
          ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx w (M j) (matLat (θ j μ0) (T j μ0))) +
            (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
            (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) +
          ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    have hZR : ((vw w (G (μ w) w) : ℤ) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) =
        (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) + (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
          (vw w (G μ0 w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (jw (HT j μ0) w (T j μ0) : ℝ)) := by
      exact_mod_cast hZ
    rw [hlw w, hZR]
    simp only [mul_add, Finset.mul_sum]

  have sx := (hIL K D XE hXE _ R hΛ0 hRlat).1
  have sx' := supp_conj hV _ sx
  have sa := G_finite hV hIC hLB hPF v0 hv0 D (XQ μ0) (hXQ μ0) (abelian₂ μ0) (hLam μ0) (G μ0) (e μ0)
    (he μ0) (hG μ0)
  have sb : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).1
  have sb' : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    supp_conj hV _ (sb j)
  have sc : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).1
  have sin : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    supp_add _ _ (supp_add _ _ (sb j) (sb' j)) (sc j)
  have sJ := supp_sum (fun j (w : HeightOneSpectrum (𝓞 K)) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) sin
  have s12 := supp_add _ _ sx sx'
  have s123 := supp_add _ _ s12 sa
  have sAll := supp_add _ _ s123 sJ
  refine ⟨sAll.subset ?_, ?_⟩
  · intro w hw
    simp only [Function.mem_support] at hw ⊢
    rwa [hFeq w] at hw

  have hsumF := finsum_congr hFeq
  rw [finsum_add_distrib s123 sJ, finsum_add_distrib s12 sa, finsum_add_distrib sx sx',
    finsum_sum_comm _ _ (fun j _ => sin j)] at hsumF
  have hcx : (∑ᶠ w, lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ)) =
      ∑ᶠ w, lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) :=
    hFC K (fun w => lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ))
  have hcb : ∑ j, (∑ᶠ w, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ))) =
      ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finsum_add_distrib (supp_add _ _ (sb j) (sb' j)) (sc j),
      finsum_add_distrib (sb j) (sb' j),
      hFC K (fun w => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ))]
    ring

  have hI1 := (hIL K D XE hXE _ R hΛ0 hRlat).2
  have hI2 := hIm K D (XQ μ0) XE (hXQ μ0) hXE (ι μ0) (hι μ0) (abelian₂ μ0) (hLam μ0)
  have hθne : ∀ j v, detRatio (XT j μ0) (XW j) (θ j μ0) v ≠ 0 := fun j v =>
    detRatio_ne (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) v
  have hlogv : ∀ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * Real.log (κ v) + ∑ j, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    intro v
    rw [hdetAll v, Real.log_mul (pow_ne_zero _ (hκ v).ne')
      (Finset.prod_ne_zero_iff.mpr fun j _ => hθne j v), Real.log_pow,
      Real.log_prod (fun j _ => hθne j v)]
  have hlogsum : ∑ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * ∑ v, Real.log (κ v) +
        ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    rw [Finset.sum_congr rfl (fun v _ => hlogv v), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have hN : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    rw [IsTotallyComplex.finrank, Formalism.HN.nPl,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    push_cast; ring
  have hmean : (2 / (finrank ℚ K : ℝ)) * ((D : ℝ) * ∑ v, Real.log (κ v)) = (D : ℝ) * meanLog κ := by
    rw [meanLog, hN]
    rcases eq_or_ne (Formalism.HN.nPl K : ℝ) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  have hθj : ∀ j, (2 / (finrank ℚ K : ℝ)) *
      ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      lcv (XW j) (M j) + (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro j
    have e1 := hIm K (d j) (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) (T j μ0)
      (hT j μ0)
    have e2 := (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).2
    have e3 := (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).2
    linarith
  have hθsum : (2 / (finrank ℚ K : ℝ)) *
      ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      ∑ j, lcv (XW j) (M j) + ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hθj j
  rw [hlogsum, mul_add] at hI2
  rw [hsumF, hcx, hcb]
  linarith

/- English proof (translation)
The claim follows from `stepBW_of prod_formula' covolume_via_basis index_change_formula valuation_basic_properties (imageLcv_of covolume_via_basis) (idxLcv_of covolume_via_basis) (ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists) conjugate_weight_gram_general finite_sum_conju …`.
-/
theorem weak_form_b : StepBW :=
  stepBW_of prod_formula' covolume_via_basis index_change_formula valuation_basic_properties
    (imageLcv_of covolume_via_basis) (idxLcv_of covolume_via_basis)
    (ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists) conjugate_weight_gram_general
    finite_sum_conjugation semilocal_basis_exists

/- English proof (translation)
Introduce `K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP hQ Mt hMt hLamP hGR R hR hRloc`. Establish `hLB0 : ∀ w, IsLocBasis (matLat P Mt) w (e μ0 w)` using `fun w => hLamP ▸ hLB μ0 w`. Establish `hRb` using `(lemmaRb K K0 hK0 v0 hv0 n D H hH hHpos P hP (XQ μ0) hQ Mt hMt (e μ0) hLB0).2`. Establish `hbase : lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ)`. Rewrite using `[hLamP]`.

Simplify `hRb` using `only [hGR]`. Conclude with `weak_form_b K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG hbase R hR hRloc`.
-/
theorem second_step_refined_weak : StepBRW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW
    M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP
    hQ Mt hMt hLamP hGR R hR hRloc
  have hLB0 : ∀ w, IsLocBasis (matLat P Mt) w (e μ0 w) := fun w => hLamP ▸ hLB μ0 w
  have hRb := (lemmaRb K K0 hK0 v0 hv0 n D H hH hHpos P hP (XQ μ0) hQ Mt hMt (e μ0) hLB0).2
  have hbase : lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ) := by
    rw [hLamP]
    simpa only [hGR] using hRb
  exact weak_form_b K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J d XW hXW M hM
    HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG hbase R hR hRloc

/- English proof (translation)
Introduce `K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP hQ Mt hMt hLamP hGR R hR hRloc S hS LG E3 L E1 E2 ell g F err Jx η hD hGb hLG hL hI hJ hE1 …`. Take `⟨-, hB⟩` from `second_step_refined_weak K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP hQ Mt hMt hLamP hGR R hR hRloc`. Establish `hsupp : (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))) ⊆ (S : Set (HeightOneSpectrum (𝓞 K)))`. Introduce `w hw`. Assume the negation of the conclusion as `hwS`.

Conclude with `hw (hS w hwS)`. Rewrite `hB` using `[finsum_eq_sum_of_support_subset _ hsupp]`. Conclude with `divisor_bounds_sum (HeightOneSpectrum (𝓞 K)) J S D hD (lcv XE R) (meanLog κ) LG E3 (fun j => lcv (XW j) (M j)) L E1 E2 lw ell (fun w => (vw w (G (μ w) w) : ℝ)) g (fun w j => (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) (fun w j => (idx (conjPl w) (M j) (matLat (θ j (μ w)) …`.
-/
theorem divisor_bounds_chain_weak : BoundsChainW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW
    M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP
    hQ Mt hMt hLamP hGR R hR hRloc S hS LG E3 L E1 E2 ell g F err Jx η hD hGb hLG hL hI hJ hE1 hE2 hE3
  obtain ⟨-, hB⟩ := second_step_refined_weak K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι
    J d XW hXW M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH
    hHpos P hP hQ Mt hMt hLamP hGR R hR hRloc
  have hsupp : (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))) ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    by_contra hwS
    exact hw (hS w hwS)
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hB
  exact divisor_bounds_sum (HeightOneSpectrum (𝓞 K)) J S D hD (lcv XE R) (meanLog κ) LG E3
    (fun j => lcv (XW j) (M j)) L E1 E2 lw ell (fun w => (vw w (G (μ w) w) : ℝ)) g
    (fun w j => (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ))
    (fun w j => (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ))
    (fun w j => (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) F err Jx η
    lw_nonneg' hB hGb hLG hL hI hJ hE1 hE2 hE3

namespace ConjugateWeightGram

section Field

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Introduce `σ _ ha` and use `ha σ`.
-/
theorem isCMSub_cmMax : IsCMSub (cmMax K) := fun σ _ ha => ha σ

/- English proof (translation)
Introduce `a ha σ` and use `h σ a ha`.
-/
theorem le_cmMax (K0 : Subfield K) (h : IsCMSub K0) : K0 ≤ cmMax K := fun a ha σ => h σ a ha

/- English proof (translation)
Introduce `σ`. Rewrite using `[star_star, ha σ, Complex.conj_conj]`.
-/
theorem star_mem_cmMax {a : K} (ha : a ∈ cmMax K) : star a ∈ cmMax K := by
  intro σ
  rw [star_star, ha σ, Complex.conj_conj]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha σ`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (σ (star a)) = σ a`. Rewrite using `[ha σ, Complex.conj_conj]`. Introduce `h σ`.

Use `h σ` as an intermediate fact. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (σ (star a)) = σ a at this`. Rewrite using `[← this, Complex.conj_conj]`.
-/
theorem mem_cmMax_iff_twist (a : K) : a ∈ cmMax K ↔ ∀ σ : K →+* ℂ, twist σ a = σ a := by
  constructor
  · intro ha σ
    change starRingEnd ℂ (σ (star a)) = σ a
    rw [ha σ, Complex.conj_conj]
  · intro h σ
    have := h σ
    change starRingEnd ℂ (σ (star a)) = σ a at this
    rw [← this, Complex.conj_conj]

end Field

end ConjugateWeightGram

/- English proof (translation)
Introduce `_ _ _ _` and use `⟨ConjugateWeightGram.isCMSub_cmMax, ConjugateWeightGram.le_cmMax, fun _ ha => ConjugateWeightGram.star_mem_cmMax ha, ConjugateWeightGram.mem_cmMax_iff_twist⟩`.
-/
theorem cm_maximal_order_spec : CmMaxSpec := fun _ _ _ _ =>
  ⟨ConjugateWeightGram.isCMSub_cmMax, ConjugateWeightGram.le_cmMax, fun _ ha => ConjugateWeightGram.star_mem_cmMax ha,
    ConjugateWeightGram.mem_cmMax_iff_twist⟩

namespace ConjugateWeightGram

/- English proof (translation)
Use `set d := finrank F Z with hd`. Set `b : Basis (Fin d) F Z` to `finBasis F Z`. Set `A : Matrix (Fin d) (Fin n) F` to `Matrix.of fun a i => (b a : Fin n → F) i`. Establish `hrow : LinearIndependent F A.row` using `b.linearIndependent.map' Z.subtype (Submodule.ker_subtype _)`. Establish `hrank : A.rank = d` using `by simpa using hrow.rank_matrix`.

Establish `hcols : Submodule.span F (Set.range A.col) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank_eq_finrank_span_cols, hrank]`. Simplify using the standard rewrite rules. Take `⟨s, hs, hspan, hli⟩` from `exists_linearIndependent F (Set.range A.col)`.

Establish `hsp : ⊤ ≤ Submodule.span F (Set.range (Subtype.val : s → Fin d → F))`. Rewrite using `[Subtype.range_coe, hspan, hcols]`. Set `bs : Basis s F (Fin d → F)` to `Basis.mk hli hsp`. Establish `: Fintype s` using `FiniteDimensional.fintypeBasisIndex bs`. Establish `hcard : Fintype.card s = d`.

Use `finrank_eq_card_basis bs` as an intermediate fact. Simplify using `using this.symm`. Set `e : Fin d ≃ s` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `choose g hg using fun x : s => hs x.2`. Set `f : Fin d → Fin n` to `fun a => g (e a)`.

Set `B : Matrix (Fin d) (Fin d) F` to `A.submatrix id f`. Establish `hBcol : B.col = fun a => ((e a : s) : Fin d → F)`. Use function extensionality and compare the values at `a`. Conclude with `hg (e a)`. Establish `hB : IsUnit B`.

Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit, hBcol]`. Conclude with `hli.comp e e.injective`. Establish `hBdet : IsUnit B.det` using `(Matrix.isUnit_iff_isUnit_det B).mp hB`. Set `z : Fin d → Fin n → F` to `fun a => (B⁻¹ * A) a`. Establish `hz : ∀ a b, z a (f b) = if a = b then 1 else 0`.

Introduce `a c`. Establish `h1 : z a (f c) = (B⁻¹ * B) a c`. Simplify using `only [z, B, Matrix.mul_apply, Matrix.submatrix_apply, id]`. Rewrite using `[h1, Matrix.nonsing_inv_mul B hBdet, Matrix.one_apply]`. Establish `hzli : LinearIndependent F z`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Use `congrFun hc (f i)` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, hz]`. Establish `hzmem : ∀ a, z a ∈ Z`.

Introduce `a`. Establish `: z a = ∑ c, B⁻¹ a c • (b c : Fin n → F)`. Use function extensionality and compare the values at `i`. Simplify using `[z, A, Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2`. Use `⟨d, z, f, hzli, ?_, hz⟩` and prove the remaining obligations. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `hzmem a`. Rewrite using `[finrank_span_eq_card hzli]`. Simplify using `[hd]`.
-/
theorem exists_reduced {F : Type} [Field F] {n : ℕ} (Z : Submodule F (Fin n → F)) :
    ∃ (d : ℕ) (z : Fin d → Fin n → F) (f : Fin d → Fin n), LinearIndependent F z ∧
      Submodule.span F (Set.range z) = Z ∧ ∀ a b, z a (f b) = if a = b then 1 else 0 := by
  classical
  set d := finrank F Z with hd
  let b : Basis (Fin d) F Z := finBasis F Z
  let A : Matrix (Fin d) (Fin n) F := Matrix.of fun a i => (b a : Fin n → F) i
  have hrow : LinearIndependent F A.row :=
    b.linearIndependent.map' Z.subtype (Submodule.ker_subtype _)
  have hrank : A.rank = d := by simpa using hrow.rank_matrix
  have hcols : Submodule.span F (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
    simp
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent F (Set.range A.col)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (Subtype.val : s → Fin d → F)) := by
    rw [Subtype.range_coe, hspan, hcols]
  let bs : Basis s F (Fin d → F) := Basis.mk hli hsp
  have : Fintype s := FiniteDimensional.fintypeBasisIndex bs
  have hcard : Fintype.card s = d := by
    have := finrank_eq_card_basis bs
    simpa using this.symm
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  choose g hg using fun x : s => hs x.2
  let f : Fin d → Fin n := fun a => g (e a)
  let B : Matrix (Fin d) (Fin d) F := A.submatrix id f
  have hBcol : B.col = fun a => ((e a : s) : Fin d → F) := by
    funext a
    exact hg (e a)
  have hB : IsUnit B := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hBcol]
    exact hli.comp e e.injective
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  let z : Fin d → Fin n → F := fun a => (B⁻¹ * A) a
  have hz : ∀ a b, z a (f b) = if a = b then 1 else 0 := by
    intro a c
    have h1 : z a (f c) = (B⁻¹ * B) a c := by
      simp only [z, B, Matrix.mul_apply, Matrix.submatrix_apply, id]
    rw [h1, Matrix.nonsing_inv_mul B hBdet, Matrix.one_apply]
  have hzli : LinearIndependent F z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc (f i)
    simpa [Finset.sum_apply, hz] using this
  have hzmem : ∀ a, z a ∈ Z := by
    intro a
    have : z a = ∑ c, B⁻¹ a c • (b c : Fin n → F) := by
      funext i
      simp [z, A, Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2
  refine ⟨d, z, f, hzli, ?_, hz⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hzmem a
  · rw [finrank_span_eq_card hzli]
    simp [hd]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `embSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hx`.

Establish `: (fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) = ∑ k, τ (c k) • (fun i => τ (z k i) : Fin n → ℂ)`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `(fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) ∈ _`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `Submodule.subset_span ⟨z c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩`.
-/
theorem embSpan_span {K : Type} [Field K] {n d : ℕ} (τ : K →+* ℂ) (z : Fin d → Fin n → K) :
    embSpan τ (Submodule.span K (Set.range z)) =
      Submodule.span ℂ (Set.range fun c => (fun i => τ (z c i) : Fin n → ℂ)) := by
  apply le_antisymm
  · unfold embSpan
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    have : (fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) =
        ∑ k, τ (c k) • (fun i => τ (z k i) : Fin n → ℂ) := by
      funext i
      simp [Finset.sum_apply]
    change (fun i => τ ((∑ k, c k • z k) i) : Fin n → ℂ) ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨z c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

end ConjugateWeightGram

open ConjugateWeightGram in
/- English proof (translation)
Introduce `K _ _ _ n Z hZ`. Take `⟨d, z, f, hli, hspan, hz⟩` from `exists_reduced Z`. Use `⟨d, z, hli, hspan, fun a i => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_cmMax_iff_twist]`. Introduce `σ`.

Use `set τ := twist σ with hτ`. Establish `hmem : (fun i => σ (z a i) : Fin n → ℂ) ∈ embSpan τ Z`. Rewrite using `[hτ, ← hZ σ]`. Conclude with `Submodule.subset_span ⟨z a, by rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩, rfl⟩`. Rewrite `hmem` using `[← hspan, embSpan_span]`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem`. Establish `hcoef : ∀ k, c k = if a = k then 1 else 0`. Introduce `k`. Use `congrFun hc (f k)` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz, apply_ite τ, apply_ite σ, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`.

Conclude with `this`. Use `congrFun hc i` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoef, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this`. Conclude with `this`.
-/
theorem descent_cm_field : DescentCM := by
  intro K _ _ _ n Z hZ
  classical
  obtain ⟨d, z, f, hli, hspan, hz⟩ := exists_reduced Z
  refine ⟨d, z, hli, hspan, fun a i => ?_⟩
  rw [mem_cmMax_iff_twist]
  intro σ
  set τ := twist σ with hτ

  have hmem : (fun i => σ (z a i) : Fin n → ℂ) ∈ embSpan τ Z := by
    rw [hτ, ← hZ σ]
    exact Submodule.subset_span ⟨z a, by rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩, rfl⟩
  rw [← hspan, embSpan_span] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hcoef : ∀ k, c k = if a = k then 1 else 0 := by
    intro k
    have := congrFun hc (f k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz, apply_ite τ, apply_ite σ, map_one,
      map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoef, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  exact this

namespace ConjugateWeightGram

open StepBAux

section Restrict

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def colMat {n d : ℕ} (z : Fin d → Fin n → K) : Matrix (Fin n) (Fin d) K := Matrix.of fun i a => z a i

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[comb, colMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem comb_eq {n d : ℕ} (z : Fin d → Fin n → K) (x : Fin d → K) :
    comb z x = (colMat z).mulVec x := by
  funext i
  simp [comb, colMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gramMat, colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramMat_eq {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K) :
    gramMat H z = (colMat z)ᴴ * H * colMat z := by
  ext a b
  simp only [gramMat, colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.mulVecLin (colMat z))`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Rewrite `hx` using `[Matrix.mulVecLin_apply, ← comb_eq]`. Use function extensionality and compare the values at `a`.

Conclude with `(Fintype.linearIndependent_iff.mp hz) x hx a`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.mpr hinj)`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `: LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin (colMat z)) = 1`. Rewrite using `[hg, LinearMap.toMatrix'_id]`.

Rewrite `this` using `[LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Conclude with `this`.
-/
theorem exists_left_inv {n d : ℕ} (z : Fin d → Fin n → K) (hz : LinearIndependent K z) :
    ∃ L : Matrix (Fin d) (Fin n) K, L * colMat z = 1 := by
  have hinj : Function.Injective (Matrix.mulVecLin (colMat z)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.mulVecLin_apply, ← comb_eq] at hx
    funext a
    exact (Fintype.linearIndependent_iff.mp hz) x hx a
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin (colMat z)) = 1 := by
    rw [hg, LinearMap.toMatrix'_id]
  rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  exact this

/- English proof (translation)
Establish `hT : ((colMat z)ᴴ).map σ = ((colMat z).map σ)ᴴ`. Use extensionality with `a i`. Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply, colMat, Matrix.of_apply]`. Rewrite using `[hz a i]`. Both sides reduce to the same expression.

Rewrite using `[gramMat_eq, Matrix.map_mul, Matrix.map_mul, hT]`.
-/
theorem map_gramMat {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K) (σ : K →+* ℂ)
    (hz : ∀ a i, σ (star (z a i)) = starRingEnd ℂ (σ (z a i))) :
    (gramMat H z).map σ = ((colMat z).map σ)ᴴ * (H.map σ) * (colMat z).map σ := by
  have hT : ((colMat z)ᴴ).map σ = ((colMat z).map σ)ᴴ := by
    ext a i
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply, colMat, Matrix.of_apply]
    rw [hz a i]
    rfl
  rw [gramMat_eq, Matrix.map_mul, Matrix.map_mul, hT]

open scoped MatrixOrder in
/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg`. Establish `hB' : A = Bᴴ * B` using `by rw [hB, Matrix.star_eq_conjTranspose]`. Establish `hdet : IsUnit B.det`. Establish `h1 : A.det ≠ 0` using `hA.det_pos.ne'`. Rewrite `h1` using `[hB', Matrix.det_mul]`.

Conclude with `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)`. Use `⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ hdet, hB']`.
-/
theorem exists_frame {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, IsUnit Y.det ∧ (Y⁻¹)ᴴ * Y⁻¹ = A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hB' : A = Bᴴ * B := by rw [hB, Matrix.star_eq_conjTranspose]
  have hdet : IsUnit B.det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [hB', Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hdet, hB']

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_left_inv z hzli`. Establish `hinj : ∀ v : InfinitePlace K, Function.Injective ((colMat z).map v.embedding).mulVec`. Introduce `v x y hxy`. Establish `h1 : (L.map v.embedding) * (colMat z).map v.embedding = 1`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`.

Use `congrArg (L.map v.embedding).mulVec hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, h1]`. Establish `hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef`. Introduce `v`. Rewrite using `[← (hH.2 v).2]`.

Apply `Matrix.PosDef.conjTranspose_mul_self` to reduce the goal to its premises. Conclude with `Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ (hH.2 v).1))`. Use `choose XT hXT1 hXT2 using fun v => exists_frame _ ((hHpos v).conjTranspose_mul_mul_same (hinj v))`. Conclude with `⟨XT, fun v => ⟨hXT1 v, hXT2 v⟩⟩`.
-/
theorem exists_restrict {K0 : Subfield K} {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hH : IsRatHerm K0 H X)
    (z : Fin d → Fin n → K) (hzli : LinearIndependent K z) :
    ∃ XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, ∀ v, IsUnit (XT v).det ∧
      ((XT v)⁻¹)ᴴ * (XT v)⁻¹ =
        ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv z hzli
  have hinj : ∀ v : InfinitePlace K, Function.Injective ((colMat z).map v.embedding).mulVec := by
    intro v x y hxy
    have h1 : (L.map v.embedding) * (colMat z).map v.embedding = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    have := congrArg (L.map v.embedding).mulVec hxy
    simpa [Matrix.mulVec_mulVec, h1] using this
  have hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := by
    intro v
    rw [← (hH.2 v).2]
    apply Matrix.PosDef.conjTranspose_mul_self
    exact Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ (hH.2 v).1))
  choose XT hXT1 hXT2 using fun v =>
    exists_frame _ ((hHpos v).conjTranspose_mul_mul_same (hinj v))
  exact ⟨XT, fun v => ⟨hXT1 v, hXT2 v⟩⟩

/- English proof (translation)
Rewrite using `[StepBAux.majAt_eq, StepBAux.majAt_eq]`. Establish `hm1 : met XT v = ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding` using `hXT`. Establish `hm2 : met X v = H.map v.embedding` using `(hH.2 v).2`. Establish `hc : ∀ u : Fin d → K, cvec v.embedding (comb z u) = ((colMat z).map v.embedding).mulVec (cvec v.embedding u)`. Introduce `u`.

Use function extensionality and compare the values at `i`. Simplify using `[cvec, comb_eq, Matrix.mulVec, dotProduct]`. Rewrite using `[hm1, hm2, hc, hc, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem majAt_restrict {K0 : Subfield K} {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hH : IsRatHerm K0 H X)
    (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (hXT : ((XT v)⁻¹)ᴴ * (XT v)⁻¹ =
      ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y) := by
  rw [StepBAux.majAt_eq, StepBAux.majAt_eq]
  have hm1 : met XT v =
      ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding := hXT
  have hm2 : met X v = H.map v.embedding := (hH.2 v).2
  have hc : ∀ u : Fin d → K, cvec v.embedding (comb z u) =
      ((colMat z).map v.embedding).mulVec (cvec v.embedding u) := by
    intro u
    funext i
    simp [cvec, comb_eq, Matrix.mulVec, dotProduct]
  rw [hm1, hm2, hc, hc, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot, comb_eq, comb_eq, gramMat_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem hform_restrict {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K)
    (x y : Fin d → K) : hform (gramMat H z) x y = hform H (comb z x) (comb z y) := by
  rw [RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot, comb_eq, comb_eq, gramMat_eq,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Restrict

end ConjugateWeightGram

open ConjugateWeightGram in
/- English proof (translation)
Introduce `K _ _ _ K0 hcm hstar n H X hH d z hzli hz`. Take `⟨XT, hXT⟩` from `exists_restrict hH z hzli`. Use `⟨XT, ⟨?_, fun v => ⟨(hXT v).1, ?_⟩⟩, fun v x y => majAt_restrict hH z XT v (hXT v).2 x y, hform_restrict H z⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `only [gramMat, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]`.

Conclude with `Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hz a i)) (Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (hH.1 i j) (hz b j))`. Rewrite using `[(hXT v).2, map_gramMat H z v.embedding fun a i => hcm _ _ (hz a i)]`.
-/
theorem restriction_rational_hermitian : RestrictRatHerm := by
  intro K _ _ _ K0 hcm hstar n H X hH d z hzli hz
  obtain ⟨XT, hXT⟩ := exists_restrict hH z hzli
  refine ⟨XT, ⟨?_, fun v => ⟨(hXT v).1, ?_⟩⟩, fun v x y => majAt_restrict hH z XT v (hXT v).2 x y,
    hform_restrict H z⟩
  · intro a b
    simp only [gramMat, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hz a i))
      (Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (hH.1 i j) (hz b j))
  · rw [(hXT v).2, map_gramMat H z v.embedding fun a i => hcm _ _ (hz a i)]

end Formalism.DivisionValues
