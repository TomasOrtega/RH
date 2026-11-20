import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace RationalHermitianForm

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold `hform`. Simplify using `[Matrix.toLinearMapₛₗ₂'_apply]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Rewrite using `[starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  unfold hform
  simp [Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [starRingEnd_apply]
  ring

/- English proof (translation)
Rewrite using `[hform_apply]`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H *ᵥ y := by
  rw [hform_apply]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `hst : ∀ x : Fin n, star ((Pi.single i (1 : K) : Fin n → K) x) = (Pi.single i (1 : K) : Fin n → K) x`. Introduce `x`. Break down `eq_or_ne x i with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.

Rewrite using `[hform_apply]`. Simplify using `only [hst]`. Simplify using `[Pi.single_apply, Matrix.mulVec, dotProduct]`.
-/
theorem hform_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (i : Fin n) (y : Fin n → K) :
    hform H (Pi.single i 1) y = (H *ᵥ y) i := by
  have hst : ∀ x : Fin n, star ((Pi.single i (1 : K) : Fin n → K) x) = (Pi.single i (1 : K) : Fin n → K) x := by
    intro x; rcases eq_or_ne x i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hform_apply]
  simp only [hst]
  simp [Pi.single_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Establish `h1` using `(hR.2 v).2`. Establish `h2 : (H.map v.embedding)ᴴ = H.map v.embedding`. Rewrite using `[← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Establish `h3` using `congrFun (congrFun h2 i) j`.

Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3`. Apply `v.embedding.injective` to reduce the goal to its premises. Rewrite using `[hcm v.embedding (H i j) (hR.1 i j), ← h3]`. Simplify using the standard rewrite rules.
-/
theorem herm_entry {K0 : Subfield K} (hcm : IsCMSub K0) {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) (i j : Fin n) :
    H j i = star (H i j) := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h1 := (hR.2 v).2
  have h2 : (H.map v.embedding)ᴴ = H.map v.embedding := by
    rw [← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3
  apply v.embedding.injective
  rw [hcm v.embedding (H i j) (hR.1 i j), ← h3]
  simp

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← (hR.2 v).2, Matrix.det_mul, Matrix.det_conjTranspose]`.
-/
theorem emb_det {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) (v : InfinitePlace K) :
    v.embedding H.det = star ((X v)⁻¹.det) * (X v)⁻¹.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← (hR.2 v).2, Matrix.det_mul,
    Matrix.det_conjTranspose]

/- English proof (translation)
The claim follows from `(Matrix.isUnit_nonsing_inv_det _ (hR.2 v).1).ne_zero`.
-/
theorem inv_det_ne_zero {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) (v : InfinitePlace K) :
    (X v)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hR.2 v).1).ne_zero

/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Introduce `h`. Establish `h1` using `emb_det hR v`. Rewrite `h1` using `[h, map_zero]`. Conclude with `mul_ne_zero (star_ne_zero.mpr (inv_det_ne_zero hR v)) (inv_det_ne_zero hR v) h1.symm`.
-/
theorem det_ne_zero {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) : H.det ≠ 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  intro h
  have h1 := emb_det hR v
  rw [h, map_zero] at h1
  exact mul_ne_zero (star_ne_zero.mpr (inv_det_ne_zero hR v)) (inv_det_ne_zero hR v) h1.symm

/- English proof (translation)
Establish `key : ∀ x y, starRingEnd K (hform H x y) = hform H y x`. Introduce `x y`. Simplify using `only [hform_apply, starRingEnd_apply, star_sum, star_mul', star_star]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations.

Use `first`. Consider the case `(rw [← hherm b a]; ring)`. Consider the case `(rw [← hherm a b]; ring)`. Consider the case `(rw [hherm b a]; ring)`. Consider the case `(rw [hherm a b]; ring)`.

Use `first`. Consider the case `exact key`. Consider the case `exact ⟨key⟩`. Consider the case `(constructor; exact key)`.
-/
theorem hform_isSymm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hherm : ∀ i j, H j i = star (H i j)) :
    (hform H).IsSymm := by
  have key : ∀ x y, starRingEnd K (hform H x y) = hform H y x := by
    intro x y
    simp only [hform_apply, starRingEnd_apply, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    first
      | (rw [← hherm b a]; ring)
      | (rw [← hherm a b]; ring)
      | (rw [hherm b a]; ring)
      | (rw [hherm a b]; ring)
  first
    | exact key
    | exact ⟨key⟩
    | (constructor; exact key)

/- English proof (translation)
Introduce `y hy`. Establish `h1 : H *ᵥ y = 0` using `funext fun i => by rw [← hform_single]; exact hy _`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hdet h1`.
-/
theorem hform_sepRight {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hdet : H.det ≠ 0) :
    (hform H).SeparatingRight := by
  intro y hy
  have h1 : H *ᵥ y = 0 := funext fun i => by rw [← hform_single]; exact hy _
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

/- English proof (translation)
Establish `hsym : ∀ x y, starRingEnd K (hform H x y) = hform H y x`. Introduce `x y`. Use `first`. Consider the case `exact hs x y`. Consider the case `exact hs.eq x y`.

Use `⟨fun x hx => hform_sepRight H hdet x (fun y => ?_), hform_sepRight H hdet⟩` and prove the remaining obligations. Rewrite using `[← hsym x y, hx y, map_zero]`.
-/
theorem hform_nondeg {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hs : (hform H).IsSymm)
    (hdet : H.det ≠ 0) : (hform H).Nondegenerate := by
  have hsym : ∀ x y, starRingEnd K (hform H x y) = hform H y x := by
    intro x y
    first
      | exact hs x y
      | exact hs.eq x y
  refine ⟨fun x hx => hform_sepRight H hdet x (fun y => ?_), hform_sepRight H hdet⟩
  rw [← hsym x y, hx y, map_zero]

/- English proof (translation)
Unfold `gramR`. Use `congr 1`. Use extensionality with `a b`. Establish `hst : ∀ x : Fin D, star ((Pi.single a (1 : K) : Fin D → K) x) = (Pi.single a (1 : K) : Fin D → K) x`. Introduce `x`.

Break down `eq_or_ne x a with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Simplify using `only [Matrix.of_apply, dotProduct, Pi.star_apply, hst]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem gramR_std {D : ℕ} (Γ : Matrix (Fin D) (Fin D) K) :
    gramR Γ (fun i => (Pi.single i 1 : Fin D → K)) = Γ.det := by
  unfold gramR
  congr 1
  ext a b
  have hst : ∀ x : Fin D, star ((Pi.single a (1 : K) : Fin D → K) x) = (Pi.single a (1 : K) : Fin D → K) x := by
    intro x; rcases eq_or_ne x a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  simp only [Matrix.of_apply, dotProduct, Pi.star_apply, hst]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem expand_std {d : ℕ} (f : Fin d → Fin d → K) :
    (fun i => ∑ k, (Matrix.of f)ᵀ k i • (Pi.single k (1 : K) : Fin d → K)) = f := by
  funext i
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Rewrite using `[Matrix.det_transpose]`. Establish `h1 : IsUnit (Matrix.of f)` using `Matrix.linearIndependent_rows_iff_isUnit.mp hf`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp h1).ne_zero`.
-/
theorem det_of_ne_zero {d : ℕ} {f : Fin d → Fin d → K} (hf : LinearIndependent K f) :
    (Matrix.of f)ᵀ.det ≠ 0 := by
  rw [Matrix.det_transpose]
  have h1 : IsUnit (Matrix.of f) := Matrix.linearIndependent_rows_iff_isUnit.mp hf
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h1).ne_zero

/- English proof (translation)
Unfold `gramR`. Establish `h1 : (Matrix.of fun a b => star (f a) ⬝ᵥ H.mulVec (f b)) = ((Matrix.of f)ᵀ)ᴴ * H * (Matrix.of f)ᵀ`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Use `first`.

Consider the case `rfl`. Consider the case `exact Finset.sum_comm`. Rewrite using `[h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramR_eq_std {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (f : Fin d → Fin d → K) :
    gramR H f = star (Matrix.of f)ᵀ.det * (Matrix.of f)ᵀ.det * H.det := by
  unfold gramR
  have h1 : (Matrix.of fun a b => star (f a) ⬝ᵥ H.mulVec (f b)) =
      ((Matrix.of f)ᵀ)ᴴ * H * (Matrix.of f)ᵀ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    first
      | rfl
      | exact Finset.sum_comm
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring

end RationalHermitianForm

open RationalHermitianForm

/- English proof (translation)
Introduce `K _ _ _ _ K0 hcm d H X hR T hT w f hf`. Apply the tactic sequence `have hherm := herm_entry hcm hR`. Establish `hdetH` using `det_ne_zero hR`. Establish `hs` using `hform_isSymm H hherm`. Establish `hnd` using `hform_nondeg H hs hdetH`.

Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)` using `fun r => ⟨cO K r, rfl⟩`. Use `set h := hform H with hh`. Use `set M : Matrix (Fin d) (Fin d) K := Matrix.of fun a b => h (f a) (f b) with hMdef`. Establish `hM : M.det = gramR H f`. Unfold `gramR`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `[M, h, hform_eq_dot]`. Establish `hG : gramR H f ≠ 0`. Rewrite using `[gramR_eq_std]`.

Use `det_of_ne_zero hf.1` as an intermediate fact. Conclude with `mul_ne_zero (mul_ne_zero (star_ne_zero.mpr this) this) hdetH`. Establish `hMu : IsUnit M.det` using `isUnit_iff_ne_zero.mpr (hM ▸ hG)`. Use `set fs : Fin d → Fin d → K := fun b => ∑ k, M⁻¹ k b • f k with hfs`. Establish `hpair : ∀ a b, h (f a) (fs b) = if a = b then 1 else 0`.

Introduce `a b`. Establish `hmul : M * M⁻¹ = 1` using `Matrix.mul_nonsing_inv M hMu`. Use `congrFun (congrFun hmul a) b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← this, hfs, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hfsli : LinearIndependent K fs`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `congrArg (h (f i)) hg` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this`. Conclude with `this`.

Establish `hspK : Submodule.span K (Set.range f) = ⊤` using `hf.1.span_eq_top_of_card_eq_finrank' (by simp)`. Establish `hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f))` using `⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩`. Establish `hone : ∀ c : K, c ∈ (1 : Submodule (𝓞 K) K) → ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) * c ∈ (1 : Submodule (𝓞 K) K)`. Introduce `c hc r`. Conclude with `Formalism.HermitianLatticesTheory.locDual_one_mul (Submodule.mem_one.mpr ⟨cO K r, rfl⟩) hc`.

Establish `hdual_span : Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f)) = Submodule.span (𝓞 K) (Set.range fs)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Establish `hc : ∀ a, h (f a) x ∈ (1 : Submodule (𝓞 K) K)` using `fun a => hx _ (Submodule.subset_span ⟨a, rfl⟩)`.

Use `set b : Basis (Fin d) K (Fin d → K) := Basis.mk hf.1 (by rw [hspK]) with hb`. Establish `hbf : ∀ i, b i = f i` using `fun i => by simp [b]`. Establish `hexp` using `Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b fs (by simpa [hbf] using hpair) x`. Rewrite using `[hexp]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hc j)`. Rewrite using `[hbf, ← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`.

Express the relevant statement in the definitionally equal form `fs b ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))`. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, rfl⟩` from `hx`. Rewrite using `[hpair]`. Use `split_ifs`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`.

Consider the case `zero => rw [map_zero, LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`.

Rewrite using `[Formalism.HermitianLatticesTheory.locDual_h_smul_left]`. Conclude with `hone _ hx r`. Establish `hdualT : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h T)` using `(Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) h hs hnd hstar T hT).1`. Establish `hLD` using `Formalism.HermitianLatticesTheory.locDual (𝓞 K) K (Fin d → K) h hs hstar`. Establish `A` using `(hLD _ hspan_f.fg).1 w.asIdeal w.isPrime`.

Establish `B` using `(hLD _ hT.fg).1 w.asIdeal w.isPrime`. Establish `hlocfs : IsLocBasis (Formalism.HermitianLatticesTheory.dual h T) w fs`. Use `⟨hfsli, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdual_span]`.

Use `_ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f))) := by`. Rewrite using `[A.1, A.2]`. Use `_ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal T) := by rw [hf.2]`. Use `_ = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h T) := by rw [B.1, B.2]`. Establish `hone_f : (fun i => ∑ k, (1 : Matrix (Fin d) (Fin d) K) k i • f k) = f`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.one_apply]`. Establish `i1` using `(hIC K d T hT f hf.1 w 1 (by rw [hone_f]; exact hf)).1`. Establish `i2` using `(hIC K d (Formalism.HermitianLatticesTheory.dual h T) hdualT f hf.1 w M⁻¹ hlocfs).1`. Establish `: w.asIdeal.IsMaximal` using `w.isMaximal`.

Establish `hIB` using `Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin d → K) h hs hnd hstar w.asIdeal T (Submodule.span (𝓞 K) (Set.range f)) (Formalism.HermitianLatticesTheory.dual h T) hT hspan_f hdualT`. Unfold `jw Formalism.HermitianLatticesTheory.jIdx`. Unfold `idx at i1 i2`. Rewrite using `[hIB.2.2.1, hIB.2.1, i1, i2, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ValuationRepresentative.vw_inv, hM, Matrix.det_one, ValuationRepresentative.vw_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jwGram_of (hIC : IdxChange) : JwGram := by
  intro K _ _ _ _ K0 hcm d H X hR T hT w f hf
  classical
  have hherm := herm_entry hcm hR
  have hdetH := det_ne_zero hR
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
Introduce `K _ _ _ _ K0 hcm d H X hR T hT`. Establish `hJ` using `jwGram_of hIC`. Use `set e : Fin d → Fin d → K := fun i => Pi.single i 1 with he_def`. Establish `he : LinearIndependent K e`. Establish `: e = ⇑(Pi.basisFun K (Fin d))` using `funext fun i => (Pi.basisFun_apply K (Fin d) i).symm`.

Rewrite using `[this]`. Conclude with `(Pi.basisFun K (Fin d)).linearIndependent`. Establish `hdetH` using `det_ne_zero hR`. Take `⟨hfinA, hlcv⟩` from `hLB K d X (fun v => (hR.2 v).1) T hT e he`. Establish `hgram : ∀ v, gram X v e = H.map v.embedding`.

Introduce `v`. Establish `hv : ∀ a : Fin d, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v (Pi.single a (1 : K)) = (Pi.single a 1 : Fin d → ℂ)`. Introduce `a`. Use function extensionality and compare the values at `i`. Unfold `Formalism.HermitianLatticesTheory.vecAt`.

Rewrite using `[Pi.basisFun_repr]`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hia]`.

Rewrite using `[← (hR.2 v).2]`. Use `Matrix.ext fun a c => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v (Pi.single a 1) (Pi.single c 1) = _`. Unfold `Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord`. Rewrite using `[hv, hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mul_apply]`.

Simplify using `[Matrix.conjTranspose_apply]`. Establish `hlog : ∀ v, Real.log (gram X v e).det.re = Real.log ‖v.embedding H.det‖`. Introduce `v`. Establish `h1 : v.embedding H.det = ((Complex.normSq ((X v)⁻¹.det) : ℝ) : ℂ)`. Rewrite using `[emb_det hR v, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]`.

Establish `h2 : (gram X v e).det = v.embedding H.det`. Rewrite using `[hgram, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Rewrite using `[h2, h1, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]`. Take `⟨hfinC, hpf⟩` from `prod_formula' K H.det hdetH`. Use `choose f hf using fun w => hEx K d T hT w`.

Use `set S := Submodule.span (𝓞 K) (Set.range e) with hS`. Establish `hpt : ∀ w, (jw H w T : ℝ) = -((idx w S T : ℝ) + (idx (conjPl w) S T : ℝ) + (vw w H.det : ℝ))`. Introduce `w`. Establish `hexp` using `expand_std (f w)`. Establish `hloc : IsLocBasis T w (fun i => ∑ k, (Matrix.of (f w))ᵀ k i • e k)`.

Rewrite using `[he_def, hexp]`. Conclude with `hf w`. Take `⟨i1, i2⟩` from `hIC K d T hT e he w _ hloc`. Establish `hj` using `hJ K K0 hcm d H X hR T hT w (f w) (hf w)`. Establish `hδ` using `det_of_ne_zero (hf w).1`.

Rewrite `hj` using `[gramR_eq_std, ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (star_ne_zero.mpr hδ) hδ) hdetH, ValuationRepresentative.vw_mul w _ _ (star_ne_zero.mpr hδ) hδ, ((valuation_basic_properties K w).2.1)]`. Rewrite using `[hj, i1, i2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlw : ∀ w, lw (conjPl w) = lw w` using `fun w => (valuation_basic_properties K w).2.2.1`.

Use `set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (idx w S T : ℝ) with ha`. Use `set c : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (vw w H.det : ℝ) with hc`. Establish `hinj : Function.Injective (conjPl (K` using `K)) := fun x y hxy => by`. Use `congrArg conjPl hxy` as an intermediate fact. Rewrite `this` using `[ValuationRepresentative.conjPl_conjPl, ValuationRepresentative.conjPl_conjPl]`. Then use the resulting hypothesis.

Establish `hfinA' : (Function.support fun w => a (conjPl w)).Finite`. Rewrite using `[show (fun w => a (conjPl w)) = a ∘ conjPl from rfl, Function.support_comp_eq_preimage]`. Conclude with `hfinA.preimage hinj.injOn`. Establish `pt2 : (fun w => lw w * (jw H w T : ℝ)) = fun w => -(a w + a (conjPl w) + c w)`. Use function extensionality and compare the values at `w`.

Simplify using `only [ha, hc, hpt w, hlw w]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum1 : ∑ᶠ w, (a w + a (conjPl w)) = ∑ᶠ w, a w + ∑ᶠ w, a (conjPl w)` using `finsum_add_distrib hfinA hfinA'`. Establish `hfin12 : (Function.support fun w => a w + a (conjPl w)).Finite` using `(hfinA.union hfinA').subset (Function.support_add _ _)`. Establish `hsum2 : ∑ᶠ w, (a w + a (conjPl w) + c w) = ∑ᶠ w, (a w + a (conjPl w)) + ∑ᶠ w, c w` using `finsum_add_distrib hfin12 hfinC`.

Establish `hconj : ∑ᶠ w, a (conjPl w) = ∑ᶠ w, a w` using `finite_sum_conjugation K a`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pt2]`. Express the relevant statement in the definitionally equal form `(Function.support (-(fun w => a w + a (conjPl w) + c w))).Finite`. Rewrite using `[Function.support_neg]`.

Conclude with `(hfin12.union hfinC).subset (Function.support_add _ _)`. Rewrite using `[pt2, finsum_neg_distrib, hsum2, hsum1, hconj, hlcv]`. Simplify using `only [hlog]`. Rewrite using `[hpf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratHermLcv_of (hLB : LcvBasis) (hIC : IdxChange) (hEx : LocBasisEx) : RatHermLcv := by
  intro K _ _ _ _ K0 hcm d H X hR T hT
  classical
  have hJ := jwGram_of hIC
  set e : Fin d → Fin d → K := fun i => Pi.single i 1 with he_def
  have he : LinearIndependent K e := by
    have : e = ⇑(Pi.basisFun K (Fin d)) := funext fun i => (Pi.basisFun_apply K (Fin d) i).symm
    rw [this]
    exact (Pi.basisFun K (Fin d)).linearIndependent
  have hdetH := det_ne_zero hR
  obtain ⟨hfinA, hlcv⟩ := hLB K d X (fun v => (hR.2 v).1) T hT e he
  have hgram : ∀ v, gram X v e = H.map v.embedding := by
    intro v
    have hv : ∀ a : Fin d, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v (Pi.single a (1 : K)) =
        (Pi.single a 1 : Fin d → ℂ) := by
      intro a
      funext i
      unfold Formalism.HermitianLatticesTheory.vecAt
      rw [Pi.basisFun_repr]
      by_cases hia : i = a
      · subst hia; simp
      · simp [hia]
    rw [← (hR.2 v).2]
    refine Matrix.ext fun a c => ?_
    change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v (Pi.single a 1) (Pi.single c 1) = _
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv, hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply]
  have hlog : ∀ v, Real.log (gram X v e).det.re = Real.log ‖v.embedding H.det‖ := by
    intro v
    have h1 : v.embedding H.det = ((Complex.normSq ((X v)⁻¹.det) : ℝ) : ℂ) := by
      rw [emb_det hR v, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    have h2 : (gram X v e).det = v.embedding H.det := by
      rw [hgram, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h2, h1, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  obtain ⟨hfinC, hpf⟩ := prod_formula' K H.det hdetH
  choose f hf using fun w => hEx K d T hT w
  set S := Submodule.span (𝓞 K) (Set.range e) with hS
  have hpt : ∀ w, (jw H w T : ℝ) =
      -((idx w S T : ℝ) + (idx (conjPl w) S T : ℝ) + (vw w H.det : ℝ)) := by
    intro w
    have hexp := expand_std (f w)
    have hloc : IsLocBasis T w (fun i => ∑ k, (Matrix.of (f w))ᵀ k i • e k) := by
      rw [he_def, hexp]; exact hf w
    obtain ⟨i1, i2⟩ := hIC K d T hT e he w _ hloc
    have hj := hJ K K0 hcm d H X hR T hT w (f w) (hf w)
    have hδ := det_of_ne_zero (hf w).1
    rw [gramR_eq_std, ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (star_ne_zero.mpr hδ) hδ) hdetH,
      ValuationRepresentative.vw_mul w _ _ (star_ne_zero.mpr hδ) hδ, ((valuation_basic_properties K w).2.1)] at hj
    rw [hj, i1, i2]
    push_cast
    ring
  have hlw : ∀ w, lw (conjPl w) = lw w := fun w => (valuation_basic_properties K w).2.2.1
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (idx w S T : ℝ) with ha
  set c : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw w * (vw w H.det : ℝ) with hc
  have hinj : Function.Injective (conjPl (K := K)) := fun x y hxy => by
    have := congrArg conjPl hxy
    rwa [ValuationRepresentative.conjPl_conjPl, ValuationRepresentative.conjPl_conjPl] at this
  have hfinA' : (Function.support fun w => a (conjPl w)).Finite := by
    rw [show (fun w => a (conjPl w)) = a ∘ conjPl from rfl, Function.support_comp_eq_preimage]
    exact hfinA.preimage hinj.injOn
  have pt2 : (fun w => lw w * (jw H w T : ℝ)) = fun w => -(a w + a (conjPl w) + c w) := by
    funext w
    simp only [ha, hc, hpt w, hlw w]
    ring
  have hsum1 : ∑ᶠ w, (a w + a (conjPl w)) = ∑ᶠ w, a w + ∑ᶠ w, a (conjPl w) :=
    finsum_add_distrib hfinA hfinA'
  have hfin12 : (Function.support fun w => a w + a (conjPl w)).Finite :=
    (hfinA.union hfinA').subset (Function.support_add _ _)
  have hsum2 : ∑ᶠ w, (a w + a (conjPl w) + c w) =
      ∑ᶠ w, (a w + a (conjPl w)) + ∑ᶠ w, c w :=
    finsum_add_distrib hfin12 hfinC
  have hconj : ∑ᶠ w, a (conjPl w) = ∑ᶠ w, a w := finite_sum_conjugation K a
  refine ⟨?_, ?_⟩
  · rw [pt2]
    change (Function.support (-(fun w => a w + a (conjPl w) + c w))).Finite
    rw [Function.support_neg]
    exact (hfin12.union hfinC).subset (Function.support_add _ _)
  · rw [pt2, finsum_neg_distrib, hsum2, hsum1, hconj, hlcv]
    simp only [hlog]
    rw [hpf]
    ring

end Formalism.DivisionValues
