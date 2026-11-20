import Mathlib
import Formalism.LocalToGlobal.Columns.SummandSlopeOfThreeLemmas
import Formalism.LocalToGlobal.Columns.BzdConjTTranspose
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.MonomialMeanResidues.ZerosPerVariable
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def stdHL (N : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := N

/- English proof (translation)
Simplify using `only [hStd, LinearMap.mk₂'ₛₗ_apply, Pi.basisFun_apply, Pi.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [Finset.sum_eq_zero]; intro k _; split_ifs <;> simp_all`.
-/
theorem brp_hStd_basis (i j : Fin n) :
    hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j) = if i = j then 1 else 0 := by
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, Pi.basisFun_apply, Pi.single_apply]
  split_ifs with h
  · subst h; simp
  · rw [Finset.sum_eq_zero]; intro k _; split_ifs <;> simp_all

/- English proof (translation)
Use `brp_hStd_basis K (n := n) i j` as an intermediate fact. Simplify `this` using `only [Pi.basisFun_apply]`.
-/
theorem brp_hStd_single (i j : Fin n) :
    hStd K n (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  have := brp_hStd_basis K (n := n) i j
  simpa only [Pi.basisFun_apply] using this

/- English proof (translation)
Use `Matrix.PosDef.one (n := Fin n) (R := ℂ) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, brp_hStd_basis, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem brp_hStd_pos (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (hStd K n (Pi.basisFun K (Fin n) i) (Pi.basisFun K (Fin n) j))).PosDef := by
  convert Matrix.PosDef.one (n := Fin n) (R := ℂ) using 1
  ext i j
  rw [Matrix.of_apply, brp_hStd_basis, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `formAt`. Simplify using `only [Pi.basisFun_repr, brp_hStd_basis]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
theorem brp_formAt_std (v : InfinitePlace K) (x y : Fin n → K) :
    formAt (Pi.basisFun K (Fin n)) (hStd K n) v x y = ∑ i, starRingEnd ℂ (v.embedding (x i)) * v.embedding (y i) := by
  unfold formAt
  simp only [Pi.basisFun_repr, brp_hStd_basis]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/- English proof (translation)
Rewrite using `[brp_formAt_std]`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt`. Use `congr 1`. Simplify using `only [inv_one, Matrix.one_mulVec, Complex.re_sum, Pi.basisFun_repr]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brp_normAt_std (v : InfinitePlace K) (x : Fin n → K) :
    normAt (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x =
      Real.sqrt (formAt (Pi.basisFun K (Fin n)) (hStd K n) v x x).re := by
  rw [brp_formAt_std]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 1
  simp only [inv_one, Matrix.one_mulVec, Complex.re_sum, Pi.basisFun_repr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Introduce `v`. Simplify using `[stdHL]`.
-/
theorem brp_stdHL_frameOK (N : Submodule (𝓞 K) (Fin n → K)) : FrameOK (stdHL K N) := by
  intro v
  simp [stdHL]

/- English proof (translation)
Establish `hs` using `formH_spec (Pi.basisFun K (Fin n)) (hStd K n) (brp_hStd_pos K) N`. Establish `h` using `frame_free K (Fin n → K) (Fin n) (Fin n) (Pi.basisFun K (Fin n)) (latK K N).X (Pi.basisFun K (Fin n)) (fun _ => 1) hs.1 (fun _ => by simp) (fun v x => by rw [hs.2.2, brp_normAt_std]) N hN`. Conclude with `h.2.1`.
-/
theorem brp_latK_mu (N : Submodule (𝓞 K) (Fin n → K)) (hN : N.FG) : (latK K N).mu = (stdHL K N).mu := by
  have hs := formH_spec (Pi.basisFun K (Fin n)) (hStd K n) (brp_hStd_pos K) N
  have h := frame_free K (Fin n → K) (Fin n) (Fin n) (Pi.basisFun K (Fin n)) (latK K N).X (Pi.basisFun K (Fin n))
    (fun _ => 1) hs.1 (fun _ => by simp) (fun v x => by rw [hs.2.2, brp_normAt_std]) N hN
  exact h.2.1

end Std

section Dual

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpDot : (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K) :=
  LinearMap.mk₂ K (fun (φ x : Fin n → K) => φ ⬝ᵥ x) add_dotProduct smul_dotProduct dotProduct_add dotProduct_smul

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem brpDot_apply (φ x : Fin n → K) : brpDot K φ x = φ ⬝ᵥ x := rfl

/- English proof (translation)
Introduce `φ ψ h`. Use function extensionality and compare the values at `i`. Establish `h2` using `LinearMap.congr_fun h (Pi.single i 1)`. Simplify `h2` using `[brpDot_apply, dotProduct_single]`.
-/
theorem brpDot_injective : Function.Injective (brpDot (n := n) K) := by
  intro φ ψ h
  funext i
  have h2 := LinearMap.congr_fun h (Pi.single i 1)
  simpa [brpDot_apply, dotProduct_single] using h2

/- English proof (translation)
Use `show Module.finrank K (Submodule.span K (N : Set (Fin n → K))) = n`. Rewrite using `[hN.span_eq_top, finrank_top, Module.finrank_fin_fun]`.
-/
theorem brp_rank_std [IsTotallyComplex K] (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) :
    (stdHL K N).rank = n := by
  show Module.finrank K (Submodule.span K (N : Set (Fin n → K))) = n
  rw [hN.span_eq_top, finrank_top, Module.finrank_fin_fun]

/- English proof (translation)
Unfold `Formalism.BasicNotions.HLat.Good`. Conclude with `⟨brp_stdHL_frameOK K N, hN.fg, hN.span_eq_top⟩`.
-/
theorem brp_stdHL_good (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) : (stdHL K N).Good := by
  unfold Formalism.BasicNotions.HLat.Good
  exact ⟨brp_stdHL_frameOK K N, hN.fg, hN.span_eq_top⟩

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, hφ, rfl⟩`. Introduce `x hx`.

Take `⟨a, ha⟩` from `Submodule.mem_one.mp (hφ x hx)`. Conclude with `⟨a, ha⟩`. Introduce `hf`. Establish `key : brpDot K (fun i => f (Pi.single i 1)) = f`. Apply `(Pi.basisFun K (Fin n)).ext` to reduce the goal to its premises.

Introduce `j`. Rewrite using `[brpDot_apply, Pi.basisFun_apply, dotProduct_single, mul_one]`. Use `⟨fun i => f (Pi.single i 1), ?_, key⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Submodule.mem_one]`.

Take `⟨a, ha⟩` from `hf x hx`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hk` using `LinearMap.congr_fun key x`. Rewrite `hk` using `[brpDot_apply]`. Rewrite using `[ha, hk]`.
-/
theorem brp_dualFr_map (N : Submodule (𝓞 K) (Fin n → K)) :
    (dualFr N).map ((brpDot K).restrictScalars (𝓞 K)) = Formalism.HN.dualLat N := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    intro x hx
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hφ x hx)
    exact ⟨a, ha⟩
  · intro hf
    have key : brpDot K (fun i => f (Pi.single i 1)) = f := by
      apply (Pi.basisFun K (Fin n)).ext
      intro j
      rw [brpDot_apply, Pi.basisFun_apply, dotProduct_single, mul_one]
    refine ⟨fun i => f (Pi.single i 1), ?_, key⟩
    intro x hx
    rw [Submodule.mem_one]
    obtain ⟨a, ha⟩ := hf x hx
    refine ⟨a, ?_⟩
    have hk := LinearMap.congr_fun key x
    rw [brpDot_apply] at hk
    rw [ha, hk]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.BasicNotions.HLat.dualB Formalism.BasicNotions.HLat.dualX Formalism.HN.dualFrame`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[stdHL, Basis.dualBasis_repr, brpDot_apply, dotProduct_single]`.
-/
theorem brp_dual_norm (N : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) (x : Fin n → K) :
    normAt (stdHL K N).dualB (stdHL K N).dualX v (brpDot K x) = normAt (stdHL K N).b (stdHL K N).X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.BasicNotions.HLat.dualB Formalism.BasicNotions.HLat.dualX Formalism.HN.dualFrame
  congr 1
  funext i
  simp [stdHL, Basis.dualBasis_repr, brpDot_apply, dotProduct_single]

/- English proof (translation)
Establish `hL' : (dualFr N).FG` using `(dualFrLattice K n (1 : Matrix (Fin n) (Fin n) K) N (by simp) hN).1.fg`. Conclude with `hlat_mu_of_dual (stdHL K N) (brp_stdHL_good K N hN) (by rw [brp_rank_std K N hN]; exact hn) (dualFr N) hL' (brpDot K) (brpDot_injective K) (brp_dualFr_map K N) (brp_dual_norm K N)`.
-/
theorem brp_dual_mu [IsTotallyComplex K] (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) (hn : 0 < n) :
    (stdHL K (dualFr N)).mu = -(stdHL K N).mu := by
  have hL' : (dualFr N).FG := (dualFrLattice K n (1 : Matrix (Fin n) (Fin n) K) N (by simp) hN).1.fg
  exact hlat_mu_of_dual (stdHL K N) (brp_stdHL_good K N hN) (by rw [brp_rank_std K N hN]; exact hn) (dualFr N) hL'
    (brpDot K) (brpDot_injective K) (brp_dualFr_map K N) (brp_dual_norm K N)

end Dual

section Star

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpCO : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem brpCO_coe (a : 𝓞 K) : ((brpCO K a : 𝓞 K) : K) = star (a : K) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show star (c • x i) = brpCO K c • star (x i)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, star_mul']`. Use `congr 1`.
-/
theorem brp_star_smul (c : 𝓞 K) (x : Fin n → K) : star (c • x) = brpCO K c • star x := by
  funext i
  show star (c • x i) = brpCO K c • star (x i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  congr 1

def starLat (N : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) where
  carrier := {x | star x ∈ N}
  add_mem' := by
    intro x y hx hy
    show star (x + y) ∈ N
    rw [star_add]
    exact N.add_mem hx hy
  zero_mem' := by
    show star (0 : Fin n → K) ∈ N
    rw [star_zero]
    exact N.zero_mem
  smul_mem' := by
    intro c x hx
    show star (c • x) ∈ N
    rw [brp_star_smul]
    exact N.smul_mem _ hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_starLat (N : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) : x ∈ starLat K N ↔ star x ∈ N := Iff.rfl

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [star_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x z _ _ hx hz => rw [star_add]`.

Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul c x _ hx => rw [brp_star_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem brp_star_mem_span (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span (𝓞 K) S) :
    star y ∈ Submodule.span (𝓞 K) (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_starLat]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `brp_star_mem_span K S (star x) h` as an intermediate fact.

Rewrite `this` using `[star_star]`. Then use the resulting hypothesis. Introduce `h`. Establish `hS : star '' (star '' S) = S`. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules.

Use `brp_star_mem_span K (star '' S) x h` as an intermediate fact. Rewrite `this` using `[hS]`. Then use the resulting hypothesis.
-/
theorem brp_starLat_span (S : Set (Fin n → K)) :
    starLat K (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K) (star '' S) := by
  ext x
  rw [mem_starLat]
  constructor
  · intro h
    have := brp_star_mem_span K S (star x) h
    rwa [star_star] at this
  · intro h
    have hS : star '' (star '' S) = S := by
      rw [Set.image_image]; simp
    have := brp_star_mem_span K (star '' S) x h
    rwa [hS] at this

end Star

section StarMu

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show star (a * x i) = star a * star (x i)`. Rewrite using `[star_mul', mul_comm]`.
-/
theorem brp_star_smulK (a : K) (x : Fin n → K) : star (a • x) = star a • star x := by
  funext i
  show star (a * x i) = star a * star (x i)
  rw [star_mul', mul_comm]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [star_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x z _ _ hx hz => rw [star_add]`.

Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul c x _ hx => rw [brp_star_smulK]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem brp_star_mem_spanK (S : Set (Fin n → K)) (y : Fin n → K) (hy : y ∈ Submodule.span K S) :
    star y ∈ Submodule.span K (star '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [brp_star_smulK]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Use `brp_star_mem_spanK K S (star x) (h ▸ Submodule.mem_top)` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.
-/
theorem brp_star_span_top (S : Set (Fin n → K)) (h : Submodule.span K S = ⊤) : Submodule.span K (star '' S) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have := brp_star_mem_spanK K S (star x) (h ▸ Submodule.mem_top)
  rwa [star_star] at this

/- English proof (translation)
Take `⟨S, hS⟩` from `hN.fg`. Use `⟨⟨S.image star, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, ← brp_starLat_span, hS]`. Establish `hset : ((starLat K N : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = star '' (N : Set (Fin n → K))`. Use extensionality with `x`.

Simplify using `only [SetLike.mem_coe, mem_starLat, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨star x, h, star_star x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite using `[star_star]` and apply the resulting hypothesis. Rewrite using `[hset]`. Conclude with `brp_star_span_top K _ hN.span_eq_top`.
-/
theorem brp_starLat_lattice (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (starLat K N) := by
  classical
  obtain ⟨S, hS⟩ := hN.fg
  refine ⟨⟨S.image star, ?_⟩, ?_⟩
  · rw [Finset.coe_image, ← brp_starLat_span, hS]
  · have hset : ((starLat K N : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = star '' (N : Set (Fin n → K)) := by
      ext x
      simp only [SetLike.mem_coe, mem_starLat, Set.mem_image]
      constructor
      · intro h
        exact ⟨star x, h, star_star x⟩
      · rintro ⟨y, hy, rfl⟩
        rwa [star_star]
    rw [hset]
    exact brp_star_span_top K _ hN.span_eq_top

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.mem_toAddSubgroup, mem_starLat, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨star x, h, star_star x⟩`.

Introduce and unpack `⟨y, hy, rfl⟩ show star (star y) ∈ N`. Rewrite using `[star_star]` and apply the resulting hypothesis.
-/
theorem brp_starLat_toAdd (N : Submodule (𝓞 K) (Fin n → K)) :
    (starLat K N).toAddSubgroup = N.toAddSubgroup.map (starAddEquiv : (Fin n → K) ≃+ (Fin n → K)).toAddMonoidHom := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_starLat, AddSubgroup.mem_map]
  constructor
  · intro h
    exact ⟨star x, h, star_star x⟩
  · rintro ⟨y, hy, rfl⟩
    show star (star y) ∈ N
    rwa [star_star]

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Formalism.HN.gramPl, Matrix.of_apply, Matrix.map_apply, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr, Pi.star_apply, hc, map_sum, map_mul]`. Simplify using `[Complex.star_def]`.
-/
theorem brp_gram_star (hc : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (v : InfinitePlace K) {j : ℕ}
    (e : Fin j → Fin n → K) :
    gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v (fun a => star (e a)) =
      (gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v e).map (starRingEnd ℂ) := by
  ext a c
  simp only [Formalism.HN.gramPl, Matrix.of_apply, Matrix.map_apply, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt,
    inv_one, Matrix.one_mulVec, Pi.basisFun_repr, Pi.star_apply, hc, map_sum, map_mul]
  simp [Complex.star_def]

variable [IsTotallyComplex K]

/- English proof (translation)
Establish `: Nontrivial (Fin n → K)` using `Pi.nontrivial_at ⟨0, hn⟩`. Use `set b := Pi.basisFun K (Fin n)`. Use `set X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun _ => 1`. Establish `hX : ∀ v, IsUnit (X v).det` using `fun _ => by simp [X]`. Take `⟨j, e, he, heN, hsp⟩` from `Formalism.LFunctionChainParameters.LLcv.covolume_exists K (Fin n → K) N`.

Establish `hN0 : N ≠ ⊥` using `isLattice_ne_bot hN`. Take `⟨hrk, hj, hdet, -, -⟩` from `Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) b X hX j e N he hN.fg hN0 hsp`. Use `set e' : Fin j → Fin n → K := fun a => star (e a) with he'def`. Establish `he' : LinearIndependent K e'`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg a`. Establish `h1 : ∑ i, star (g i) • e i = 0`. Use `congrArg star hg` as an intermediate fact. Simplify `this` using `[star_sum, brp_star_smulK, he'def]`. Establish `h2` using `(Fintype.linearIndependent_iff.1 he) _ h1 a`.

Simplify using `using congrArg star h2`. Establish `hrange : Set.range e' = star '' Set.range e`. Use extensionality with `x`. Simplify using `only [he'def, Set.mem_range, Set.mem_image, exists_exists_eq_and]`. Establish `hL'` using `brp_starLat_lattice K N hN`.

Establish `hspT : Submodule.span K (Set.range e) = ⊤` using `hsp ▸ hN.span_eq_top`. Establish `hsp' : Submodule.span K ((starLat K N : Set (Fin n → K))) = Submodule.span K (Set.range e')`. Rewrite using `[hL'.span_eq_top, hrange, brp_star_span_top K _ hspT]`. Establish `hN0' : starLat K N ≠ ⊥` using `isLattice_ne_bot hL'`. Take `⟨hrk', -, hdet', -, -⟩` from `Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) b X hX j e' (starLat K N) he' hL'.fg hN0' hsp'`.

Take `⟨hG1, hG2⟩` from `htGram K (Fin n → K) (Fin n) b X hX j e he`. Take `⟨hG1', hG2'⟩` from `htGram K (Fin n → K) (Fin n) b X hX j e' he'`. Establish `hle : Submodule.span (𝓞 K) (Set.range e) ≤ N` using `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact heN a)`. Establish `hle' : Submodule.span (𝓞 K) (Set.range e') ≤ starLat K N` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨a, rfl⟩`.

Use `show star (star (e a)) ∈ N`. Rewrite using `[star_star]`. Conclude with `heN a)`. Establish `hG3` using `hG2 N hN.fg hle hrk`. Establish `hG3'` using `hG2' (starLat K N) hL'.fg hle' hrk'`.

Establish `hspan' : Submodule.span (𝓞 K) (Set.range e') = starLat K (Submodule.span (𝓞 K) (Set.range e))`. Rewrite using `[brp_starLat_span, hrange]`. Establish `hI : (Submodule.span (𝓞 K) (Set.range e')).toAddSubgroup.relIndex (starLat K N).toAddSubgroup = (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup`. Rewrite using `[hspan', brp_starLat_toAdd, brp_starLat_toAdd]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ (starAddEquiv : (Fin n → K) ≃+ (Fin n → K)).injective`.

Establish `hdetEq : ∀ v, (gramPl b X v e').det.re = (gramPl b X v e).det.re`. Introduce `v`. Rewrite using `[brp_gram_star K hc v e]`. Use `(starRingEnd ℂ).map_det (gramPl b X v e)` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`.

Rewrite using `[← this, Complex.conj_re]`. Establish `hht : ht b X (Submodule.span (𝓞 K) (Set.range e')) = ht b X (Submodule.span (𝓞 K) (Set.range e))`. Rewrite using `[hG1, hG1']`. Conclude with `Finset.prod_congr rfl fun v _ => hdetEq v`. Establish `hpos : 0 < ht b X (Submodule.span (𝓞 K) (Set.range e))`.

Rewrite using `[hG1]`. Conclude with `Finset.prod_pos fun v _ => (hdet v).1`. Use `set I := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup`. Establish `hI0 : (I : ℝ) ≠ 0`. Introduce `h0`.

Rewrite `hG3` using `[h0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hhtN : ht b X (starLat K N) = ht b X N`. Rewrite `hG3'` using `[hI, hht, ← hG3]`. Conclude with `mul_right_cancel₀ hI0 hG3'`.

Use `show muDef b X (starLat K N) = muDef b X N`. Rewrite using `[T2.mu_eq_log_ht b X hX _ hL'.fg hN0', T2.mu_eq_log_ht b X hX _ hN.fg hN0, hhtN, hrk, hrk']`.
-/
theorem brp_star_mu (hc : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (N : Submodule (𝓞 K) (Fin n → K))
    (hN : Submodule.IsLattice K N) (hn : 0 < n) : (stdHL K (starLat K N)).mu = (stdHL K N).mu := by
  classical
  have : Nontrivial (Fin n → K) := Pi.nontrivial_at ⟨0, hn⟩
  set b := Pi.basisFun K (Fin n)
  set X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun _ => 1
  have hX : ∀ v, IsUnit (X v).det := fun _ => by simp [X]
  obtain ⟨j, e, he, heN, hsp⟩ := Formalism.LFunctionChainParameters.LLcv.covolume_exists K (Fin n → K) N
  have hN0 : N ≠ ⊥ := isLattice_ne_bot hN
  obtain ⟨hrk, hj, hdet, -, -⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) b X hX j e N he hN.fg hN0 hsp
  set e' : Fin j → Fin n → K := fun a => star (e a) with he'def
  have he' : LinearIndependent K e' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h1 : ∑ i, star (g i) • e i = 0 := by
      have := congrArg star hg
      simpa [star_sum, brp_star_smulK, he'def] using this
    have h2 := (Fintype.linearIndependent_iff.1 he) _ h1 a
    simpa using congrArg star h2
  have hrange : Set.range e' = star '' Set.range e := by
    ext x
    simp only [he'def, Set.mem_range, Set.mem_image, exists_exists_eq_and]
  have hL' := brp_starLat_lattice K N hN
  have hspT : Submodule.span K (Set.range e) = ⊤ := hsp ▸ hN.span_eq_top
  have hsp' : Submodule.span K ((starLat K N : Set (Fin n → K))) = Submodule.span K (Set.range e') := by
    rw [hL'.span_eq_top, hrange, brp_star_span_top K _ hspT]
  have hN0' : starLat K N ≠ ⊥ := isLattice_ne_bot hL'
  obtain ⟨hrk', -, hdet', -, -⟩ :=
    Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K (Fin n → K) (Fin n) b X hX j e' (starLat K N) he' hL'.fg hN0' hsp'
  obtain ⟨hG1, hG2⟩ := htGram K (Fin n → K) (Fin n) b X hX j e he
  obtain ⟨hG1', hG2'⟩ := htGram K (Fin n → K) (Fin n) b X hX j e' he'
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ N := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact heN a)
  have hle' : Submodule.span (𝓞 K) (Set.range e') ≤ starLat K N := Submodule.span_le.2 (by
    rintro _ ⟨a, rfl⟩
    show star (star (e a)) ∈ N
    rw [star_star]; exact heN a)
  have hG3 := hG2 N hN.fg hle hrk
  have hG3' := hG2' (starLat K N) hL'.fg hle' hrk'
  have hspan' : Submodule.span (𝓞 K) (Set.range e') = starLat K (Submodule.span (𝓞 K) (Set.range e)) := by
    rw [brp_starLat_span, hrange]
  have hI : (Submodule.span (𝓞 K) (Set.range e')).toAddSubgroup.relIndex (starLat K N).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup := by
    rw [hspan', brp_starLat_toAdd, brp_starLat_toAdd]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (starAddEquiv : (Fin n → K) ≃+ (Fin n → K)).injective
  have hdetEq : ∀ v, (gramPl b X v e').det.re = (gramPl b X v e).det.re := by
    intro v
    rw [brp_gram_star K hc v e]
    have := (starRingEnd ℂ).map_det (gramPl b X v e)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this, Complex.conj_re]
  have hht : ht b X (Submodule.span (𝓞 K) (Set.range e')) = ht b X (Submodule.span (𝓞 K) (Set.range e)) := by
    rw [hG1, hG1']
    exact Finset.prod_congr rfl fun v _ => hdetEq v
  have hpos : 0 < ht b X (Submodule.span (𝓞 K) (Set.range e)) := by
    rw [hG1]; exact Finset.prod_pos fun v _ => (hdet v).1
  set I := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup
  have hI0 : (I : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hG3
    linarith
  have hhtN : ht b X (starLat K N) = ht b X N := by
    rw [hI, hht, ← hG3] at hG3'
    exact mul_right_cancel₀ hI0 hG3'
  show muDef b X (starLat K N) = muDef b X N
  rw [T2.mu_eq_log_ht b X hX _ hL'.fg hN0', T2.mu_eq_log_ht b X hX _ hN.fg hN0, hhtN, hrk, hrk']

end StarMu

section ESide

variable (E : Type) [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Simplify using `only [Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨brpCO E y, ?_⟩` and prove the remaining obligations. Establish `h1 : ((brpCO E y : 𝓞 E) : E) = star (y : E)` using `brpCO_coe E y`.

Establish `h2 : (algebraMap (𝓞 E) E y) = star z` using `hy`. Establish `h3 : (y : E) = star z` using `h2`. Use `show ((brpCO E y : 𝓞 E) : E) = z`. Rewrite using `[h1, h3, star_star]`. Introduce and unpack `⟨y, hy⟩`.

Use `⟨brpCO E y, ?_⟩` and prove the remaining obligations. Establish `h1 : ((brpCO E y : 𝓞 E) : E) = star (y : E)` using `brpCO_coe E y`. Establish `h3 : (y : E) = z` using `hy`. Use `show ((brpCO E y : 𝓞 E) : E) = star z`. Rewrite using `[h1, h3]`.
-/
theorem brp_star_mem_one (z : E) : star z ∈ (1 : Submodule (𝓞 E) E) ↔ z ∈ (1 : Submodule (𝓞 E) E) := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨brpCO E y, ?_⟩
    have h1 : ((brpCO E y : 𝓞 E) : E) = star (y : E) := brpCO_coe E y
    have h2 : (algebraMap (𝓞 E) E y) = star z := hy
    have h3 : (y : E) = star z := h2
    show ((brpCO E y : 𝓞 E) : E) = z
    rw [h1, h3, star_star]
  · rintro ⟨y, hy⟩
    refine ⟨brpCO E y, ?_⟩
    have h1 : ((brpCO E y : 𝓞 E) : E) = star (y : E) := brpCO_coe E y
    have h3 : (y : E) = z := hy
    show ((brpCO E y : 𝓞 E) : E) = star z
    rw [h1, h3]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_dual, mem_starLat, mem_dualFr]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← brp_star_mem_one]`. Establish `: star (hStd E n y x) = star x ⬝ᵥ y`.

Simplify using `only [hStd, LinearMap.mk₂'ₛₗ_apply, star_sum, star_mul', star_star, dotProduct, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[this]`.
-/
theorem brp_dual_eq (L : Submodule (𝓞 E) (Fin n → E)) : dual (hStd E n) L = starLat E (dualFr L) := by
  ext x
  rw [mem_dual, mem_starLat, mem_dualFr]
  refine forall₂_congr fun y _ => ?_
  rw [← brp_star_mem_one]
  have : star (hStd E n y x) = star x ⬝ᵥ y := by
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply, star_sum, star_mul', star_star, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `hD` using `(dualFrLattice E n (1 : Matrix (Fin n) (Fin n) E) L (by simp) hL).1`. Rewrite using `[brp_dual_eq, brp_star_mu E hc _ hD hn, brp_dual_mu E L hL hn]`.
-/
theorem brp_hdual_mu (hc : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hn : 0 < n) : (stdHL E (dual (hStd E n) L)).mu = -(stdHL E L).mu := by
  have hD := (dualFrLattice E n (1 : Matrix (Fin n) (Fin n) E) L (by simp) hL).1
  rw [brp_dual_eq, brp_star_mu E hc _ hD hn, brp_dual_mu E L hL hn]

/- English proof (translation)
Establish `: Nontrivial (Fin n → E)` using `Pi.nontrivial_at ⟨0, hn⟩`. Establish `h` using `(with_lattice_index E (stdHL E L') L (brp_stdHL_frameOK E L') hL'.fg hle (isLattice_ne_bot hL)).2 (by rw [show (withL (stdHL E L') L).rank = (stdHL E L).rank from rfl, brp_rank_std E L hL, brp_rank_std E L' hL'])`. Rewrite `h` using `[brp_rank_std E L' hL']`. Conclude with `h`.
-/
theorem brp_index_mu (L L' : Submodule (𝓞 E) (Fin n → E)) (hle : L ≤ L') (hL : Submodule.IsLattice E L)
    (hL' : Submodule.IsLattice E L') (hn : 0 < n) :
    (stdHL E L).mu = (stdHL E L').mu - 2 * Real.log (L.toAddSubgroup.relIndex L'.toAddSubgroup : ℝ) /
      ((Module.finrank ℚ E : ℝ) * (n : ℝ)) := by
  have : Nontrivial (Fin n → E) := Pi.nontrivial_at ⟨0, hn⟩
  have h := (with_lattice_index E (stdHL E L') L (brp_stdHL_frameOK E L') hL'.fg hle (isLattice_ne_bot hL)).2
    (by rw [show (withL (stdHL E L') L).rank = (stdHL E L).rank from rfl, brp_rank_std E L hL, brp_rank_std E L' hL'])
  rw [brp_rank_std E L' hL'] at h
  exact h

end ESide

section Tau

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [IsTotallyComplex E] [Field K] [NumberField K] [StarRing K]
  [IsTotallyComplex K] {n : ℕ}

/- English proof (translation)
Rewrite using `[T2.mu_eq_log_ht b X hX L hL h0]`. Unfold `Formalism.HermiteSiegelSlopes.degT`. Establish `h1 : (0 : ℝ) < (nPl K : ℝ)`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions.

Establish `h2 : (0 : ℝ) < (rkK L : ℝ)` using `by exact_mod_cast hr`. Clear the denominators using the available nonvanishing facts.
-/
theorem brp_mu_degT {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (h0 : L ≠ ⊥) (hr : 0 < rkK L) :
    muDef b X L = 2 * Formalism.HermiteSiegelSlopes.degT b X L / (rkK L : ℝ) := by
  rw [T2.mu_eq_log_ht b X hX L hL h0]
  unfold Formalism.HermiteSiegelSlopes.degT
  have h1 : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have h2 : (0 : ℝ) < (rkK L : ℝ) := by exact_mod_cast hr
  field_simp

/- English proof (translation)
Set `_ : Algebra E K` to `φ.toAlgebra`. Establish `hT : Submodule.IsLattice K (du_tl φ M)` using `tauLatLattice E K Unit n (fun _ => φ) () M hM`. Establish `h` using `Formalism.HermiteSiegelSlopes.baseChange E K (Fin n) (fun _ => 1) (fun _ => 1) (fun _ => by simp) (fun _ => by simp) (fun w x => by`. Simplify using `only [normAt, cnorm, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq, InfinitePlace.comap_apply]) M hM.fg`. Establish `hE : Nontrivial (Fin n → E)` using `Pi.nontrivial_at ⟨0, hn⟩`. Establish `hK : Nontrivial (Fin n → K)` using `Pi.nontrivial_at ⟨0, hn⟩`. Establish `hrM : rkK M = n` using `brp_rank_std E M hM`.

Establish `hrT : rkK (du_tl φ M) = n` using `brp_rank_std K _ hT`. Use `show muDef (Pi.basisFun K (Fin n)) (fun _ => 1) (du_tl φ M) = muDef (Pi.basisFun E (Fin n)) (fun _ => 1) M`. Rewrite using `[brp_mu_degT _ _ (fun _ => by simp) _ hT.fg (isLattice_ne_bot hT) (by rw [hrT]; exact hn), brp_mu_degT _ _ (fun _ => by simp) _ hM.fg (isLattice_ne_bot hM) (by rw [hrM]; exact hn), hrM, hrT]`. Use `congr 2`. Conclude with `h.2`.
-/
theorem brp_tau_mu (φ : E →+* K) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) (hn : 0 < n) :
    (stdHL K (du_tl φ M)).mu = (stdHL E M).mu := by
  let _ : Algebra E K := φ.toAlgebra
  have hT : Submodule.IsLattice K (du_tl φ M) :=
    tauLatLattice E K Unit n (fun _ => φ) () M hM
  have h := Formalism.HermiteSiegelSlopes.baseChange E K (Fin n) (fun _ => 1) (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
    (fun w x => by
      simp only [normAt, cnorm, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq, InfinitePlace.comap_apply]) M hM.fg
  have hE : Nontrivial (Fin n → E) := Pi.nontrivial_at ⟨0, hn⟩
  have hK : Nontrivial (Fin n → K) := Pi.nontrivial_at ⟨0, hn⟩
  have hrM : rkK M = n := brp_rank_std E M hM
  have hrT : rkK (du_tl φ M) = n := brp_rank_std K _ hT
  show muDef (Pi.basisFun K (Fin n)) (fun _ => 1) (du_tl φ M) = muDef (Pi.basisFun E (Fin n)) (fun _ => 1) M
  rw [brp_mu_degT _ _ (fun _ => by simp) _ hT.fg (isLattice_ne_bot hT) (by rw [hrT]; exact hn),
    brp_mu_degT _ _ (fun _ => by simp) _ hM.fg (isLattice_ne_bot hM) (by rw [hrM]; exact hn), hrM, hrT]
  congr 2
  exact h.2

end Tau

section EE

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

/- English proof (translation)
Rewrite using `[← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]`.
-/
theorem brp_finrank_E (hX : X.Ok) : Module.finrank ℚ X.E = 2 * X.f := by
  rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]

/- English proof (translation)
Rewrite using `[Fields.f, hX.card_Tau]`. Conclude with `Module.finrank_pos`.
-/
theorem brp_f_pos (hX : X.Ok) : 0 < X.f := by
  rw [Fields.f, hX.card_Tau]
  exact Module.finrank_pos

/- English proof (translation)
Introduce `d τ`. Use `hX.cplxE` as an intermediate fact. Use `hX.cplxK` as an intermediate fact. Establish `hd` using `(d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).2`. Use `set L := (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.L with hLdef`.

Use `set Lsh := (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh with hLshdef`. Establish `hn : 0 < R.N 0` using `R.N_pos 0`. Establish `hL : Submodule.IsLattice X.E L` using `hd.L_lattice`. Establish `hLsh : Submodule.IsLattice X.E Lsh` using `hd.Lsh_lattice`. Establish `e1 : EEC W Ch u d τ = du_tl (X.emb τ) (dualFr Lsh)`.

Unfold `EEC`. Rewrite using `[du_tauLat_eq, du_dualFr_tl basisAtEx (X.emb τ) _ hLsh]`. Establish `hDL : Submodule.IsLattice X.E (dualFr Lsh)` using `(dualFrLattice X.E _ (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) _ (by simp) hLsh).1`. Establish `hT : Submodule.IsLattice X.K (EEC W Ch u d τ)` using `EEC_isLattice W Ch u d τ`. Rewrite using `[brp_latK_mu X.K _ hT.fg, e1, brp_tau_mu (X.emb τ) _ hDL hn, brp_dual_mu X.E _ hLsh hn]`.

Establish `h1 : (stdHL X.E Lsh).mu = -(stdHL X.E L).mu` using `brp_hdual_mu X.E hX.conjE L hL hn`. Establish `h2` using `brp_index_mu X.E L Lsh hd.L_le_Lsh hL hLsh hn`. Establish `hI : (L.toAddSubgroup.relIndex Lsh.toAddSubgroup : ℝ) = (Pr.T u : ℝ) ^ (2 * X.f)`. Establish `h` using `card_Lsh_quot_L_of_ok hPr u (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)`. Rewrite using `[show L.toAddSubgroup.relIndex Lsh.toAddSubgroup = Nat.card (Lsh ⧸ L.submoduleOf Lsh) from rfl, h]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `h2` using `[hI, Real.log_pow, brp_finrank_E hX]`. Establish `hf : (0 : ℝ) < (X.f : ℝ)` using `by exact_mod_cast brp_f_pos hX`. Establish `hnR : (0 : ℝ) < (R.N 0 : ℝ)` using `by exact_mod_cast hn`.

Establish `h3 : 2 * (((2 * X.f : ℕ) : ℝ) * Real.log (Pr.T u : ℝ)) / (((2 * X.f : ℕ) : ℝ) * (R.N 0 : ℝ)) = 2 * Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[h3]`. Unfold `logTC`.

Rewrite using `[← brz_N_zero R]`. Establish `h4 : (stdHL X.E Lsh).mu = Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ)`. Establish `: 2 * Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ) = 2 * (Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h4, neg_div]`.
-/
theorem eeSlope (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) : EESlope W Ch u := by
  intro d τ
  have := hX.cplxE
  have := hX.cplxK
  have hd := (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).2
  set L := (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.L with hLdef
  set Lsh := (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh with hLshdef
  have hn : 0 < R.N 0 := R.N_pos 0
  have hL : Submodule.IsLattice X.E L := hd.L_lattice
  have hLsh : Submodule.IsLattice X.E Lsh := hd.Lsh_lattice
  have e1 : EEC W Ch u d τ = du_tl (X.emb τ) (dualFr Lsh) := by
    unfold EEC
    rw [du_tauLat_eq, du_dualFr_tl basisAtEx (X.emb τ) _ hLsh]
  have hDL : Submodule.IsLattice X.E (dualFr Lsh) :=
    (dualFrLattice X.E _ (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) _ (by simp) hLsh).1
  have hT : Submodule.IsLattice X.K (EEC W Ch u d τ) := EEC_isLattice W Ch u d τ
  rw [brp_latK_mu X.K _ hT.fg, e1, brp_tau_mu (X.emb τ) _ hDL hn, brp_dual_mu X.E _ hLsh hn]
  have h1 : (stdHL X.E Lsh).mu = -(stdHL X.E L).mu := brp_hdual_mu X.E hX.conjE L hL hn
  have h2 := brp_index_mu X.E L Lsh hd.L_le_Lsh hL hLsh hn
  have hI : (L.toAddSubgroup.relIndex Lsh.toAddSubgroup : ℝ) = (Pr.T u : ℝ) ^ (2 * X.f) := by
    have h := card_Lsh_quot_L_of_ok hPr u (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs)
    rw [show L.toAddSubgroup.relIndex Lsh.toAddSubgroup = Nat.card (Lsh ⧸ L.submoduleOf Lsh) from rfl, h]
    push_cast
    rfl
  rw [hI, Real.log_pow, brp_finrank_E hX] at h2
  have hf : (0 : ℝ) < (X.f : ℝ) := by exact_mod_cast brp_f_pos hX
  have hnR : (0 : ℝ) < (R.N 0 : ℝ) := by exact_mod_cast hn
  have h3 : 2 * (((2 * X.f : ℕ) : ℝ) * Real.log (Pr.T u : ℝ)) / (((2 * X.f : ℕ) : ℝ) * (R.N 0 : ℝ)) =
      2 * Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ) := by
    push_cast
    field_simp
  rw [h3] at h2
  unfold logTC
  rw [← brz_N_zero R]
  have h4 : (stdHL X.E Lsh).mu = Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ) := by
    have : 2 * Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ) = 2 * (Real.log (Pr.T u : ℝ) / (R.N 0 : ℝ)) := by ring
    linarith
  rw [h4, neg_div]

end EE

end Formalism.L2.Col
