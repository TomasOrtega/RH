import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStA

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hvO : LinearIndependent (𝓞 K) v` using `hv.restrict_scalars' (𝓞 K)`. Set `Φ : (Fin r → 𝓞 K) →+ V` to `{ toFun := fun c => ∑ i, c i • v i map_zero' := by simp map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }`. Establish `hΦ : ∀ c, Φ c = ∑ i, c i • v i` using `fun c => rfl`. Establish `hΦinj : Function.Injective Φ`. Introduce `a b hab`.

Establish `h0 : ∑ i, (a - b) i • v i = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hΦ, ← hΦ, hab, sub_self]`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hvO _ h0 i)`.

Establish `hrange : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = AddSubgroup.map Φ ⊤`. Rewrite using `[← AddMonoidHom.range_eq_map]`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_range, Submodule.mem_span_range_iff_exists_fun, hΦ]`. Establish `hcomb : ∀ d : Fin r → 𝓞 K, Φ (g.mulVec d) = ∑ j, d j • ∑ i, g i j • v i`.

Introduce `d`. Simplify using `only [hΦ, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]` and prove the remaining obligations. Establish `hcomap : AddSubgroup.comap Φ (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup = (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup`.

Use extensionality with `c`. Simplify using `only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, hd⟩`. Conclude with `⟨d, hΦinj (by rw [hcomb, hd])⟩`.

Introduce and unpack `⟨d, rfl⟩`. Conclude with `⟨d, (hcomb d).symm⟩`. Establish `hTinj : Function.Injective (Matrix.mulVecLin g)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`.

Assume the negation of the conclusion as `hc0`. Conclude with `hg (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hc⟩)`. Set `T : (Fin r → 𝓞 K) →ₗ[ℤ] (Fin r → 𝓞 K)` to `(Matrix.mulVecLin g).restrictScalars ℤ`. Set `N : Submodule ℤ (Fin r → 𝓞 K)` to `LinearMap.range T`. Set `e : (Fin r → 𝓞 K) ≃ₗ[ℤ] N` to `LinearEquiv.ofInjective T hTinj`.

Establish `hcard` using `Submodule.natAbs_det_equiv N e`. Establish `hcomp : N.subtype ∘ₗ ((e : (Fin r → 𝓞 K) →+ N)).toIntLinearMap = T` using `LinearMap.ext fun c => rfl`. Rewrite `hcard` using `[hcomp]`. Establish `hdetT : LinearMap.det T = Algebra.norm ℤ g.det`. Rewrite using `[LinearMap.det_restrictScalars, ← LinearMap.det_toLin' g]`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[AddSubgroup.relIndex_top_right, hcomap]`. Use `_ = Nat.card ((Fin r → 𝓞 K) ⧸ N) := rfl`. Use `_ = _ := by rw [← hcard, hdetT]`.
-/
theorem ds_relIndex_span_comb {r : ℕ} {v : Fin r → V} (hv : LinearIndependent K v)
    (g : Matrix (Fin r) (Fin r) (𝓞 K)) (hg : g.det ≠ 0) :
    (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = (Algebra.norm ℤ g.det).natAbs := by
  classical
  have hvO : LinearIndependent (𝓞 K) v := hv.restrict_scalars' (𝓞 K)
  let Φ : (Fin r → 𝓞 K) →+ V :=
    { toFun := fun c => ∑ i, c i • v i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have hΦ : ∀ c, Φ c = ∑ i, c i • v i := fun c => rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∑ i, (a - b) i • v i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← hΦ, ← hΦ, hab, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hvO _ h0 i)
  have hrange : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = AddSubgroup.map Φ ⊤ := by
    rw [← AddMonoidHom.range_eq_map]
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_range,
      Submodule.mem_span_range_iff_exists_fun, hΦ]
  have hcomb : ∀ d : Fin r → 𝓞 K, Φ (g.mulVec d) = ∑ j, d j • ∑ i, g i j • v i := by
    intro d
    simp only [hΦ, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hcomap : AddSubgroup.comap Φ
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup =
      (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup := by
    ext c
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      Matrix.mulVecLin_apply, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, hΦinj (by rw [hcomb, hd])⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hcomb d).symm⟩
  have hTinj : Function.Injective (Matrix.mulVecLin g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hc0
    exact hg (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hc⟩)
  let T : (Fin r → 𝓞 K) →ₗ[ℤ] (Fin r → 𝓞 K) := (Matrix.mulVecLin g).restrictScalars ℤ
  let N : Submodule ℤ (Fin r → 𝓞 K) := LinearMap.range T
  let e : (Fin r → 𝓞 K) ≃ₗ[ℤ] N := LinearEquiv.ofInjective T hTinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ ((e : (Fin r → 𝓞 K) →+ N)).toIntLinearMap = T :=
    LinearMap.ext fun c => rfl
  rw [hcomp] at hcard
  have hdetT : LinearMap.det T = Algebra.norm ℤ g.det := by
    rw [LinearMap.det_restrictScalars, ← LinearMap.det_toLin' g]
    rfl
  calc _ = (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
        (AddSubgroup.map Φ ⊤) := by rw [hrange]
    _ = (AddSubgroup.comap Φ (Submodule.span (𝓞 K)
          (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup).relIndex ⊤ :=
        (AddSubgroup.relIndex_comap _ _ _).symm
    _ = (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup.index := by
        rw [AddSubgroup.relIndex_top_right, hcomap]
    _ = Nat.card ((Fin r → 𝓞 K) ⧸ N) := rfl
    _ = _ := by rw [← hcard, hdetT]

/- English proof (translation)
Introduce `hdet`. Establish `hG : (g.map (algebraMap (𝓞 K) K)).det = 0`. Establish `h1` using `RingHom.map_det (algebraMap (𝓞 K) K) g`. Rewrite `h1` using `[hdet, map_zero]`. Conclude with `h1.symm`.

Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hG`. Apply `hc0` to reduce the goal to its premises. Establish `hconv : (fun j => ∑ i, g i j • v i) = fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.map_apply, algebraMap_smul]`.

Rewrite `hv'` using `[hconv]`. Establish `hsum : ∑ j, c j • ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i = ∑ i, ((g.map (algebraMap (𝓞 K) K)).mulVec c) i • v i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]` and prove the remaining obligations.

Rewrite `hsum` using `[hc]`. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hsum`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 hv' c hsum j`.
-/
theorem ds_det_ne_zero_of_comb {r : ℕ} {v : Fin r → V} (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i)) : g.det ≠ 0 := by
  classical
  intro hdet
  have hG : (g.map (algebraMap (𝓞 K) K)).det = 0 := by
    have h1 := RingHom.map_det (algebraMap (𝓞 K) K) g
    rw [hdet, map_zero] at h1
    exact h1.symm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
  apply hc0
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  rw [hconv] at hv'
  have hsum : ∑ j, c j • ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i =
      ∑ i, ((g.map (algebraMap (𝓞 K) K)).mulVec c) i • v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [hc] at hsum
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hsum
  funext j
  exact Fintype.linearIndependent_iff.1 hv' c hsum j

/- English proof (translation)
Establish `hg` using `ds_det_ne_zero_of_comb g hv'`. Establish `hle : Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i) ≤ Submodule.span (𝓞 K) (Set.range v)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle) ((Submodule.toAddSubgroup_le _ _).2 hvE)`. Rewrite `hmul` using `[ds_relIndex_span_comb hv g hg]`. Establish `hconv : (fun j => ∑ i, g i j • v i) = fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.map_apply, algebraMap_smul]`.

Establish `hdetmap : algebraMap (𝓞 K) K g.det = (g.map (algebraMap (𝓞 K) K)).det` using `RingHom.map_det (algebraMap (𝓞 K) K) g`. Establish `hGdet : (g.map (algebraMap (𝓞 K) K)).det ≠ 0`. Rewrite using `[← hdetmap]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hg`. Establish `hsum : ∑ σ : K →+* ℂ, Real.log (h.gram σ (fun j => ∑ i, g i j • v i)).det.re = 2 * Real.log |(Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ)| + ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re`.

Rewrite using `[hconv, ← ds_sum_log_normSq_embeddings _ hGdet, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun σ _ => h.ds_log_gram_comb σ hv _ hGdet`. Establish `hnorm : (Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ) = ((Algebra.norm ℤ g.det : ℤ) : ℝ)`. Rewrite using `[← hdetmap]`. Establish `h1` using `Algebra.coe_norm_int g.det`.

Establish `h2 : ((Algebra.norm ℚ (algebraMap (𝓞 K) K g.det) : ℚ) : ℝ) = (((Algebra.norm ℤ g.det : ℤ) : ℚ) : ℝ)`. Rewrite using `[h1]`. Rewrite using `[h2]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hne1 : (((Algebra.norm ℤ g.det).natAbs : ℕ) : ℝ) ≠ 0`. Establish `: Algebra.norm ℤ g.det ≠ 0` using `Algebra.norm_ne_zero_iff.2 hg`. Conclude with `Int.natAbs_ne_zero.2 this` after adjusting the coercions. Establish `hne2 : (((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast hne`. Unfold `degreeOfFamily`.

Rewrite using `[← hmul, Nat.cast_mul, Real.log_mul hne1 hne2, hsum, hnorm, Nat.cast_natAbs, Int.cast_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degreeOfFamily_linearCombination (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i))
    (hvE : Submodule.span (𝓞 K) (Set.range v) ≤ E)
    (hne : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0) :
    degreeOfFamily h E (fun j => ∑ i, g i j • v i) = degreeOfFamily h E v := by
  classical
  have hg := ds_det_ne_zero_of_comb g hv'
  have hle : Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i) ≤
      Submodule.span (𝓞 K) (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle)
    ((Submodule.toAddSubgroup_le _ _).2 hvE)
  rw [ds_relIndex_span_comb hv g hg] at hmul
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  have hdetmap : algebraMap (𝓞 K) K g.det = (g.map (algebraMap (𝓞 K) K)).det :=
    RingHom.map_det (algebraMap (𝓞 K) K) g
  have hGdet : (g.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [← hdetmap]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hg
  have hsum : ∑ σ : K →+* ℂ, Real.log (h.gram σ (fun j => ∑ i, g i j • v i)).det.re =
      2 * Real.log |(Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ)| +
        ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re := by
    rw [hconv, ← ds_sum_log_normSq_embeddings _ hGdet, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => h.ds_log_gram_comb σ hv _ hGdet
  have hnorm : (Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ) =
      ((Algebra.norm ℤ g.det : ℤ) : ℝ) := by
    rw [← hdetmap]
    have h1 := Algebra.coe_norm_int g.det
    have h2 : ((Algebra.norm ℚ (algebraMap (𝓞 K) K g.det) : ℚ) : ℝ) =
        (((Algebra.norm ℤ g.det : ℤ) : ℚ) : ℝ) := by
      rw [h1]
    rw [h2]
    push_cast
    rfl
  have hne1 : (((Algebra.norm ℤ g.det).natAbs : ℕ) : ℝ) ≠ 0 := by
    have : Algebra.norm ℤ g.det ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
    exact_mod_cast Int.natAbs_ne_zero.2 this
  have hne2 : (((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℕ) : ℝ)
      ≠ 0 := by exact_mod_cast hne
  unfold degreeOfFamily
  rw [← hmul, Nat.cast_mul, Real.log_mul hne1 hne2, hsum, hnorm, Nat.cast_natAbs, Int.cast_abs]
  ring

/- English proof (translation)
Take `⟨hvE, hvli, hvsp⟩` from `hv`. Take `⟨hv'E, hv'li, hv'sp⟩` from `hv'`. Establish `hneV` using `IsFrame.relIndex_span_frame_ne_zero hE ⟨hvE, hvli, hvsp⟩`. Establish `hneV'` using `IsFrame.relIndex_span_frame_ne_zero hE ⟨hv'E, hv'li, hv'sp⟩`. Establish `hc : ∀ j, ∃ c : Fin r → K, ∑ i, c i • v i = v' j` using `fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hvsp (hv'E j))`.

Use `choose c hc using hc`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image fun p : Fin r × Fin r => c p.2 p.1)`. Establish `hint : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • c j i` using `fun i j => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))`. Use `choose gm hgm using hint`. Establish `hb0 : (b : 𝓞 K) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`.

Set `g : Matrix (Fin r) (Fin r) (𝓞 K)` to `Matrix.of gm`. Set `g₂ : Matrix (Fin r) (Fin r) (𝓞 K)` to `Matrix.diagonal fun _ => (b : 𝓞 K)`. Establish `hu : (fun j => ∑ i, g i j • v i) = fun j => (b : 𝓞 K) • v' j`. Use function extensionality and compare the values at `j`. Rewrite using `[← hc j, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show gm i j • v i = (b : 𝓞 K) • (c j i • v i)`. Rewrite using `[← algebraMap_smul K (gm i j) (v i), hgm, smul_assoc]`. Establish `hu2 : (fun j => ∑ i, g₂ i j • v' i) = fun j => (b : 𝓞 K) • v' j`. Use function extensionality and compare the values at `j`.

Simplify using `[g₂, Matrix.diagonal_apply, ite_smul]`. Establish `hbK : algebraMap (𝓞 K) K b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb0`. Establish `huli : LinearIndependent K fun j => (b : 𝓞 K) • v' j`. Establish `e1 : (fun j => (b : 𝓞 K) • v' j) = fun j => ((Units.mk0 _ hbK : Kˣ) : K) • v' j`. Use function extensionality and compare the values at `j`.

Rewrite using `[Units.val_mk0, algebraMap_smul]`. Rewrite using `[e1]`. Conclude with `hv'li.units_smul fun _ => Units.mk0 _ hbK`. Establish `e1` using `degreeOfFamily_linearCombination h E hvli g (by rw [hu]; exact huli) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvE i)) hneV`. Establish `e2` using `degreeOfFamily_linearCombination h E hv'li g₂ (by rw [hu2]; exact huli) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv'E i)) hneV'`.

Rewrite using `[← e1, ← e2, hu, hu2]`.
-/
theorem degreeOfFamily_eq_of_isFullRankFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v v' : Fin r → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  classical
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  obtain ⟨hv'E, hv'li, hv'sp⟩ := hv'
  have hneV := IsFrame.relIndex_span_frame_ne_zero hE ⟨hvE, hvli, hvsp⟩
  have hneV' := IsFrame.relIndex_span_frame_ne_zero hE ⟨hv'E, hv'li, hv'sp⟩
  have hc : ∀ j, ∃ c : Fin r → K, ∑ i, c i • v i = v' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hvsp (hv'E j))
  choose c hc using hc
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin r × Fin r => c p.2 p.1)
  have hint : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • c j i := fun i j =>
    hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  choose gm hgm using hint
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  let g : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.of gm
  let g₂ : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.diagonal fun _ => (b : 𝓞 K)
  have hu : (fun j => ∑ i, g i j • v i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    rw [← hc j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show gm i j • v i = (b : 𝓞 K) • (c j i • v i)
    rw [← algebraMap_smul K (gm i j) (v i), hgm, smul_assoc]
  have hu2 : (fun j => ∑ i, g₂ i j • v' i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    simp [g₂, Matrix.diagonal_apply, ite_smul]
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb0
  have huli : LinearIndependent K fun j => (b : 𝓞 K) • v' j := by
    have e1 : (fun j => (b : 𝓞 K) • v' j) = fun j => ((Units.mk0 _ hbK : Kˣ) : K) • v' j := by
      funext j
      rw [Units.val_mk0, algebraMap_smul]
    rw [e1]
    exact hv'li.units_smul fun _ => Units.mk0 _ hbK
  have e1 := degreeOfFamily_linearCombination h E hvli g (by rw [hu]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvE i)) hneV
  have e2 := degreeOfFamily_linearCombination h E hv'li g₂ (by rw [hu2]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv'E i)) hneV'
  rw [← e1, ← e2, hu, hu2]

end ReciprocityTheory.GeometryOfNumbersTheory
