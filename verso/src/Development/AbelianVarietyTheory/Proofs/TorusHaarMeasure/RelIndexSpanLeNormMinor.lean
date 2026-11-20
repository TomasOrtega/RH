import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndexRangeMulVecLinEqAbsNormDet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.AbsNormEqProdCmTypeSq
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

/- English proof (translation)
Introduce `r X`. Take `⟨n, hn, hint⟩` from `(GlobalTheory.LatDen.latDen r X).2`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hn0 : (n : E) ≠ 0` using `by exact_mod_cast hn.ne'`. Use `⟨∏ _τ : X.Ψ, ((n : ℝ) ^ r) ^ 2, Finset.prod_pos fun _ _ => by positivity, ?_⟩` and prove the remaining obligations.

Introduce `ι _ _ w _ hw e he hdet`. Use `set M : Matrix ι ι E := Matrix.of fun k a => w a (e k) with hM`. Use `set L : AddSubgroup (Fin r → E) := X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup with hL`. Set `A : Matrix ι ι (𝓞 E)` to `Matrix.of fun k a => ⟨(n : E) * w a (e k), hint _ (hw a) _⟩`. Establish `hA : (algebraMap (𝓞 E) E).mapMatrix A = (n : E) • M`.

Use extensionality with `k a`. Both sides reduce to the same expression. Establish `hdetA : ((A.det : 𝓞 E) : E) = (n : E) ^ Fintype.card ι * M.det`. Rewrite using `[← Matrix.det_smul, ← hA, ← RingHom.map_det]`. Establish `hA0 : A.det ≠ 0`.

Introduce `h`. Rewrite `hdetA` using `[h]`. Conclude with `mul_ne_zero (pow_ne_zero _ hn0) hdet (hdetA.symm.trans rfl)`. Set `φ : L →+ (ι → 𝓞 E)` to `{ toFun := fun v k => ⟨(n : E) * v.1 (e k), hint _ v.2.1 _⟩ map_zero' := by`. Use extensionality with `k`.

Conclude with `mul_zero (n : E)`. Use the proof step `map_add' := fun u v => by`. Use extensionality with `k`. Conclude with `mul_add (n : E) _ _ }`. Use `set R := (LinearMap.range A.mulVecLin).toAddSubgroup with hR`.

Establish `hidx` using `index_range_mulVecLin_eq_abs_norm_det ι A hA0`. Rewrite `hidx` using `[← hR]`. Establish `hR0 : R.index ≠ 0`. Introduce `h`. Rewrite `hidx` using `[h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff]`.

Conclude with `hA0 (by exact_mod_cast hidx)`. Establish `hle : R.comap φ ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.addSubgroupOf L`. Introduce and unpack `⟨v, hvΛ, hv⟩ ⟨c, hc⟩`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hv`. Establish `hb : M *ᵥ (fun a => (c a : E)) = M *ᵥ b`.

Use function extensionality and compare the values at `k`. Establish `h` using `congrArg (algebraMap (𝓞 E) E) (congrFun hc k)`. Rewrite `h` using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum]`. Apply `mul_left_cancel₀ hn0` to reduce the goal to its premises. Establish `h2 : (algebraMap (𝓞 E) E) (φ ⟨∑ i, b i • w i, hvΛ, hv⟩ k) = (n : E) * (∑ i, b i • w i) (e k)` using `rfl`.

Rewrite `h` using `[h2]`. Establish `h3 : (M *ᵥ b) k = (∑ i, b i • w i) (e k)`. Simplify using `[Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]`. Rewrite using `[h3, ← h, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← mul_assoc]`. Both sides reduce to the same expression. Establish `hcb` using `Matrix.mulVec_injective_of_det_ne_zero hdet hb`. Express the relevant statement in the definitionally equal form `(∑ i, b i • w i) ∈ Submodule.span (𝓞 E) (Set.range w)`. Rewrite using `[← hcb]`.

Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (c a) (Submodule.subset_span ⟨a, rfl⟩)`. Establish `h1 : (R.comap φ).index ≤ R.index`. Rewrite using `[AddSubgroup.index_comap, ← AddSubgroup.relIndex_top_right]`. Conclude with `AddSubgroup.relIndex_le_of_le_right le_top (by rwa [AddSubgroup.relIndex_top_right])`.

Establish `h0 : (R.comap φ).index ≠ 0`. Rewrite using `[AddSubgroup.index_comap]`. Conclude with `fun h => hR0 (AddSubgroup.index_eq_zero_of_relIndex_eq_zero h)`. Establish `h2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex L ≤ R.index` using `(Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (AddSubgroup.index_dvd_of_le hle)).trans h1`. Establish `h3 : (R.index : ℝ) = ∏ τ : X.Ψ, ‖τ.1 ((A.det : 𝓞 E) : E)‖ ^ 2`.

Rewrite using `[← abs_norm_eq_prod_cmType_sq r X, ← hidx, Rat.cast_natCast]`. Establish `hcard : Fintype.card ι ≤ r` using `by simpa using Fintype.card_le_of_injective e he`. Use `(Nat.cast_le.2 h2).trans ?_` and prove the remaining obligations. Rewrite using `[h3, ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun _ _ => by positivity) fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[hdetA, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]`. Use `gcongr`.
-/
theorem relIndex_span_le_norm_minor :
    (∀ (r : ℕ) (X : Data E r), ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ e : ι → Fin r, Function.Injective e → (Matrix.of fun k a => w a (e k)).det ≠ 0 → (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ) ≤ C * ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2) := by
  intro r X
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.LatDen.latDen r X).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨∏ _τ : X.Ψ, ((n : ℝ) ^ r) ^ 2, Finset.prod_pos fun _ _ => by positivity, ?_⟩
  intro ι _ _ w _ hw e he hdet
  set M : Matrix ι ι E := Matrix.of fun k a => w a (e k) with hM
  set L : AddSubgroup (Fin r → E) :=
    X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup with hL
  let A : Matrix ι ι (𝓞 E) := Matrix.of fun k a => ⟨(n : E) * w a (e k), hint _ (hw a) _⟩
  have hA : (algebraMap (𝓞 E) E).mapMatrix A = (n : E) • M := by
    ext k a
    rfl
  have hdetA : ((A.det : 𝓞 E) : E) = (n : E) ^ Fintype.card ι * M.det := by
    rw [← Matrix.det_smul, ← hA, ← RingHom.map_det]
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h] at hdetA
    exact mul_ne_zero (pow_ne_zero _ hn0) hdet (hdetA.symm.trans rfl)
  let φ : L →+ (ι → 𝓞 E) :=
    { toFun := fun v k => ⟨(n : E) * v.1 (e k), hint _ v.2.1 _⟩
      map_zero' := by
        ext k
        exact mul_zero (n : E)
      map_add' := fun u v => by
        ext k
        exact mul_add (n : E) _ _ }
  set R := (LinearMap.range A.mulVecLin).toAddSubgroup with hR
  have hidx := index_range_mulVecLin_eq_abs_norm_det ι A hA0
  rw [← hR] at hidx
  have hR0 : R.index ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at hidx
    exact hA0 (by exact_mod_cast hidx)
  have hle : R.comap φ ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.addSubgroupOf L := by
    rintro ⟨v, hvΛ, hv⟩ ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    have hb : M *ᵥ (fun a => (c a : E)) = M *ᵥ b := by
      funext k
      have h := congrArg (algebraMap (𝓞 E) E) (congrFun hc k)
      rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum] at h
      apply mul_left_cancel₀ hn0
      have h2 : (algebraMap (𝓞 E) E) (φ ⟨∑ i, b i • w i, hvΛ, hv⟩ k) =
          (n : E) * (∑ i, b i • w i) (e k) := rfl
      rw [h2] at h
      have h3 : (M *ᵥ b) k = (∑ i, b i • w i) (e k) := by
        simp [Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]
      rw [h3, ← h, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ← mul_assoc]
      rfl
    have hcb := Matrix.mulVec_injective_of_det_ne_zero hdet hb
    change (∑ i, b i • w i) ∈ Submodule.span (𝓞 E) (Set.range w)
    rw [← hcb]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact Submodule.smul_mem _ (c a) (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : (R.comap φ).index ≤ R.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_top_right]
    exact AddSubgroup.relIndex_le_of_le_right le_top (by rwa [AddSubgroup.relIndex_top_right])
  have h0 : (R.comap φ).index ≠ 0 := by
    rw [AddSubgroup.index_comap]
    exact fun h => hR0 (AddSubgroup.index_eq_zero_of_relIndex_eq_zero h)
  have h2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex L ≤ R.index :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (AddSubgroup.index_dvd_of_le hle)).trans h1
  have h3 : (R.index : ℝ) = ∏ τ : X.Ψ, ‖τ.1 ((A.det : 𝓞 E) : E)‖ ^ 2 := by
    rw [← abs_norm_eq_prod_cmType_sq r X, ← hidx, Rat.cast_natCast]
  have hcard : Fintype.card ι ≤ r := by simpa using Fintype.card_le_of_injective e he
  refine (Nat.cast_le.2 h2).trans ?_
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun τ _ => ?_
  rw [hdetA, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr

end GlobalTheory
