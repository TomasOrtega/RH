import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise

noncomputable section

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace K))`. Establish `ha : (⟨c, hc⟩ : 𝓞 K) ≠ 0` using `fun h0 => hne (congrArg ((↑) : 𝓞 K → K) h0)`. Conclude with `absurd (InfinitePlace.one_le_of_lt_one ha (fun z _ => hlt z)) (not_le.2 (hlt w))`.
-/
theorem eq_zero_of_isIntegral_of_forall_place_lt_one {K : Type*} [Field K] [NumberField K] {c : K}
    (hc : IsIntegral ℤ c) (hlt : ∀ w : InfinitePlace K, w c < 1) : c = 0 := by
  by_contra hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have ha : (⟨c, hc⟩ : 𝓞 K) ≠ 0 := fun h0 => hne (congrArg ((↑) : 𝓞 K → K) h0)
  exact absurd (InfinitePlace.one_le_of_lt_one ha (fun z _ => hlt z)) (not_le.2 (hlt w))

section Discrete

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← unitaryGroupEquivMatrix_apply]`. Both sides reduce to the same expression.
-/
theorem archEmbed_apply_val (h : HermitianForm F E W) (v : Basis ι E W) (g : h.unitaryGroup)
    (w : InfinitePlace E) :
    ((((archEmbed h v g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) :
        Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

/- English proof (translation)
Introduce `La hLa`. Take `⟨S, hS⟩` from `hLa.fg`. Establish `hSLa : ∀ s ∈ S, s ∈ La` using `fun s hs => hS ▸ AddSubgroup.subset_closure hs`. Take `⟨d, hd0, hd⟩` from `exists_integral_multiples ℤ ℚ (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)`. Set `T : AddSubgroup W` to `{ carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)} add_mem' := fun {a b} ha hb i => by`.

Simplify `(ha i).add (hb i)` using `only [map_add, Finsupp.add_apply, smul_add]`. Use the proof step `zero_mem' := fun i => by`. Simplify `isIntegral_zero` using `only [map_zero, Finsupp.zero_apply, smul_zero]`. Use the proof step `neg_mem' := fun {a} ha i => by`. Simplify `(ha i).neg }` using `only [map_neg, Finsupp.neg_apply, smul_neg]`.

Establish `hLaT : La ≤ T`. Rewrite using `[← hS, AddSubgroup.closure_le]`. Introduce `s hs i`. Conclude with `hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)`. Establish `hdE : (d : E) ≠ 0` using `Int.cast_ne_zero.2 hd0`.

Establish `key : ∀ y ∈ La, (∀ (w : InfinitePlace E) (i : ι), |(d : ℝ)| * ‖w.embedding (v.repr y i)‖ < 1) → y = 0`. Introduce `y hy hsmall`. Use `v.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations. Establish `hz` using `eq_zero_of_isIntegral_of_forall_place_lt_one (hLaT hy i) fun w => by`. Rewrite using `[← InfinitePlace.norm_embedding_eq, zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast]`.

Conclude with `hsmall w i`. Rewrite `hz` using `[zsmul_eq_mul]`. Simplify `hz` using `[hdE]`. Use `set B : ℝ := ∑ s ∈ S, ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖ with hB`. Establish `hB0 : 0 ≤ B` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.

Establish `hdpos : 0 < |(d : ℝ)|` using `abs_pos.2 (Int.cast_ne_zero.2 hd0)`. Use `set δ : ℝ := 1 / (|(d : ℝ)| * (B + 1)) with hδ`. Establish `hδpos : 0 < δ` using `by positivity`. Establish `hdδB : |(d : ℝ)| * δ * B < 1`. Establish `e : |(d : ℝ)| * δ = 1 / (B + 1)`.

Rewrite using `[hδ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `U : Set (InfinitePlace E → GL ι ℂ)` to `{g | ∀ w i j, ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}`.

Establish `hU : IsOpen U`. Establish `e : U = ⋂ w, ⋂ i, ⋂ j, {g : InfinitePlace E → GL ι ℂ | ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}`. Use extensionality with `g`. Simplify using `[U]`. Rewrite using `[e]`.

Use `isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const` and prove the remaining obligations. Conclude with `(((Units.continuous_val.comp (continuous_apply w)).matrix_elem i j).sub continuous_const).norm`. Establish `hone : ∀ γ ∈ latticeStab h La, ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) ∈ U → γ = 1`. Introduce `γ hγ hγU`. Use `set M := LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) with hM`.

Establish `hγLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x ∈ La`. Introduce `x hx`. Establish `h1 : γ • x ∈ γ • La` using `AddSubgroup.smul_mem_pointwise_smul x γ La hx`. Rewrite `h1` using `[MulAction.mem_stabilizer_iff.1 hγ]`. Then use the resulting hypothesis. Establish `hrep : ∀ x : W, ∀ i, v.repr ((γ : W ≃ₗ[E] W) x - x) i = ∑ j, (M i j - (1 : Matrix ι ι E) i j) * v.repr x j`.

Introduce `x i`. Establish `h1` using `congrFun (LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i`. Simplify using `only [LinearEquiv.coe_coe] at h1`. Rewrite using `[map_sub, Finsupp.sub_apply, ← h1]`. Simplify using `only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hM]`.

Establish `h1ij : ∀ (w : InfinitePlace E) i j, w.embedding ((1 : Matrix ι ι E) i j) = (1 : Matrix ι ι ℂ) i j`. Introduce `w i j`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hfix : ∀ s ∈ S, (γ : W ≃ₗ[E] W) s = s`.

Introduce `s hs`. Use `sub_eq_zero.1 (key _ (sub_mem (hγLa s (hSLa s hs)) (hSLa s hs)) fun w i => ?_)` and prove the remaining obligations. Apply the tactic sequence `have entry : ∀ j, ‖w.embedding (M i j - (1 : Matrix ι ι E) i j)‖ < δ := by`. Introduce `j`. Use `hγU w i j` as an intermediate fact.

Rewrite `this` using `[archEmbed_apply_val, Matrix.map_apply]`. Rewrite using `[map_sub, h1ij]` and apply the resulting hypothesis. Establish `hsum : ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖ ≤ δ * ∑ j, ‖w.embedding (v.repr s j)‖`. Rewrite using `[hrep, map_sum, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, norm_mul]`. Apply the tactic sequence `exact mul_le_mul_of_nonneg_right (entry j).le (norm_nonneg _)`. Establish `hsB : ∑ j, ‖w.embedding (v.repr s j)‖ ≤ B`. Use `le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hs)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun w : InfinitePlace E => ∑ j, ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hsum.trans (mul_le_mul_of_nonneg_left hsB hδpos.le)`. Use `_ = |(d : ℝ)| * δ * B := by ring`. Use `_ < 1 := hdδB`. Establish `hfixLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x = x`.

Introduce `x hx`. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hfix x hx`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [map_add, hx, hy]`. Consider the case `neg x _ hx => simp [map_neg, hx]`. Establish `hlin : ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) = LinearMap.id` using `LinearMap.ext_on hLa.span_eq_top fun x hx => hfixLa x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearEquiv.ext` to reduce the goal to its premises.

Introduce `x`. Simplify using `using LinearMap.congr_fun hlin x`. Use `discreteTopology_of_isOpen_singleton_one ?_` and prove the remaining obligations. Establish `hcont : Continuous fun x : archLatticeGroup h v La => ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)` using `continuous_subtype_val.comp continuous_subtype_val`. Establish `e : ({1} : Set (archLatticeGroup h v La)) = (fun x : archLatticeGroup h v La => ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)) ⁻¹' U`.

Use extensionality with `x`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl w i j`. Simplify using `using hδpos`.

Introduce `hx`. Take `⟨γ, hγ, hγx⟩` from `Subgroup.mem_map.1 x.2`. Establish `h1` using `hone γ hγ (by rw [hγx]; exact hx)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hγx, h1, map_one]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hU.preimage hcont`.
-/
theorem ArchLatticeDiscrete.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchLatticeDiscrete.Statement h v := by
  classical
  intro La hLa
  obtain ⟨S, hS⟩ := hLa.fg
  have hSLa : ∀ s ∈ S, s ∈ La := fun s hs => hS ▸ AddSubgroup.subset_closure hs

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add, Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    rw [← hS, AddSubgroup.closure_le]
    intro s hs i
    exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  have key : ∀ y ∈ La, (∀ (w : InfinitePlace E) (i : ι),
      |(d : ℝ)| * ‖w.embedding (v.repr y i)‖ < 1) → y = 0 := by
    intro y hy hsmall
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have hz := eq_zero_of_isIntegral_of_forall_place_lt_one (hLaT hy i) fun w => by
      rw [← InfinitePlace.norm_embedding_eq, zsmul_eq_mul, map_mul, map_intCast, norm_mul,
        Complex.norm_intCast]
      exact hsmall w i
    rw [zsmul_eq_mul] at hz
    simpa [hdE] using hz

  set B : ℝ := ∑ s ∈ S, ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdpos : 0 < |(d : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd0)
  set δ : ℝ := 1 / (|(d : ℝ)| * (B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hdδB : |(d : ℝ)| * δ * B < 1 := by
    have e : |(d : ℝ)| * δ = 1 / (B + 1) := by
      rw [hδ]; field_simp
    rw [e, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  let U : Set (InfinitePlace E → GL ι ℂ) :=
    {g | ∀ w i j, ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}
  have hU : IsOpen U := by
    have e : U = ⋂ w, ⋂ i, ⋂ j, {g : InfinitePlace E → GL ι ℂ |
        ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ} := by
      ext g; simp [U]
    rw [e]
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact (((Units.continuous_val.comp (continuous_apply w)).matrix_elem i j).sub
      continuous_const).norm

  have hone : ∀ γ ∈ latticeStab h La,
      ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) ∈ U → γ = 1 := by
    intro γ hγ hγU
    set M := LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) with hM
    have hγLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x ∈ La := by
      intro x hx
      have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul x γ La hx
      rwa [MulAction.mem_stabilizer_iff.1 hγ] at h1
    have hrep : ∀ x : W, ∀ i, v.repr ((γ : W ≃ₗ[E] W) x - x) i =
        ∑ j, (M i j - (1 : Matrix ι ι E) i j) * v.repr x j := by
      intro x i
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i
      simp only [LinearEquiv.coe_coe] at h1
      rw [map_sub, Finsupp.sub_apply, ← h1]
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hM]
    have h1ij : ∀ (w : InfinitePlace E) i j,
        w.embedding ((1 : Matrix ι ι E) i j) = (1 : Matrix ι ι ℂ) i j := by
      intro w i j
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hfix : ∀ s ∈ S, (γ : W ≃ₗ[E] W) s = s := by
      intro s hs
      refine sub_eq_zero.1 (key _ (sub_mem (hγLa s (hSLa s hs)) (hSLa s hs)) fun w i => ?_)
      have entry : ∀ j, ‖w.embedding (M i j - (1 : Matrix ι ι E) i j)‖ < δ := by
        intro j
        have := hγU w i j
        rw [archEmbed_apply_val, Matrix.map_apply] at this
        rwa [map_sub, h1ij]
      have hsum : ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖ ≤
          δ * ∑ j, ‖w.embedding (v.repr s j)‖ := by
        rw [hrep, map_sum, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (entry j).le (norm_nonneg _)
      have hsB : ∑ j, ‖w.embedding (v.repr s j)‖ ≤ B := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ w : InfinitePlace E, ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) hs)
        exact Finset.single_le_sum (f := fun w : InfinitePlace E => ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)
      calc |(d : ℝ)| * ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖
          ≤ |(d : ℝ)| * (δ * B) := by
            gcongr
            exact hsum.trans (mul_le_mul_of_nonneg_left hsB hδpos.le)
        _ = |(d : ℝ)| * δ * B := by ring
        _ < 1 := hdδB
    have hfixLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x = x := by
      intro x hx
      rw [← hS] at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx => exact hfix x hx
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | neg x _ hx => simp [map_neg, hx]
    have hlin : ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) = LinearMap.id :=
      LinearMap.ext_on hLa.span_eq_top fun x hx => hfixLa x hx
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simpa using LinearMap.congr_fun hlin x

  refine discreteTopology_of_isOpen_singleton_one ?_
  have hcont : Continuous fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have e : ({1} : Set (archLatticeGroup h v La)) = (fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)) ⁻¹' U := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl w i j
      simpa using hδpos
    · intro hx
      obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 x.2
      have h1 := hone γ hγ (by rw [hγx]; exact hx)
      apply Subtype.ext
      rw [← hγx, h1, map_one]
      rfl
  rw [e]
  exact hU.preimage hcont

end Discrete

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
