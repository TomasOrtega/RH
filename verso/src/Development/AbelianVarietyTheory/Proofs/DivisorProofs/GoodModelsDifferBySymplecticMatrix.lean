import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ ψ n d X W M M₁ hM hM₁`. Set `ι` to `algebraMap F (AF F)`. Establish `hι : Function.Injective ι` using `AdeleRing.algebraMap_injective (𝓞 F) F`. Set `sp` to `LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)`. Set `Φ₀` to `M.co.e.trans sp.symm`.

Set `Φ₁` to `M₁.co.e.trans sp.symm`. Establish `hΦ₀ : ∀ u, Φ₀ u = Sum.elim (M.co.e u).1 (M.co.e u).2` using `fun u => rfl`. Establish `hΦ₁ : ∀ u, Φ₁ u = Sum.elim (M₁.co.e u).1 (M₁.co.e u).2` using `fun u => rfl`. Set `A : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F)` to `LinearMap.toMatrix' ((Φ₀.symm.trans Φ₁ : _ ≃ₗ[AF F] _) : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] _)`. Establish `hA : ∀ u, A *ᵥ Φ₀ u = Φ₁ u`.

Introduce `u`. Simplify using `[A, LinearMap.toMatrix'_mulVec]`. Establish `hspan : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `U _`.

Rewrite using `[Matrix.matrix_eq_sum_single U]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Generalize the expression as in `U i j = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e`. Establish `: Matrix.single i j (a ⊗ₜ[F] e : AE F E) = a • incM F (Matrix.single i j e)`. Use extensionality with `k l`. Simplify using `only [incM, Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply, inclR]`. Use `split_ifs`.

Simplify using `[TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `add x y hx hy => rw [Matrix.single_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Establish `hspan' : Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) = ⊤`. Rewrite using `[Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]`. Establish `hrat0 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₀ (incM F x) = fun i => ι (w i)`. Introduce `x`.

Take `⟨y, z, h⟩` from `hM.rat x`. Apply the tactic sequence `refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₀, h]; cases i <;> rfl`. Establish `hrat1 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₁ (incM F x) = fun i => ι (w i)`. Introduce `x`. Take `⟨y, z, h⟩` from `hM₁.rat x`.

Apply the tactic sequence `refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₁, h]; cases i <;> rfl`. Set `G : Set ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F)` to `{w | ∃ x, Φ₀ (incM F x) = fun i => ι (w i)}`. Establish `hG : Submodule.span F G = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hfk⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`.

Set `c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F` to `fun i => f (fun j => if i = j then 1 else 0)`. Establish `hfc : ∀ w, f w = ∑ i, w i * c i`. Introduce `w`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f w]`. Simplify using `[c, smul_eq_mul]`.

Establish `hP : ∀ V ∈ Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))), ∑ i, V i * ι (c i) = 0`. Introduce `V hV`. Proceed by induction on `hV using Submodule.span_induction with`. Consider the case `mem V hV`. Take `⟨_, ⟨x, rfl⟩, rfl⟩` from `hV`.

Take `⟨w, hw⟩` from `hrat0 x`. Establish `h1` using `hfk (Submodule.subset_span (show w ∈ G from ⟨x, hw⟩))`. Rewrite `h1` using `[LinearMap.mem_ker, hfc]`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, hw, ← map_mul, ← map_sum, h1, map_zero]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]`. Consider the case `smul a x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]`. Establish `hc : ∀ i, c i = 0`. Introduce `i`. Establish `h1` using `hP (Pi.single i 1) (by rw [hspan']; trivial)`.

Simplify using `[Pi.single_apply] at h1`. Conclude with `hι (by simpa using h1)`. Conclude with `hf0 (LinearMap.ext fun w => by simp [hfc, hc])`. Establish `hrat : ∀ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, ∃ q : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, A *ᵥ (fun i => ι (w i)) = fun i => ι (q i)`. Introduce `w`.

Establish `hw : w ∈ Submodule.span F G` using `hG ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x, hx⟩` from `hw`. Take `⟨q, hq⟩` from `hrat1 x`.

Conclude with `⟨q, (congrArg (A *ᵥ ·) hx).symm.trans ((hA _).trans hq)⟩`. Consider the case `zero => exact ⟨0, by funext i; simp [Matrix.mulVec, dotProduct]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`.

Use `⟨p + q, ?_⟩` and prove the remaining obligations. Establish `: (fun i => ι ((x + y) i)) = (fun i => ι (x i)) + (fun i => ι (y i))` using `by funext i; simp`. Rewrite using `[this, Matrix.mulVec_add, hp, hq]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `smul c x _ hx`. Take `⟨p, hp⟩` from `hx`. Use `⟨c • p, ?_⟩` and prove the remaining obligations. Establish `: (fun i => ι ((c • x) i)) = ι c • (fun i => ι (x i))` using `by funext i; simp`. Rewrite using `[this, Matrix.mulVec_smul, hp]`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Use `choose q hq using fun j : (Fin n × Fin d) ⊕ (Fin n × Fin d) => hrat (Pi.single j 1)`. Set `a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F` to `Matrix.of fun i j => q j i`. Establish `haA : a.map ι = A`.

Use extensionality with `i j`. Establish `h1 : A *ᵥ Pi.single j 1 = fun i => ι (q j i)`. Rewrite using `[← hq j]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `[Pi.single_apply]`. Establish `h2` using `congrFun h1 i`. Rewrite `h2` using `[Matrix.mulVec_single_one]`. Simplify `h2.symm` using `[a]`. Establish `hstd : ∀ w w' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F, w ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ w') = (w ∘ Sum.inl) ⬝ᵥ (w' ∘ Sum.inr) - (w' ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr)`.

Introduce `w w'`. Rewrite using `[Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, mul_comm, sub_eq_add_neg]`. Establish `hform : ∀ u u', Φ₁ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₁ u') = Φ₀ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₀ u')`. Introduce `u u'`.

Rewrite using `[hstd, hstd, hΦ₀, hΦ₀, hΦ₁, hΦ₁]`. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr]`. Rewrite using `[← M.co.form, ← M₁.co.form]`. Establish `hsympA : Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0`. Use extensionality with `i j`.

Establish `key : ∀ N : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F), N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1)`. Introduce `N`. Simplify using `[Matrix.mulVec_single_one]`. Rewrite using `[key (Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A), key (Matrix.fromBlocks 0 1 (-1) 0)]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.

Establish `e1 : ∀ s, A *ᵥ s = Φ₁ (Φ₀.symm s)` using `fun s => by rw [← hA, LinearEquiv.apply_symm_apply]`. Rewrite using `[e1, e1, hform]`. Simplify using the standard rewrite rules. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Apply `Matrix.map_injective hι` to reduce the goal to its premises.

Simplify using `only [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map]`. Rewrite using `[haA]`. Simplify `hsympA` using `[Matrix.map_zero, Matrix.map_one, Matrix.map_neg]`. Introduce `u`. Rewrite using `[show a.map (algebraMap F (AF F)) = A from haA, ← hΦ₀, hA, hΦ₁]`.

Both sides reduce to the same expression.
-/
theorem goodModel_coords_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  intro F E _ _ _ _ _ σ ψ n d X W M M₁ hM hM₁
  classical
  let ι := algebraMap F (AF F)
  have hι : Function.Injective ι := AdeleRing.algebraMap_injective (𝓞 F) F
  let sp := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let Φ₀ := M.co.e.trans sp.symm
  let Φ₁ := M₁.co.e.trans sp.symm
  have hΦ₀ : ∀ u, Φ₀ u = Sum.elim (M.co.e u).1 (M.co.e u).2 := fun u => rfl
  have hΦ₁ : ∀ u, Φ₁ u = Sum.elim (M₁.co.e u).1 (M₁.co.e u).2 := fun u => rfl
  let A : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F) :=
    LinearMap.toMatrix' ((Φ₀.symm.trans Φ₁ : _ ≃ₗ[AF F] _) : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] _)
  have hA : ∀ u, A *ᵥ Φ₀ u = Φ₁ u := by
    intro u; simp [A, LinearMap.toMatrix'_mulVec]

  have hspan : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) = ⊤ := by
    rw [eq_top_iff]; intro U _
    rw [Matrix.matrix_eq_sum_single U]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    generalize U i j = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have : Matrix.single i j (a ⊗ₜ[F] e : AE F E) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply, inclR]
        split_ifs
        · simp [TensorProduct.smul_tmul']
        · simp
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  have hspan' : Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))) = ⊤ := by
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hrat0 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₀ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₀, h]; cases i <;> rfl
  have hrat1 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₁ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM₁.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₁, h]; cases i <;> rfl
  let G : Set ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) := {w | ∃ x, Φ₀ (incM F x) = fun i => ι (w i)}
  have hG : Submodule.span F G = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F := fun i => f (fun j => if i = j then 1 else 0)
    have hfc : ∀ w, f w = ∑ i, w i * c i := by
      intro w; rw [LinearMap.pi_apply_eq_sum_univ f w]; simp [c, smul_eq_mul]
    have hP : ∀ V ∈ Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E))),
        ∑ i, V i * ι (c i) = 0 := by
      intro V hV
      induction hV using Submodule.span_induction with
      | mem V hV =>
        obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hV
        obtain ⟨w, hw⟩ := hrat0 x
        have h1 := hfk (Submodule.subset_span (show w ∈ G from ⟨x, hw⟩))
        rw [LinearMap.mem_ker, hfc] at h1
        simp only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, hw, ← map_mul, ← map_sum, h1, map_zero]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul a x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]
    have hc : ∀ i, c i = 0 := by
      intro i
      have h1 := hP (Pi.single i 1) (by rw [hspan']; trivial)
      simp [Pi.single_apply] at h1
      exact hι (by simpa using h1)
    exact hf0 (LinearMap.ext fun w => by simp [hfc, hc])

  have hrat : ∀ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, ∃ q : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
      A *ᵥ (fun i => ι (w i)) = fun i => ι (q i) := by
    intro w
    have hw : w ∈ Submodule.span F G := hG ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx⟩ := hw
      obtain ⟨q, hq⟩ := hrat1 x
      exact ⟨q, (congrArg (A *ᵥ ·) hx).symm.trans ((hA _).trans hq)⟩
    | zero => exact ⟨0, by funext i; simp [Matrix.mulVec, dotProduct]⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx; obtain ⟨q, hq⟩ := hy
      refine ⟨p + q, ?_⟩
      have : (fun i => ι ((x + y) i)) = (fun i => ι (x i)) + (fun i => ι (y i)) := by funext i; simp
      rw [this, Matrix.mulVec_add, hp, hq]; funext i; simp
    | smul c x _ hx =>
      obtain ⟨p, hp⟩ := hx
      refine ⟨c • p, ?_⟩
      have : (fun i => ι ((c • x) i)) = ι c • (fun i => ι (x i)) := by funext i; simp
      rw [this, Matrix.mulVec_smul, hp]; funext i; simp
  choose q hq using fun j : (Fin n × Fin d) ⊕ (Fin n × Fin d) => hrat (Pi.single j 1)
  let a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F := Matrix.of fun i j => q j i
  have haA : a.map ι = A := by
    ext i j
    have h1 : A *ᵥ Pi.single j 1 = fun i => ι (q j i) := by
      rw [← hq j]; congr 1; funext k; simp [Pi.single_apply]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one] at h2
    simpa [a] using h2.symm
  have hstd : ∀ w w' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      w ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ w') = (w ∘ Sum.inl) ⬝ᵥ (w' ∘ Sum.inr) - (w' ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) := by
    intro w w'
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, mul_comm, sub_eq_add_neg]
  have hform : ∀ u u', Φ₁ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₁ u') = Φ₀ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₀ u') := by
    intro u u'
    rw [hstd, hstd, hΦ₀, hΦ₀, hΦ₁, hΦ₁]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← M.co.form, ← M₁.co.form]
  have hsympA : Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 := by
    ext i j
    have key : ∀ N : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F),
        N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
      intro N; simp [Matrix.mulVec_single_one]
    rw [key (Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A), key (Matrix.fromBlocks 0 1 (-1) 0)]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e1 : ∀ s, A *ᵥ s = Φ₁ (Φ₀.symm s) := fun s => by rw [← hA, LinearEquiv.apply_symm_apply]
    rw [e1, e1, hform]
    simp
  refine ⟨a, ?_, ?_⟩
  · apply Matrix.map_injective hι
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map]
    rw [haA]
    simpa [Matrix.map_zero, Matrix.map_one, Matrix.map_neg] using hsympA
  · intro u
    rw [show a.map (algebraMap F (AF F)) = A from haA, ← hΦ₀, hA, hΦ₁]
    rfl

end GlobalTheory
