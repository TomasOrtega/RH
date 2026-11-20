import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LieMapEqSumIdempotentGen
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Use `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`. Use `S.add_mem ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `S.algebraMap_mem _`.

Conclude with `S.zero_mem`.
-/
private theorem qdet_mem' {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (S : Subalgebra ℂ A) (X : Fin n → Fin n → A)
    (h : ∀ a b, X a b ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

/- English proof (translation)
Set `j : B →ₐ[ℝ] ℂ ⊗[ℝ] B` to `Algebra.TensorProduct.includeRight`. Set `ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A` to `Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)`. Establish `hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x` using `fun c x => (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm`. Set `l' : Matrix (Fin n) (Fin n) R →ₗ[ℝ] ℂ ⊗[ℝ] B` to `j.toLinearMap ∘ₗ l`. Establish `hl' : IsLie l'` using `fun X Y => by`.

Express the relevant statement in the definitionally equal form `j (l X) * j (l Y) - j (l Y) * j (l X) = j (l (X * Y - Y * X))`. Rewrite using `[← hl, map_sub, map_mul, map_mul]`. Take `⟨hrel, hc⟩` from `UpperTheory.gen_glRelations_and_commute_of_isLie R ι n _ D l' hl'`. Use `set w := Formalism.REAL.qdet (gen D l' τ) u with hw`. Establish `h0 : ∀ σ a b, gen D l' σ a b ∈ Subalgebra.centralizer ℂ {w}` using `fun σ a b => by`.

Introduce and unpack `_ rfl`. Distinguish the cases in `e : σ = τ`. Substitute `e` using the available equality. Conclude with `(Formalism.REAL.qDetCentral _ n _ (hrel σ) u a b)`. Use `(qdet_mem' (Subalgebra.centralizer ℂ {gen D l' σ a b}) _ (fun c d => ?_) u _ rfl).symm` and prove the remaining obligations.

Introduce and unpack `_ rfl`. Conclude with `hc σ τ e a b c d`. Establish `h1 : ∀ x : B, j x * w = w * j x` using `fun x => by`. Establish `: Algebra.adjoin ℝ (Set.range l) ≤ (Subalgebra.centralizer ℝ {w}).comap j`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨X, rfl⟩`. Establish `h2 : l' X ∈ Subalgebra.centralizer ℂ {w}`. Rewrite using `[UpperTheory.lieMap_eq_sum_idempotent_gen R ι n _ D l' X]`. Conclude with `sum_mem fun σ _ => sum_mem fun a _ => sum_mem fun b _ => Subalgebra.smul_mem _ (h0 σ a b) _`. Conclude with `h2`.

Conclude with `(this (htop ▸ Algebra.mem_top) w rfl).symm`. Take `⟨p, hp, q, hq, e⟩` from `UpperTheory.V.Fb.exists_re_im w h1`. Establish `h2 : ψ w = Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u`. Rewrite using `[hw, UpperTheory.V.Fb.map_qdet]`. Use `congr 1`.

Use function extensionality and compare the values at `a b`. Conclude with `gen_inter D l' (ρ.toLinearMap ∘ₗ l) τ a b a b ψ.toLinearMap LinearMap.id fun x => (hψ 1 _).trans (one_smul _ _)`. Rewrite using `[← h2, e, map_add, hψ, hψ]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))`.
-/
private theorem aux {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ} {A : Type} [Ring A]
    [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] {B : Type} [Ring B] [Algebra ℝ B] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] B) (hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X))
    (htop : Algebra.adjoin ℝ (Set.range l) = ⊤) (ρ : B →ₐ[ℝ] A) (τ : ι) (u : ℂ) :
    Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u ∈
      Submodule.span ℂ (ρ '' (Subalgebra.center ℝ B : Set B)) := by
  let j : B →ₐ[ℝ] ℂ ⊗[ℝ] B := Algebra.TensorProduct.includeRight
  let ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A := Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)
  have hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x := fun c x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm
  let l' : Matrix (Fin n) (Fin n) R →ₗ[ℝ] ℂ ⊗[ℝ] B := j.toLinearMap ∘ₗ l
  have hl' : IsLie l' := fun X Y => by
    change j (l X) * j (l Y) - j (l Y) * j (l X) = j (l (X * Y - Y * X))
    rw [← hl, map_sub, map_mul, map_mul]
  obtain ⟨hrel, hc⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie R ι n _ D l' hl'
  set w := Formalism.REAL.qdet (gen D l' τ) u with hw
  have h0 : ∀ σ a b, gen D l' σ a b ∈ Subalgebra.centralizer ℂ {w} := fun σ a b => by
    rintro _ rfl
    by_cases e : σ = τ
    · subst e
      exact (Formalism.REAL.qDetCentral _ n _ (hrel σ) u a b)
    · refine (qdet_mem' (Subalgebra.centralizer ℂ {gen D l' σ a b}) _ (fun c d => ?_) u _ rfl).symm
      rintro _ rfl
      exact hc σ τ e a b c d
  have h1 : ∀ x : B, j x * w = w * j x := fun x => by
    have : Algebra.adjoin ℝ (Set.range l) ≤ (Subalgebra.centralizer ℝ {w}).comap j := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨X, rfl⟩
      have h2 : l' X ∈ Subalgebra.centralizer ℂ {w} := by
        rw [UpperTheory.lieMap_eq_sum_idempotent_gen R ι n _ D l' X]
        exact sum_mem fun σ _ => sum_mem fun a _ => sum_mem fun b _ => Subalgebra.smul_mem _ (h0 σ a b) _
      exact h2
    exact (this (htop ▸ Algebra.mem_top) w rfl).symm
  obtain ⟨p, hp, q, hq, e⟩ := UpperTheory.V.Fb.exists_re_im w h1
  have h2 : ψ w = Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u := by
    rw [hw, UpperTheory.V.Fb.map_qdet]
    congr 1
    funext a b
    exact gen_inter D l' (ρ.toLinearMap ∘ₗ l) τ a b a b ψ.toLinearMap LinearMap.id fun x =>
      (hψ 1 _).trans (one_smul _ _)
  rw [← h2, e, map_add, hψ, hψ]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

/- English proof (translation)
Introduce `K _ _ n ι _ D τ u`. Set `l : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] UEnv K n` to `(UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap`. Establish `hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X)` using `fun X Y => by`. Express the relevant statement in the definitionally equal form `UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) - UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) = UniversalEnvelopingAlgebra.ι ℝ (toLie K n (X * Y - Y * X))`. Rewrite using `[← Ring.lie_def, ← LieHom.map_lie]`.

Both sides reduce to the same expression. Establish `htop : Algebra.adjoin ℝ (Set.range l) = ⊤`. Use `eq_top_iff.2 fun z hz => ?_` and prove the remaining obligations. Use `clear hz`. Proceed by induction on `z using UEnv.induction with`.

Consider the case `halg r => exact Subalgebra.algebraMap_mem _ r`. Consider the case `hι X => exact Algebra.subset_adjoin ⟨(toLie K n).symm X, by simp [l]⟩`. Consider the case `hmul a b ha hb => exact mul_mem ha hb`. Consider the case `hadd a b ha hb => exact add_mem ha hb`. Establish `h` using `aux D l hl htop (uAction (K := K) (n := n)) τ u`.

Conclude with `Algebra.span_le_adjoin ℂ _ h`.
-/
theorem UpperTheory.qdet_generates_universalEnveloping_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), capOp D n τ u ∈ Zc K n := by
  intro K _ _ n ι _ D τ u
  let l : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] UEnv K n :=
    (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap
  have hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X) := fun X Y => by
    change UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) -
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) =
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n (X * Y - Y * X))
    rw [← Ring.lie_def, ← LieHom.map_lie]
    rfl
  have htop : Algebra.adjoin ℝ (Set.range l) = ⊤ := by
    refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using UEnv.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X => exact Algebra.subset_adjoin ⟨(toLie K n).symm X, by simp [l]⟩
    | hmul a b ha hb => exact mul_mem ha hb
    | hadd a b ha hb => exact add_mem ha hb
  have h := aux D l hl htop (uAction (K := K) (n := n)) τ u
  exact Algebra.span_le_adjoin ℂ _ h
