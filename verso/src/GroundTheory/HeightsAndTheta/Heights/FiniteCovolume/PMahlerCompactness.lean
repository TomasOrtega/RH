import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedGenerators
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLenCauchySchwarz
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StGramDetermines
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedInverseCompact

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1 : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding`. Rewrite using `[← unitaryGroupEquivMatrix_apply]`. Both sides reduce to the same expression. Establish `h2` using `LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x`. Rewrite `h2` using `[LinearEquiv.coe_coe]`.

Rewrite using `[h1]`. Use extensionality with `i`. Simplify using `only [vecAt]`. Rewrite using `[← h2, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem vecAt_unitary (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup) (x : W)
    (w : InfinitePlace E) :
    vecAt v ((γ : W ≃ₗ[E] W) x) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w := by
  have h1 : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  have h2 := LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x
  rw [LinearEquiv.coe_coe] at h2
  rw [h1]
  ext i
  simp only [vecAt]
  rw [← h2, RingHom.map_mulVec]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [invApply, vecAt_unitary, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Matrix.mulVec_mulVec]`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
theorem invApply_archEmbed_mul (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (g : archUnitary h v) (x : W) :
    invApply (archEmbed h v γ * g) (vecAt v ((γ : W ≃ₗ[E] W) x)) = invApply g (vecAt v x) := by
  funext w
  simp only [invApply, vecAt_unitary, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
    Matrix.mulVec_mulVec]
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `M D t ht`. Take `⟨n, C, hC⟩` from `hB M D t ht`. Set `P : Set (AddSubgroup W × (Fin n → W))` to `{p | IsDIntegral h D p.1 ∧ AddSubgroup.closure (Set.range p.2) = p.1 ∧ ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}`. Set `gr : (Fin n → W) → Matrix (Fin n) (Fin n) E` to `fun e a b => h.toSesq (e a) (e b)`. Set `T : Set (Matrix (Fin n) (Fin n) E)` to `(fun p => gr p.2) '' P`.

Establish `hT : T.Finite`. Use `(Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C}) fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩`. Introduce `a _ b _`. Establish `hmem : ∀ c, p.2 c ∈ p.1` using `fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩`.

Use `Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩` and prove the remaining obligations. Establish `h1` using `hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)`. Rewrite `h1` using `[InfinitePlace.norm_embedding_eq, InfinitePlace.apply]`. Conclude with `h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))`. Establish `hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H` using `fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩`.

Use `choose! rep hrepP hrepG using hrep`. Set `Kset : (Fin n → W) → Set (archUnitary h v)` to `fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}`. Use `⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2, hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩` and prove the remaining obligations. Take `⟨hD, hcl, -⟩` from `hrepP H hH`. Establish `hsp` using `hD.isLattice.span_eq_top`.

Rewrite `hsp` using `[← hcl]`. Rewrite using `[eq_top_iff, ← hsp]`. Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations. Conclude with `(AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2 Submodule.subset_span hx`. Introduce `La g hLa hmin`.

Take `⟨e, he, heC⟩` from `hC La g hLa hmin`. Establish `hH : gr e ∈ T` using `⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩`. Take `⟨hD', hcl', -⟩` from `hrepP _ hH`. Establish `hgr` using `hrepG _ hH`. Take `⟨γ, hγ⟩` from `hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice) fun a b => (congrFun (congrFun hgr a) b).symm`.

Use `⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩` and prove the remaining obligations. Use `show (rep (gr e)).1 = γ • La`. Rewrite using `[← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]`. Use `erw [AddMonoidHom.map_closure]`. Rewrite using `[← Set.range_comp]`.

Conclude with `congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)`. Use `show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C`. Rewrite using `[← hγ a, invApply_archEmbed_mul]`. Conclude with `heC a`.
-/
theorem MahlerCompactness.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by
  intro M D t ht
  obtain ⟨n, C, hC⟩ := hB M D t ht

  let P : Set (AddSubgroup W × (Fin n → W)) := {p | IsDIntegral h D p.1 ∧
    AddSubgroup.closure (Set.range p.2) = p.1 ∧
      ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}
  let gr : (Fin n → W) → Matrix (Fin n) (Fin n) E := fun e a b => h.toSesq (e a) (e b)
  let T : Set (Matrix (Fin n) (Fin n) E) := (fun p => gr p.2) '' P
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C})
      fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_
    rintro _ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩
    intro a _ b _
    have hmem : ∀ c, p.2 c ∈ p.1 := fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩
    refine Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩
    have h1 := hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))
  have hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H := fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩
  choose! rep hrepP hrepG using hrep
  let Kset : (Fin n → W) → Set (archUnitary h v) :=
    fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  refine ⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2,
    hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩
  · obtain ⟨hD, hcl, -⟩ := hrepP H hH
    have hsp := hD.isLattice.span_eq_top
    rw [← hcl] at hsp
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    exact (AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2
      Submodule.subset_span hx
  · intro La g hLa hmin
    obtain ⟨e, he, heC⟩ := hC La g hLa hmin
    have hH : gr e ∈ T := ⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩
    obtain ⟨hD', hcl', -⟩ := hrepP _ hH
    have hgr := hrepG _ hH
    obtain ⟨γ, hγ⟩ := hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice)
      fun a b => (congrFun (congrFun hgr a) b).symm
    refine ⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩
    · show (rep (gr e)).1 = γ • La
      rw [← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]
      erw [AddMonoidHom.map_closure]
      rw [← Set.range_comp]
      exact congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)
    · show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C
      rw [← hγ a, invApply_archEmbed_mul]
      exact heC a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
