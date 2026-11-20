import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Simplify using `[Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
theorem repr_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]

end Coord

section Box

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `R` to `fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F`. Set `A` to `fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Establish `hAo : ∀ v, IsOpen (A v)` using `fun v => Valued.isOpen_valuationSubring _`. Establish `hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)`. Rewrite using `[Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]`.

Conclude with `S.finite_toSet`. Establish `hemb` using `RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF`. Establish `hcoe` using `RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A) (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)`. Set `K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)))` to `{x | ∀ v, x v ∈ C v}`. Establish `hK : IsCompact K`.

Rewrite using `[hcoe.isCompact_iff]`. Establish `: (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ v _`.

Conclude with `hy v`. Introduce `hx`. Use `⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩, fun v => hx v (Set.mem_univ v), rfl⟩` and prove the remaining obligations. Rewrite using `[this]`. Conclude with `isCompact_univ_pi hC`.

Establish `himg` using `hK.image hemb.continuous`. Establish `hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v` using `Filter.eventually_principal.2 fun v hv => hS v hv (hy v)`. Conclude with `⟨⟨y, hy'⟩, hy, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩ v`. Conclude with `hx v`. Rewrite using `[hset]`.

Conclude with `himg`.
-/
theorem isCompact_box (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v, IsCompact (C v))
    (hS : ∀ v, v ∉ S → C v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    IsCompact {y : Af F | ∀ v, y v ∈ C v} := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF
  have hcoe := RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)
  let K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) :=
    {x | ∀ v, x v ∈ C v}
  have hK : IsCompact K := by
    rw [hcoe.isCompact_iff]
    have : (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hx
        refine ⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩,
          fun v => hx v (Set.mem_univ v), rfl⟩
    rw [this]
    exact isCompact_univ_pi hC
  have himg := hK.image hemb.continuous
  have hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v :=
        Filter.eventually_principal.2 fun v hv => hS v hv (hy v)
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      exact hx v
  rw [hset]
  exact himg

end Box

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
The claim follows from `repr_map b (evalV F v) (X a i) k`.
-/
theorem coord_projV (v : HeightOneSpectrum (𝓞 F)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → Af F ⊗[F] E) (a : Fin 1) (i : Fin M) (k : Fin d) :
    coordH (Fv F v) b (projV v X a i) k = (coordH (Af F) b (X a i) k) v :=
  repr_map b (evalV F v) (X a i) k

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Establish `h : (fun X : Fin 1 → Fin M → Af F ⊗[F] E => projV v X a i) = fun X => (coordH (Fv F v) b).symm (fun k => (coordH (Af F) b (X a i) k) v)`. Use function extensionality and compare the values at `X`. Apply `(coordH (Fv F v) b).injective` to reduce the goal to its premises. Rewrite using `[Homeomorph.apply_symm_apply]`.

Use function extensionality and compare the values at `k`. Conclude with `coord_projV v b X a i k`. Rewrite using `[h]`. Use `(coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)` and prove the remaining obligations. Conclude with `(RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp ((coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))`.
-/
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (projV v : (Fin 1 → Fin M → Af F ⊗[F] E) → Fin 1 → Fin M → Fv F v ⊗[F] E) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h : (fun X : Fin 1 → Fin M → Af F ⊗[F] E => projV v X a i) = fun X =>
      (coordH (Fv F v) b).symm (fun k => (coordH (Af F) b (X a i) k) v) := by
    funext X
    apply (coordH (Fv F v) b).injective
    rw [Homeomorph.apply_symm_apply]
    funext k
    exact coord_projV v b X a i k
  rw [h]
  refine (coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)
  exact (RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp
    ((coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))

/- English proof (translation)
Use `forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_` and prove the remaining obligations. Rewrite using `[← coord_projV v b X a i k]`. Both sides reduce to the same expression.
-/
theorem projV_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → Af F ⊗[F] E) :
    projV v X ∈ latV b v ↔ ∀ a i k, (coordH (Af F) b (X a i) k) v ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_
  rw [← coord_projV v b X a i k]
  rfl

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))

include b in

/- English proof (translation)
Establish `h : boxF A = ⋂ v, projV v ⁻¹' A v`. Use extensionality with `X`. Simplify using `[boxF]`. Rewrite using `[h]`. Use `isClosed_iInter fun v => ?_` and prove the remaining obligations.

Use `haveI : T2Space (Fv F v ⊗[F] E) := (coordH (Fv F v) b).isEmbedding.t2Space`. Conclude with `(hA v).isClosed.preimage (continuous_projV v b)`.
-/
theorem isClosed_boxF (hA : ∀ v, IsCompact (A v)) : IsClosed (boxF A) := by
  have h : boxF A = ⋂ v, projV v ⁻¹' A v := by
    ext X
    simp [boxF]
  rw [h]
  refine isClosed_iInter fun v => ?_
  haveI : T2Space (Fv F v ⊗[F] E) := (coordH (Fv F v) b).isEmbedding.t2Space
  exact (hA v).isClosed.preimage (continuous_projV v b)

/- English proof (translation)
Establish `hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _`. Establish `hI : IsOpen {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k, coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}}`. Establish `e : {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k, coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} = ⋂ a, ⋂ i, ⋂ k, (fun X : Fin 1 → Fin M → Af F ⊗[F] E => coordH (Af F) b (X a i) k) ⁻¹' {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers …`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]`.

Rewrite using `[e]`. Use `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_` and prove the remaining obligations. Establish `hc : Continuous fun X : Fin 1 → Fin M → Af F ⊗[F] E => coordH (Af F) b (X a i) k` using `(continuous_apply k).comp ((coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))`. Conclude with `hT.preimage hc`. Establish `h : boxF A = {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k, coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩ ⋂ v ∈ S, projV v ⁻¹' A v`.

Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Use `⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩` and prove the remaining obligations. Use `hX v` as an intermediate fact.

Rewrite `this` using `[hS v hv]`. Conclude with `(projV_mem_latV v b X).1 this a i k`. Introduce and unpack `⟨h1, h2⟩ v`. Distinguish the cases in `hv : v ∈ S`. Conclude with `Set.mem_iInter₂.1 h2 v hv`.

Rewrite using `[hS v hv]`. Conclude with `(projV_mem_latV v b X).2 fun a i k => h1 a i k v hv`. Rewrite using `[h]`. Conclude with `hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))`.
-/
theorem isOpen_boxF (hA : ∀ v, IsOpen (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) : IsOpen (boxF A) := by
  have hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hI : IsOpen {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k,
      coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} := by
    have e : {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k,
        coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} =
        ⋂ a, ⋂ i, ⋂ k, (fun X : Fin 1 → Fin M → Af F ⊗[F] E => coordH (Af F) b (X a i) k) ⁻¹'
          {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun X : Fin 1 → Fin M → Af F ⊗[F] E => coordH (Af F) b (X a i) k :=
      (continuous_apply k).comp
        ((coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))
    exact hT.preimage hc
  have h : boxF A = {X : Fin 1 → Fin M → Af F ⊗[F] E | ∀ a i k,
      coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩
      ⋂ v ∈ S, projV v ⁻¹' A v := by
    ext X
    constructor
    · intro hX
      refine ⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩
      have := hX v
      rw [hS v hv] at this
      exact (projV_mem_latV v b X).1 this a i k
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter₂.1 h2 v hv
      · rw [hS v hv]
        exact (projV_mem_latV v b X).2 fun a i k => h1 a i k v hv
  rw [h]
  exact hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))

/- English proof (translation)
Set `B : Fin 1 → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)` to `fun a i k v => (fun Y : Fin 1 → Fin M → Fv F v ⊗[F] E => coordH (Fv F v) b (Y a i) k) '' A v`. Establish `hB : ∀ a i k v, IsCompact (B a i k v)` using `fun a i k v => (hA v).image ((continuous_apply k).comp ((coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))`. Establish `hBS : ∀ a i k v, v ∉ S → B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Introduce and unpack `a i k v hv _ ⟨Y, hY, rfl⟩`. Rewrite `hY` using `[hS v hv]`.

Conclude with `hY a i k`. Set `eW : (Fin 1 → Fin M → Af F ⊗[F] E) ≃ₜ (Fin 1 → Fin M → Fin d → Af F)` to `Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => coordH (Af F) b`. Establish `hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k => {y : Af F | ∀ v, y v ∈ B a i k v})` using `eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i => isCompact_univ_pi fun k => isCompact_box S (B a i k) (hB a i k) (hBS a i k))`. Use `hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_` and prove the remaining obligations. Conclude with `⟨projV v X, hX v, coord_projV v b X a i k⟩`.
-/
theorem isCompact_boxF (hA : ∀ v, IsCompact (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    IsCompact (boxF A) := by
  let B : Fin 1 → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun a i k v => (fun Y : Fin 1 → Fin M → Fv F v ⊗[F] E => coordH (Fv F v) b (Y a i) k) '' A v
  have hB : ∀ a i k v, IsCompact (B a i k v) := fun a i k v =>
    (hA v).image ((continuous_apply k).comp
      ((coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))
  have hBS : ∀ a i k v, v ∉ S →
      B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro a i k v hv _ ⟨Y, hY, rfl⟩
    rw [hS v hv] at hY
    exact hY a i k
  let eW : (Fin 1 → Fin M → Af F ⊗[F] E) ≃ₜ (Fin 1 → Fin M → Fin d → Af F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => coordH (Af F) b
  have hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k =>
      {y : Af F | ∀ v, y v ∈ B a i k v}) :=
    eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun k => isCompact_box S (B a i k) (hB a i k) (hBS a i k))
  refine hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_
  exact ⟨projV v X, hX v, coord_projV v b X a i k⟩

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
