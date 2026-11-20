import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeasProj

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Simplify using `[Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
theorem repr_map {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]

/- English proof (translation)
Rewrite using `[(TopK.isHomeomorph_coord S b).isInducing.continuous_iff]`. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_def, repr_map]`. Conclude with `hf.comp ((continuous_apply k).comp (TopK.isHomeomorph_coord R b).continuous)`.
-/
theorem continuous_mapTens {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E) : R ⊗[F] E → S ⊗[F] E) := by
  rw [(TopK.isHomeomorph_coord S b).isInducing.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_map]
  exact hf.comp ((continuous_apply k).comp (TopK.isHomeomorph_coord R b).continuous)

/- English proof (translation)
The claim follows from `continuous_pi fun a => continuous_pi fun i => (continuous_mapTens b f hf).comp ((continuous_apply i).comp (continuous_apply a))`.
-/
theorem continuous_mapTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (fun (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n) (i : Fin M) =>
      Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_mapTens b f hf).comp ((continuous_apply i).comp (continuous_apply a))

omit [IsTopologicalRing S] [TopologicalSpace S] [CommRing S] [Algebra F S] in

def tupHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → R) :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => TopK.coordHomeo R b

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
The claim follows from `continuous_fst`.
-/
theorem continuous_fstA : Continuous (fstA F) := continuous_fst

/- English proof (translation)
The claim follows from `continuous_snd`.
-/
theorem continuous_sndA : Continuous (sndA F) := continuous_snd

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval v`.
-/
theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

/- English proof (translation)
The claim follows from `repr_map b (fstA F) _ k`.
-/
theorem coord_projInf {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

/- English proof (translation)
The claim follows from `repr_map b (sndA F) _ k`.
-/
theorem coord_projFin {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (projFin X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 :=
  repr_map b (sndA F) _ k

/- English proof (translation)
The claim follows from `repr_map b (evalV F v) _ k`.
-/
theorem coord_projV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v X a i) k =
      ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v :=
  repr_map b (evalV F v) _ k

/- English proof (translation)
Use extensionality with `Y`. Simplify using `only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]`. Both sides reduce to the same expression.
-/
theorem latV_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      tupHomeo b n M ⁻¹' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext Y
  simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

/- English proof (translation)
Establish `hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))` using `isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))`. Rewrite using `[latV_eq, (tupHomeo b n M).isCompact_preimage]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc`.
-/
theorem isCompact_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  rw [latV_eq, (tupHomeo b n M).isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc

/- English proof (translation)
Establish `ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Rewrite using `[latV_eq]`. Use `IsOpen.preimage (tupHomeo b n M).continuous ?_` and prove the remaining obligations. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho`.
-/
theorem isOpen_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [latV_eq]
  refine IsOpen.preimage (tupHomeo b n M).continuous ?_
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => ho

/- English proof (translation)
Simplify using `only [latV, Set.mem_setOf_eq, coord_projV]`.
-/
theorem projV_mem_latV_iff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ↔
      ∀ a i k, ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v ∈
        v.adicCompletionIntegers F := by
  simp only [latV, Set.mem_setOf_eq, coord_projV]

end Adelic

section Adelic2

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `hA : IsOpen {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)`. Establish `hE : (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k, (fun X : Fin n → Fin M → AF F ⊗[F] E => sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹' {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}`. Use extensionality with `X`. Simplify using `only [intOff, Set.mem_setOf_eq, projV_mem_latV_iff, coord_projFin, Set.mem_iInter, Set.mem_preimage]`. Conclude with `⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩`.

Rewrite using `[hE]`. Use `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => hA.preimage (continuous_sndA.comp ?_)` and prove the remaining obligations. Conclude with `(continuous_apply k).comp ((TopK.isHomeomorph_coord (AF F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))`.
-/
theorem isOpen_intOff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := by
  have hA : IsOpen {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v => v ∉ S)
  have hE : (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [intOff, Set.mem_setOf_eq, projV_mem_latV_iff, coord_projFin, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [hE]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => hA.preimage (continuous_sndA.comp ?_)
  exact (continuous_apply k).comp ((TopK.isHomeomorph_coord (AF F) b).continuous.comp
    ((continuous_apply i).comp (continuous_apply a)))

/- English proof (translation)
Simplify using `only [projV_mem_latV_iff, Filter.eventually_all]`. Introduce `a i k`. Conclude with `((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k).2`.
-/
theorem eventually_mem_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  simp only [projV_mem_latV_iff, Filter.eventually_all]
  intro a i k
  exact ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k).2

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Apply `(Algebra.TensorProduct.basis (AF F) b).repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Use `Prod.ext (α := Ainf F) (β := Af F) ?_ ?_` and prove the remaining obligations. Rewrite using `[← coord_projInf, ← coord_projInf, h1]`.

Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Establish `e : ∀ T : Fin n → Fin M → AF F ⊗[F] E, ((Algebra.TensorProduct.basis (AF F) b).repr (T a i) k).2 v = (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin T) a i) k` using `fun T => by`. Rewrite using `[coord_projV, coord_projFin]`. Establish `h3 : (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k = (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin Y) a i) k` using `by rw [h2 v]`. Conclude with `(e X).trans (h3.trans (e Y).symm)`.
-/
theorem ext_proj {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (h1 : projInf X = projInf Y) (h2 : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  refine Prod.ext (α := Ainf F) (β := Af F) ?_ ?_
  · rw [← coord_projInf, ← coord_projInf, h1]
  · refine Subtype.ext (funext fun v => ?_)
    have e : ∀ T : Fin n → Fin M → AF F ⊗[F] E, ((Algebra.TensorProduct.basis (AF F) b).repr (T a i) k).2 v =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin T) a i) k := fun T => by
      rw [coord_projV, coord_projFin]
    have h3 : (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin Y) a i) k := by rw [h2 v]
    exact (e X).trans (h3.trans (e Y).symm)

def glueFin (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in Filter.cofinite, z v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨z, h⟩ : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)

/- English proof (translation)
Establish `ev : ∀ a i k, ∀ᶠ v in Filter.cofinite, (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k ∈ v.adicCompletionIntegers F` using `fun a i k => hZ.mono fun v hv => hv a i k`. Set `x : Fin n → Fin M → Fin d → AF F` to `fun a i k => pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k) (glueFin (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k) (ev a i k))`. Set `X : Fin n → Fin M → AF F ⊗[F] E` to `fun a i => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (x a i)`. Establish `hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = x a i k` using `fun a i k => congrFun ((Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (x a i)) k`. Use `⟨X, ?_, fun v => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a i`. Apply `(Algebra.TensorProduct.basis (Ainf F) b).repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Rewrite using `[coord_projInf, hX]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `a i`. Apply `(Algebra.TensorProduct.basis (Fv F v) b).repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Rewrite using `[coord_projV, coord_projFin, hX]`. Both sides reduce to the same expression.
-/
theorem exists_glue {d n M : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → Ainf F ⊗[F] E)
    (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E))
    (hZ : ∀ᶠ v in Filter.cofinite, Z v ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v := by
  have ev : ∀ a i k, ∀ᶠ v in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k ∈ v.adicCompletionIntegers F :=
    fun a i k => hZ.mono fun v hv => hv a i k
  let x : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k)
      (glueFin (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k) (ev a i k))
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i =>
    (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (x a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = x a i k := fun a i k =>
    congrFun ((Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (x a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
    ext k
    rw [coord_projInf, hX]
    rfl
  · funext a i
    apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
    ext k
    rw [coord_projV, coord_projFin, hX]
    rfl

/- English proof (translation)
Unfold `sizeTup sizeInf`. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun v _ => continuous_norm.comp ?_` and prove the remaining obligations. Conclude with `(continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp ((continuous_apply k).comp ((TopK.isHomeomorph_coord (Ainf F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))`.
-/
theorem continuous_sizeTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  unfold sizeTup sizeInf
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun v _ => continuous_norm.comp ?_
  exact (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp
    ((continuous_apply k).comp ((TopK.isHomeomorph_coord (Ainf F) b).continuous.comp
      ((continuous_apply i).comp (continuous_apply a))))

end Adelic2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ d b n M`. Conclude with `⟨continuous_mapTup b (fstA F) continuous_fstA, continuous_mapTup b (sndA F) continuous_sndA, fun v => continuous_mapTup b (evalV F v) (continuous_evalV v), fun v => ⟨isCompact_latV b v, isOpen_latV b v⟩, fun S => isOpen_intOff b S, fun X => eventually_mem_latV b X, fun X Y => ext …`.
-/
theorem proj_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨continuous_mapTup b (fstA F) continuous_fstA, continuous_mapTup b (sndA F) continuous_sndA,
    fun v => continuous_mapTup b (evalV F v) (continuous_evalV v),
    fun v => ⟨isCompact_latV b v, isOpen_latV b v⟩, fun S => isOpen_intOff b S,
    fun X => eventually_mem_latV b X, fun X Y => ext_proj b X Y,
    fun Y Z h => exists_glue b Y Z h, continuous_sizeTup b⟩

end GlobalTheory.CompanionTheory.SW.MeasProj
