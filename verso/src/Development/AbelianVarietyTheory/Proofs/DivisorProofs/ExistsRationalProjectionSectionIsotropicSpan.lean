import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ κ _ S hS`. Set `ι` to `algebraMap F (AF F)`. Set `Φ : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F))` to `LinearMap.prodMap ((Algebra.linearMap F (AF F)).compLeft κ) ((Algebra.linearMap F (AF F)).compLeft κ)`. Set `T : Submodule F ((κ → F) × (κ → F))` to `(S.restrictScalars F).comap Φ`. Establish `hT : ∀ y z, (y, z) ∈ T ↔ ((fun i => ι (y i)), (fun i => ι (z i))) ∈ S` using `fun y z => Iff.rfl`.

Set `f : T →ₗ[F] (κ → F)` to `LinearMap.fst F _ _ ∘ₗ T.subtype`. Set `L₁` to `LinearMap.range f`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl L₁`. Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)`. Set `π : (κ → F) →ₗ[F] (κ → F)` to `C.subtype ∘ₗ Submodule.linearProjOfIsCompl C L₁ hC.symm`.

Set `q : (κ → F) →ₗ[F] (κ → F)` to `LinearMap.snd F _ _ ∘ₗ T.subtype ∘ₗ g ∘ₗ Submodule.linearProjOfIsCompl L₁ C hC`. Establish `hπ : ∀ y, π y = 0 ↔ y ∈ L₁`. Introduce `y`. Simplify using `only [π, LinearMap.comp_apply, Submodule.coe_subtype, ZeroMemClass.coe_eq_zero]`. Conclude with `Submodule.linearProjOfIsCompl_apply_eq_zero_iff hC.symm`.

Establish `hq : ∀ y ∈ L₁, (y, q y) ∈ T`. Introduce `y hy`. Establish `h1 : Submodule.linearProjOfIsCompl L₁ C hC y = ⟨y, hy⟩` using `Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩`. Establish `h2 : f.rangeRestrict (g ⟨y, hy⟩) = ⟨y, hy⟩` using `LinearMap.congr_fun hg ⟨y, hy⟩`. Establish `h3 : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)).1 = y`.

Use `congrArg Subtype.val h2` as an intermediate fact. Simplify `this` using `[f]`. Establish `hm` using `(g ⟨y, hy⟩).2`. Establish `e : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)) = (y, q y)` using `by ext1`. Conclude with `h3`.

Simplify using `[q, h1]`. Rewrite using `[← e]`. Conclude with `hm`. Establish `hL : ∀ y z, (y, z) ∈ T → y ∈ L₁` using `fun y z h => ⟨⟨(y, z), h⟩, rfl⟩`. Establish `hmv : ∀ (M : Matrix κ κ F) (v : κ → F), (M.map ι) *ᵥ (fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i)`.

Introduce `M v`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec ι M v i).symm`. Use `⟨LinearMap.toMatrix' π, LinearMap.toMatrix' q, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Set `A : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] (κ → AF F)` to `(Matrix.mulVecLin ((LinearMap.toMatrix' π).map ι)) ∘ₗ LinearMap.fst _ _ _`. Establish `hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F, s = (fun i => ι (y i), fun i => ι (z i))} ≤ LinearMap.ker A`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨hs', y, z, rfl⟩`. Establish `hy : y ∈ L₁` using `hL y z hs'`.

Establish `h0 : π y = 0` using `(hπ y).2 hy`. Use `show (LinearMap.toMatrix' π).map ι *ᵥ (fun i => ι (y i)) = 0`. Rewrite using `[hmv, LinearMap.toMatrix'_mulVec, h0]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Conclude with `hle (hS hs)`. Introduce `s hs`. Set `B : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))` to `LinearMap.prod (LinearMap.fst _ _ _) ((Matrix.mulVecLin ((LinearMap.toMatrix' q).map ι)) ∘ₗ LinearMap.fst _ _ _)`. Establish `hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F, s = (fun i => ι (y i), fun i => ι (z i))} ≤ S.comap B`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨hs', y, z, rfl⟩`. Establish `hy : y ∈ L₁` using `hL y z hs'`. Use `show ((fun i => ι (y i)), (LinearMap.toMatrix' q).map ι *ᵥ (fun i => ι (y i))) ∈ S`. Rewrite using `[hmv, LinearMap.toMatrix'_mulVec]`. Conclude with `hq y hy`.

Conclude with `hle (hS hs)`. Introduce `ξ hξ`. Rewrite `hξ` using `[LinearMap.toMatrix'_mulVec]`. Establish `hx : ξ ∈ L₁` using `(hπ ξ).1 hξ`. Rewrite using `[LinearMap.toMatrix'_mulVec]`.

Conclude with `hq ξ hx`.
-/
theorem rational_proj_section_of_span : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  intro F _ _ κ _ S hS
  classical
  let ι := algebraMap F (AF F)
  let Φ : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    LinearMap.prodMap ((Algebra.linearMap F (AF F)).compLeft κ) ((Algebra.linearMap F (AF F)).compLeft κ)
  let T : Submodule F ((κ → F) × (κ → F)) := (S.restrictScalars F).comap Φ
  have hT : ∀ y z, (y, z) ∈ T ↔ ((fun i => ι (y i)), (fun i => ι (z i))) ∈ S := fun y z => Iff.rfl
  let f : T →ₗ[F] (κ → F) := LinearMap.fst F _ _ ∘ₗ T.subtype
  let L₁ := LinearMap.range f
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L₁
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  let π : (κ → F) →ₗ[F] (κ → F) := C.subtype ∘ₗ Submodule.linearProjOfIsCompl C L₁ hC.symm
  let q : (κ → F) →ₗ[F] (κ → F) := LinearMap.snd F _ _ ∘ₗ T.subtype ∘ₗ g ∘ₗ Submodule.linearProjOfIsCompl L₁ C hC
  have hπ : ∀ y, π y = 0 ↔ y ∈ L₁ := by
    intro y
    simp only [π, LinearMap.comp_apply, Submodule.coe_subtype, ZeroMemClass.coe_eq_zero]
    exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff hC.symm
  have hq : ∀ y ∈ L₁, (y, q y) ∈ T := by
    intro y hy
    have h1 : Submodule.linearProjOfIsCompl L₁ C hC y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩
    have h2 : f.rangeRestrict (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hg ⟨y, hy⟩
    have h3 : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)).1 = y := by
      have := congrArg Subtype.val h2
      simpa [f] using this
    have hm := (g ⟨y, hy⟩).2
    have e : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)) = (y, q y) := by
      ext1
      · exact h3
      · simp [q, h1]
    rw [← e]; exact hm
  have hL : ∀ y z, (y, z) ∈ T → y ∈ L₁ := fun y z h => ⟨⟨(y, z), h⟩, rfl⟩
  have hmv : ∀ (M : Matrix κ κ F) (v : κ → F),
      (M.map ι) *ᵥ (fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i) := by
    intro M v; funext i
    exact (RingHom.map_mulVec ι M v i).symm
  refine ⟨LinearMap.toMatrix' π, LinearMap.toMatrix' q, ?_, ?_, ?_⟩
  · intro s hs
    let A : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] (κ → AF F) :=
      (Matrix.mulVecLin ((LinearMap.toMatrix' π).map ι)) ∘ₗ LinearMap.fst _ _ _
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ LinearMap.ker A := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      have h0 : π y = 0 := (hπ y).2 hy
      show (LinearMap.toMatrix' π).map ι *ᵥ (fun i => ι (y i)) = 0
      rw [hmv, LinearMap.toMatrix'_mulVec, h0]
      funext i; simp
    exact hle (hS hs)
  · intro s hs
    let B : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) :=
      LinearMap.prod (LinearMap.fst _ _ _)
        ((Matrix.mulVecLin ((LinearMap.toMatrix' q).map ι)) ∘ₗ LinearMap.fst _ _ _)
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ S.comap B := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      show ((fun i => ι (y i)), (LinearMap.toMatrix' q).map ι *ᵥ (fun i => ι (y i))) ∈ S
      rw [hmv, LinearMap.toMatrix'_mulVec]
      exact hq y hy
    exact hle (hS hs)
  · intro ξ hξ
    rw [LinearMap.toMatrix'_mulVec] at hξ
    have hx : ξ ∈ L₁ := (hπ ξ).1 hξ
    rw [LinearMap.toMatrix'_mulVec]
    exact hq ξ hx

end GlobalTheory
