import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Rewrite `hg` using `[mir_Kset_eq]`. Take `⟨hu, hc⟩` from `hg`. Use `show gᴴ * Jm ε * g = Jm ε`. Establish `h1 : gᴴ * g = 1`. Simplify `Matrix.mem_unitaryGroup_iff'.mp hu` using `[Matrix.star_eq_conjTranspose]`.

Rewrite using `[Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem propsSchur_kset_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ UJset ε := by
  rw [mir_Kset_eq] at hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Jm ε * g = Jm ε
  have h1 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

/- English proof (translation)
Establish `hS` using `data_isKTypeOf hgap hσ hD hV hc hVK`. Establish `htop` using `data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0`. Establish `hlow` using `data_lowK_eq hgap hσ hD hV hc hVK`. Use `set S := V.map D.subtype with hSdef`. Take `⟨hfd, hKs, hirrK, ⟨v0, hv0S, hv0, hv0w⟩, hcd⟩` from `hS`.

Establish `hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε` using `fun g hg => propsSchur_kset_mem hg`. Set `N : Submodule ℂ H` to `S ⊓ LinearMap.ker (A : H →ₗ[ℂ] H)`. Establish `hNK : Formalism.MainNotions.S.IsKStableOn ε σ N`. Introduce `g hg v hv`. Use `⟨hKs g hg v hv.1, ?_⟩` and prove the remaining obligations.

Establish `h2 : A v = 0` using `by simpa using hv.2`. Use `show (A : H →ₗ[ℂ] H) (σ g v) = 0`. Simplify using `[hA g (hKU g hg), h2]`. Break down `hirrK N inf_le_left hNK with hN | hN` into its components or cases. Establish `hinj : ∀ x ∈ S, A x = 0 → x = 0` using `fun x hx h0 => by`.

Establish `hxN : x ∈ N` using `⟨hx, by simpa using h0⟩`. Rewrite `hxN` using `[hN]`. Simplify using `using hxN`. Set `T : Submodule ℂ H` to `S.map (A : H →ₗ[ℂ] H)`. Establish `hT : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) T`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hfd infer_instance`. Introduce `g hg w hw`. Take `⟨x, hx, rfl⟩` from `hw`. Conclude with `⟨σ g x, hKs g hg x hx, by simp [hA g (hKU g hg)]⟩`.

Introduce `S' hS'T hS'K`. Set `P : Submodule ℂ H` to `S ⊓ S'.comap (A : H →ₗ[ℂ] H)`. Establish `hPK : Formalism.MainNotions.S.IsKStableOn ε σ P`. Introduce `g hg v hv`. Use `⟨hKs g hg v hv.1, ?_⟩` and prove the remaining obligations.

Establish `h2 : A v ∈ S'` using `hv.2`. Use `show A (σ g v) ∈ S'`. Rewrite using `[hA g (hKU g hg)]`. Conclude with `hS'K g hg _ h2`. Break down `hirrK P inf_le_left hPK with hP | hP` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Take `⟨x, hx, rfl⟩` from `hS'T hw`. Establish `hxP : x ∈ P` using `⟨hx, hw⟩`.

Rewrite `hxP` using `[hP]`. Establish `: x = 0` using `by simpa using hxP`. Simplify using `[this]`. Use `right`. Use `le_antisymm hS'T ?_` and prove the remaining obligations.

Introduce and unpack `w ⟨x, hx, rfl⟩`. Establish `hxP : x ∈ P` using `hP ▸ hx`. Conclude with `hxP.2`. Use `⟨A v0, ⟨v0, hv0S, rfl⟩, fun h => hv0 (hinj v0 hv0S h), ?_⟩` and prove the remaining obligations. Introduce `θ hθ`.

Rewrite using `[← hA _ (hKU _ hθ), hv0w θ hθ, map_smul]`. Introduce `μ w hw hw0 hww`. Take `⟨x, hx, rfl⟩` from `hw`. Use `hcd μ x hx (fun h => hw0 (by simp [h])) ?_` and prove the remaining obligations. Introduce `θ hθ`.

Establish `h1` using `hww θ hθ`. Establish `h3 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x - Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x) = 0`. Rewrite using `[map_sub, map_smul, hA _ (hKU _ hθ)]`. Conclude with `sub_eq_zero.mpr h1`. Establish `hmem : σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x - Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x ∈ S` using `S.sub_mem (hKs _ hθ x hx) (S.smul_mem _ hx)`.

Conclude with `sub_eq_zero.mp (hinj _ hmem h3)`. Establish `hTle : T ≤ closGen E V` using `by rw [htop]; exact le_top`. Establish `hTS` using `hlow T hTle hT`. Introduce `x hx`. Rewrite using `[← hTS]`.

Conclude with `⟨x, hx, rfl⟩`. Introduce `x hx`. Establish `hxN : x ∈ N` using `hN ▸ hx`. Establish `h0 : A x = 0` using `by simpa using hxN.2`. Rewrite using `[h0]`.

Conclude with `S.zero_mem`.
-/
theorem propsSchur_maps (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) (A : H →L[ℂ] H)
    (hA : ∀ g ∈ UJset ε, ∀ x, A (σ g x) = σ g (A x)) : ∀ x ∈ V.map D.subtype, A x ∈ V.map D.subtype := by
  have hS := data_isKTypeOf hgap hσ hD hV hc hVK
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  have hlow := data_lowK_eq hgap hσ hD hV hc hVK
  set S := V.map D.subtype with hSdef
  obtain ⟨hfd, hKs, hirrK, ⟨v0, hv0S, hv0, hv0w⟩, hcd⟩ := hS
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε := fun g hg => propsSchur_kset_mem hg
  let N : Submodule ℂ H := S ⊓ LinearMap.ker (A : H →ₗ[ℂ] H)
  have hNK : Formalism.MainNotions.S.IsKStableOn ε σ N := by
    intro g hg v hv
    refine ⟨hKs g hg v hv.1, ?_⟩
    have h2 : A v = 0 := by simpa using hv.2
    show (A : H →ₗ[ℂ] H) (σ g v) = 0
    simp [hA g (hKU g hg), h2]
  rcases hirrK N inf_le_left hNK with hN | hN
  · have hinj : ∀ x ∈ S, A x = 0 → x = 0 := fun x hx h0 => by
      have hxN : x ∈ N := ⟨hx, by simpa using h0⟩
      rw [hN] at hxN
      simpa using hxN
    let T : Submodule ℂ H := S.map (A : H →ₗ[ℂ] H)
    have hT : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) T := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · haveI := hfd
        infer_instance
      · intro g hg w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨σ g x, hKs g hg x hx, by simp [hA g (hKU g hg)]⟩
      · intro S' hS'T hS'K
        let P : Submodule ℂ H := S ⊓ S'.comap (A : H →ₗ[ℂ] H)
        have hPK : Formalism.MainNotions.S.IsKStableOn ε σ P := by
          intro g hg v hv
          refine ⟨hKs g hg v hv.1, ?_⟩
          have h2 : A v ∈ S' := hv.2
          show A (σ g v) ∈ S'
          rw [hA g (hKU g hg)]
          exact hS'K g hg _ h2
        rcases hirrK P inf_le_left hPK with hP | hP
        · left
          rw [eq_bot_iff]
          intro w hw
          obtain ⟨x, hx, rfl⟩ := hS'T hw
          have hxP : x ∈ P := ⟨hx, hw⟩
          rw [hP] at hxP
          have : x = 0 := by simpa using hxP
          simp [this]
        · right
          refine le_antisymm hS'T ?_
          rintro w ⟨x, hx, rfl⟩
          have hxP : x ∈ P := hP ▸ hx
          exact hxP.2
      · refine ⟨A v0, ⟨v0, hv0S, rfl⟩, fun h => hv0 (hinj v0 hv0S h), ?_⟩
        intro θ hθ
        rw [← hA _ (hKU _ hθ), hv0w θ hθ, map_smul]
      · intro μ w hw hw0 hww
        obtain ⟨x, hx, rfl⟩ := hw
        refine hcd μ x hx (fun h => hw0 (by simp [h])) ?_
        intro θ hθ
        have h1 := hww θ hθ
        have h3 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x -
            Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x) = 0 := by
          rw [map_sub, map_smul, hA _ (hKU _ hθ)]
          exact sub_eq_zero.mpr h1
        have hmem : σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x -
            Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x ∈ S :=
          S.sub_mem (hKs _ hθ x hx) (S.smul_mem _ hx)
        exact sub_eq_zero.mp (hinj _ hmem h3)
    have hTle : T ≤ closGen E V := by rw [htop]; exact le_top
    have hTS := hlow T hTle hT
    intro x hx
    rw [← hTS]
    exact ⟨x, hx, rfl⟩
  · intro x hx
    have hxN : x ∈ N := hN ▸ hx
    have h0 : A x = 0 := by simpa using hxN.2
    rw [h0]
    exact S.zero_mem

/- English proof (translation)
Establish `hAS` using `propsSchur_maps hgap hσ hD hV hc hVK hirr hV0 A hA`. Take `⟨hfd, -, -, ⟨v0, hv0S, hv0, -⟩, -⟩` from `data_isKTypeOf hgap hσ hD hV hc hVK`. Use `set S := V.map D.subtype with hSdef`. Set `AS : Module.End ℂ S` to `(A : H →ₗ[ℂ] H).restrict hAS`. Use `haveI := hfd`.

Use `haveI : Nontrivial S := ⟨⟨⟨v0, hv0S⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩`. Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue AS`. Take `⟨u, hu⟩` from `hc'.exists_hasEigenvector`. Establish `hAu : A u = c • (u : H)` using `congrArg Subtype.val hu.apply_eq_smul`. Set `K0 : Submodule ℂ H` to `LinearMap.ker ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)`.

Establish `hK0c : IsClosed (K0 : Set H)` using `ContinuousLinearMap.isClosed_ker _`. Establish `hK0s : ∀ g ∈ UJset ε, ∀ v ∈ K0, σ g v ∈ K0`. Introduce `g hg v hv`. Establish `hv' : A v - c • v = 0` using `by simpa [K0] using hv`. Use `show ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) (σ g v) = 0`.

Simplify using `only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]`. Rewrite using `[hA g hg, ← map_smul, ← map_sub, hv', map_zero]`. Break down `hirr K0 hK0c hK0s with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `hu0 : (u : H) ∈ K0` using `by simp [K0, hAu]`.

Rewrite `hu0` using `[h0]`. Conclude with `hu.2 (Subtype.ext (by simpa using hu0))`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `hx : x ∈ K0` using `h0 ▸ Submodule.mem_top`.

Establish `: A x - c • x = 0` using `by simpa [K0] using hx`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem data_schur (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) (A : H →L[ℂ] H)
    (hA : ∀ g ∈ UJset ε, ∀ x, A (σ g x) = σ g (A x)) : ∃ c : ℂ, A = c • 1 := by
  have hAS := propsSchur_maps hgap hσ hD hV hc hVK hirr hV0 A hA
  obtain ⟨hfd, -, -, ⟨v0, hv0S, hv0, -⟩, -⟩ := data_isKTypeOf hgap hσ hD hV hc hVK
  set S := V.map D.subtype with hSdef
  let AS : Module.End ℂ S := (A : H →ₗ[ℂ] H).restrict hAS
  haveI := hfd
  haveI : Nontrivial S := ⟨⟨⟨v0, hv0S⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue AS
  obtain ⟨u, hu⟩ := hc'.exists_hasEigenvector
  have hAu : A u = c • (u : H) := congrArg Subtype.val hu.apply_eq_smul
  let K0 : Submodule ℂ H := LinearMap.ker ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hK0c : IsClosed (K0 : Set H) := ContinuousLinearMap.isClosed_ker _
  have hK0s : ∀ g ∈ UJset ε, ∀ v ∈ K0, σ g v ∈ K0 := by
    intro g hg v hv
    have hv' : A v - c • v = 0 := by simpa [K0] using hv
    show ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) (σ g v) = 0
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [hA g hg, ← map_smul, ← map_sub, hv', map_zero]
  rcases hirr K0 hK0c hK0s with h0 | h0
  · exfalso
    have hu0 : (u : H) ∈ K0 := by simp [K0, hAu]
    rw [h0] at hu0
    exact hu.2 (Subtype.ext (by simpa using hu0))
  · refine ⟨c, ?_⟩
    ext x
    have hx : x ∈ K0 := h0 ▸ Submodule.mem_top
    have : A x - c • x = 0 := by simpa [K0] using hx
    simpa [sub_eq_zero] using this

end ReciprocityTheory.ChartRestriction.DS
