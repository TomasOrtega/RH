import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEab
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsAdm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOneA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section Transfer

variable {n : ℕ} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {ε : Fin n → Bool}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `h g hg _ ⟨x, hx, rfl⟩`. Conclude with `⟨σ₁ g x, h g hg x hx, hint g hg x⟩`. Introduce `h g hg v hv`. Take `⟨w, hw, hwe⟩` from `Submodule.mem_map.mp (h g hg (φ v) (Submodule.mem_map_of_mem hv))`.

Rewrite `hwe` using `[← hint g hg v]`. Rewrite using `[← hφ hwe]`. Conclude with `hw`.
-/
theorem kStableOn_map_iff (φ : H₁ →ₗ[ℂ] H₂) (hφ : Function.Injective φ)
    (hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ₁ g x) = σ₂ g (φ x)) (S : Submodule ℂ H₁) :
    Formalism.MainNotions.S.IsKStableOn ε σ₁ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ₂ (S.map φ) := by
  constructor
  · rintro h g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ₁ g x, h g hg x hx, hint g hg x⟩
  · intro h g hg v hv
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp (h g hg (φ v) (Submodule.mem_map_of_mem hv))
    rw [← hint g hg v] at hwe
    rw [← hφ hwe]
    exact hw

/- English proof (translation)
Unfold `Formalism.MainNotions.S.IsWtOn`. Prove the components needed by the constructor for the conclusion. Introduce `h θ hθ`. Rewrite using `[← hint _ hθ x, h θ hθ, map_smul]`. Introduce `h θ hθ`.

Apply `hφ` to reduce the goal to its premises. Rewrite using `[hint _ hθ x, h θ hθ, map_smul]`.
-/
theorem isWtOn_map_iff (φ : H₁ →ₗ[ℂ] H₂) (hφ : Function.Injective φ)
    (hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ₁ g x) = σ₂ g (φ x)) (μ : Fin n → ℝ) (x : H₁) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ x ↔ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₂ μ (φ x) := by
  unfold Formalism.MainNotions.S.IsWtOn
  constructor
  · intro h θ hθ
    rw [← hint _ hθ x, h θ hθ, map_smul]
  · intro h θ hθ
    apply hφ
    rw [hint _ hθ x, h θ hθ, map_smul]

/- English proof (translation)
Establish `hfd : FiniteDimensional ℂ S ↔ FiniteDimensional ℂ (S.map φ)` using `⟨fun _ => (Submodule.equivMapOfInjective φ hφ S).finiteDimensional, fun _ => (Submodule.equivMapOfInjective φ hφ S).symm.finiteDimensional⟩`. Establish `hst` using `kStableOn_map_iff φ hφ hint`. Establish `hwt` using `isWtOn_map_iff φ hφ hint`. Unfold `Formalism.MainNotions.S.IsKTypeOf`. Use `and_congr hfd (and_congr (hst S) (and_congr ?_ (and_congr ?_ ?_)))` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h S' hS' hst'`. Establish `hle : S'.comap φ ≤ S`. Introduce `x hx`. Take `⟨w, hw, hwx⟩` from `Submodule.mem_map.mp (hS' hx)`.

Rewrite using `[← hφ hwx]`. Conclude with `hw`. Establish `hst'' : Formalism.MainNotions.S.IsKStableOn ε σ₁ (S'.comap φ)`. Introduce `g hg x hx`. Use `show φ (σ₁ g x) ∈ S'`.

Rewrite using `[hint g hg x]`. Conclude with `hst' g hg (φ x) hx`. Establish `hS'eq : (S'.comap φ).map φ = S'`. Use `le_antisymm (Submodule.map_comap_le _ _) fun y hy => ?_` and prove the remaining obligations. Take `⟨w, -, rfl⟩` from `Submodule.mem_map.mp (hS' hy)`.

Conclude with `Submodule.mem_map_of_mem hy`. Break down `h _ hle hst'' with h0 | h1` into its components or cases. Use `left`. Rewrite using `[← hS'eq, h0, Submodule.map_bot]`. Use `right`.

Rewrite using `[← hS'eq, h1]`. Introduce `h S' hS' hst'`. Break down `h (S'.map φ) (Submodule.map_mono hS') ((hst S').mp hst') with h0 | h1` into its components or cases. Use `left`. Apply `Submodule.map_injective_of_injective hφ` to reduce the goal to its premises.

Rewrite using `[h0, Submodule.map_bot]`. Use `right`. Conclude with `Submodule.map_injective_of_injective hφ h1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hv0, hvw⟩`.

Conclude with `⟨φ v, Submodule.mem_map_of_mem hv, (map_ne_zero_iff φ hφ).mpr hv0, (hwt μ v).mp hvw⟩`. Introduce and unpack `⟨v, hv, hv0, hvw⟩`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.mp hv`. Conclude with `⟨w, hw, (map_ne_zero_iff φ hφ).mp hv0, (hwt μ w).mpr hvw⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `h ν v hv hv0 hvw`. Take `⟨w, hw, rfl⟩` from `Submodule.mem_map.mp hv`. Conclude with `h ν w hw ((map_ne_zero_iff φ hφ).mp hv0) ((hwt ν w).mpr hvw)`. Introduce `h ν v hv hv0 hvw`. Conclude with `h ν (φ v) (Submodule.mem_map_of_mem hv) ((map_ne_zero_iff φ hφ).mpr hv0) ((hwt ν v).mp hvw)`.
-/
theorem isKTypeOf_map_iff (φ : H₁ →ₗ[ℂ] H₂) (hφ : Function.Injective φ)
    (hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ₁ g x) = σ₂ g (φ x)) (μ : Fin n → ℝ) (S : Submodule ℂ H₁) :
    Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ₂ μ (S.map φ) := by
  have hfd : FiniteDimensional ℂ S ↔ FiniteDimensional ℂ (S.map φ) :=
    ⟨fun _ => (Submodule.equivMapOfInjective φ hφ S).finiteDimensional,
     fun _ => (Submodule.equivMapOfInjective φ hφ S).symm.finiteDimensional⟩
  have hst := kStableOn_map_iff φ hφ hint
  have hwt := isWtOn_map_iff φ hφ hint
  unfold Formalism.MainNotions.S.IsKTypeOf
  refine and_congr hfd (and_congr (hst S) (and_congr ?_ (and_congr ?_ ?_)))
  · constructor
    · intro h S' hS' hst'
      have hle : S'.comap φ ≤ S := by
        intro x hx
        obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (hS' hx)
        rw [← hφ hwx]
        exact hw
      have hst'' : Formalism.MainNotions.S.IsKStableOn ε σ₁ (S'.comap φ) := by
        intro g hg x hx
        show φ (σ₁ g x) ∈ S'
        rw [hint g hg x]
        exact hst' g hg (φ x) hx
      have hS'eq : (S'.comap φ).map φ = S' := by
        refine le_antisymm (Submodule.map_comap_le _ _) fun y hy => ?_
        obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp (hS' hy)
        exact Submodule.mem_map_of_mem hy
      rcases h _ hle hst'' with h0 | h1
      · left
        rw [← hS'eq, h0, Submodule.map_bot]
      · right
        rw [← hS'eq, h1]
    · intro h S' hS' hst'
      rcases h (S'.map φ) (Submodule.map_mono hS') ((hst S').mp hst') with h0 | h1
      · left
        apply Submodule.map_injective_of_injective hφ
        rw [h0, Submodule.map_bot]
      · right
        exact Submodule.map_injective_of_injective hφ h1
  · constructor
    · rintro ⟨v, hv, hv0, hvw⟩
      exact ⟨φ v, Submodule.mem_map_of_mem hv, (map_ne_zero_iff φ hφ).mpr hv0, (hwt μ v).mp hvw⟩
    · rintro ⟨v, hv, hv0, hvw⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      exact ⟨w, hw, (map_ne_zero_iff φ hφ).mp hv0, (hwt μ w).mpr hvw⟩
  · constructor
    · intro h ν v hv hv0 hvw
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      exact h ν w hw ((map_ne_zero_iff φ hφ).mp hv0) ((hwt ν w).mpr hvw)
    · intro h ν v hv hv0 hvw
      exact h ν (φ v) (Submodule.mem_map_of_mem hv) ((map_ne_zero_iff φ hφ).mpr hv0) ((hwt ν v).mp hvw)

end Transfer

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}

def Hlam (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : Submodule ℂ (L2 ε) :=
  closGen (smE ε (rreg ε)) (datumV ε Ψ v₀)

instance Hlam.completeSpace (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    CompleteSpace (Hlam ε Ψ v₀) := by
  unfold Hlam closGen; infer_instance

def sigLam (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V)
    (g : Matrix (Fin n) (Fin n) ℂ) : Hlam ε Ψ v₀ →L[ℂ] Hlam ε Ψ v₀ :=
  (Hlam ε Ψ v₀).orthogonalProjectionOnto ∘L (rreg ε g) ∘L (Hlam ε Ψ v₀).subtypeL

def lowKSubLam (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    Submodule ℂ (Hlam ε Ψ v₀) :=
  ((datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype).comap (Hlam ε Ψ v₀).subtype

def kfinLam (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    Submodule ℂ (Hlam ε Ψ v₀) :=
  ((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype).comap (Hlam ε Ψ v₀).subtype

variable {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

/- English proof (translation)
Establish `hD` using `datumEmbedding_mem_smooth hP v₀ v`. Establish `hV : (⟨uniformisationL2 ε Ψ v₀ v, hD⟩ : smD ε (rreg ε)) ∈ datumV ε Ψ v₀` using `by show uniformisationL2 ε Ψ v₀ v ∈ Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀))`. Conclude with `Submodule.subset_span ⟨v, rfl⟩`. Establish `hG : (⟨uniformisationL2 ε Ψ v₀ v, hD⟩ : smD ε (rreg ε)) ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)` using `Submodule.mem_sInf.mpr fun U hU => hU.1 hV`. Unfold `Hlam closGen`.

Conclude with `Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hG)`.
-/
theorem datumEmbedding_mem_Hlam (hP : IsPsiFor ε lam T Ψ) (v : T.V) : uniformisationL2 ε Ψ v₀ v ∈ Hlam ε Ψ v₀ := by
  have hD := datumEmbedding_mem_smooth hP v₀ v
  have hV : (⟨uniformisationL2 ε Ψ v₀ v, hD⟩ : smD ε (rreg ε)) ∈ datumV ε Ψ v₀ := by
    show uniformisationL2 ε Ψ v₀ v ∈ Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀))
    exact Submodule.subset_span ⟨v, rfl⟩
  have hG : (⟨uniformisationL2 ε Ψ v₀ v, hD⟩ : smD ε (rreg ε)) ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) :=
    Submodule.mem_sInf.mpr fun U hU => hU.1 hV
  unfold Hlam closGen
  exact Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hG)

/- English proof (translation)
The claim follows from `closGen_stable hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀)`.
-/
theorem rreg_mem_Hlam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ v₀, rreg ε g x ∈ Hlam ε Ψ v₀ :=
  closGen_stable hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀)

/- English proof (translation)
Establish `hm` using `rreg_mem_Hlam hgap hP hv₀ g hg x x.2`. Establish `h1 : sigLam ε Ψ v₀ g x = ⟨rreg ε g x, hm⟩` using `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨rreg ε g x, hm⟩ : Hlam ε Ψ v₀)`. Rewrite using `[h1]`.
-/
theorem sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (x : Hlam ε Ψ v₀) :
    ((sigLam ε Ψ v₀ g x : Hlam ε Ψ v₀) : L2 ε) = rreg ε g x := by
  have hm := rreg_mem_Hlam hgap hP hv₀ g hg x x.2
  have h1 : sigLam ε Ψ v₀ g x = ⟨rreg ε g x, hm⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨rreg ε g x, hm⟩ : Hlam ε Ψ v₀)
  rw [h1]

/- English proof (translation)
Establish `hR` using `rreg_isURepOn ε`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x : 1 show (Hlam ε Ψ v₀).orthogonalProjectionOnto (rreg ε 1 (x : L2 ε)) = x`. Rewrite using `[hR.1.1]`. Conclude with `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x`.

Introduce `a ha b hb`. Use extensionality with `x : 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hy : rreg ε a (rreg ε b (x : L2 ε)) ∈ Hlam ε Ψ v₀` using `rreg_mem_Hlam hgap hP hv₀ a ha _ (rreg_mem_Hlam hgap hP hv₀ b hb _ x.2)`. Establish `e1 : sigLam ε Ψ v₀ (a * b) x = ⟨_, hy⟩` using `by show (Hlam ε Ψ v₀).orthogonalProjectionOnto (rreg ε (a * b) (x : L2 ε)) = _`.

Rewrite using `[hR.1.2 a ha b hb]`. Conclude with `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hy⟩`. Rewrite using `[e1, ContinuousLinearMap.comp_apply, sigLam_coe hgap hP hv₀ ha, sigLam_coe hgap hP hv₀ hb]`. Introduce `g hg v show ‖((sigLam ε Ψ v₀ g v : Hlam ε Ψ v₀) : L2 ε)‖ = ‖(v : L2 ε)‖`. Rewrite using `[sigLam_coe hgap hP hv₀ hg v, hR.2.1 g hg]`.

Introduce `v`. Conclude with `(Hlam ε Ψ v₀).orthogonalProjectionOnto.continuous.comp_continuousOn (hR.2.2 (v : L2 ε))`.
-/
theorem sigLam_isURepOn (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := by
  have hR := rreg_isURepOn ε
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext x : 1
    show (Hlam ε Ψ v₀).orthogonalProjectionOnto (rreg ε 1 (x : L2 ε)) = x
    rw [hR.1.1]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  · intro a ha b hb
    ext x : 1
    apply Subtype.ext
    have hy : rreg ε a (rreg ε b (x : L2 ε)) ∈ Hlam ε Ψ v₀ :=
      rreg_mem_Hlam hgap hP hv₀ a ha _ (rreg_mem_Hlam hgap hP hv₀ b hb _ x.2)
    have e1 : sigLam ε Ψ v₀ (a * b) x = ⟨_, hy⟩ := by
      show (Hlam ε Ψ v₀).orthogonalProjectionOnto (rreg ε (a * b) (x : L2 ε)) = _
      rw [hR.1.2 a ha b hb]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hy⟩
    rw [e1, ContinuousLinearMap.comp_apply, sigLam_coe hgap hP hv₀ ha, sigLam_coe hgap hP hv₀ hb]
  · intro g hg v
    show ‖((sigLam ε Ψ v₀ g v : Hlam ε Ψ v₀) : L2 ε)‖ = ‖(v : L2 ε)‖
    rw [sigLam_coe hgap hP hv₀ hg v, hR.2.1 g hg]
  · intro v
    exact (Hlam ε Ψ v₀).orthogonalProjectionOnto.continuous.comp_continuousOn (hR.2.2 (v : L2 ε))

/- English proof (translation)
Introduce `S hSc hSG`. Establish `hinj : Function.Injective (Hlam ε Ψ v₀).subtype` using `Subtype.val_injective`. Establish `hcl : IsClosed ((S.map (Hlam ε Ψ v₀).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε))`. Establish `h` using `(Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap (S : Set (Hlam ε Ψ v₀)) hSc`. Rewrite using `[Submodule.map_coe]`.

Conclude with `h`. Establish `hle : S.map (Hlam ε Ψ v₀).subtype ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ v₀)`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.2`. Establish `hst : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype, rreg ε g x ∈ S.map (Hlam ε Ψ v₀).subtype`.

Introduce and unpack `g hg _ ⟨x, hx, rfl⟩`. Conclude with `⟨sigLam ε Ψ v₀ g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, sigLam_coe hgap hP hv₀ hg x⟩`. Break down `rigid_irred hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ hle hcl hst with h | h` into its components or cases. Use `left`. Conclude with `Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)`.

Use `right`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_top, Submodule.range_subtype]`. Both sides reduce to the same expression.
-/
theorem sigLam_irred (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ v₀) := by
  intro S hSc hSG
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  have hcl : IsClosed ((S.map (Hlam ε Ψ v₀).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    have h := (Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap
      (S : Set (Hlam ε Ψ v₀)) hSc
    rw [Submodule.map_coe]
    exact h
  have hle : S.map (Hlam ε Ψ v₀).subtype ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ v₀) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hst : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype, rreg ε g x ∈ S.map (Hlam ε Ψ v₀).subtype := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨sigLam ε Ψ v₀ g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, sigLam_coe hgap hP hv₀ hg x⟩
  rcases rigid_irred hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀)
      (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ hle hcl hst with h | h
  · left
    exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, Submodule.range_subtype]
    rfl

/- English proof (translation)
Take `⟨-, -, -, w, hw, hw0, -⟩` from `datumV_isKIrrHW hP hv₀`. Establish `hm : ((w : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀`. Unfold `Hlam closGen`. Conclude with `Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (Submodule.mem_sInf.mpr fun U hU => hU.1 hw))`. Use `⟨⟨⟨w, hm⟩, 0, fun h => hw0 ?_⟩⟩` and prove the remaining obligations.

Establish `h2 : ((w : smD ε (rreg ε)) : L2 ε) = 0` using `congrArg (fun z : Hlam ε Ψ v₀ => (z : L2 ε)) h`. Conclude with `Subtype.ext h2`.
-/
theorem Hlam_nontrivial (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Nontrivial (Hlam ε Ψ v₀) := by
  obtain ⟨-, -, -, w, hw, hw0, -⟩ := datumV_isKIrrHW hP hv₀
  have hm : ((w : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by
    unfold Hlam closGen
    exact Submodule.le_topologicalClosure _
      (Submodule.mem_map_of_mem (Submodule.mem_sInf.mpr fun U hU => hU.1 hw))
  refine ⟨⟨⟨w, hm⟩, 0, fun h => hw0 ?_⟩⟩
  have h2 : ((w : smD ε (rreg ε)) : L2 ε) = 0 := congrArg (fun z : Hlam ε Ψ v₀ => (z : L2 ε)) h
  exact Subtype.ext h2

/- English proof (translation)
Take `⟨hu, hc⟩` from `hg`. Establish `h1 : star g * g = 1` using `Matrix.mem_unitaryGroup_iff'.mp hu`. Establish `hJ : ReciprocityTheory.ChartRestriction.DS.Jm ε = Formalism.REAL.Jm ε` using `rfl`. Use `show gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g = ReciprocityTheory.ChartRestriction.DS.Jm ε`. Rewrite using `[hJ, mul_assoc, ← hc, ← mul_assoc, ← Matrix.star_eq_conjTranspose, h1, one_mul]`.
-/
private theorem Kset_subset_UJset_mem {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hJ : ReciprocityTheory.ChartRestriction.DS.Jm ε = Formalism.REAL.Jm ε := rfl
  show gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g = ReciprocityTheory.ChartRestriction.DS.Jm ε
  rw [hJ, mul_assoc, ← hc, ← mul_assoc, ← Matrix.star_eq_conjTranspose, h1, one_mul]

/- English proof (translation)
Introduce `g hg x`. Conclude with `sigLam_coe hgap hP hv₀ (Kset_subset_UJset_mem hg) x`.
-/
theorem subtype_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ v₀).subtype (sigLam ε Ψ v₀ g x) =
      rreg ε g ((Hlam ε Ψ v₀).subtype x) := by
  intro g hg x
  exact sigLam_coe hgap hP hv₀ (Kset_subset_UJset_mem hg) x

/- English proof (translation)
Unfold `lowKSubLam`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Unfold `Hlam closGen`. Conclude with `Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (Submodule.mem_sInf.mpr fun U hU => hU.1 hy))`.
-/
theorem map_lowKSubLam : (lowKSubLam ε Ψ v₀).map (Hlam ε Ψ v₀).subtype =
    (datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype := by
  unfold lowKSubLam
  rw [Submodule.map_comap_subtype, inf_eq_right]
  rintro _ ⟨y, hy, rfl⟩
  unfold Hlam closGen
  exact Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem (Submodule.mem_sInf.mpr fun U hU => hU.1 hy))

/- English proof (translation)
Conclude with `Submodule.map_subtype_le _ S`.
-/
theorem map_subtype_le_closGen (S : Submodule ℂ (Hlam ε Ψ v₀)) :
    S.map (Hlam ε Ψ v₀).subtype ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ v₀) := by
  exact Submodule.map_subtype_le _ S

/- English proof (translation)
Establish `hinj : Function.Injective (Hlam ε Ψ v₀).subtype` using `Subtype.val_injective`. Establish `hint` using `subtype_sigLam hgap hP hv₀`. Establish `hK` using `data_isKTypeOf hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀)`. Use `⟨?_, fun S hS => ?_⟩` and prove the remaining obligations. Rewrite using `[isKTypeOf_map_iff _ hinj hint, map_lowKSubLam, mir_lowK_eq]`.

Conclude with `hK`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[map_lowKSubLam]`. Rewrite `hS` using `[isKTypeOf_map_iff _ hinj hint, mir_lowK_eq]`. Conclude with `data_lowK_eq hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hS`.
-/
theorem sigLam_lowK (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) (lowKSubLam ε Ψ v₀) ∧
      ∀ S : Submodule ℂ (Hlam ε Ψ v₀), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) S →
        S = lowKSubLam ε Ψ v₀ := by
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  have hint := subtype_sigLam hgap hP hv₀
  have hK := data_isKTypeOf hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀)
  refine ⟨?_, fun S hS => ?_⟩
  · rw [isKTypeOf_map_iff _ hinj hint, map_lowKSubLam, mir_lowK_eq]
    exact hK
  · apply Submodule.map_injective_of_injective hinj
    rw [map_lowKSubLam]
    rw [isKTypeOf_map_iff _ hinj hint, mir_lowK_eq] at hS
    exact data_lowK_eq hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
      (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hS

/- English proof (translation)
Establish `hinj : Function.Injective (Hlam ε Ψ v₀).subtype` using `Subtype.val_injective`. Rewrite `hS` using `[isKTypeOf_map_iff _ hinj (subtype_sigLam hgap hP hv₀)]`. Conclude with `⟨data_vogan hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hS, fun h hh hbig hμ => data_casValK_gap hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_i …`.
-/
theorem sigLam_kType_bounds (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {μ : Fin n → ℝ} (S : Submodule ℂ (Hlam ε Ψ v₀))
    (hS : Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ ∧
      ∀ h : ℝ, GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h → μ ≠ lowK ε lam →
        casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  rw [isKTypeOf_map_iff _ hinj (subtype_sigLam hgap hP hv₀)] at hS
  exact ⟨data_vogan hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
      (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hS,
    fun h hh hbig hμ => data_casValK_gap hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
      (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) hh hbig _ (map_subtype_le_closGen S) hS hμ⟩

/- English proof (translation)
Establish `hinj : Function.Injective (Hlam ε Ψ v₀).subtype` using `Subtype.val_injective`. Establish `hint` using `subtype_sigLam hgap hP hv₀`. Establish `hfin` using `data_admissible hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) μ`. Establish `hle : (sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S}).map (Hlam ε Ψ v₀).subtype ≤ sSup {S : Submodule ℂ (L2 ε) | S ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ v₀) ∧ Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) μ S}`. Rewrite using `[Submodule.map_le_iff_le_comap]`.

Use `sSup_le fun S hS => ?_` and prove the remaining obligations. Rewrite using `[← Submodule.map_le_iff_le_comap]`. Conclude with `le_sSup ⟨map_subtype_le_closGen S, (isKTypeOf_map_iff _ hinj hint μ S).1 hS⟩`. Use `Submodule.finiteDimensional_of_le hle` as an intermediate fact. Conclude with `(Submodule.equivMapOfInjective _ hinj _).symm.finiteDimensional`.
-/
theorem sigLam_admissible (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S} :
        Submodule ℂ (Hlam ε Ψ v₀)) := by
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  have hint := subtype_sigLam hgap hP hv₀
  have hfin := data_admissible hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) μ
  have hle : (sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S}).map
      (Hlam ε Ψ v₀).subtype ≤ sSup {S : Submodule ℂ (L2 ε) |
        S ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ v₀) ∧ Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) μ S} := by
    rw [Submodule.map_le_iff_le_comap]
    refine sSup_le fun S hS => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup ⟨map_subtype_le_closGen S, (isKTypeOf_map_iff _ hinj hint μ S).1 hS⟩
  have := Submodule.finiteDimensional_of_le hle
  exact (Submodule.equivMapOfInjective _ hinj _).symm.finiteDimensional

/- English proof (translation)
Establish `hinj : Function.Injective (Hlam ε Ψ v₀).subtype` using `Subtype.val_injective`. Establish `hint` using `subtype_sigLam hgap hP hv₀`. Use `hSf` as an intermediate fact. Establish `hf : FiniteDimensional ℂ (S.map (Hlam ε Ψ v₀).subtype)` using `(Submodule.equivMapOfInjective _ hinj S).finiteDimensional`. Establish `hK : ∀ k ∈ Kset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype, rreg ε k x ∈ S.map (Hlam ε Ψ v₀).subtype`.

Introduce `k hk x hx`. Rewrite `hk` using `[← mir_Kset_eq]`. Conclude with `(kStableOn_map_iff _ hinj hint S).1 hSK k hk x hx`. Establish `h` using `data_kfin_le hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hf hK`. Introduce `x hx`.

Conclude with `h ⟨x, hx, rfl⟩`.
-/
theorem sigLam_kfin (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (S : Submodule ℂ (Hlam ε Ψ v₀)) (hSf : FiniteDimensional ℂ S)
    (hSK : Formalism.MainNotions.S.IsKStableOn ε (sigLam ε Ψ v₀) S) : S ≤ kfinLam ε Ψ v₀ := by
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  have hint := subtype_sigLam hgap hP hv₀
  have := hSf
  have hf : FiniteDimensional ℂ (S.map (Hlam ε Ψ v₀).subtype) :=
    (Submodule.equivMapOfInjective _ hinj S).finiteDimensional
  have hK : ∀ k ∈ Kset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype, rreg ε k x ∈ S.map (Hlam ε Ψ v₀).subtype := by
    intro k hk x hx
    rw [← mir_Kset_eq] at hk
    exact (kStableOn_map_iff _ hinj hint S).1 hSK k hk x hx
  have h := data_kfin_le hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hf hK
  intro x hx
  exact h ⟨x, hx, rfl⟩

end ReciprocityTheory.ChartRestriction.DS
