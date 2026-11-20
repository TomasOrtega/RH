import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockHomomorphism

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.Form.LeviSmoothness.Ex

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩` and prove the remaining obligations. Establish `e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = (A : Set (Fin (m + 1) → k)) + (B : Set (Fin (m + 1) → k))`. Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `hA.1.add hB.1`.
-/
theorem isLat_sup {m : ℕ} {A B : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (A : Set (Fin (m + 1) → k)) + (B : Set (Fin (m + 1) → k)) := by
    ext x
    rw [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
    rfl
  rw [e]
  exact hA.1.add hB.1

/- English proof (translation)
Use `⟨AddSubgroup.pi Set.univ fun _ => (𝒪[k]).toAddSubgroup, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : IsCompact ((𝒪[k] : Set k))` using `isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[k]))`. Establish `e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k)`. Use extensionality with `x`. Simplify using `[AddSubgroup.mem_pi]`.

Rewrite using `[e]`. Conclude with `isCompact_univ_pi fun _ => hc`. Establish `ho : IsOpen ((𝒪[k] : Set k))` using `by first`. Consider the case `exact IsValuativeTopology.isOpen_integer`. Consider the case `exact Valuation.isOpen_integer _`.

Consider the case `exact (valuation k).isOpen_integer`. Consider the case `exact isOpen_integer`. Establish `e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k)`. Use extensionality with `x`. Simplify using `[AddSubgroup.mem_pi]`.

Rewrite using `[e]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => ho`.
-/
theorem exists_lat (m : ℕ) : ∃ A₀ : AddSubgroup (Fin (m + 1) → k), IsLat A₀ := by
  refine ⟨AddSubgroup.pi Set.univ fun _ => (𝒪[k]).toAddSubgroup, ?_, ?_⟩
  · have hc : IsCompact ((𝒪[k] : Set k)) := isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[k]))
    have e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup :
        AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
      ext x
      simp [AddSubgroup.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => hc
  · have ho : IsOpen ((𝒪[k] : Set k)) := by
      first
        | exact IsValuativeTopology.isOpen_integer
        | exact Valuation.isOpen_integer _
        | exact (valuation k).isOpen_integer
        | exact isOpen_integer
    have e : ((AddSubgroup.pi Set.univ fun _ : Fin (m + 1) => (𝒪[k]).toAddSubgroup :
        AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
      ext x
      simp [AddSubgroup.mem_pi]
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => ho

section

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK <;> assumption`.
-/
theorem exists_fixK (hπ : IsSmooth π) (v w : V) :
    ∃ K : Subgroup (GL (Fin (m + 1)) k), IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
      FixK (by omega) π K v ∧ FixK (by omega) π K w :=
  by apply _root_.UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK <;> assumption

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem avg_adj (hherm : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hsa : ∀ (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)), IsLat A → ∀ v w,
      B (avg ψ h π ξ A v) w = B (avg ψ h π ξ A v) (avg ψ h π ξ A w))
    (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (x w : V) :
    B (avg ψ h π ξ A x) w = B x (avg ψ h π ξ A w) := by
  calc B (avg ψ h π ξ A x) w = B (avg ψ h π ξ A x) (avg ψ h π ξ A w) := hsa ξ A hA x w
    _ = starRingEnd ℂ (B (avg ψ h π ξ A w) (avg ψ h π ξ A x)) := hherm _ _
    _ = starRingEnd ℂ (B (avg ψ h π ξ A w) x) := by rw [← hsa ξ A hA w x]
    _ = B x (avg ψ h π ξ A w) := (hherm _ _).symm

/- English proof (translation)
Set `T : AddSubgroup (Fin (m + 1) → k) → V → V → ℂ` to `fun A v w => ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w`. Establish `hex : ∀ v w : V, ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A → T A v w = T A₁ v w`. Introduce `v w`. Take `⟨K, hK, hv, hw⟩` from `exists_fixK (h := h) hB.smooth v w`. Take `⟨A₁, hA₁, h01, hst⟩` from `hstab K hK hA₀`.

Conclude with `⟨A₁, hA₁, h01, fun A hAl hle => hst v w hv hw A hAl hle⟩`. Use `choose L hL h0L hLs using hex`. Set `f : V → V → ℂ` to `fun v w => T (L v w) v w`. Establish `hf : ∀ v w A, IsLat A → L v w ≤ A → f v w = T A v w` using `fun v w A hA hle => (hLs v w A hA hle).symm`. Establish `hherm` using `hB.psd.1`.

Establish `hadj` using `avg_adj (ψ := ψ) (h := h) (π := π) hherm hsa`. Establish `big : ∀ A₁ A₂ A₃ : AddSubgroup (Fin (m + 1) → k), IsLat A₁ → IsLat A₂ → IsLat A₃ → IsLat (A₁ ⊔ A₂ ⊔ A₃) ∧ A₁ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₂ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₃ ≤ A₁ ⊔ A₂ ⊔ A₃` using `fun A₁ A₂ A₃ h1 h2 h3 => ⟨isLat_sup (isLat_sup h1 h2) h3, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, le_sup_right⟩`. Set `B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f (fun v₁ v₂ w => by`. Take `⟨hA, h1, h2, h3⟩` from `big (L (v₁ + v₂) w) (L v₁ w) (L v₂ w) (hL _ _) (hL _ _) (hL _ _)`. Rewrite using `[hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]`.

Simplify using `only [T]`. Rewrite using `[hadj _ hA, hadj _ hA, hadj _ hA, map_add, LinearMap.add_apply, mul_add])`. Use the proof step `(fun c v w => by`. Take `⟨hA, h1, h2, -⟩` from `big (L (c • v) w) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)`. Rewrite using `[hf _ _ _ hA h1, hf _ _ _ hA h2]`.

Simplify using `only [T, RingHom.id_apply, smul_eq_mul]`. Rewrite using `[hadj _ hA, hadj _ hA, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Use the proof step `ring)`. Use the proof step `(fun v w₁ w₂ => by`. Take `⟨hA, h1, h2, h3⟩` from `big (L v (w₁ + w₂)) (L v w₁) (L v w₂) (hL _ _) (hL _ _) (hL _ _)`.

Rewrite using `[hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]`. Simplify using `only [T]`. Rewrite using `[map_add, mul_add])`. Use the proof step `(fun c v w => by`. Take `⟨hA, h1, h2, -⟩` from `big (L v (c • w)) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)`.

Rewrite using `[hf _ _ _ hA h1, hf _ _ _ hA h2]`. Simplify using `only [T, smul_eq_mul]`. Rewrite using `[LinearMap.map_smulₛₗ, smul_eq_mul]`. Use the proof step `ring)`. Establish `hB'f : ∀ v w, B' v w = f v w` using `fun v w => rfl`.

Use `⟨B', fun v w => ⟨L v w, hL v w, h0L v w, fun A hA hle => by rw [hB'f, hf v w A hA hle]⟩, ?_⟩` and prove the remaining obligations. Introduce `K hK`. Take `⟨A₁, hA₁, h01, hA⟩` from `hstab K hK hA₀`. Use `⟨A₁, hA₁, h01, fun v w hv hw A hA' hle => ?_⟩` and prove the remaining obligations. Establish `hs` using `isLat_sup hA' (hL v w)`.

Establish `e1` using `hf v w (A ⊔ L v w) hs le_sup_right`. Establish `e2` using `hA v w hv hw A hA' hle`. Establish `e3` using `hA v w hv hw (A ⊔ L v w) hs (hle.trans le_sup_left)`. Rewrite using `[hB'f, e1]`. Conclude with `e3.trans e2.symm`.
-/
theorem dens_exists_of (hB : Lv ψ h π s B)
    (hsa : ∀ (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)), IsLat A → ∀ v w,
      B (avg ψ h π ξ A v) w = B (avg ψ h π ξ A v) (avg ψ h π ξ A w))
    (hstab : ∀ (K : Subgroup (GL (Fin (m + 1)) k)), IsOpen (K : Set (GL (Fin (m + 1)) k)) →
      ∀ {A₀ : AddSubgroup (Fin (m + 1) → k)}, IsLat A₀ →
      ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
        ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
          ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w)
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsDens ψ h π A₀ B B' ∧ ∀ K : Subgroup (GL (Fin (m + 1)) k),
      IsOpen (K : Set (GL (Fin (m + 1)) k)) → ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v →
        FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
          B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w := by
  classical

  let T : AddSubgroup (Fin (m + 1) → k) → V → V → ℂ := fun A v w =>
    ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w

  have hex : ∀ v w : V, ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A → T A v w = T A₁ v w := by
    intro v w
    obtain ⟨K, hK, hv, hw⟩ := exists_fixK (h := h) hB.smooth v w
    obtain ⟨A₁, hA₁, h01, hst⟩ := hstab K hK hA₀
    exact ⟨A₁, hA₁, h01, fun A hAl hle => hst v w hv hw A hAl hle⟩
  choose L hL h0L hLs using hex
  let f : V → V → ℂ := fun v w => T (L v w) v w
  have hf : ∀ v w A, IsLat A → L v w ≤ A → f v w = T A v w := fun v w A hA hle => (hLs v w A hA hle).symm
  have hherm := hB.psd.1
  have hadj := avg_adj (ψ := ψ) (h := h) (π := π) hherm hsa

  have big : ∀ A₁ A₂ A₃ : AddSubgroup (Fin (m + 1) → k), IsLat A₁ → IsLat A₂ → IsLat A₃ →
      IsLat (A₁ ⊔ A₂ ⊔ A₃) ∧ A₁ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₂ ≤ A₁ ⊔ A₂ ⊔ A₃ ∧ A₃ ≤ A₁ ⊔ A₂ ⊔ A₃ :=
    fun A₁ A₂ A₃ h1 h2 h3 => ⟨isLat_sup (isLat_sup h1 h2) h3, le_sup_left.trans le_sup_left,
      le_sup_right.trans le_sup_left, le_sup_right⟩
  let B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f
    (fun v₁ v₂ w => by
      obtain ⟨hA, h1, h2, h3⟩ := big (L (v₁ + v₂) w) (L v₁ w) (L v₂ w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]
      simp only [T]
      rw [hadj _ hA, hadj _ hA, hadj _ hA, map_add, LinearMap.add_apply, mul_add])
    (fun c v w => by
      obtain ⟨hA, h1, h2, -⟩ := big (L (c • v) w) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2]
      simp only [T, RingHom.id_apply, smul_eq_mul]
      rw [hadj _ hA, hadj _ hA, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun v w₁ w₂ => by
      obtain ⟨hA, h1, h2, h3⟩ := big (L v (w₁ + w₂)) (L v w₁) (L v w₂) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2, hf _ _ _ hA h3]
      simp only [T]
      rw [map_add, mul_add])
    (fun c v w => by
      obtain ⟨hA, h1, h2, -⟩ := big (L v (c • w)) (L v w) (L v w) (hL _ _) (hL _ _) (hL _ _)
      rw [hf _ _ _ hA h1, hf _ _ _ hA h2]
      simp only [T, smul_eq_mul]
      rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring)
  have hB'f : ∀ v w, B' v w = f v w := fun v w => rfl
  refine ⟨B', fun v w => ⟨L v w, hL v w, h0L v w, fun A hA hle => by rw [hB'f, hf v w A hA hle]⟩, ?_⟩
  intro K hK
  obtain ⟨A₁, hA₁, h01, hA⟩ := hstab K hK hA₀
  refine ⟨A₁, hA₁, h01, fun v w hv hw A hA' hle => ?_⟩
  have hs := isLat_sup hA' (hL v w)
  have e1 := hf v w (A ⊔ L v w) hs le_sup_right
  have e2 := hA v w hv hw A hA' hle
  have e3 := hA v w hv hw (A ⊔ L v w) hs (hle.trans le_sup_left)
  rw [hB'f, e1]
  exact e3.trans e2.symm

end

end PositivityTheory.RgUd.Form.LeviSmoothness.Ex
