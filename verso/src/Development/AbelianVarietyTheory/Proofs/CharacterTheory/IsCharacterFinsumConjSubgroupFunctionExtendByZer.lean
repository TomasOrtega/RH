import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

/- English proof (translation)
Establish `hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W)) = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.

Rewrite using `[hdec, map_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.trace_comp_comm', LinearMap.comp_assoc]`. Use `split_ifs with h`. Establish `hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Simplify using `[h]`. Rewrite using `[hid, LinearMap.comp_id]`. Establish `hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Simplify using `[h]`. Rewrite using `[hz, LinearMap.comp_zero, map_zero]`.
-/
private theorem trace_block_permutation (K : Type) [Field K] (X : Type) [Fintype X] [DecidableEq X]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (π : X → X)
    (A : X → W →ₗ[K] W) :
    LinearMap.trace K (X → W) (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q))
      = ∑ q, if π q = q then LinearMap.trace K W (A q) else 0 := by
  have hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W))
      = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q)) := by
    apply LinearMap.ext
    intro f
    funext p
    simp
  rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · have hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hid, LinearMap.comp_id]
  · have hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0 := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hz, LinearMap.comp_zero, map_zero]

section
variable {G : Type} [Group G] (H : Subgroup G)

/- English proof (translation)
Establish `h : ((g⁻¹ * q.out : G) : G ⧸ H) = (((g⁻¹ • q).out : G) : G ⧸ H)`. Rewrite using `[QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`. Establish `hm` using `QuotientGroup.eq.mp h`. Simplify `hm` using `[mul_assoc]`.
-/
theorem cosetCocycle_mem (g : G) (q : G ⧸ H) : q.out⁻¹ * g * (g⁻¹ • q).out ∈ H := by
  have h : ((g⁻¹ * q.out : G) : G ⧸ H) = (((g⁻¹ • q).out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  have hm := QuotientGroup.eq.mp h
  simpa [mul_assoc] using hm

def cosetCocycle (g : G) (q : G ⧸ H) : H := ⟨_, cosetCocycle_mem H g q⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[cosetCocycle]`.
-/
theorem cosetCocycle_one (q : G ⧸ H) : cosetCocycle H 1 q = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [cosetCocycle, Subgroup.coe_mul]`. Rewrite using `[mul_inv_rev, mul_smul]`. Use `group`.
-/
theorem cosetCocycle_mul (a b : G) (q : G ⧸ H) :
    cosetCocycle H (a * b) q = cosetCocycle H a q * cosetCocycle H b (a⁻¹ • q) := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul]
  rw [mul_inv_rev, mul_smul]
  group

/- English proof (translation)
Establish `hs : g⁻¹ • q = ((g⁻¹ * q.out : G) : G ⧸ H)`. Rewrite using `[← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs, QuotientGroup.out_eq']`. Use `_ ↔ q.out⁻¹ * g * q.out ∈ H := by`.

Rewrite using `[QuotientGroup.eq]`. Simplify using `[mul_assoc]`.
-/
theorem inv_smul_eq_iff_conj_mem (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by
  have hs : g⁻¹ • q = ((g⁻¹ * q.out : G) : G ⧸ H) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  calc g⁻¹ • q = q ↔ ((g⁻¹ * q.out : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) := by
        rw [hs, QuotientGroup.out_eq']
    _ ↔ q.out⁻¹ * g * q.out ∈ H := by
        rw [QuotientGroup.eq]
        simp [mul_assoc]

def cosetIndRep {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : Representation K H W) :
    Representation K G (G ⧸ H → W) where
  toFun g := LinearMap.pi fun q => σ (cosetCocycle H g q) ∘ₗ LinearMap.proj (g⁻¹ • q)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_mul, mul_smul]
end

/- English proof (translation)
Introduce `K L _ _ _ G _ _ H ψ hψ`. Use `haveI : Fintype G := Fintype.ofFinite G`. Use `haveI : Fintype (G ⧸ H) := Fintype.ofFinite _`. Take `⟨n, σ, hσ⟩` from `hψ`. Take `⟨m, ρ, hρ⟩` from `(isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1`.

Use `⟨m, ρ, fun g => ?_⟩` and prove the remaining obligations. Establish `hg` using `hρ g`. Simplify using `only at hg`. Rewrite using `[← hg]`. Use `show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _`.

Establish `hc : (cosetIndRep H σ).character g = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0` using `trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q) (fun q => σ (cosetCocycle H g q))`. Rewrite using `[finsum_eq_sum_of_fintype, hc, map_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : g⁻¹ • q = q`. Establish `hm : q.out⁻¹ * g * q.out ∈ H` using `(inv_smul_eq_iff_conj_mem H g q).mp h`.

Establish `he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q` using `Subtype.ext (by simp [cosetCocycle, h])`. Rewrite using `[if_pos h, ext0, dif_pos hm, hσ, he]`. Both sides reduce to the same expression. Establish `hm : q.out⁻¹ * g * q.out ∉ H` using `fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)`. Rewrite using `[if_neg h, ext0, dif_neg hm, map_zero]`.
-/
theorem isChar_finsum_conj_ext0_of_isChar :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  intro K L _ _ _ G _ _ H ψ hψ
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨n, σ, hσ⟩ := hψ
  obtain ⟨m, ρ, hρ⟩ :=
    (isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1
  refine ⟨m, ρ, fun g => ?_⟩
  have hg := hρ g
  simp only at hg
  rw [← hg]
  show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _
  have hc : (cosetIndRep H σ).character g
      = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0 :=
    trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q)
      (fun q => σ (cosetCocycle H g q))
  rw [finsum_eq_sum_of_fintype, hc, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g⁻¹ • q = q
  · have hm : q.out⁻¹ * g * q.out ∈ H := (inv_smul_eq_iff_conj_mem H g q).mp h
    have he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q :=
      Subtype.ext (by simp [cosetCocycle, h])
    rw [if_pos h, ext0, dif_pos hm, hσ, he]
    rfl
  · have hm : q.out⁻¹ * g * q.out ∉ H := fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)
    rw [if_neg h, ext0, dif_neg hm, map_zero]

end GlobalTheory.BI
