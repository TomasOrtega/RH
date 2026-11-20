import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalSum

open GlobalTheory.CuspRep.ParLaws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

/- English proof (translation)
Unfold `diagU`. Use `erw [map_mul]`. Rewrite using `[Pi.mul_apply, map_mul]`.
-/
theorem diagU_mul (p q : borel k (Fin N)) (i : Fin N) : diagU (p * q) i = diagU p i * diagU q i := by
  unfold diagU
  erw [map_mul]
  rw [Pi.mul_apply, map_mul]

/- English proof (translation)
Take `⟨b', hb', w, hw, rfl⟩` from `iwasawa_blockTriangular k (Fin N) Fin.val x`. Establish `hb'' : b' ∈ borel k (Fin N)` using `(mem_borel _).2 hb'`. Establish `hbb : b * b' ∈ borel k (Fin N)` using `mul_mem hb hb''`. Establish `e1 : b * (b' * w) = (b * b') * w` using `(mul_assoc _ _ _).symm`. Rewrite using `[e1, h.1 _ _ hw, h.1 _ _ hw]`.

Establish `t1` using `fun i => (val_diagU ⟨b, hb⟩ i).symm`. Establish `t2` using `fun i => (val_diagU ⟨b', hb''⟩ i).symm`. Establish `t3` using `fun i => (val_diagU ⟨b * b', hbb⟩ i).symm`. Rewrite using `[h.2 _ hb _ t1, h.2 _ hb'' _ t2, h.2 _ hbb _ t3, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `e2 : (⟨b * b', hbb⟩ : borel k (Fin N)) = ⟨b, hb⟩ * ⟨b', hb''⟩` using `rfl`. Rewrite using `[e2, diagU_mul, ord_mul, zpow_add₀ (hγ i)]`.
-/
theorem borelSph_mul_left {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin N) k} (hb : b ∈ borel k (Fin N)) (x : GL (Fin N) k) : ψ (b * x) = ψ b * ψ x := by
  obtain ⟨b', hb', w, hw, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val x
  have hb'' : b' ∈ borel k (Fin N) := (mem_borel _).2 hb'
  have hbb : b * b' ∈ borel k (Fin N) := mul_mem hb hb''
  have e1 : b * (b' * w) = (b * b') * w := (mul_assoc _ _ _).symm
  rw [e1, h.1 _ _ hw, h.1 _ _ hw]
  have t1 := fun i => (val_diagU ⟨b, hb⟩ i).symm
  have t2 := fun i => (val_diagU ⟨b', hb''⟩ i).symm
  have t3 := fun i => (val_diagU ⟨b * b', hbb⟩ i).symm
  rw [h.2 _ hb _ t1, h.2 _ hb'' _ t2, h.2 _ hbb _ t3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e2 : (⟨b * b', hbb⟩ : borel k (Fin N)) = ⟨b, hb⟩ * ⟨b', hb''⟩ := rfl
  rw [e2, diagU_mul, ord_mul, zpow_add₀ (hγ i)]

/- English proof (translation)
Take `⟨κ, hκ, κ', hκ', e⟩` from `hR.1 g₂ h₂`. Take `⟨g, -, hu⟩` from `hR.2 κ hκ`. Establish `a2 : g₂⁻¹ * (κ * g₀) ∈ KO k (Fin N)`. Establish `: g₂⁻¹ * (κ * g₀) = κ'⁻¹` using `by rw [e]; group`. Rewrite using `[this]`.

Conclude with `inv_mem hκ'`. Establish `a1 : g₁⁻¹ * (κ * g₀) ∈ KO k (Fin N)`. Establish `: g₁⁻¹ * (κ * g₀) = (g₁⁻¹ * g₂) * (g₂⁻¹ * (κ * g₀))` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem h a2`.

Rewrite using `[hu g₁ ⟨h₁, a1⟩, hu g₂ ⟨h₂, a2⟩]`.
-/
theorem eq_of_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {g₁ g₂ : GL (Fin N) k} (h₁ : g₁ ∈ R) (h₂ : g₂ ∈ R) (h : g₁⁻¹ * g₂ ∈ KO k (Fin N)) : g₁ = g₂ := by
  obtain ⟨κ, hκ, κ', hκ', e⟩ := hR.1 g₂ h₂
  obtain ⟨g, -, hu⟩ := hR.2 κ hκ
  have a2 : g₂⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₂⁻¹ * (κ * g₀) = κ'⁻¹ := by rw [e]; group
    rw [this]; exact inv_mem hκ'
  have a1 : g₁⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₁⁻¹ * (κ * g₀) = (g₁⁻¹ * g₂) * (g₂⁻¹ * (κ * g₀)) := by group
    rw [this]; exact mul_mem h a2
  rw [hu g₁ ⟨h₁, a1⟩, hu g₂ ⟨h₂, a2⟩]

/- English proof (translation)
Take `⟨κ₁, hκ₁, κ₁', hκ₁', e⟩` from `hR.1 g hg`. Take `⟨g', ⟨hg', hm⟩, -⟩` from `hR.2 (κ * κ₁) (mul_mem hκ hκ₁)`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Establish `: g'⁻¹ * (κ * g) = (g'⁻¹ * (κ * κ₁ * g₀)) * κ₁'` using `by rw [e]; group`. Rewrite using `[this]`.

Conclude with `mul_mem hm hκ₁'`.
-/
theorem exists_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) {g : GL (Fin N) k} (hg : g ∈ R) :
    ∃ g' ∈ R, g'⁻¹ * (κ * g) ∈ KO k (Fin N) := by
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', e⟩ := hR.1 g hg
  obtain ⟨g', ⟨hg', hm⟩, -⟩ := hR.2 (κ * κ₁) (mul_mem hκ hκ₁)
  refine ⟨g', hg', ?_⟩
  have : g'⁻¹ * (κ * g) = (g'⁻¹ * (κ * κ₁ * g₀)) * κ₁' := by rw [e]; group
  rw [this]; exact mul_mem hm hκ₁'

/- English proof (translation)
Use `choose f hf hfK using fun g (hg : g ∈ R) => exists_isRepsK hR hκ hg`. Use `Finset.sum_bij f hf (fun a ha b hb e => ?_) (fun c hc => ?_) (fun a ha => ?_)` and prove the remaining obligations. Establish `h1` using `hfK a ha`. Establish `h2` using `hfK b hb`. Rewrite `h1` using `[e]`.

Apply `eq_of_isRepsK hR ha hb` to reduce the goal to its premises. Establish `: a⁻¹ * b = ((f b hb)⁻¹ * (κ * a))⁻¹ * ((f b hb)⁻¹ * (κ * b))` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem (inv_mem h1) h2`. Take `⟨a, ha, hm⟩` from `exists_isRepsK hR (inv_mem hκ) hc`.

Use `⟨a, ha, eq_of_isRepsK hR (hf a ha) hc ?_⟩` and prove the remaining obligations. Establish `: (f a ha)⁻¹ * c = ((f a ha)⁻¹ * (κ * a)) * (a⁻¹ * (κ⁻¹ * c))` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem (hfK a ha) hm`. Establish `: κ * a = f a ha * ((f a ha)⁻¹ * (κ * a))` using `by group`.

Rewrite using `[this, h.1 _ _ (hfK a ha)]`.
-/
theorem sum_kappa_mul {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ)
    {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) : ∑ g ∈ R, ψ (κ * g) = ∑ g ∈ R, ψ g := by
  classical
  choose f hf hfK using fun g (hg : g ∈ R) => exists_isRepsK hR hκ hg
  refine Finset.sum_bij f hf (fun a ha b hb e => ?_) (fun c hc => ?_) (fun a ha => ?_)
  · have h1 := hfK a ha
    have h2 := hfK b hb
    rw [e] at h1
    apply eq_of_isRepsK hR ha hb
    have : a⁻¹ * b = ((f b hb)⁻¹ * (κ * a))⁻¹ * ((f b hb)⁻¹ * (κ * b)) := by group
    rw [this]; exact mul_mem (inv_mem h1) h2
  · obtain ⟨a, ha, hm⟩ := exists_isRepsK hR (inv_mem hκ) hc
    refine ⟨a, ha, eq_of_isRepsK hR (hf a ha) hc ?_⟩
    have : (f a ha)⁻¹ * c = ((f a ha)⁻¹ * (κ * a)) * (a⁻¹ * (κ⁻¹ * c)) := by group
    rw [this]; exact mul_mem (hfK a ha) hm
  · have : κ * a = f a ha * ((f a ha)⁻¹ * (κ * a)) := by group
    rw [this, h.1 _ _ (hfK a ha)]

end GlobalTheory.ZonalSum

open GlobalTheory.ZonalSum in

/- English proof (translation)
Introduce `k _ _ _ _ N γ ψ h hγ g₀ R hR m`. Take `⟨b, hb, κ, hκ, rfl⟩` from `iwasawa_blockTriangular k (Fin N) Fin.val m`. Establish `hb' : b ∈ borel k (Fin N)` using `(mem_borel _).2 hb`. Establish `e : ∀ g, ψ (b * κ * g) = ψ b * ψ (κ * g)` using `fun g => by`. Rewrite using `[mul_assoc]`.

Conclude with `borelSph_mul_left h hγ hb' _`. Simplify using `only [e]`. Rewrite using `[← Finset.mul_sum, sum_kappa_mul h hR hκ, h.1 _ _ hκ]`.
-/
theorem GlobalTheory.ZonalSum.sum_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  intro k _ _ _ _ N γ ψ h hγ g₀ R hR m
  obtain ⟨b, hb, κ, hκ, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val m
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have e : ∀ g, ψ (b * κ * g) = ψ b * ψ (κ * g) := fun g => by
    rw [mul_assoc]; exact borelSph_mul_left h hγ hb' _
  simp only [e]
  rw [← Finset.mul_sum, sum_kappa_mul h hR hκ, h.1 _ _ hκ]

end
