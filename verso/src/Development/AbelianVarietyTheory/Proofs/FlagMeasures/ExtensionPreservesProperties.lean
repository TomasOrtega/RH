import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SURestrict

variable {n : ℕ}

/- English proof (translation)
Use `⟨?_, by simp⟩` and prove the remaining obligations. Use `show inUJ ε 1`. Simplify using `[inUJ]`.
-/
theorem one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show inUJ ε 1
  simp [inUJ]

/- English proof (translation)
Take `⟨ha1, ha2⟩` from `ha`. Take `⟨hb1, hb2⟩` from `hb`. Use `⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩` and prove the remaining obligations. Establish `ha1' : aᴴ * Jm ε * a = Jm ε` using `ha1`. Establish `hb1' : bᴴ * Jm ε * b = Jm ε` using `hb1`.

Use `show (a * b)ᴴ * Jm ε * (a * b) = Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Jm ε := by rw [ha1', hb1']`.
-/
theorem mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  have ha1' : aᴴ * Jm ε * a = Jm ε := ha1
  have hb1' : bᴴ * Jm ε * b = Jm ε := hb1
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha1', hb1']

/- English proof (translation)
Take `⟨hu, hc⟩` from `hg`. Establish `h1 : star g * g = 1` using `(Matrix.mem_unitaryGroup_iff').mp hu`. Use `show gᴴ * Jm ε * g = Jm ε`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Kset_sub_UJset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').mp hu
  show gᴴ * Jm ε * g = Jm ε
  calc gᴴ * Jm ε * g = gᴴ * (g * Jm ε) := by rw [Matrix.mul_assoc, hc]
    _ = (star g * g) * Jm ε := by rw [← Matrix.mul_assoc]; rfl
    _ = Jm ε := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Kset_sub_UJset hg.1, hg.2⟩`.
-/
theorem KS_sub_SUset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ KS ε) :
    g ∈ SUset ε := ⟨Kset_sub_UJset hg.1, hg.2⟩

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Use `he 1 (by simp) g hg` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_on_SU {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : Ext ε m π' π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

/- English proof (translation)
Introduce `n hn ε H _ _ m π' π he`. Take `⟨hsplit, -, -⟩` from `GlobalTheory.T.unitary_to_special_unitary_local n hn ε`. Establish `heq : ∀ g ∈ SUset ε, π g = π' g` using `fun g hg => eq_on_SU he hg`. Establish `hSU : ∀ g ∈ SUset ε, g ∈ UJset ε` using `fun g hg => hg.1`. Establish `hstab : ∀ S : Submodule ℂ H, (∀ g ∈ UJset ε, ∀ v ∈ S, π g v ∈ S) ↔ (∀ g ∈ SUset ε, ∀ v ∈ S, π' g v ∈ S)`.

Introduce `S`. Prove the components needed by the constructor for the conclusion. Introduce `h g hg v hv`. Rewrite using `[← heq g hg]`. Conclude with `h g (hSU g hg) v hv`.

Introduce `h g hg v hv`. Take `⟨z, hz, g₀, hg₀, rfl, -⟩` from `hsplit g hg`. Rewrite using `[he z hz g₀ hg₀]`. Conclude with `S.smul_mem _ (h g₀ hg₀ v hv)`. Establish `hK : ∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S`.

Introduce `S`. Prove the components needed by the constructor for the conclusion. Introduce `h g hg v hv`. Rewrite using `[← heq g (KS_sub_SUset hg)]`. Conclude with `h g hg.1 v hv`.

Introduce `h g hg v hv`. Take `⟨z, hz, g₀, hg₀, rfl, hiff⟩` from `hsplit g (Kset_sub_UJset hg)`. Rewrite using `[he z hz g₀ hg₀]`. Conclude with `S.smul_mem _ (h g₀ (hiff.mp hg) v hv)`. Use `⟨?_, ?_, hK, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨h1, hmul⟩, hiso, hcont⟩`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← heq 1 (one_mem_SUset ε)]`. Conclude with `h1`. Introduce `a ha b hb`.

Rewrite using `[← heq _ (mul_mem_SUset ha hb), ← heq a ha, ← heq b hb]`. Conclude with `hmul a (hSU a ha) b (hSU b hb)`. Introduce `g hg v`. Rewrite using `[← heq g hg]`. Conclude with `hiso g (hSU g hg) v`.

Introduce `v`. Conclude with `((hcont v).mono (fun g hg => hSU g hg)).congr (fun g hg => by simp only [heq g hg])`. Prove the components needed by the constructor for the conclusion. Introduce `h S hS hst`. Conclude with `h S hS ((hstab S).mpr hst)`.

Introduce `h S hS hst`. Conclude with `h S hS ((hstab S).mp hst)`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hfd, hv, hs⟩`.

Conclude with `⟨S, hfd, hv, (hK S).mp hs⟩`. Introduce and unpack `⟨S, hfd, hv, hs⟩`. Conclude with `⟨S, hfd, hv, (hK S).mpr hs⟩`.
-/
theorem restrict_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (IsURepOn (UJset ε) π → IsURepOn (SUset ε) π') ∧ (IsIrredOn (UJset ε) π ↔ IsIrredOn (SUset ε) π') ∧ (∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S) ∧ ∀ v, IsKFin ε π v ↔ IsKFinS ε π' v := by
  intro n hn ε H _ _ m π' π he
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have heq : ∀ g ∈ SUset ε, π g = π' g := fun g hg => eq_on_SU he hg
  have hSU : ∀ g ∈ SUset ε, g ∈ UJset ε := fun g hg => hg.1

  have hstab : ∀ S : Submodule ℂ H, (∀ g ∈ UJset ε, ∀ v ∈ S, π g v ∈ S) ↔
      (∀ g ∈ SUset ε, ∀ v ∈ S, π' g v ∈ S) := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g hg]; exact h g (hSU g hg) v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ hg₀ v hv)
  have hK : ∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g (KS_sub_SUset hg)]; exact h g hg.1 v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, hiff⟩ := hsplit g (Kset_sub_UJset hg)
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ (hiff.mp hg) v hv)
  refine ⟨?_, ?_, hK, ?_⟩
  · rintro ⟨⟨h1, hmul⟩, hiso, hcont⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← heq 1 (one_mem_SUset ε)]; exact h1
    · intro a ha b hb
      rw [← heq _ (mul_mem_SUset ha hb), ← heq a ha, ← heq b hb]
      exact hmul a (hSU a ha) b (hSU b hb)
    · intro g hg v
      rw [← heq g hg]; exact hiso g (hSU g hg) v
    · intro v
      exact ((hcont v).mono (fun g hg => hSU g hg)).congr (fun g hg => by simp only [heq g hg])
  · constructor
    · intro h S hS hst
      exact h S hS ((hstab S).mpr hst)
    · intro h S hS hst
      exact h S hS ((hstab S).mp hst)
  · intro v
    constructor
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mp hs⟩
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mpr hs⟩

end GlobalTheory.SURestrict
