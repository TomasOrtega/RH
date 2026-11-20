import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.LeviUniq

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t m m' hm hm'`. Set `S : Submodule E (Fin d → E)` to `{ carrier := {e | mat m *ᵥ incV F e = mat m' *ᵥ incV F e} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at *`. Establish `: incV F (a + b) = incV F a + incV F b`.

Use function extensionality and compare the values at `i`. Simplify using `[incV, map_add]`. Rewrite using `[this, Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq]`.

Establish `: incV F (0 : Fin d → E) = 0` using `by funext i; simp [incV]`. Rewrite using `[this, Matrix.mulVec_zero, Matrix.mulVec_zero]`. Use the proof step `smul_mem' := by`. Introduce `c a ha`. Simplify using `only [Set.mem_setOf_eq] at *`.

Establish `: incV F (c • a) = inclR (F` using `F) (AF F) c • incV F a := by`. Use function extensionality and compare the values at `i`. Simplify using `[incV, map_mul]`. Rewrite using `[this, Matrix.mulVec_smul, Matrix.mulVec_smul, ha] }`. Establish `hone : mat (1 : UA σ W₁.J) = 1` using `rfl`.

Establish `hι : ∀ (g : UA σ W.J), IsLevi (W₁` using `W₁) H' t 1 g → ∀ u : Fin d₁ → E, mat g *ᵥ incV F (H'.ι *ᵥ u) = incV F (H'.ι *ᵥ u) := by`. Introduce `g hg u`. Establish `hv : incV F (H'.ι *ᵥ u) = incM F H'.ι *ᵥ incV F u`. Use function extensionality and compare the values at `i`. Simplify using `[incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]`.

Rewrite using `[hv, Matrix.mulVec_mulVec, hg.2.2, hone, Matrix.mul_one]`. Establish `hx : H'.x ∈ S` using `by show mat m *ᵥ incV F H'.x = mat m' *ᵥ incV F H'.x`. Rewrite using `[hm.1, hm'.1]`. Establish `hy : H'.y ∈ S` using `by show mat m *ᵥ incV F H'.y = mat m' *ᵥ incV F H'.y`. Rewrite using `[hm.2.1, hm'.2.1]`.

Establish `hιS : ∀ u, H'.ι *ᵥ u ∈ S`. Introduce `u`. Use `show mat m *ᵥ incV F (H'.ι *ᵥ u) = mat m' *ᵥ incV F (H'.ι *ᵥ u)`. Rewrite using `[hι m hm, hι m' hm']`. Establish `hL : ∀ z ∈ W.L, z ∈ S`.

Introduce `z hz`. Take `⟨a, b, u, -, -, -, rfl⟩` from `hH.split z hz`. Conclude with `S.add_mem (S.add_mem (S.smul_mem a hx) (hιS u)) (S.smul_mem b hy)`. Establish `htop : S = ⊤`. Establish `h1 : Submodule.span E (W.L : Set (Fin d → E)) ≤ S` using `Submodule.span_le.2 hL`.

Rewrite `h1` using `[hW.lat.span_eq_top]`. Conclude with `top_le_iff.1 h1`. Establish `hall : ∀ e, mat m *ᵥ incV F e = mat m' *ᵥ incV F e` using `fun e => by`. Establish `: e ∈ S` using `htop ▸ Submodule.mem_top`. Conclude with `this`.

Establish `hmat : mat m = mat m'`. Use extensionality with `i j`. Establish `h` using `congrFun (hall (Pi.single j 1)) i`. Establish `hs : incV F (Pi.single j (1 : E)) = Pi.single j 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[incV]`. Simplify using `[incV, Pi.single_apply, hk]`. Rewrite `h` using `[hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one]`.

Simplify using `using h`. Conclude with `Subtype.ext (Units.ext hmat)`.
-/
theorem levi_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m m' : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t 1 m' → m = m' := by
  intro F E _ _ _ _ _ σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t m m' hm hm'

  let S : Submodule E (Fin d → E) :=
    { carrier := {e | mat m *ᵥ incV F e = mat m' *ᵥ incV F e}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        have : incV F (a + b) = incV F a + incV F b := by
          funext i; simp [incV, map_add]
        rw [this, Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : incV F (0 : Fin d → E) = 0 := by funext i; simp [incV]
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        have : incV F (c • a) = inclR (F := F) (AF F) c • incV F a := by
          funext i; simp [incV, map_mul]
        rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul, ha] }
  have hone : mat (1 : UA σ W₁.J) = 1 := rfl
  have hι : ∀ (g : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 g → ∀ u : Fin d₁ → E,
      mat g *ᵥ incV F (H'.ι *ᵥ u) = incV F (H'.ι *ᵥ u) := by
    intro g hg u
    have hv : incV F (H'.ι *ᵥ u) = incM F H'.ι *ᵥ incV F u := by
      funext i; simp [incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [hv, Matrix.mulVec_mulVec, hg.2.2, hone, Matrix.mul_one]
  have hx : H'.x ∈ S := by
    show mat m *ᵥ incV F H'.x = mat m' *ᵥ incV F H'.x
    rw [hm.1, hm'.1]
  have hy : H'.y ∈ S := by
    show mat m *ᵥ incV F H'.y = mat m' *ᵥ incV F H'.y
    rw [hm.2.1, hm'.2.1]
  have hιS : ∀ u, H'.ι *ᵥ u ∈ S := by
    intro u
    show mat m *ᵥ incV F (H'.ι *ᵥ u) = mat m' *ᵥ incV F (H'.ι *ᵥ u)
    rw [hι m hm, hι m' hm']
  have hL : ∀ z ∈ W.L, z ∈ S := by
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    exact S.add_mem (S.add_mem (S.smul_mem a hx) (hιS u)) (S.smul_mem b hy)
  have htop : S = ⊤ := by
    have h1 : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := Submodule.span_le.2 hL
    rw [hW.lat.span_eq_top] at h1
    exact top_le_iff.1 h1
  have hall : ∀ e, mat m *ᵥ incV F e = mat m' *ᵥ incV F e := fun e => by
    have : e ∈ S := htop ▸ Submodule.mem_top
    exact this
  have hmat : mat m = mat m' := by
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k; by_cases hk : k = j
      · subst hk; simp [incV]
      · simp [incV, Pi.single_apply, hk]
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa using h
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniq
