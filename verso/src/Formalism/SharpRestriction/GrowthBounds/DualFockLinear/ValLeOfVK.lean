import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.XiStepNOfP
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14 Formalism.MainNotions.G.Joints

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨q, hq, hqD⟩` from `h`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : vK p (algebraMap O (KK O) 0) = ⊤` using `by simp [vK, ordW]`. Rewrite `hq` using `[h0]`.

Conclude with `WithTop.top_ne_coe hq`. Rewrite `hq` using `[vK_alg p a ha]`. Establish `hq' : (nv a : ℚ) / (ramE p O : ℚ) = q` using `WithTop.coe_injective hq`. Establish `hr : (0 : ℝ) < (ramE p O : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero (ramE_ne_zero S)`. Establish `hle : nv a ≤ D * ramE p O`.

Rewrite `hqD` using `[← hq']`. Move the coercions through the operations in `at hqD`. Rewrite `hqD` using `[div_le_iff₀ hr]`. Conclude with `hqD` after adjusting the coercions. Establish `hne : IsDiscreteValuationRing.addVal O a ≠ ⊤` using `fun h0 => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)`.

Establish `hne' : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤` using `fun h0 => S.p_ne (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)`. Establish `e1 : IsDiscreteValuationRing.addVal O a = (nv a : ℕ∞)` using `(ENat.coe_toNat hne).symm`. Establish `e2 : IsDiscreteValuationRing.addVal O (p : O) = (ramE p O : ℕ∞)` using `(ENat.coe_toNat hne').symm`. Establish `hdvd : a ∣ (p : O) ^ D`. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, e1, e2, nsmul_eq_mul]`.

Conclude with `hle` after adjusting the coercions. Take `⟨b, hb⟩` from `hdvd`. Conclude with `⟨a, b, rfl, hb.symm⟩`.
-/
theorem valLe_of_vK {p : ℕ} (S : UniformizedDVR p O) (D : ℕ) (a : O)
    (h : Formalism.MainNotions.PlaneGramData.leQ (vK p (algebraMap O (KK O) a)) (D : ℝ)) :
    ValLe (Kf := KK O) (p : O) D (algebraMap O (KK O) a) := by
  obtain ⟨q, hq, hqD⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : vK p (algebraMap O (KK O) 0) = ⊤ := by simp [vK, ordW]
    rw [h0] at hq
    exact WithTop.top_ne_coe hq
  rw [vK_alg p a ha] at hq
  have hq' : (nv a : ℚ) / (ramE p O : ℚ) = q := WithTop.coe_injective hq
  have hr : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (ramE_ne_zero S)
  have hle : nv a ≤ D * ramE p O := by
    rw [← hq'] at hqD
    push_cast at hqD
    rw [div_le_iff₀ hr] at hqD
    exact_mod_cast hqD
  have hne : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h0 =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have hne' : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := fun h0 =>
    S.p_ne (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have e1 : IsDiscreteValuationRing.addVal O a = (nv a : ℕ∞) := (ENat.coe_toNat hne).symm
  have e2 : IsDiscreteValuationRing.addVal O (p : O) = (ramE p O : ℕ∞) := (ENat.coe_toNat hne').symm
  have hdvd : a ∣ (p : O) ^ D := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, e1, e2,
      nsmul_eq_mul]
    exact_mod_cast hle
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨a, b, rfl, hb.symm⟩

end Formalism.MainNotions.TestSideCounting
