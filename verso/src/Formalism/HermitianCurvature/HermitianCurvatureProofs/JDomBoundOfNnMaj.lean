import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMaj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeas : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

/- English proof (translation)
Introduce `hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC` and use `⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩`.
-/
theorem jDom_of_parts : JDomMeas → JDomBound → Formalism.FourierDecayAlt.JF.JDom := fun hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC =>
  ⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩

variable {k r : ℕ}

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem gv_mul_lemma (a b : Mat k r) (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Unfold `UWset QuantumDeterminants.Nset at hp`. Take `⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩` from `hp`. Unfold `sL`. Conclude with `gv_mul_lemma _ _ h12 h11`.
-/
lemma sL_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sL p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩ := hp
  unfold sL
  exact gv_mul_lemma _ _ h12 h11

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Unfold `UWset QuantumDeterminants.Nset at hp`. Take `⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩` from `hp`. Unfold `sR`. Conclude with `gv_mul_lemma _ _ h22 h21`.
-/
lemma sR_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sR p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩ := hp
  unfold sR
  exact gv_mul_lemma _ _ h22 h21

/- English proof (translation)
Simplify using `[B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]`.
-/
lemma pn_lr (p : SS k r) (u v : List (Mat k r)) :
    B4.pn (B4.lr (u.map (AdL p)) (v.map (AdR p))) =
      (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod := by
  simp [B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]

/- English proof (translation)
Establish `hHH : Hpk k r * Hpk k r = 1` using `Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A` using `fun A => by rw [← mul_assoc, hHH, one_mul]`. Establish `hX' : Xᴴ * Hpk k r + Hpk k r * X = 0` using `hX`. Establish `hy' : yᴴ * Hpk k r * y = Hpk k r` using `hy`. Establish `hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Simplify using `only [mul_assoc] at hy' ⊢`. Rewrite using `[hy', hHH]`. Establish `e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y`. Rewrite using `[hinv]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hHH, mul_one]`. Establish `e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y`. Rewrite using `[hinv]`. Simplify using `only [mul_assoc, hHH']`. Use `show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0`.

Rewrite using `[e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]`.
-/
private theorem inLie_inv_mul_mul_of_mem_gv {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

/- English proof (translation)
Unfold `B4.AllLie B4.lr AdL AdR`. Introduce `x hx`. Simplify using `only [List.mem_append, List.mem_map] at hx`. Break down `hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩` into its components or cases. Conclude with `inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1`.

Conclude with `inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1`.
-/
lemma allLie_ad {p : SS k r} (hL : sL p ∈ GV k r) (hR : sR p ∈ GV k r) {u v : List (Mat k r)}
    (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    B4.AllLie (B4.lr (u.map (AdL p)) (v.map (AdR p))) := by
  unfold B4.AllLie B4.lr AdL AdR
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  · exact inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1
  · exact inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1

/- English proof (translation)
Introduce `hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub`. Take `⟨c, hc⟩` from `hCC`. Take `⟨b, hbI, hb⟩` from `hNN k r Wp Wq D A m hThr K hK hKsub`. Use `⟨fun p => c * b p, hbI.const_mul c, ?_⟩` and prove the remaining obligations. Introduce `u v hu hv hl g hg`.

Use `filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin`. Establish `hgG : g ∈ GV k r` using `(hKsub hg).1`. Establish `hsG : sgs p g ∈ GV k r` using `B7.sgs_mem D hin hgG`. Establish `hN : 0 < gN (sgs p g)` using `B6.gN_pos hsG`. Establish `hgA : 0 < gN (sgs p g) ^ A` using `Real.rpow_pos_of_pos hN A`.

Establish `hc0 : 0 ≤ c`. Establish `h0` using `hc.2 [] [] (by simp) (by simp) (by simp) g hgG`. Conclude with `le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0`. Establish `hall` using `allLie_ad (sL_mem hin) (sR_mem hin) hu hv`. Establish `hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m`.

Rewrite using `[B4.length_lr, List.length_map, List.length_map]`. Conclude with `hl`. Establish `hbd` using `B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG`. Rewrite `hbd` using `[← B4.dLR_eq, pn_lr]`. Use `(B7.norm_rho_le D hin _ g).trans ?_` and prove the remaining obligations.

Establish `h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤ ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A`. Rewrite using `[le_div_iff₀ hgA]`. Combine the linear relations using `[hbd]`. Use `h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))` and prove the remaining obligations. Rewrite using `[Real.rpow_neg hN.le]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem jDomBound_of_nnMaj : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp

end Formalism.FourierDecayAlt.P.JFxDs2
