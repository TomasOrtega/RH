import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellInversePair

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh.1`. Establish `key : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v`. Introduce `v hv`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨WeylGroupFacts.uh_inv hh.1, fun a => ⟨key _ (hh.2.1 a).1, key _ (hh.2.1 a).2⟩, key _ hh.2.2⟩`.
-/
theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨WeylGroupFacts.uh_inv hh.1, fun a => ⟨key _ (hh.2.1 a).1, key _ (hh.2.1 a).2⟩, key _ hh.2.2⟩

def invP (p : SS k r) : SS k r :=
  ((((Matrix.of p.1.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * (Matrix.of p.1.1 : Mat k r) : Mat k r)),
    (((Matrix.of p.2.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ * (Matrix.of p.2.1 : Mat k r) : Mat k r)))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hp`. Establish `hu1` using `WeylGroupFacts.isUnit_of_uh h1.1`. Establish `hu3` using `WeylGroupFacts.isUnit_of_uh h3.1`. Use `⟨uw_inv h1, ?_, uw_inv h3, ?_⟩` and prove the remaining obligations. Use `(uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1` as an intermediate fact.

Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hu1]`. Then use the resulting hypothesis. Use `(uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1` as an intermediate fact. Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hu3]`. Then use the resulting hypothesis.
-/
theorem invP_inSS (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : D.inSS (invP p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  refine ⟨uw_inv h1, ?_, uw_inv h3, ?_⟩
  · have := (uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu1] at this
  · have := (uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu3] at this

/- English proof (translation)
Use `show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 …`. Generalize the expression as in `(Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢`. Generalize the expression as in `(Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢`. Generalize the expression as in `(Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢`. Generalize the expression as in `(Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢`.

Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1, Matrix.nonsing_inv_nonsing_inv B hp2]`. Simplify using `only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left, Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]`.
-/
theorem sgs_invP (p : SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : Mat k r).det) (hp2 : IsUnit (Matrix.of p.1.2 : Mat k r).det)
    (hp3 : IsUnit (Matrix.of p.2.1 : Mat k r).det) (hp4 : IsUnit (Matrix.of p.2.2 : Mat k r).det) (x : Mat k r) :
    sgs (invP p) (sgs p x) = x := by
  show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ *
      Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x *
      Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ *
      Matrix.of p.2.1) * (Matrix.of p.2.1 : Mat k r)⁻¹ = x
  generalize (Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢
  generalize (Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢
  generalize (Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢
  generalize (Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1,
    Matrix.nonsing_inv_nonsing_inv B hp2]
  simp only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
    Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]

end Formalism.FourierDecayAlt.P.BigCellInversePair

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

/- English proof (translation)
Introduce `hOnto k r Wp Wq _ _ _ _ D f f' hf hf' hq g hg`. Take `⟨p, hp, q, hqD, rfl⟩` from `hOnto k r Wp Wq D g hg`. Establish `hx` using `BigCellInversePair.sgs_invP p (WeylGroupFacts.isUnit_of_uh hp.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.2.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.2.2.1) (gq D q)`. Establish `hP` using `BigCellInversePair.invP_inSS D hp`. Rewrite using `[← hf _ hP _ hg, ← hf' _ hP _ hg]`.

Unfold `rho`. Rewrite using `[hx, hq q hqD]`.
-/
theorem equiv_det_of_onto : Formalism.FourierDecayAlt.JF.EquivDetOfOnto := by
  intro hOnto k r Wp Wq _ _ _ _ D f f' hf hf' hq g hg
  obtain ⟨p, hp, q, hqD, rfl⟩ := hOnto k r Wp Wq D g hg
  have hx := BigCellInversePair.sgs_invP p (WeylGroupFacts.isUnit_of_uh hp.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.1.1)
    (WeylGroupFacts.isUnit_of_uh hp.2.2.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.2.2.1) (gq D q)
  have hP := BigCellInversePair.invP_inSS D hp
  rw [← hf _ hP _ hg, ← hf' _ hP _ hg]
  unfold rho
  rw [hx, hq q hqD]

/- English proof (translation)
Introduce `hJ hG k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC`. Use `filter_upwards [hG k r Wp Wq D] with q hq`. Conclude with `(hJ k r Wp Wq D A m F Θ ho hT hF hC _ hq).symm`.
-/
theorem radial_part_intertwines_of_parts : Formalism.FourierDecayAlt.JF.RadialPartIntertwinesFromComponents := by
  intro hJ hG k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC
  filter_upwards [hG k r Wp Wq D] with q hq
  exact (hJ k r Wp Wq D A m F Θ ho hT hF hC _ hq).symm

end Formalism.FourierDecayAlt.P
