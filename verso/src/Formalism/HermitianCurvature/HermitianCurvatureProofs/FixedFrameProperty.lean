import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

/- English proof (translation)
Introduce `k r z hz`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hgV, hfix⟩`. Establish `hS : g ∈ Sset k r z`.

Rewrite using `[← standard_flag_property k r z hz]`. Conclude with `⟨hgV, fun a => by simp [hfix a]⟩`. Use `⟨hS, uMap_eq hz g 1 fun b => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.one_apply, hfix b]`. Introduce and unpack `⟨hS, hU⟩`.

Establish `hS'` using `hS`. Rewrite `hS'` using `[← standard_flag_property k r z hz]`. Use `⟨hS'.1, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[((unipotent_map_frame k r z hz).1 g hS).1 a, hU]`. Simplify using `[Matrix.one_apply]`.
-/
theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

/- English proof (translation)
Introduce `k r z z' hstd g hg _`. Establish `hHdet : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_right_inverse (majorant_estimate k r).2.1`. Take `⟨_, hmul, hinv⟩` from `uHGroup _ (Hpk k r) hHdet`. Establish `hgu : IsUnit g.det` using `(hinv g hg).1`. Establish `hFz` using `fixed_frame_property k r z hstd.2.1`.

Establish `hFz'` using `fixed_frame_property k r z' hstd.2.2`. Use extensionality with `⟨p, q⟩`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, hq, hpq⟩`.

Rewrite `hp` using `[← hFz]`. Establish `hpu : IsUnit p.det` using `(hinv p hp.1).1`. Establish `h1 : g * q = p * g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hpu, Matrix.one_mul]`.

Use `_ = p * g := by rw [hpq]`. Establish `hq_eq : g⁻¹ * p * g = q`. Combine the equalities or inequalities in the displayed calculation. Use `⟨p, ⟨hp.1, ?_⟩, rfl, hq_eq⟩` and prove the remaining obligations. Introduce and unpack `(a | b)`.

Conclude with `hp.2 a`. Rewrite using `[← hFz'] at hq show p *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b`. Rewrite using `[Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, hq.2 b]`. Introduce and unpack `⟨h, ⟨hhV, hhfix⟩, rfl, rfl⟩`. Establish `hhu : IsUnit h.det` using `(hinv h hhV).1`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hFz]`. Conclude with `⟨hhV, fun a => hhfix (Sum.inl a)⟩`. Rewrite using `[← hFz']`. Use `⟨hmul _ (hmul _ (hinv g hg).2 h hhV) g hg, fun b => ?_⟩` and prove the remaining obligations.

Establish `hb : h *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b` using `hhfix (Sum.inr b)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul]`.
-/
theorem fibre_stabilizer : C2.FibreStab := by
  intro k r z z' hstd g hg _
  have hHdet : IsUnit (Hpk k r).det :=
    Matrix.isUnit_det_of_right_inverse (majorant_estimate k r).2.1
  obtain ⟨_, hmul, hinv⟩ := uHGroup _ (Hpk k r) hHdet
  have hgu : IsUnit g.det := (hinv g hg).1
  have hFz := fixed_frame_property k r z hstd.2.1
  have hFz' := fixed_frame_property k r z' hstd.2.2
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq⟩
    rw [← hFz] at hp
    have hpu : IsUnit p.det := (hinv p hp.1).1
    have h1 : g * q = p * g := by
      calc g * q = p * (p⁻¹ * g * q) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hpu, Matrix.one_mul]
        _ = p * g := by rw [hpq]
    have hq_eq : g⁻¹ * p * g = q := by
      calc g⁻¹ * p * g = g⁻¹ * (g * q) := by rw [h1, Matrix.mul_assoc]
        _ = q := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    refine ⟨p, ⟨hp.1, ?_⟩, rfl, hq_eq⟩
    rintro (a | b)
    · exact hp.2 a
    · rw [← hFz'] at hq
      show p *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b
      rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, hq.2 b]
  · rintro ⟨h, ⟨hhV, hhfix⟩, rfl, rfl⟩
    have hhu : IsUnit h.det := (hinv h hhV).1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hFz]
      exact ⟨hhV, fun a => hhfix (Sum.inl a)⟩
    · rw [← hFz']
      refine ⟨hmul _ (hmul _ (hinv g hg).2 h hhV) g hg, fun b => ?_⟩
      have hb : h *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b := hhfix (Sum.inr b)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hgu, Matrix.one_mulVec]
    · calc h⁻¹ * g * (g⁻¹ * h * g) = h⁻¹ * (g * g⁻¹) * h * g := by simp only [Matrix.mul_assoc]
        _ = g := by
          rw [Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul]

end Formalism.FourierDecayAlt.P
