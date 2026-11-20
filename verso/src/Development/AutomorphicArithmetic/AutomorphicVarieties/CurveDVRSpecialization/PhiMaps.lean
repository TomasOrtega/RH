import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA

namespace UpperTheory.V.Pr

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem gdet_map_inj {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B)
    (hf : Function.Injective f) {D D' : GDet n A G} (h : D.map f = D'.map f) : D = D' := by
  refine d_gext D D' fun g i _ _ => hf ?_
  rw [← ((d_gmap D).2.2.1 f _).2 i, ← ((d_gmap D').2.2.1 f _).2 i, h]

section Link

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem TwLink.tw_map (f : A →ₐ[O] A') (ρ : NRep F n A) :
    K.tw (ρ.map (f : A →+* A')) = (f : A →+* A').mapMatrix.toMonoidHom.comp (K.tw ρ) := by
  ext g i j
  change algebraMap O A' (K.κ g) * f (ρ.r (K.π g) i j) = f (algebraMap O A (K.κ g) * ρ.r (K.π g) i j)
  rw [map_mul, f.commutes]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem TwLink.ofRep_tw_map (f : A →ₐ[O] A') (ρ : NRep F n A) :
    (GDet.ofRep (K.tw ρ)).map (f : A →+* A') = GDet.ofRep (K.tw (ρ.map (f : A →+* A'))) := by
  rw [K.tw_map, (d_gmap (GDet.ofRep (K.tw ρ))).2.2.2]

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem TwLink.twψ_map (f : A →ₐ[O] A') (ρ : NRep F n A) (v : G.Vl) (i : Fin n) :
    pushCh (f : A →+* A') (K.twψ ρ v i) = K.twψ (ρ.map (f : A →+* A')) v i := by
  ext g
  change f (ρ.ψ (K.e v) i (K.lam v g) * algebraMap O A (K.κ (G.φ v g))) =
    f (ρ.ψ (K.e v) i (K.lam v g)) * algebraMap O A' (K.κ (G.φ v g))
  rw [map_mul, f.commutes]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem TwLink.tw_irr (ρ : NRep F n A) (h : MatIrr ⊤ ρ.r) : MatIrr ⊤ (K.tw ρ) := by
  intro W hW
  refine h W fun g _ v hv => ?_
  obtain ⟨g', rfl⟩ := K.π_surj g
  have h1 := W.smul_mem (((K.κA A g')⁻¹ : Aˣ) : A) (hW g' trivial v hv)
  change _ • ((((K.κA A g' : Aˣ) : A) • ρ.r (K.π g')) *ᵥ v) ∈ W at h1
  rwa [Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h1

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument.

By extensionality, compare the relevant components. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem TwLink.IsPhi.maps_inc {B : W.UniversalOrdinaryDeterminantRing r} {S : Space O F n} {Φ : B.B →ₐ[O] S.B} (h : K.IsPhi B S Φ) :
    B.u.Maps ((S.inc.comp Φ : B.B →ₐ[O] S.A) : B.B →+* S.A) (GDet.ofRep (K.tw S.u)) (K.twψ S.u) := by
  have e : S.u.map (S.A.val : S.A →+* S.R) = S.ρ := by
    refine NRep.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext g; rfl
  refine ⟨gdet_map_inj (S.A.val : S.A →+* S.R) Subtype.val_injective ?_, fun v i => ?_⟩
  · rw [K.ofRep_tw_map, e, (d_gmap _).2.1, ← h.1]
    rfl
  · have h3 := K.twψ_map S.A.val S.u v i
    rw [e, ← h.2 v i] at h3
    refine MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)
    exact (congrArg (fun χ : G.Gv v →* S.Rˣ => (χ g : S.R)) h3).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem TwLink.IsPhi.maps {B : W.UniversalOrdinaryDeterminantRing r} {S : Space O F n} {Φ : B.B →ₐ[O] S.B} (h : K.IsPhi B S Φ)
    (f : S.A →ₐ[O] A') :
    B.u.Maps ((f.comp (S.inc.comp Φ) : B.B →ₐ[O] A') : B.B →+* A') (GDet.ofRep (K.tw (S.u.map (f : S.A →+* A'))))
      (K.twψ (S.u.map (f : S.A →+* A'))) := by
  obtain ⟨h1, h2⟩ := h.maps_inc
  refine ⟨?_, fun v i => ?_⟩
  · rw [← K.ofRep_tw_map, ← h1, (d_gmap _).2.1]
    rfl
  · rw [← K.twψ_map, ← h2]
    rfl

end Link

end UpperTheory.V.Pr
