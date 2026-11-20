import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ToMatrixMulVec

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def Th (e : Matrix (Fin N) (Fin N) k) : Module.End k (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun f := LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e)
  map_add' f g := by rw [← map_add]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma Th_mulVec (f : Module.End k (Wd e)) (v : Fin N → k) : Th e f *ᵥ v = (f (Pe e v) : Fin N → k) := by
  show LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e) *ᵥ v = _
  exact toMatrix'_mulVec' _ v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
lemma Th_inj : Function.Injective (Th (k := k) (N := N) e) := by
  intro f g h
  ext w : 1
  obtain ⟨v, rfl⟩ := Pe_surj e w
  have := congrArg (· *ᵥ v) h
  simp only [Th_mulVec] at this
  exact Subtype.ext this

variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma Th_rho (a : A) : Th e (rho hA he a) = e * a.1 := by
  apply mat_ext; intro v
  rw [Th_mulVec, rho_apply]
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA _ a.2 _ he]

abbrev Fe : Subalgebra k (Module.End k (Wd e)) := (rho hA he).range

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
lemma map_Th_Fe : (Fe hA he).toSubmodule.map (Th e) = A.toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.1, a.2, by simp [Th_rho hA he]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho hA he ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, by simp [Th_rho hA he]⟩

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma Fe_isField (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) : IsField (Fe hA he) := by
  have hW : ∃ v : Fin N → k, e *ᵥ v ≠ 0 := by
    by_contra h; push Not at h; exact hne (mat_ext fun v => by simp [h v])
  obtain ⟨v₀, hv₀⟩ := hW
  refine ⟨⟨0, 1, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (fun x : Fe hA he => ((x.1 (Pe e v₀) : Wd e) : Fin N → k)) h
    change 0 = e *ᵥ v₀ at this
    exact hv₀ this.symm
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show rho hA he a * rho hA he b = rho hA he b * rho hA he a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ a.2 _ b.2)
  · rintro ⟨_, a, rfl⟩ hx
    have hea : e * a.1 ≠ 0 := by
      intro h0; apply hx; apply Subtype.ext
      ext w : 1; apply Subtype.ext
      obtain ⟨v, rfl⟩ := Pe_surj e w
      show a.1 *ᵥ (e *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hA _ a.2 _ he, h0, Matrix.zero_mulVec]
    rcases hf a.1 a.2 with h0 | ⟨b, hb, hab⟩
    · exact absurd h0 hea
    refine ⟨⟨rho hA he ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    ext w : 1; apply Subtype.ext
    obtain ⟨v, rfl⟩ := Pe_surj e w
    show a.1 *ᵥ (b *ᵥ (e *ᵥ v)) = e *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hA _ hb _ he, ← mul_assoc,
      hA _ a.2 _ he, hab]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
