import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FeIsField

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

instance Fe_tower : IsScalarTower k (Fe hA he) (Wd e) := ⟨fun _ _ _ => rfl⟩

def Psi : Module.End (Fe hA he) (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun φ := Th e (φ.restrictScalars k)
  map_add' f g := by rw [← map_add]; rfl
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; rfl

/- English proof (translation)
The claim follows from `Th_mulVec (φ.restrictScalars k) v`.
-/
lemma Psi_mulVec (φ : Module.End (Fe hA he) (Wd e)) (v : Fin N → k) :
    Psi hA he φ *ᵥ v = (φ (Pe e v) : Fin N → k) := Th_mulVec (φ.restrictScalars k) v

/- English proof (translation)
Introduce `f g h`. Use `Th_inj h` as an intermediate fact. Use extensionality with `w : 1`. Conclude with `congrArg (fun F : Module.End k (Wd e) => F w) this`.
-/
lemma Psi_inj : Function.Injective (Psi hA he) := by
  intro f g h
  have := Th_inj h
  ext w : 1
  exact congrArg (fun F : Module.End k (Wd e) => F w) this

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show e *ᵥ (a.1 *ᵥ v) = a.1 *ᵥ (e *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA _ a.2 _ he]`.
-/
lemma Pe_smul (a : A) (v : Fin N → k) :
    Pe e (a.1 *ᵥ v) = (⟨rho hA he a, a, rfl⟩ : Fe hA he) • Pe e v := by
  apply Subtype.ext
  show e *ᵥ (a.1 *ᵥ v) = a.1 *ᵥ (e *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA _ a.2 _ he]

def phiOf (c : Matrix (Fin N) (Fin N) k) (hc : ∀ a ∈ A, a * c = c * a) : Module.End (Fe hA he) (Wd e) where
  toFun w := ⟨c *ᵥ (w : Fin N → k), W_stable (hc e he).symm w.2⟩
  map_add' w w' := by apply Subtype.ext; exact Matrix.mulVec_add c w.1 w'.1
  map_smul' := by
    rintro ⟨_, a, rfl⟩ w
    apply Subtype.ext
    show c *ᵥ (a.1 *ᵥ (w : Fin N → k)) = a.1 *ᵥ (c *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc _ a.2]

/- English proof (translation)
Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, rfl⟩`. Use `⟨Psi hA he φ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]`.

Introduce `a ha`. Apply `mat_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Psi_mulVec, Psi_mulVec, Pe_smul hA he ⟨a, ha⟩, map_smul]`. Both sides reduce to the same expression.

Apply `mat_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [LinearMap.mulLeft_apply]`. Rewrite using `[← Matrix.mulVec_mulVec, Psi_mulVec]`. Conclude with `W_fix hid (φ (Pe e v)).2`.

Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite `hc` using `[SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]`. Use `⟨phiOf hA he c hc, ?_⟩` and prove the remaining obligations. Apply `mat_ext` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[Psi_mulVec]`. Use `show c *ᵥ (e *ᵥ v) = (e * c) *ᵥ v`. Rewrite using `[Matrix.mulVec_mulVec, hc e he]`.
-/
lemma range_Psi (hid : IsIdempotentElem e) :
    LinearMap.range (Psi hA he) =
      (Subalgebra.centralizer k (A : Set (Matrix (Fin N) (Fin N) k))).toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨Psi hA he φ, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      intro a ha
      apply mat_ext; intro v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Psi_mulVec, Psi_mulVec,
        Pe_smul hA he ⟨a, ha⟩, map_smul]
      rfl
    · apply mat_ext; intro v
      simp only [LinearMap.mulLeft_apply]
      rw [← Matrix.mulVec_mulVec, Psi_mulVec]
      exact W_fix hid (φ (Pe e v)).2
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hc
    refine ⟨phiOf hA he c hc, ?_⟩
    apply mat_ext; intro v
    rw [Psi_mulVec]
    show c *ᵥ (e *ᵥ v) = (e * c) *ᵥ v
    rw [Matrix.mulVec_mulVec, hc e he]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
