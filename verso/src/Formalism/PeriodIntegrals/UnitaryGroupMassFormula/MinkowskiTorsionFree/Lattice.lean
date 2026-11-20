import Mathlib
import Formalism.PeriodIntegrals.MinkowskiQ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski

namespace PI.MkQ

open Matrix

variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))

def orbitSet : Set (Fin N → ℚ) :=
  Set.range fun p : G × Fin N =>
    ((p.1 : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single p.2 1)

def lat : Submodule ℤ (Fin N → ℚ) := Submodule.span ℤ (orbitSet G)

/- English proof (translation)
Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨(1, i), ?_⟩` and prove the remaining obligations. Use `show (((1 : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 = Pi.single i 1`. Conclude with `Matrix.one_mulVec _`.
-/
theorem single_mem (i : Fin N) : (Pi.single i 1 : Fin N → ℚ) ∈ lat G := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  show (((1 : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
    Pi.single i 1
  exact Matrix.one_mulVec _

/- English proof (translation)
Establish `hv' : v ∈ Submodule.span ℤ (orbitSet G)` using `hv`. Use `clear hv`. Proceed by induction on `hv' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨h, i⟩, rfl⟩` from `hx`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨(g * h, i), ?_⟩` and prove the remaining obligations. Use `show (((g * h : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 = ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ (((h : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1)`. Rewrite using `[Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem mulVec_mem (g : G) {v : Fin N → ℚ} (hv : v ∈ lat G) :
    ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v ∈ lat G := by
  have hv' : v ∈ Submodule.span ℤ (orbitSet G) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    show (((g * h : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ
        (((h : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec]
    rfl
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

noncomputable def rho : G →* Module.End ℤ (lat G) where
  toFun g := ((((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVecLin).restrictScalars
    ℤ).restrict (fun v hv => mulVec_mem G g hv)
  map_one' := by ext v i; simp
  map_mul' g g' := by
    ext v : 1
    apply Subtype.ext
    show _ = ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec
      (((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (v : Fin N → ℚ))
    simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho_apply_coe (g : G) (v : lat G) :
    ((rho G g v : lat G) : Fin N → ℚ) =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v := rfl

section finite

variable [Finite G]

/- English proof (translation)
The claim follows from `Set.finite_range _`.
-/
theorem orbitSet_finite : (orbitSet G).Finite := Set.finite_range _

instance : Module.Finite ℤ (lat G) := Module.Finite.span_of_finite ℤ (orbitSet_finite G)

instance : Module.IsTorsionFree ℤ (lat G) := inferInstance

instance : Module.Free ℤ (lat G) := Module.free_of_finite_type_torsion_free'

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1 : LinearIndependent ℤ (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ))` using `(Module.Free.chooseBasis ℤ (lat G)).linearIndependent.map' (lat G).subtype (Submodule.ker_subtype _)`. Establish `h2 : LinearIndependent ℚ (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ))` using `(LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h1`. Simplify using `using h2.fintype_card_le_finrank`. Establish `h3 : LinearIndependent ℚ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ))`.

Establish `h7` using `(Pi.basisFun ℚ (Fin N)).linearIndependent`. Rewrite using `[show ⇑(Pi.basisFun ℚ (Fin N)) = fun i : Fin N => (Pi.single i 1 : Fin N → ℚ) from` and apply the resulting hypothesis. Use function extensionality and compare the values at `fun i => by simp] at h7`. Establish `h4 : LinearIndependent ℤ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ))` using `(LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).2 h3`. Establish `h5 : LinearIndependent ℤ (fun i : Fin N => (⟨Pi.single i 1, single_mem G i⟩ : lat G))` using `LinearIndependent.of_comp (lat G).subtype h4`.

Establish `h6` using `h5.fintype_card_le_finrank`. Rewrite `h6` using `[Module.finrank_eq_card_chooseBasisIndex]`. Simplify using `using h6`.
-/
theorem card_basis : Fintype.card (Module.Free.ChooseBasisIndex ℤ (lat G)) = N := by
  classical
  apply le_antisymm
  · have h1 : LinearIndependent ℤ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (Module.Free.chooseBasis ℤ (lat G)).linearIndependent.map' (lat G).subtype
        (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℚ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h1
    simpa using h2.fintype_card_le_finrank
  · have h3 : LinearIndependent ℚ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) := by
      have h7 := (Pi.basisFun ℚ (Fin N)).linearIndependent
      rwa [show ⇑(Pi.basisFun ℚ (Fin N)) = fun i : Fin N => (Pi.single i 1 : Fin N → ℚ) from
        funext fun i => by simp] at h7
    have h4 : LinearIndependent ℤ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).2 h3
    have h5 : LinearIndependent ℤ (fun i : Fin N => (⟨Pi.single i 1, single_mem G i⟩ : lat G)) :=
      LinearIndependent.of_comp (lat G).subtype h4
    have h6 := h5.fintype_card_le_finrank
    rw [Module.finrank_eq_card_chooseBasisIndex] at h6
    simpa using h6

noncomputable def basisFin : Module.Basis (Fin N) ℤ (lat G) :=
  (Module.Free.chooseBasis ℤ (lat G)).reindex (Fintype.equivFinOfCardEq (card_basis G))

noncomputable def phi : G →* GeneralLinearGroup (Fin N) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisFin G)).toRingEquiv.toMonoidHom).comp
    (rho G).toHomUnits

/- English proof (translation)
Introduce `g g' h`. Establish `h1 : rho G g = rho G g'`. Establish `h0` using `congrArg (fun u : GeneralLinearGroup (Fin N) ℤ => (u : Matrix (Fin N) (Fin N) ℤ)) h`. Express the relevant statement in the definitionally equal form `(LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g) = (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g') at h0`. Conclude with `(LinearMap.toMatrixAlgEquiv (basisFin G)).injective h0`.

Establish `h2 : ∀ i, ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) = ((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1)`. Introduce `i`. Establish `h0` using `congrArg (fun f : Module.End ℤ (lat G) => ((f ⟨Pi.single i 1, single_mem G i⟩ : lat G) : Fin N → ℚ)) h1`. Simplify `h0` using `[rho_apply_coe]`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Establish `h0` using `congrFun (h2 b) a`. Simplify `h0` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem phi_injective : Function.Injective (phi G) := by
  intro g g' h
  have h1 : rho G g = rho G g' := by
    have h0 := congrArg (fun u : GeneralLinearGroup (Fin N) ℤ => (u : Matrix (Fin N) (Fin N) ℤ)) h
    change (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g) =
      (LinearMap.toMatrixAlgEquiv (basisFin G)) (rho G g') at h0
    exact (LinearMap.toMatrixAlgEquiv (basisFin G)).injective h0
  have h2 : ∀ i, ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) =
      ((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single i 1) := by
    intro i
    have h0 := congrArg
      (fun f : Module.End ℤ (lat G) => ((f ⟨Pi.single i 1, single_mem G i⟩ : lat G) : Fin N → ℚ)) h1
    simpa [rho_apply_coe] using h0
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h0 := congrFun (h2 b) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0

end finite

/- English proof (translation)
Introduce `N G hG`. Set `e` to `MonoidHom.ofInjective (phi_injective G)`. Establish `: Finite (phi G).range` using `Finite.of_equiv _ e.toEquiv`. Rewrite using `[Nat.card_congr e.toEquiv]`. Conclude with `card_dvd_minkowskiNumber N _ inferInstance`.
-/
theorem minkowskiBoundQ : PI.MinkowskiBoundQ := by
  intro N G hG
  let e := MonoidHom.ofInjective (phi_injective G)
  have : Finite (phi G).range := Finite.of_equiv _ e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact card_dvd_minkowskiNumber N _ inferInstance

end PI.MkQ
