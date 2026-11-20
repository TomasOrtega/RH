import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def hJ (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hJ_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hJ J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

/- English proof (translation)
Establish `hJij : ∀ i j, starRingEnd E (J j i) = J i j` using `fun i j => by`. Use `congrFun (congrFun hJh i) j` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT]`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x`.

Simplify using `only [Formalism.UG.hform, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_self_apply, hJij]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hJ_symm {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J) :
    (hJ J).IsSymm := by
  have hJij : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJh i) j
    simpa [Formalism.UG.cT] using this
  refine ⟨fun x y => ?_⟩
  change starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x
  simp only [Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_self_apply, hJij]
  ring

/- English proof (translation)
Rewrite using `[hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules.
-/
theorem hJ_single (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by
  rw [hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/- English proof (translation)
Establish `h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[← hJ_single]`. Conclude with `hx _`. Establish `h1` using `Matrix.eq_zero_of_vecMul_eq_zero hdet h0`.

Use function extensionality and compare the values at `i`. Use `congrFun h1 i` as an intermediate fact. Simplify using `using this`.
-/
theorem hJ_nondeg {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) (x : Fin n → E)
    (hx : ∀ y, hJ J x y = 0) : x = 0 := by
  have h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0 := by
    funext j; rw [← hJ_single]; exact hx _
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  funext i
  have := congrFun h1 i
  simpa using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨conjO E r, algebraMap_conjO r⟩`.
-/
theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨conjO E r, algebraMap_conjO r⟩

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`. Use extensionality with `x`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Rewrite using `[hL x]`. Prove the components needed by the constructor for the conclusion.

Introduce `h y hy`. Take `⟨r, hr⟩` from `h y hy`. Conclude with `⟨r, hr⟩`. Introduce `h y hy`. Take `⟨r, hr⟩` from `h y hy`.

Conclude with `⟨r, hr⟩`.
-/
theorem unimod_of_selfDual {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : SelfDual J L) : Formalism.HermitianLatticesTheory.IsUnimodular (hJ J) L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [hL x]
  constructor
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩

/- English proof (translation)
Establish `hu` using `(Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1 (unimod_of_selfDual hL) p hp`. Conclude with `isSelfDualMod_loc ⟨hfg, hsp⟩ hp.isPrime hu`.
-/
theorem selfDualMod_loc {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J)
    {L : Submodule (𝓞 E) (Fin n → E)} (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hL : SelfDual J L) {p : Ideal (𝓞 E)} (hp : p.IsMaximal) :
    IsSelfDualMod (locRing p) (hJ J) (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup := by
  have hu := (Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1
    (unimod_of_selfDual hL) p hp
  exact isSelfDualMod_loc ⟨hfg, hsp⟩ hp.isPrime hu

/- English proof (translation)
Set `A` to `LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))`. Set `B` to `LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))`. Establish `hAB : A * B = 1`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: (g : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, LinearMap.toMatrix'_id]`. Establish `hBA : B * A = 1`. Rewrite using `[← LinearMap.toMatrix'_comp]`.

Establish `: (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, LinearMap.toMatrix'_id]`. Set `γ : GL (Fin n) E` to `⟨A, B, hAB, hBA⟩`.

Establish `hmul : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w` using `fun w => by`. Express the relevant statement in the definitionally equal form `A *ᵥ w = g w`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression. Use `⟨γ, ?_, hmul⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Formalism.UG.cT (starRingEnd E) A * J * A = J`. Use extensionality with `i j`. Establish `e1` using `hg (Pi.single i 1) (Pi.single j 1)`. Establish `hsingle : ∀ k l, hJ J (Pi.single k 1) (Pi.single l 1) = J k l`. Introduce `k l`.

Rewrite using `[hJ_single, Matrix.vecMul, dotProduct]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Simplify using the standard rewrite rules. Rewrite `e1` using `[hsingle]`. Rewrite using `[← e1, hJ_apply, Formalism.UG.hform]`. Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Establish `hcol : ∀ k l, A k l = g (Pi.single l 1) k` using `fun k l => by`.

Simplify using `[A, LinearMap.toMatrix'_apply]`. Simplify using `only [hcol, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gl_of_isom {J : Matrix (Fin n) (Fin n) E} (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ x y, hJ J (g x) (g y) = hJ J x y) :
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := by
  let A := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  let B := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  let γ : GL (Fin n) E := ⟨A, B, hAB, hBA⟩
  have hmul : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := fun w => by
    change A *ᵥ w = g w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨γ, ?_, hmul⟩
  change Formalism.UG.cT (starRingEnd E) A * J * A = J
  ext i j
  have e1 := hg (Pi.single i 1) (Pi.single j 1)
  have hsingle : ∀ k l, hJ J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    rw [hJ_single, Matrix.vecMul, dotProduct]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hsingle] at e1
  rw [← e1, hJ_apply, Formalism.UG.hform]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  have hcol : ∀ k l, A k l = g (Pi.single l 1) k := fun k l => by
    simp [A, LinearMap.toMatrix'_apply]
  simp only [hcol, Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
