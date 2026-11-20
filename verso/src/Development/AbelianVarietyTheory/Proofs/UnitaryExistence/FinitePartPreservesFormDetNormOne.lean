import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u)`. Introduce `u v`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring` and prove the remaining obligations.

Establish `h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g`. Use function extensionality and compare the values at `b`. Simplify using `[Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]`. Rewrite using `[key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem unit_form_inv {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    ∑ a, ∑ b, (g *ᵥ x) a * J b a * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * J b a * σ (y b) := by
  have key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u) := by
    intro u v
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g := by
    funext b
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose]`. Establish `h2 : (g.map σ).det = σ g.det` using `(σ.map_det g).symm`. Rewrite `h1` using `[h2]`. Apply `hJ.mul_left_cancel` to reduce the goal to its premises.

Take the linear combination `h1`.
-/
theorem unit_det_norm {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hJ : IsUnit J.det) (h : Formalism.UG.cT σ g * J * g = J) : g.det * σ g.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [h2] at h1
  apply hJ.mul_left_cancel
  linear_combination h1

/- English proof (translation)
Use `set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ`. Establish `hs : ∀ z, π (sigR R σ z) = sigR S σ (π z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e => simp [hπ, sigR]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hJ : (JR R J).map π = JR S J`. Use extensionality with `i j`. Simplify using `[hπ, JR, inclR]`.

Establish `hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π)`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]`. Establish `h2` using `congrArg (fun M => Matrix.map M π) h`. Simplify using `only [Matrix.map_mul] at h2`.

Rewrite `h2` using `[hJ, hc]`. Conclude with `h2`.
-/
theorem unitary_map {F E R S : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (h : Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J) :
    Formalism.UG.cT (sigR S σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) * JR S J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = JR S J := by
  set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ
  have hs : ∀ z, π (sigR R σ z) = sigR S σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hπ, sigR]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hJ : (JR R J).map π = JR S J := by
    ext i j
    simp [hπ, JR, inclR]
  have hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]
  have h2 := congrArg (fun M => Matrix.map M π) h
  simp only [Matrix.map_mul] at h2
  rw [hJ, hc] at h2
  exact h2

/- English proof (translation)
The claim follows from `unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1 (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2`.
-/
theorem finHom_unitary {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g).1 * JR (F := D.host.F) (Af D.host.F) V.gram * (finHom V g).1 =
      JR (F := D.host.F) (Af D.host.F) V.gram :=
  unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

/- English proof (translation)
Introduce `D V g`. Establish `hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F` using `D.host.F) R V.gram).det := by`. Introduce `R _ _`. Establish `e : (JR (F` using `D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm`. Rewrite using `[e]`.

Conclude with `(isUnit_iff_ne_zero.2 (gram_det_ne V)).map _`. Use `⟨fun x y => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `unit_form_inv _ _ _ (finHom_unitary V g) x y`. Conclude with `unit_det_norm _ _ _ (hu _) (finHom_unitary V g)`. Conclude with `unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2`.
-/
theorem finHom_herm_det : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  intro D V g
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F := D.host.F) R V.gram).det := by
    intro R _ _
    have e : (JR (F := D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne V)).map _
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · exact unit_form_inv _ _ _ (finHom_unitary V g) x y
  · exact unit_det_norm _ _ _ (hu _) (finHom_unitary V g)
  · exact unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

end GlobalTheory.Member
