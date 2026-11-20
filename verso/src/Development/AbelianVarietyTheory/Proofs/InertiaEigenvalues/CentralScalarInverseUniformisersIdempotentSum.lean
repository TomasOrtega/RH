import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CentralScalar

section Alg

variable {R ι : Type} [CommRing R] {s : Finset ι} {p q : ι → R}

def comp (s : Finset ι) (p q u v : ι → R) : R := 1 + ∑ i ∈ s, (p i * (u i - 1) + q i * (v i - 1))

/- English proof (translation)
Unfold `comp`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => add_comm _ _`.
-/
theorem comp_swap (u v : ι → R) : comp s p q u v = comp s q p v u := by
  unfold comp
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

/- English proof (translation)
Unfold `comp`. Rewrite using `[mul_add, Finset.mul_sum, Finset.sum_eq_single_of_mem i hi]`. Rewrite using `[mul_add, ← mul_assoc, ← mul_assoc, h1 i hi, h3 i hi i hi]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j hj hji`.

Rewrite using `[mul_add, ← mul_assoc, ← mul_assoc, h2 i hi j hj hji, h3 i hi j hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem left_mul_comp (h1 : ∀ i ∈ s, p i * p i = p i) (h2 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0)
    (h3 : ∀ i ∈ s, ∀ j ∈ s, p i * q j = 0) (u v : ι → R) {i : ι} (hi : i ∈ s) :
    p i * comp s p q u v = p i * u i := by
  unfold comp
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [mul_add, ← mul_assoc, ← mul_assoc, h1 i hi, h3 i hi i hi]; ring
  · intro j hj hji
    rw [mul_add, ← mul_assoc, ← mul_assoc, h2 i hi j hj hji, h3 i hi j hj]; ring

/- English proof (translation)
Establish `h : comp s p q u v * comp s p q u' v' = comp s p q u' v' + ∑ i ∈ s, (p i * u' i * (u i - 1) + q i * v' i * (v i - 1))` using `by conv_lhs => rw [comp]`. Rewrite using `[add_mul, one_mul, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← hp u' v' i hi, ← hq u' v' i hi]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Unfold `comp`. Rewrite using `[add_assoc, ← Finset.sum_add_distrib]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem comp_mul (hp : ∀ u v : ι → R, ∀ i ∈ s, p i * comp s p q u v = p i * u i)
    (hq : ∀ u v : ι → R, ∀ i ∈ s, q i * comp s p q u v = q i * v i) (u v u' v' : ι → R) :
    comp s p q u v * comp s p q u' v' = comp s p q (fun i => u i * u' i) (fun i => v i * v' i) := by
  have h : comp s p q u v * comp s p q u' v' =
      comp s p q u' v' + ∑ i ∈ s, (p i * u' i * (u i - 1) + q i * v' i * (v i - 1)) := by
    conv_lhs => rw [comp]
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hp u' v' i hi, ← hq u' v' i hi]; ring
  rw [h]
  unfold comp
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Unfold `comp`. Rewrite using `[Finset.sum_eq_zero, add_zero]`. Introduce `i hi`. Rewrite using `[hu i hi, hv i hi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comp_eq_one {u v : ι → R} (hu : ∀ i ∈ s, u i = 1) (hv : ∀ i ∈ s, v i = 1) : comp s p q u v = 1 := by
  unfold comp
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [hu i hi, hv i hi]; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_right_comm, h, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_pow_of_mul_eq {e a w : R} (h : e * a = e * w) (n : ℕ) : e * a ^ n = e * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_right_comm, h, pow_succ]; ring

/- English proof (translation)
Unfold `comp`. Rewrite using `[map_add, map_one, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_sub, map_one, hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_comp (c : R →+* R) (hc : ∀ x, c (c x) = x) (u v : ι → R) :
    c (comp s p (fun i => c (p i)) u v) = comp s p (fun i => c (p i)) (fun i => c (v i)) (fun i => c (u i)) := by
  unfold comp
  rw [map_add, map_one, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_sub, map_one, hc]
  ring

end Alg

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem mt_inj (V : HSp D) {a b : GA D V} (h : Formalism.L2.Theta.mt V a = Formalism.L2.Theta.mt V b) : a = b :=
  Subtype.ext (Units.ext h)

/- English proof (translation)
Establish `h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]`. Establish `h2 : (Matrix.diagonal fun _ : Fin V.rank => cA D a) * (Matrix.diagonal fun _ => a) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]`. Use `⟨⟨⟨_, _, h1, h2⟩, ?_⟩, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Formalism.UG.cT (cA D) (Matrix.diagonal fun _ => a) * _ * (Matrix.diagonal fun _ => a) = _`. Establish `h3 : Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin V.rank => a) = Matrix.diagonal fun _ => cA D a`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[Formalism.UG.cT]`. Simplify using `[Formalism.UG.cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]`. Rewrite using `[h3]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, mul_right_comm, ha, one_mul]`.
-/
theorem exists_scalar (V : HSp D) (a : AE D) (ha : cA D a * a = 1) :
    ∃ z : GA D V, Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h2 : (Matrix.diagonal fun _ : Fin V.rank => cA D a) * (Matrix.diagonal fun _ => a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]
  refine ⟨⟨⟨_, _, h1, h2⟩, ?_⟩, rfl⟩
  change Formalism.UG.cT (cA D) (Matrix.diagonal fun _ => a) * _ * (Matrix.diagonal fun _ => a) = _
  have h3 : Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin V.rank => a) = Matrix.diagonal fun _ => cA D a := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [h3]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_right_comm, ha, one_mul]

/- English proof (translation)
Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`. Apply `mt_inj V` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V z = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V g`. Rewrite using `[hz]`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]`.
-/
theorem scalar_central (V : HSp D) {a : AE D} {z : GA D V} (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    z ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mt_inj V
  change Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V z = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V g
  rw [hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

/- English proof (translation)
Use `MonoidHom.mem_ker.2 (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Formalism.L2.Theta.mt V z).map (infPart D) = 1`. Rewrite using `[hz, Matrix.diagonal_map (map_zero _)]`. Simplify using `only [ha, Matrix.diagonal_one]`.
-/
theorem scalar_fin (V : HSp D) {a : AE D} (ha : infPart D a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : z ∈ GfC V := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V z).map (infPart D) = 1
  rw [hz, Matrix.diagonal_map (map_zero _)]
  simp only [ha, Matrix.diagonal_one]

/- English proof (translation)
Establish `h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]`. Establish `h` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_inv_mul V z`. Rewrite using `[← Matrix.mul_one (Formalism.L2.Theta.mt V z⁻¹), ← h1, ← Matrix.mul_assoc, ← hz, h, Matrix.one_mul]`.
-/
theorem scalar_inv (V : HSp D) {a : AE D} (ha : cA D a * a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    Formalism.L2.Theta.mt V z⁻¹ = Matrix.diagonal fun _ => cA D a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_inv_mul V z
  rw [← Matrix.mul_one (Formalism.L2.Theta.mt V z⁻¹), ← h1, ← Matrix.mul_assoc, ← hz, h, Matrix.one_mul]

/- English proof (translation)
Introduce `i j`. Rewrite using `[hz]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify `ha` using `only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`.

Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]`.
-/
theorem scalar_supp (V : HSp D) {e a : AE D} (ha : (e + cA D e) * (a - 1) = a - 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : SuppAt e V z := by
  intro i j
  rw [hz]
  by_cases h : i = j
  · subst h
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using ha
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]

/- English proof (translation)
Introduce `D V Q es ϖ hes hc hϖ`. Establish `h1 : ∀ i ∈ Q, es i * es i = es i` using `fun i hi => (hes i hi).1.1`. Establish `hx` using `GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc`. Establish `h2 : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0` using `fun i hi j hj h => GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hx i hi j hj) (hx j hj i hi) h`. Establish `hp : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q, es i * comp Q es (fun i => cA D (es i)) u v = es i * u i` using `fun u v i hi => left_mul_comp h1 h2 hx u v hi`.

Establish `hq : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q, cA D (es i) * comp Q es (fun i => cA D (es i)) u v = cA D (es i) * v i` using `fun u v i hi => by`. Rewrite using `[comp_swap]`. Use `left_mul_comp (p := fun i => cA D (es i)) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun i hi j hj => ?_) v u hi` and prove the remaining obligations. Rewrite using `[← map_mul, h1 i hi]`. Rewrite using `[← map_mul, h2 i hi j hj h, map_zero]`.

Rewrite using `[mul_comm]`. Conclude with `hx j hj i hi`. Establish `hne : ∀ i ∈ Q, (ϖ i : D.host.E) ≠ 0` using `fun i hi h => hϖ i hi (RingOfIntegers.coe_eq_zero_iff.1 h)`. Use `set a : AE D := 1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) with ha`. Establish `ha' : a = comp Q es (fun i => cA D (es i)) (fun PP => incA D ((ϖ PP : D.host.E)⁻¹)) (fun PP => incA D (star (ϖ PP : D.host.E)))` using `rfl`.

Establish `hca : cA D a = comp Q es (fun i => cA D (es i)) (fun PP => incA D (ϖ PP : D.host.E)) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹))`. Rewrite using `[ha', map_comp (cA D) GlobalTheory.DualPairCheck.cA_cA]`. Simplify using `only [cA_incA, star_star]`. Establish `hn : cA D a * a = 1`. Rewrite using `[hca, ha', comp_mul hp hq]`.

Use `comp_eq_one (fun i hi => ?_) (fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[← map_mul, mul_inv_cancel₀ (hne i hi), map_one]`. Rewrite using `[← map_mul, ← star_mul, mul_inv_cancel₀ (hne i hi), star_one, map_one]`. Use `⟨exists_scalar V a hn, fun z hz => ⟨scalar_central V hz, scalar_fin V ?_ hz, scalar_supp V ?_ hz, ?_, scalar_inv V hn hz, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[ha, map_add, map_one, map_sum, Finset.sum_eq_zero, add_zero]`.

Introduce `i hi`. Establish `h0` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem (hes i hi).1`. Rewrite using `[map_add, map_mul, map_mul, h0, GlobalTheory.PlaceVec.infPart_cA h0, zero_mul, zero_mul, add_zero]`. Establish `: a - 1 = ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))` using `by rw [ha, add_sub_cancel_left] conv_rhs => rw [this]`. Rewrite using `[map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[add_mul, mul_sub, mul_sub, ha', hp _ _ i hi, hq _ _ i hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) * comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹) ^ V.rank) = 1`. Rewrite using `[comp_mul hp hq]`.

Use `comp_eq_one (fun i _ => one_mul _) (fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[← mul_pow, ← map_mul, ← star_mul, inv_mul_cancel₀ (hne i hi), star_one, map_one, one_pow]`. Establish `hv : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)`. Simplify using `only [comp, sub_self, mul_zero, zero_add]`. Use `⟨Units.mkOfMulEqOne _ _ hu, ?_, hv⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = _`. Rewrite using `[hv, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_sum, Finset.sum_mul]`. Establish `: ∀ i ∈ Q, cA D (es i) * a ^ V.rank = cA D (es i) * incA D (star (ϖ i : D.host.E)) ^ V.rank` using `fun i hi => mul_pow_of_mul_eq (hq _ _ i hi) _`. Rewrite using `[Finset.sum_congr rfl this]`. Simplify using `only [mul_sub, mul_one, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_comm, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i hi => hp _ _ i hi`. Rewrite using `[mul_comm, Finset.sum_mul, hca]`. Conclude with `Finset.sum_congr rfl fun i hi => hp _ _ i hi`.

Rewrite using `[mul_comm, map_sum, map_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi`. Rewrite using `[mul_comm, map_sum, map_sum, Finset.sum_mul, hca]`. Conclude with `Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi`.
-/
theorem centralScalar : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  intro D V Q es ϖ hes hc hϖ
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have h2 : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj h =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hx i hi j hj) (hx j hj i hi) h
  have hp : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      es i * comp Q es (fun i => cA D (es i)) u v = es i * u i := fun u v i hi => left_mul_comp h1 h2 hx u v hi
  have hq : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      cA D (es i) * comp Q es (fun i => cA D (es i)) u v = cA D (es i) * v i := fun u v i hi => by
    rw [comp_swap]
    refine left_mul_comp (p := fun i => cA D (es i)) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun i hi j hj => ?_) v u hi
    · rw [← map_mul, h1 i hi]
    · rw [← map_mul, h2 i hi j hj h, map_zero]
    · rw [mul_comm]; exact hx j hj i hi
  have hne : ∀ i ∈ Q, (ϖ i : D.host.E) ≠ 0 := fun i hi h => hϖ i hi (RingOfIntegers.coe_eq_zero_iff.1 h)
  set a : AE D := 1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
    cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) with ha
  have ha' : a = comp Q es (fun i => cA D (es i)) (fun PP => incA D ((ϖ PP : D.host.E)⁻¹))
    (fun PP => incA D (star (ϖ PP : D.host.E))) := rfl
  have hca : cA D a = comp Q es (fun i => cA D (es i)) (fun PP => incA D (ϖ PP : D.host.E))
      (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹)) := by
    rw [ha', map_comp (cA D) GlobalTheory.DualPairCheck.cA_cA]
    simp only [cA_incA, star_star]
  have hn : cA D a * a = 1 := by
    rw [hca, ha', comp_mul hp hq]
    refine comp_eq_one (fun i hi => ?_) (fun i hi => ?_)
    · rw [← map_mul, mul_inv_cancel₀ (hne i hi), map_one]
    · rw [← map_mul, ← star_mul, mul_inv_cancel₀ (hne i hi), star_one, map_one]
  refine ⟨exists_scalar V a hn, fun z hz => ⟨scalar_central V hz, scalar_fin V ?_ hz, scalar_supp V ?_ hz, ?_,
    scalar_inv V hn hz, ?_, ?_, ?_, ?_⟩⟩
  · rw [ha, map_add, map_one, map_sum, Finset.sum_eq_zero, add_zero]
    intro i hi
    have h0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem (hes i hi).1
    rw [map_add, map_mul, map_mul, h0, GlobalTheory.PlaceVec.infPart_cA h0, zero_mul, zero_mul, add_zero]
  · have : a - 1 = ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
      cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) := by rw [ha, add_sub_cancel_left]
    conv_rhs => rw [this]
    rw [map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [add_mul, mul_sub, mul_sub, ha', hp _ _ i hi, hq _ _ i hi]
    ring
  · have hu : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) *
        comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹) ^ V.rank) = 1 := by
      rw [comp_mul hp hq]
      refine comp_eq_one (fun i _ => one_mul _) (fun i hi => ?_)
      rw [← mul_pow, ← map_mul, ← star_mul, inv_mul_cancel₀ (hne i hi), star_one, map_one, one_pow]
    have hv : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) =
        1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1) := by
      simp only [comp, sub_self, mul_zero, zero_add]
    refine ⟨Units.mkOfMulEqOne _ _ hu, ?_, hv⟩
    change comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = _
    rw [hv, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_sum, Finset.sum_mul]
    have : ∀ i ∈ Q, cA D (es i) * a ^ V.rank = cA D (es i) * incA D (star (ϖ i : D.host.E)) ^ V.rank :=
      fun i hi => mul_pow_of_mul_eq (hq _ _ i hi) _
    rw [Finset.sum_congr rfl this]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  · rw [mul_comm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi
  · rw [mul_comm, map_sum, map_sum, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi

end GlobalTheory.CentralScalar
