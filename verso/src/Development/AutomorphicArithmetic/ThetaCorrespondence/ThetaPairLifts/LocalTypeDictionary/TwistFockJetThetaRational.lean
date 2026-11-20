import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableThetaLocalSum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumIsVacuumIntegral

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets
noncomputable section
namespace GlobalTheory.RatMoveFock
section SlopeTestRemainingChoices
open Matrix
variable {D : D7}
/- English proof (translation)
Establish `e : (fun i => Formalism.UG.inclE (F` using `F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((A *ᵥ y) i)) = g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (y i) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[hg]`. Conclude with `RingHom.map_mulVec _ _ _ i`. Unfold `Formalism.UG.CS.globLat`.

Simplify using `only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Rewrite using `[e, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
private theorem mem_globLat_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (A : Matrix (Fin n) (Fin n) E)
    (hg : g.val = A.map (Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))) (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E) : A *ᵥ y ∈ Formalism.UG.CS.globLat (g * h) Λ ↔ y ∈ Formalism.UG.CS.globLat h Λ := by
  have e : (fun i => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((A *ᵥ y) i)) =
      g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (y i) := by
    funext i
    rw [hg]
    exact RingHom.map_mulVec _ _ _ i
  unfold Formalism.UG.CS.globLat
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [e, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
/- English proof (translation)
Take `⟨γ, -, h2, h3⟩` from `h`. Establish `hg : (finG (G.V X) r).val = ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1).map (Formalism.UG.inclE (F` using `D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by`. Establish `e : (finG (G.V X) r).val = (Formalism.L2.Theta.mt (G.V X) γ).map (toEAf D)` using `Matrix.ext fun i j => congrArg (fun x : GL (Fin (G.V X).rank) _ => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (x.1 i j)) h2.symm`. Rewrite using `[e, h3]`. Both sides reduce to the same expression.

Establish `key : ∀ y, U.1 *ᵥ y ∈ GlobalTheory.SumSize.latAt S X (r * x) ↔ y ∈ GlobalTheory.SumSize.latAt S X x` using `fun y => by`. Unfold `GlobalTheory.SumSize.latAt`. Rewrite using `[Submodule.mem_comap, Submodule.mem_comap, map_mul, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]`. Establish `e : (S.N.fr X).1 *ᵥ (U.1 *ᵥ y) = ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1) *ᵥ ((S.N.fr X).1 *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (S.N.fr X).1, Units.inv_mul, Matrix.mul_one]`.

Rewrite using `[e]`. Conclude with `mem_globLat_mul _ _ _ hg (G.Λ X) _`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Establish `e : U.1 *ᵥ (star U.1 *ᵥ z) = z` using `by rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]`. Conclude with `⟨_, (key _).1 (e.symm ▸ hz), e⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(key y).2 hy`.
-/
private theorem latAt_rat {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E)
    (h : RatCoord (G.V X) (S.N.fr X) r U) (x : FinPt G X) :
    GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  obtain ⟨γ, -, h2, h3⟩ := h
  have hg : (finG (G.V X) r).val = ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1).map
      (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    have e : (finG (G.V X) r).val = (Formalism.L2.Theta.mt (G.V X) γ).map (toEAf D) :=
      Matrix.ext fun i j => congrArg (fun x : GL (Fin (G.V X).rank) _ =>
        Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (x.1 i j)) h2.symm
    rw [e, h3]
    rfl
  have key : ∀ y, U.1 *ᵥ y ∈ GlobalTheory.SumSize.latAt S X (r * x) ↔ y ∈ GlobalTheory.SumSize.latAt S X x := fun y => by
    unfold GlobalTheory.SumSize.latAt
    rw [Submodule.mem_comap, Submodule.mem_comap, map_mul, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    have e : (S.N.fr X).1 *ᵥ (U.1 *ᵥ y) =
        ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL _ _).1) *ᵥ ((S.N.fr X).1 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (S.N.fr X).1, Units.inv_mul, Matrix.mul_one]
    rw [e]
    exact mem_globLat_mul _ _ _ hg (G.Λ X) _
  ext z
  constructor
  · intro hz
    have e : U.1 *ᵥ (star U.1 *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
    exact ⟨_, (key _).1 (e.symm ▸ hz), e⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y).2 hy
private def NormOne {F : Type} [NormedField F] (lam : Qbar →+* F) (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ = 1
section
variable {F : Type} [NormedField F] {lam : Qbar →+* F}
/- English proof (translation)
Assemble the required witnesses or components as `⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : Qbar) = 1 from rfl, map_one, norm_one]⟩`.
-/
private theorem NormOne.one : NormOne lam 1 := ⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : Qbar) = 1 from rfl, map_one, norm_one]⟩
/- English proof (translation)
Take `⟨h1, h2⟩` from `hx`. Take `⟨h3, h4⟩` from `hy`. Use `⟨mul_mem h1 h3, ?_⟩` and prove the remaining obligations. Rewrite using `[show (⟨x * y, mul_mem h1 h3⟩ : Qbar) = ⟨x, h1⟩ * ⟨y, h3⟩ from rfl, map_mul, norm_mul, h2, h4, one_mul]`.
-/
private theorem NormOne.mul {x y : ℂ} (hx : NormOne lam x) (hy : NormOne lam y) : NormOne lam (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨mul_mem h1 h3, ?_⟩
  rw [show (⟨x * y, mul_mem h1 h3⟩ : Qbar) = ⟨x, h1⟩ * ⟨y, h3⟩ from rfl, map_mul, norm_mul, h2, h4, one_mul]
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `NormOne.one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hx`.
-/
private theorem NormOne.pow {x : ℂ} (hx : NormOne lam x) (n : ℕ) : NormOne lam (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact NormOne.one
  | succ n ih => rw [pow_succ]; exact ih.mul hx
/- English proof (translation)
The claim follows from `Finset.prod_induction f (NormOne lam) (fun _ _ => NormOne.mul) NormOne.one fun i _ => h i`.
-/
private theorem NormOne.prod {ι : Type} [Fintype ι] (f : ι → ℂ) (h : ∀ i, NormOne lam (f i)) : NormOne lam (∏ i, f i) :=
  Finset.prod_induction f (NormOne lam) (fun _ _ => NormOne.mul) NormOne.one fun i _ => h i
/- English proof (translation)
Take `⟨h1, h2⟩` from `hx`. Establish `h3 : x ∈ Qbar` using `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h1))`. Use `⟨h3, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[show (⟨x ^ n, h1⟩ : Qbar) = ⟨x, h3⟩ ^ n from rfl, map_pow, norm_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2`.
-/
private theorem NormOne.of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (hx : NormOne lam (x ^ n)) : NormOne lam x := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : x ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h1))
  refine ⟨h3, ?_⟩
  rw [show (⟨x ^ n, h1⟩ : Qbar) = ⟨x, h3⟩ ^ n from rfl, map_pow, norm_pow] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
/- English proof (translation)
Establish `hm : ∀ b : E, τ b ∈ Qbar` using `fun b => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) b).algHom τ.toRatAlgHom)`. Conclude with `⟨hm a, h (lam.comp (τ.codRestrict Qbar hm))⟩`.
-/
private theorem normOne_emb (lam : Qbar →+* F) {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) (a : E)
    (h : ∀ φ : E →+* F, ‖φ a‖ = 1) : NormOne lam (τ a) := by
  have hm : ∀ b : E, τ b ∈ Qbar := fun b =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) b).algHom τ.toRatAlgHom)
  exact ⟨hm a, h (lam.comp (τ.codRestrict Qbar hm))⟩
end
/- English proof (translation)
Unfold `SDLat.smulLat`. Rewrite using `[Submodule.mem_map]`. Both sides reduce to the same expression.
-/
private theorem mem_smulLat {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (y : Fin N → D.host.E) : y ∈ SDLat.smulLat γ L ↔ ∃ x ∈ L, γ.mulVec x = y := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  rfl
/- English proof (translation)
Establish `e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p])` using `(map_natCast _ n).symm`. Rewrite using `[e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `h.symm`.
-/
private theorem norm_natCast_coprime {p : ℕ} [Fact p.Prime] {n : ℕ} (h : Nat.Coprime n p) : ‖(n : ℂ_[p])‖ = 1 := by
  have e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := (map_natCast _ n).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm
/- English proof (translation)
Rewrite using `[← Matrix.det_mul, U.2.2, Matrix.det_one]`.
-/
private theorem det_mul_star {N : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) : U.1.det * (star U.1).det = 1 := by
  rw [← Matrix.det_mul, U.2.2, Matrix.det_one]
/- English proof (translation)
Establish `hs : φ (star U.1.det) = starRingEnd ℂ (φ U.1.det)`. Use `D.host.isCMField_hostE` as an intermediate fact. Conclude with `IsCMField.complexEmbedding_complexConj D.host.E φ _`. Establish `h` using `congrArg (fun a => ‖φ a‖) (det_mul_star U)`. Rewrite `h` using `[star_eq_conjTranspose, Matrix.det_conjTranspose]`.

Simplify using `only [map_mul, norm_mul, hs, Complex.norm_conj, map_one, norm_one] at h`. Conclude with `(mul_self_eq_one_iff.1 h).resolve_right fun e => by linarith [norm_nonneg (φ U.1.det)]`.
-/
private theorem norm_det_complex {N : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) (φ : D.host.E →+* ℂ) : ‖φ U.1.det‖ = 1 := by
  have hs : φ (star U.1.det) = starRingEnd ℂ (φ U.1.det) := by
    have := D.host.isCMField_hostE
    exact IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h := congrArg (fun a => ‖φ a‖) (det_mul_star U)
  rw [star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simp only [map_mul, norm_mul, hs, Complex.norm_conj, map_one, norm_one] at h
  exact (mul_self_eq_one_iff.1 h).resolve_right fun e => by linarith [norm_nonneg (φ U.1.det)]
/- English proof (translation)
Establish `h1 : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap _ D.host.E b = ((s : D.host.E) • A) i j` using `fun i j => by`. Establish `h2` using `h (Pi.single j 1) (fun k _ => by`. Distinguish the cases in `e : k = j`. Substitute `e` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `Submodule.one_le.1 le_rfl`. Rewrite using `[Pi.single_eq_of_ne e]`. Conclude with `zero_mem _) i (Set.mem_univ _)`. Rewrite `h2` using `[Matrix.mulVec_single_one]`. Conclude with `Submodule.mem_one.1 h2`.

Use `choose B hB using h1`. Establish `e : algebraMap _ D.host.E (Matrix.of B).det = (s : D.host.E) ^ N * A.det`. Rewrite using `[RingHom.map_det, show (algebraMap _ D.host.E).mapMatrix (Matrix.of B) = (s : D.host.E) • A from Matrix.ext hB, Matrix.det_smul, Fintype.card_fin]`. Establish `h3` using `GlobalTheory.Proof.IdempotentLatticeSequence.norm_int_le φ (Matrix.of B).det`. Express the relevant statement in the definitionally equal form `‖φ (algebraMap _ D.host.E _)‖ ≤ 1 at h3`.

Rewrite `h3` using `[e, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_natCast_coprime hs, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
private theorem norm_det_le {N q : ℕ} [Fact q.Prime] (A : Matrix (Fin N) (Fin N) D.host.E) {s : ℕ} (hs : s.Coprime q)
    (h : ∀ x ∈ stdL D N, ((s : D.host.E) • A) *ᵥ x ∈ stdL D N) (φ : D.host.E →+* ℂ_[q]) : ‖φ A.det‖ ≤ 1 := by
  have h1 : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap _ D.host.E b = ((s : D.host.E) • A) i j := fun i j => by
    have h2 := h (Pi.single j 1) (fun k _ => by
      by_cases e : k = j
      · subst e; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _) i (Set.mem_univ _)
    rw [Matrix.mulVec_single_one] at h2
    exact Submodule.mem_one.1 h2
  choose B hB using h1
  have e : algebraMap _ D.host.E (Matrix.of B).det = (s : D.host.E) ^ N * A.det := by
    rw [RingHom.map_det, show (algebraMap _ D.host.E).mapMatrix (Matrix.of B) = (s : D.host.E) • A from
      Matrix.ext hB, Matrix.det_smul, Fintype.card_fin]
  have h3 := GlobalTheory.Proof.IdempotentLatticeSequence.norm_int_le φ (Matrix.of B).det
  change ‖φ (algebraMap _ D.host.E _)‖ ≤ 1 at h3
  rwa [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_natCast_coprime hs, one_pow, one_mul] at h3
/- English proof (translation)
Take `⟨s, hs, a1, a2⟩` from `h1`. Take `⟨t, ht, b1, b2⟩` from `h2`. Establish `c1` using `norm_det_le U.1 (Nat.Coprime.mul_left ht hs) (fun x hx => by`. Use `b1 _ ((mem_smulLat _ _ _).2 ⟨_, a2 x hx, rfl⟩)` as an intermediate fact. Rewrite using `[Matrix.mulVec_smul, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ` and apply the resulting hypothesis.

Establish `c2` using `norm_det_le (star U.1) (Nat.Coprime.mul_left hs ht) (fun x hx => by`. Take `⟨y, hy, e⟩` from `(mem_smulLat _ _ _).1 (b2 x hx)`. Establish `e2 : y = (t : D.host.E) • (star U.1 *ᵥ x)`. Rewrite using `[← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec]`. Use `a1 y hy` as an intermediate fact.

Rewrite using `[e2, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ` and apply the resulting hypothesis. Establish `h` using `congrArg (fun a => ‖φ a‖) (det_mul_star U)`. Simplify using `only [map_mul, norm_mul, map_one, norm_one] at h`. Use polynomial arithmetic with `[norm_nonneg (φ U.1.det), norm_nonneg (φ (star U.1).det)]`.
-/
private theorem norm_det_padic {N q : ℕ} [Fact q.Prime] (U : Matrix.unitaryGroup (Fin N) D.host.E)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h1 : EqAt D q M (stdL D N))
    (h2 : EqAt D q (SDLat.smulLat U.1 M) (stdL D N)) (φ : D.host.E →+* ℂ_[q]) : ‖φ U.1.det‖ = 1 := by
  obtain ⟨s, hs, a1, a2⟩ := h1
  obtain ⟨t, ht, b1, b2⟩ := h2
  have c1 := norm_det_le U.1 (Nat.Coprime.mul_left ht hs) (fun x hx => by
    have := b1 _ ((mem_smulLat _ _ _).2 ⟨_, a2 x hx, rfl⟩)
    rwa [Matrix.mulVec_smul, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ
  have c2 := norm_det_le (star U.1) (Nat.Coprime.mul_left hs ht) (fun x hx => by
    obtain ⟨y, hy, e⟩ := (mem_smulLat _ _ _).1 (b2 x hx)
    have e2 : y = (t : D.host.E) • (star U.1 *ᵥ x) := by
      rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec]
    have := a1 y hy
    rwa [e2, smul_smul, ← Nat.cast_mul, ← Matrix.smul_mulVec] at this) φ
  have h := congrArg (fun a => ‖φ a‖) (det_mul_star U)
  simp only [map_mul, norm_mul, map_one, norm_one] at h
  nlinarith [norm_nonneg (φ U.1.det), norm_nonneg (φ (star U.1).det)]
end SlopeTestRemainingChoices
open Matrix GlobalTheory.AdForm.RatMove
open scoped ComplexOrder
variable {D : D7}
/- English proof (translation)
Break down `hs with rfl | rfl` into its components or cases. Use `⟨1, fun a b => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.WeilParts.detPlus`. Rewrite using `[Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, add_mul, one_mul, ← two_smul ℂ, smul_smul, Matrix.det_smul, Matrix.det_kronecker]`. Simplify using the standard rewrite rules.

Use `⟨0, fun a b => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.WeilParts.detPlus`. Establish `e : Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2) (1 : Matrix (Fin m) (Fin m) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1`. Rewrite using `[← Matrix.one_kronecker_one, Matrix.transpose_neg, Matrix.transpose_one]`. Use extensionality with `⟨i, j⟩ ⟨k, l⟩`.

Simplify using `only [Matrix.kroneckerMap_apply, Matrix.neg_apply, mul_neg]`. Rewrite using `[e, add_neg_cancel, zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]`. Simplify using the standard rewrite rules.
-/
private theorem detPlus_def {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} (hs : s = 1 ∨ s = -1) :
    ∃ e : ℕ, ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ),
      GlobalTheory.WeilParts.detPlus s 1 a b = (b.det ^ n * a.det ^ m) ^ e := by
  rcases hs with rfl | rfl
  · refine ⟨1, fun a b => ?_⟩
    unfold GlobalTheory.WeilParts.detPlus
    rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, add_mul, one_mul, ← two_smul ℂ,
      smul_smul, Matrix.det_smul, Matrix.det_kronecker]
    simp
  · refine ⟨0, fun a b => ?_⟩
    unfold GlobalTheory.WeilParts.detPlus
    have e : Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2) (1 : Matrix (Fin m) (Fin m) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
      rw [← Matrix.one_kronecker_one, Matrix.transpose_neg, Matrix.transpose_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, mul_neg]
    rw [e, add_neg_cancel, zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    simp
/- English proof (translation)
Establish `key : ∀ τ, ∃ c : ℤ, HasInfExp D ((χ * (η ^ k)⁻¹) * (χ * (η ^ k)⁻¹)) τ c` using `fun τ => by`. Take `⟨a, ha⟩` from `GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ h1 h2`. Establish `hb` using `GlobalTheory.VacuumCharacter.hasInfExp_twist ha (hη τ) k`. Take `⟨c, hc, -⟩` from `id hb`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc, two_mul]`. Conclude with `GlobalTheory.Mem.HeckeExp.hasInfExp_mul hb hb`. Conclude with `⟨_, fun τ => (key τ).choose_spec⟩`.
-/
private theorem sq_exp {θ : InfFam D} (hθ : IsInfFam θ) {χ η : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h1 : IsHeckeChar D χ)
    (h2 : ResEta D χ n) (hη : ∀ τ, HasInfExp D η τ (1 / 2)) (k : ℕ) :
    ∃ c : D.what₂.Tau → ℤ, ∀ τ, HasInfExp D ((χ * (η ^ k)⁻¹) * (χ * (η ^ k)⁻¹)) τ (c τ) := by
  have key : ∀ τ, ∃ c : ℤ, HasInfExp D ((χ * (η ^ k)⁻¹) * (χ * (η ^ k)⁻¹)) τ c := fun τ => by
    obtain ⟨a, ha⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ h1 h2
    have hb := GlobalTheory.VacuumCharacter.hasInfExp_twist ha (hη τ) k
    obtain ⟨c, hc, -⟩ := id hb
    refine ⟨c, ?_⟩
    rw [hc, two_mul]
    exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul hb hb
  exact ⟨_, fun τ => (key τ).choose_spec⟩
/- English proof (translation)
Take `⟨h1, h2⟩` from `hx`. Use `⟨inv_mem h1, ?_⟩` and prove the remaining obligations. Rewrite using `[show (⟨x⁻¹, inv_mem h1⟩ : Qbar) = (⟨x, h1⟩ : Qbar)⁻¹ from rfl, map_inv₀, norm_inv, h2, inv_one]`.
-/
private theorem NormOne.inv' {F : Type} [NormedField F] {lam : Qbar →+* F} {x : ℂ} (hx : NormOne lam x) : NormOne lam x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨inv_mem h1, ?_⟩
  rw [show (⟨x⁻¹, inv_mem h1⟩ : Qbar) = (⟨x, h1⟩ : Qbar)⁻¹ from rfl, map_inv₀, norm_inv, h2, inv_one]
/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using hx.pow n`. Consider the case `negSucc n => rw [zpow_negSucc]`. Conclude with `NormOne.inv' (hx.pow _)`.
-/
private theorem NormOne.zpow' {F : Type} [NormedField F] {lam : Qbar →+* F} {x : ℂ} (hx : NormOne lam x) (n : ℤ) :
    NormOne lam (x ^ n) := by
  cases n with
  | ofNat n => simpa using hx.pow n
  | negSucc n => rw [zpow_negSucc]; exact NormOne.inv' (hx.pow _)
/- English proof (translation)
Take `⟨η, e1, e2, e3, e4⟩` from `GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D`. Establish `hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0` using `fun {k G s} hG => by`. Use `hG.2.2.det_pos.ne'` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul]`. Conclude with `left_ne_zero_of_mul this`.

Take `⟨x, hx, hxv⟩` from `GlobalTheory.VacuumCharacter.exists_root hθ S (fun τ => hdet (hS τ)) g hg`. Take `⟨y, hy, hyv⟩` from `GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT τ)) h hh`. Take `⟨e, he⟩` from `detPlus_def (m := T.rank) hs`. Take `⟨a, ha⟩` from `sq_exp hθ hW.hecT hW.resT e2 T.rank`. Take `⟨b, hb⟩` from `sq_exp hθ hW.hecS hW.resS e2 S.rank`.

Apply the tactic sequence `refine ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => s) (fun _ => 1) hS hT g hg h hh (fun τ => by rcases hs with rfl | rfl <;> simp) (fun τ => by rw [one_mul, mul_one]) x y hx hy f hf hv, fun F _ lam h1 h …`. Establish `inv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)).det = ((compAt θ τ (Formalism.L2.Theta.mt S g)).det)⁻¹` using `fun τ => by`. Use `eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]`. Unfold `Formalism.L2.Theta.mt`.

Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]`. Establish `k1` using `hxv _ a ha`. Establish `k2` using `hyv _ b hb`. Rewrite `k1`, `k2` using `[MonoidHom.mul_apply, Circle.coe_mul, ← pow_two]`. Rewrite using `[Circle.coe_mul, Circle.coe_inv]`.

Use `NormOne.mul (NormOne.mul (NormOne.inv' (NormOne.of_pow two_pos ?_)) (NormOne.of_pow two_pos ?_)) (NormOne.prod _ fun τ => ?_)` and prove the remaining obligations. Rewrite using `[k1]`. Conclude with `NormOne.prod _ fun τ => NormOne.zpow' (h1 τ) _`. Rewrite using `[k2]`. Conclude with `NormOne.prod _ fun τ => NormOne.zpow' (h2 τ) _`.

Rewrite using `[he, inv]`. Conclude with `(((h2 τ).pow _).mul ((NormOne.inv' (h1 τ)).pow _)).pow _`.
-/
private theorem vac_scalar {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : s = 1 ∨ s = -1)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) s) (hT : ∀ τ, IsCartanInv (gramAt D T τ) 1)
    {g : Formalism.L2.Theta.GA D S} (hg : g ∈ GinfC S) {h : Formalism.L2.Theta.GA D T} (hh : h ∈ GinfC T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO s 1) f) :
    ∃ c : ℂ, om (g, h) f = c • f ∧ ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt S g)).det) → (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt T h)).det) →
        NormOne lam c := by
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT τ)) h hh
  obtain ⟨e, he⟩ := detPlus_def (m := T.rank) hs
  obtain ⟨a, ha⟩ := sq_exp hθ hW.hecT hW.resT e2 T.rank
  obtain ⟨b, hb⟩ := sq_exp hθ hW.hecS hW.resS e2 S.rank
  refine ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => s) (fun _ => 1) hS hT g hg h hh
    (fun τ => by rcases hs with rfl | rfl <;> simp) (fun τ => by rw [one_mul, mul_one]) x y hx hy f hf hv,
    fun F _ lam h1 h2 => ?_⟩
  have inv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)).det = ((compAt θ τ (Formalism.L2.Theta.mt S g)).det)⁻¹ := fun τ => by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have k1 := hxv _ a ha
  have k2 := hyv _ b hb
  rw [MonoidHom.mul_apply, Circle.coe_mul, ← pow_two] at k1 k2
  rw [Circle.coe_mul, Circle.coe_inv]
  refine NormOne.mul (NormOne.mul (NormOne.inv' (NormOne.of_pow two_pos ?_)) (NormOne.of_pow two_pos ?_))
    (NormOne.prod _ fun τ => ?_)
  · rw [k1]; exact NormOne.prod _ fun τ => NormOne.zpow' (h1 τ) _
  · rw [k2]; exact NormOne.prod _ fun τ => NormOne.zpow' (h2 τ) _
  · rw [he, inv]
    exact (((h2 τ).pow _).mul ((NormOne.inv' (h1 τ)).pow _)).pow _
/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`.
-/
private theorem mt_mul_inv (V : HSp D) (g : Formalism.L2.Theta.GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
/- English proof (translation)
Establish `hrat : ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w` using `fun w => by`. Establish `h1` using `hW.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf w)`. Rewrite `h1` using `[hW.om_heis _ _ _ _ hf]`. Simplify `h1` using `[heisO, symplOH, symplO, hO]`. Rewrite using `[← hrat]`.

Unfold `actO`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]`.
-/
private theorem om_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {γ : Formalism.L2.Theta.GA D S} (hγ : γ ∈ GQ S) {γ' : Formalism.L2.Theta.GA D T} (hγ' : γ' ∈ GQ T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)) :
    om (γ, γ') f w = f (Formalism.L2.Theta.mt T γ'⁻¹ * w * Formalism.L2.Theta.mt S γ : Matrix _ _ _) := by
  have hrat : ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := fun w => by
    have h1 := hW.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf w)
    rw [hW.om_heis _ _ _ _ hf] at h1
    simpa [heisO, symplOH, symplO, hO] using h1
  rw [← hrat]
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
/- English proof (translation)
Establish `key : ∀ (V : HSp D) (γ r : Formalism.L2.Theta.GA D V), infHom V r = 1 → finHom V γ = finHom V r → γ * r⁻¹ ∈ GinfC V ∧ ∀ τ, compAt θ τ (Formalism.L2.Theta.mt V (γ * r⁻¹)) = compAt θ τ (Formalism.L2.Theta.mt V γ)`. Introduce `V γ r h1 h2`. Use `⟨?_, fun τ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finHom V _ = 1`. Rewrite using `[map_mul, map_inv, h2, mul_inv_cancel]`.

Establish `h3 : infHom V (γ * r⁻¹) = infHom V γ` using `by rw [map_mul, map_inv, h1, inv_one, mul_one]`. Conclude with `congrArg (fun x : GL (Fin V.rank) _ => x.1.map (θ τ)) h3`. Take `⟨a1, a2⟩` from `key S γ r hr hγr`. Take `⟨b1, b2⟩` from `key T γ' r' hr' hγr'`. Take `⟨c, hc, hn⟩` from `vac_scalar hθ hW hs hS hT a1 b1 hf' hv`.

Simplify using `only [a2, b2] at hn`. Use `⟨c, fun w => ?_, hn⟩` and prove the remaining obligations. Rewrite using `[← om_rat hW hγ hγ' hf]`. Establish `e : om (γ, γ') (om (g, h) f) = om (γ * r⁻¹, γ' * r'⁻¹) (om (r * g, r' * h) f)`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_left]`.

Rewrite using `[e, hc]`. Both sides reduce to the same expression.
-/
private theorem move_fin {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : s = 1 ∨ s = -1)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) s) (hT : ∀ τ, IsCartanInv (gramAt D T τ) 1)
    {γ r g : Formalism.L2.Theta.GA D S} (hγ : γ ∈ GQ S) (hr : infHom S r = 1) (hγr : finHom S γ = finHom S r)
    {γ' r' h : Formalism.L2.Theta.GA D T} (hγ' : γ' ∈ GQ T) (hr' : infHom T r' = 1) (hγr' : finHom T γ' = finHom T r')
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T (om (g, h) f)) (hf' : IsThetaFunO ψ S T (om (r * g, r' * h) f))
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO s 1) (om (r * g, r' * h) f)) :
    ∃ c : ℂ, (∀ w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D),
      c * om (r * g, r' * h) f w = om (g, h) f (Formalism.L2.Theta.mt T γ'⁻¹ * w * Formalism.L2.Theta.mt S γ : Matrix _ _ _)) ∧
      ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt S γ)).det) → (∀ τ, NormOne lam (compAt θ τ (Formalism.L2.Theta.mt T γ')).det) →
        NormOne lam c := by
  have key : ∀ (V : HSp D) (γ r : Formalism.L2.Theta.GA D V), infHom V r = 1 → finHom V γ = finHom V r →
      γ * r⁻¹ ∈ GinfC V ∧ ∀ τ, compAt θ τ (Formalism.L2.Theta.mt V (γ * r⁻¹)) = compAt θ τ (Formalism.L2.Theta.mt V γ) := by
    intro V γ r h1 h2
    refine ⟨?_, fun τ => ?_⟩
    · change finHom V _ = 1
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    · have h3 : infHom V (γ * r⁻¹) = infHom V γ := by rw [map_mul, map_inv, h1, inv_one, mul_one]
      exact congrArg (fun x : GL (Fin V.rank) _ => x.1.map (θ τ)) h3
  obtain ⟨a1, a2⟩ := key S γ r hr hγr
  obtain ⟨b1, b2⟩ := key T γ' r' hr' hγr'
  obtain ⟨c, hc, hn⟩ := vac_scalar hθ hW hs hS hT a1 b1 hf' hv
  simp only [a2, b2] at hn
  refine ⟨c, fun w => ?_, hn⟩
  rw [← om_rat hW hγ hγ' hf]
  have e : om (γ, γ') (om (g, h) f) = om (γ * r⁻¹, γ' * r'⁻¹) (om (r * g, r' * h) f) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_left]
  rw [e, hc]
  rfl
/- English proof (translation)
Establish `hd : Differentiable ℂ fun z : VC D N N' => Θ (δ • z)` using `hΘ.comp (differentiable_id.const_smul δ)`. Rewrite using `[GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.taylor_comp_smul' D _ hΘ]`. Establish `hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)`. Introduce `τ`. Rewrite using `[GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]`.

Establish `hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) = (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n)`. Simplify using `only [hper, Finsupp.prod, Finsupp.sum]`. Conclude with `Finset.prod_pow_eq_pow_sum _ _ _`. Rewrite using `[hprod, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem jets_scale {N N' : ℕ} (δ a : ℂ) {Θ : VC D N N' → ℂ} (hΘ : Differentiable ℂ Θ) (k : FVar D N' N →₀ ℕ) :
    a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ) =
      ((((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ k.sum fun _ n => n) *
        Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => a * Θ (δ • z) := by
  have hd : Differentiable ℂ fun z : VC D N N' => Θ (δ • z) := hΘ.comp (differentiable_id.const_smul δ)
  rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
    GlobalTheory.FockPos.taylor_comp_smul' D _ hΘ]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
      δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, mul_pow]
  ring
/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply, Complex.mul_conj']`.
-/
private theorem sum_norm_sq {m n : ℕ} (y : Matrix (Fin m) (Fin n) ℂ) : ∑ i, ∑ j, ((‖y i j‖ ^ 2 : ℝ) : ℂ) = (y * yᴴ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj']
/- English proof (translation)
Rewrite using `[sum_norm_sq, sum_norm_sq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc A, hA, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ B, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul …`.
-/
private theorem sum_norm_sq_unitary {m n : ℕ} (y : Matrix (Fin m) (Fin n) ℂ) {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    ∑ i, ∑ j, ((‖(Bᴴ * y * A) i j‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ((‖y i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [sum_norm_sq, sum_norm_sq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc A, hA, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ B,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul]
/- English proof (translation)
Establish `h1 : (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) * GlobalTheory.FockPos.frAt fr τ = 1`. Unfold `GlobalTheory.FockPos.frAt`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `⟨Matrix.inv_eq_left_inv h1, h1, mul_eq_one_comm.1 h1⟩`.
-/
private theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ = (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) ∧
    (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) * GlobalTheory.FockPos.frAt fr τ = 1 ∧
    GlobalTheory.FockPos.frAt fr τ * (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) = 1 := by
  have h1 : (fr⁻¹ : GL (Fin n) D.host.E).1.map (tauE D τ) * GlobalTheory.FockPos.frAt fr τ = 1 := by
    unfold GlobalTheory.FockPos.frAt
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨Matrix.inv_eq_left_inv h1, h1, mul_eq_one_comm.1 h1⟩
/- English proof (translation)
Establish `hθ` using `hf.2.inf`. Take `⟨Φ, hΦ, hr⟩` from `GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf`. Take `⟨Φ', hΦ', hr'⟩` from `GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f' hf'`. Establish `hs : (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ≠ 0`. Establish `hx : 0 < Formalism.L2.Pj.xiR D` using `norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))`.

Conclude with `inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (mul_pos Real.two_pi_pos hx)).ne')`. Establish `e1 : Φ = fun z => a * Θ (δ • z)`. Use `GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq _ _ hΦ ((hΘ.comp (differentiable_id.const_smul δ)).const_mul a) fun k => ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hθ hS hT f Φ hΦ hr k`. Rewrite `h1` using `[hj, jets_scale δ a hΘ]`.

Conclude with `(mul_left_cancel₀ (pow_ne_zero _ hs) h1).symm`. Establish `hd : Differentiable ℂ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1)` using `(LinearMap.toContinuousLinearMap (IsLinearMap.mk' (R := ℂ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1) ⟨fun x y => funext fun τ => by`. Express the relevant statement in the definitionally equal form `((U'.1.map (tauE D τ))ᴴ * (Matrix.of (x τ) + Matrix.of (y τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) = (U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ) + (U'.1.map (tauE D τ))ᴴ * Matrix.of (y τ) * U.1.map (tauE D τ)`. Rewrite using `[Matrix.mul_add, Matrix.add_mul],`. Use `fun c x => funext fun τ => by`.

Express the relevant statement in the definitionally equal form `((U'.1.map (tauE D τ))ᴴ * (c • Matrix.of (x τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) = c • ((U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ))`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]⟩)).differentiable`. Establish `e2 : Φ' = fun z => a * (c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 (δ • z)))`. Use function extensionality and compare the values at `z`. Take `⟨s1, s2⟩` from `realPt_spec hθ fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹`.

Generalize the expression as in `GlobalTheory.AdForm.realPt θ _ = w at s1 s2`. Establish `z1 : GlobalTheory.FockPos.zCo θ frS frT w = z`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `(GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w * GlobalTheory.FockPos.frAt frS τ = Matrix.of (z τ)`. Rewrite using `[s2, (frAt_inv frT τ).1, (frAt_inv frS τ).1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (frAt_inv frT τ).2.1, Matrix.one_mul, Matrix.mul_assoc, (frAt_inv frS τ).2.1, Matrix.mul_one]`.

Establish `h0` using `hsub w`. Take `⟨w₁, hw₁⟩ : ∃ w₁ : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D), w₁ = HMul.hMul (HMul.hMul MT w : Mx D T.rank S.rank) MS` from `⟨_, rfl⟩`. Rewrite `h0` using `[← hw₁]`. Establish `t1 : w₁.map (finPart D) = 0`. Rewrite using `[hw₁, Matrix.map_mul, Matrix.map_mul, s1, Matrix.mul_zero, Matrix.zero_mul]`.

Establish `z2 : ∀ τ, GlobalTheory.FockPos.zCo θ frS frT w₁ τ = ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ)` using `fun τ => by`. Express the relevant statement in the definitionally equal form `(GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w₁ * GlobalTheory.FockPos.frAt frS τ = _`. Establish `a1 : (star U'.1).map (tauE D τ) = (U'.1.map (tauE D τ))ᴴ`. Use extensionality with `i j`. Conclude with `GlobalTheory.FockCompare.tauE_star τ _`.

Rewrite using `[hw₁, compAt_mul, compAt_mul, s2, hMT, hMS, compAt_rat hθ, compAt_rat hθ, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, a1, (frAt_inv frT τ).1, (frAt_inv frS τ).1]`. Establish `b1` using `(frAt_inv frT τ).2.1`. Establish `b2` using `(frAt_inv frS τ).2.1`. Express the relevant statement in the definitionally equal form `_ * (GlobalTheory.FockPos.frAt frT τ * _ * _ * _ * (GlobalTheory.FockPos.frAt frS τ * _ * _)) * _ = _`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[b2, Matrix.mul_one, ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frS τ), b2, Matrix.one_mul, ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul, ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul]`. Establish `z3 : GlobalTheory.FockPos.zCo θ frS frT w₁ = Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z` using `funext z2`. Establish `g1 : GlobalTheory.FockPos.gaussO θ frS frT w₁ = GlobalTheory.FockPos.gaussO θ frS frT w`. Unfold `GlobalTheory.FockPos.gaussO`. Rewrite using `[z1]`.

Use `congr 2`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[z2]`. Conclude with `sum_norm_sq_unitary (Matrix.of (z τ)) (map_unitary τ U) (map_unitary τ U')`. Establish `g0 : GlobalTheory.FockPos.gaussO θ frS frT w ≠ 0` using `Complex.exp_ne_zero _`.

Rewrite `h0` using `[hr w₁ t1, hr' w s1, g1, z1, z3, e1]`. Use `beta_reduce at h0`. Rewrite using `[Formalism.L2.KerInert.PullbackComparison.tPull_smul]`. Use `mul_left_cancel₀ (mul_ne_zero hc g0) ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, h0]`.

Clear the denominators using the available nonvanishing facts. Establish `hd2 : Differentiable ℂ fun z => c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z)` using `(hΘ.comp hd).const_mul _`. Rewrite using `[jets_scale δ a hd2, GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hθ hS hT f' Φ' hΦ' hr' k, e2]`.
-/
private theorem jets_subst {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    {LS LS' : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)} {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f) (hf' : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS' LT' f')
    (U : Matrix.unitaryGroup (Fin S.rank) D.host.E) (U' : Matrix.unitaryGroup (Fin T.rank) D.host.E) {c : ℂ} (hc : c ≠ 0)
    {MT : Matrix (Fin T.rank) (Fin T.rank) (Formalism.L2.Theta.AE D)} {MS : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)}
    (hMT : MT = (frT.1 * star U'.1 * (frT⁻¹ : GL _ _).1).map (incA D)) (hMS : MS = (frS.1 * U.1 * (frS⁻¹ : GL _ _).1).map (incA D))
    (hsub : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D), c * f' w = f (MT * w * MS : Matrix _ _ _))
    (cc : Ideal (𝓞 D.host.K)) (δ a : ℂ) {Θ : VC D S.rank T.rank → ℂ} (hΘ : Differentiable ℂ Θ)
    (hj : ∀ k : FVar D T.rank S.rank →₀ ℕ,
      pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f (MvPolynomial.monomial k 1) 0 =
        a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ))
    (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f' (MvPolynomial.monomial k 1) 0 =
      a * ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
        fun z => c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z)) := by
  have hθ := hf.2.inf
  obtain ⟨Φ, hΦ, hr⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  obtain ⟨Φ', hΦ', hr'⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f' hf'
  have hs : (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ≠ 0 := by
    have hx : 0 < Formalism.L2.Pj.xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (mul_pos Real.two_pi_pos hx)).ne')
  have e1 : Φ = fun z => a * Θ (δ • z) := by
    refine GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq _ _ hΦ
      ((hΘ.comp (differentiable_id.const_smul δ)).const_mul a) fun k => ?_
    have h1 := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hθ hS hT f Φ hΦ hr k
    rw [hj, jets_scale δ a hΘ] at h1
    exact (mul_left_cancel₀ (pow_ne_zero _ hs) h1).symm
  have hd : Differentiable ℂ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1) :=
    (LinearMap.toContinuousLinearMap (IsLinearMap.mk' (R := ℂ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1)
      ⟨fun x y => funext fun τ => by
        change ((U'.1.map (tauE D τ))ᴴ * (Matrix.of (x τ) + Matrix.of (y τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) =
          (U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ) + (U'.1.map (tauE D τ))ᴴ * Matrix.of (y τ) * U.1.map (tauE D τ)
        rw [Matrix.mul_add, Matrix.add_mul],
      fun c x => funext fun τ => by
        change ((U'.1.map (tauE D τ))ᴴ * (c • Matrix.of (x τ)) * U.1.map (tauE D τ) : Matrix _ _ ℂ) =
          c • ((U'.1.map (tauE D τ))ᴴ * Matrix.of (x τ) * U.1.map (tauE D τ))
        rw [Matrix.mul_smul, Matrix.smul_mul]⟩)).differentiable
  have e2 : Φ' = fun z => a * (c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 (δ • z))) := by
    funext z
    obtain ⟨s1, s2⟩ := realPt_spec hθ fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹
    generalize GlobalTheory.AdForm.realPt θ _ = w at s1 s2
    have z1 : GlobalTheory.FockPos.zCo θ frS frT w = z := by
      funext τ
      change (GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w * GlobalTheory.FockPos.frAt frS τ = Matrix.of (z τ)
      rw [s2, (frAt_inv frT τ).1, (frAt_inv frS τ).1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (frAt_inv frT τ).2.1,
        Matrix.one_mul, Matrix.mul_assoc, (frAt_inv frS τ).2.1, Matrix.mul_one]
    have h0 := hsub w
    obtain ⟨w₁, hw₁⟩ : ∃ w₁ : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D),
        w₁ = HMul.hMul (HMul.hMul MT w : Mx D T.rank S.rank) MS := ⟨_, rfl⟩
    rw [← hw₁] at h0
    have t1 : w₁.map (finPart D) = 0 := by
      rw [hw₁, Matrix.map_mul, Matrix.map_mul, s1, Matrix.mul_zero, Matrix.zero_mul]
    have z2 : ∀ τ, GlobalTheory.FockPos.zCo θ frS frT w₁ τ =
        ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ) := fun τ => by
      change (GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ w₁ * GlobalTheory.FockPos.frAt frS τ = _
      have a1 : (star U'.1).map (tauE D τ) = (U'.1.map (tauE D τ))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.tauE_star τ _
      rw [hw₁, compAt_mul, compAt_mul, s2, hMT, hMS, compAt_rat hθ, compAt_rat hθ, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        Matrix.map_mul, a1, (frAt_inv frT τ).1, (frAt_inv frS τ).1]
      have b1 := (frAt_inv frT τ).2.1
      have b2 := (frAt_inv frS τ).2.1
      change _ * (GlobalTheory.FockPos.frAt frT τ * _ * _ * _ * (GlobalTheory.FockPos.frAt frS τ * _ * _)) * _ = _
      simp only [Matrix.mul_assoc]
      rw [b2, Matrix.mul_one, ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frS τ), b2, Matrix.one_mul,
        ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul,
        ← Matrix.mul_assoc _ (GlobalTheory.FockPos.frAt frT τ), b1, Matrix.one_mul]
    have z3 : GlobalTheory.FockPos.zCo θ frS frT w₁ = Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z := funext z2
    have g1 : GlobalTheory.FockPos.gaussO θ frS frT w₁ = GlobalTheory.FockPos.gaussO θ frS frT w := by
      unfold GlobalTheory.FockPos.gaussO
      rw [z1]
      congr 2
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [z2]
      exact sum_norm_sq_unitary (Matrix.of (z τ)) (map_unitary τ U) (map_unitary τ U')
    have g0 : GlobalTheory.FockPos.gaussO θ frS frT w ≠ 0 := Complex.exp_ne_zero _
    rw [hr w₁ t1, hr' w s1, g1, z1, z3, e1] at h0
    beta_reduce at h0
    rw [Formalism.L2.KerInert.PullbackComparison.tPull_smul]
    refine mul_left_cancel₀ (mul_ne_zero hc g0) ?_
    rw [mul_assoc, h0]
    field_simp
  have hd2 : Differentiable ℂ fun z => c⁻¹ * Θ (Formalism.L2.KerInert.tPull D (tor0 D cc δ) U.1 U'.1 z) := (hΘ.comp hd).const_mul _
  rw [jets_scale δ a hd2, GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hθ hS hT f' Φ' hΦ' hr' k, e2]
/- English proof (translation)
Take `⟨γ, h1, h2, h3⟩` from `h`. Use `⟨γ, h1, h2, h3, ?_, fun τ => ?_⟩` and prove the remaining obligations. Establish `: Formalism.L2.Theta.mt V γ⁻¹ = ((matHom V γ)⁻¹).1` using `congrArg Units.val (map_inv (matHom V) γ)`. Rewrite using `[this]`. Use `Units.inv_eq_of_mul_eq_one_left ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ * Formalism.L2.Theta.mt V γ = 1`. Rewrite using `[h3, ← Matrix.map_mul, Matrix.mul_assoc fr.1 U.1, Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_assoc, ← Matrix.mul_assoc (star U.1), U.2.1, Matrix.one_mul, Units.mul_inv, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]`. Rewrite using `[h3, compAt_rat hθ]`. Use `(RingHom.map_det (tauE D τ) _).symm.trans (congrArg _ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_mul_right_comm, Units.mul_inv, Matrix.one_mul]`.
-/
private theorem coord_data {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {fr : GL (Fin V.rank) D.host.E} {r : GfC V}
    {U : Matrix.unitaryGroup (Fin V.rank) D.host.E} (h : RatCoord V fr r U) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V (r : Formalism.L2.Theta.GA D V) ∧
      Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL _ _).1).map (incA D) ∧
      Formalism.L2.Theta.mt V γ⁻¹ = (fr.1 * star U.1 * (fr⁻¹ : GL _ _).1).map (incA D) ∧
      ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V γ)).det = tauE D τ U.1.det := by
  obtain ⟨γ, h1, h2, h3⟩ := h
  refine ⟨γ, h1, h2, h3, ?_, fun τ => ?_⟩
  · have : Formalism.L2.Theta.mt V γ⁻¹ = ((matHom V γ)⁻¹).1 := congrArg Units.val (map_inv (matHom V) γ)
    rw [this]
    refine Units.inv_eq_of_mul_eq_one_left ?_
    change _ * Formalism.L2.Theta.mt V γ = 1
    rw [h3, ← Matrix.map_mul, Matrix.mul_assoc fr.1 U.1, Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_assoc,
      ← Matrix.mul_assoc (star U.1), U.2.1, Matrix.one_mul, Units.mul_inv,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  · rw [h3, compAt_rat hθ]
    refine (RingHom.map_det (tauE D τ) _).symm.trans (congrArg _ ?_)
    rw [Matrix.det_mul_right_comm, Units.mul_inv, Matrix.one_mul]
/- English proof (translation)
Establish `hc : ∀ σ : Qbar →+* ℂ, NormOne σ c` using `fun σ => h ℂ σ (fun τ => normOne_emb σ _ _ (norm_det_complex U)) fun τ => normOne_emb σ _ _ (norm_det_complex U')`. Use `⟨⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, (hc (algebraMap Qbar ℂ)).2, fun M M' q _ a1 a2 a3 a4 lam => ?_⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `h ℂ_[q] lam (fun τ => normOne_emb lam _ _ (norm_det_padic U a1 a3)) fun τ => normOne_emb lam _ _ (norm_det_padic U' a2 a4)`. Rewrite using `[lamC, dif_pos h3]`. Conclude with `h4`.
-/
private theorem arith {N N' : ℕ} (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E) {c : ℂ}
    (h : ∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
      (∀ τ, NormOne lam (tauE D τ U.1.det)) → (∀ τ, NormOne lam (tauE D τ U'.1.det)) → NormOne lam c) :
    Mod1All c ∧ ‖c‖ = 1 ∧ ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q c := by
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ c := fun σ =>
    h ℂ σ (fun τ => normOne_emb σ _ _ (norm_det_complex U)) fun τ => normOne_emb σ _ _ (norm_det_complex U')
  refine ⟨⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, (hc (algebraMap Qbar ℂ)).2, fun M M' q _ a1 a2 a3 a4 lam => ?_⟩
  obtain ⟨h3, h4⟩ := h ℂ_[q] lam (fun τ => normOne_emb lam _ _ (norm_det_padic U a1 a3))
    fun τ => normOne_emb lam _ _ (norm_det_padic U' a2 a4)
  rw [lamC, dif_pos h3]
  exact h4
/- English proof (translation)
Introduce `hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y Θ hΘ hJ r r' U U' hU hU'`. Establish `hθ` using `ch.W.θ_is`. Establish `hv` using `_root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y`. Establish `hv'` using `_root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp (r * x) (r' * y)`. Establish `hlx` using `latAt_rat ch.S.toGridChoice _ r U hU x`.

Establish `hly` using `latAt_rat ch.S.toGridChoice _ r' U' hU' y`. Take `⟨γ, g1, g2, g3, g4, g5⟩` from `coord_data hθ hU`. Take `⟨γ', h1, h2, h3, h4, h5⟩` from `coord_data hθ hU'`. Rewrite using `[hlx, hly]`. Unfold `JetTh at hJ ⊢`.

Rewrite `hv'`, the goal using `[mul_assoc r, mul_assoc r']`. Generalize the expression as in `x * ch.S.N.u p.small = a at hv hv' hJ ⊢`. Generalize the expression as in `y * ch.S.N.u p.big = b at hv hv' hJ ⊢`. Generalize the expression as in `ch.S.Z.vac p = f at hv hv' hJ ⊢`. Consider the cases of `p with`.

Consider the case `mu t i j => exact absurd hp id`. Consider the case `core i => exact absurd hp id`. Consider the case `top t j`. Establish `hj1 : j + 1 ≤ D.R.m` using `hp`. Establish `hS` using `ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)`.

Establish `hT` using `ch.S.N.fr_on (.top (j + 1)) hj1`. Establish `cS` using `ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)`. Establish `cT` using `ch.W.cart_is (.top (j + 1)) hj1`. Establish `eS` using `GlobalTheory.FockPos.cart_one _ hS cS`. Establish `eT` using `GlobalTheory.FockPos.cart_one _ hT cT`.

Establish `hW` using `ch.W.om_is (.top t j) hj1`. Express the relevant statement in the definitionally equal form `IsVacO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ at hv hv'`. Express the relevant statement in the definitionally equal form `∀ k, pureTensorO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ _ _ = _ at hJ`. Express the relevant statement in the definitionally equal form `∃ ε : ℂ, _ ∧ _ ∧ ∀ k, pureTensorO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ _ _ = _`. Rewrite `hv`, `hv'`, `hJ`, `cS`, the goal using `[eS]`.

Rewrite `hv`, `hv'`, `hJ`, `cT`, the goal using `[eT]`. Take `⟨c, hc, hn⟩` from `move_fin hθ hW (Or.inl rfl) cS cT g1 r.2 g2 h1 r'.2 h2 hv.2.theta hv'.2.theta hv'.2.fock`. Establish `hn'` using `fun (F : Type) [NormedField F] (lam : Qbar →+* F) (a1 : ∀ τ, NormOne lam (tauE D τ U.1.det)) (a2 : ∀ τ, NormOne lam (tauE D τ U'.1.det)) => NormOne.inv' (hn F lam (fun τ => (g5 τ).symm ▸ a1 τ) (fun τ => (h5 τ).symm ▸ a2 τ))`. Take `⟨m1, m2, m3⟩` from `arith U U' hn'`. Establish `hc0 : c ≠ 0` using `by rintro rfl; simp at m2`.

Conclude with `⟨c⁻¹, m1, fun q _ => m3 _ _ q, jets_subst _ _ hS hT hv hv' U U' hc0 h4 g3 hc _ _ _ hΘ hJ⟩`. Consider the case `chi i j`. Take `⟨hi, rfl⟩` from `hp`. Establish `hS` using `ch.S.N.fr_on (.grid (i + 1) D.R.m) ⟨hi, rfl⟩`. Establish `hT` using `ch.S.N.fr_on (.grid i D.R.m) ⟨by omega, rfl⟩`.

Establish `cS` using `ch.W.cart_is (.grid (i + 1) D.R.m) ⟨hi, le_rfl⟩`. Establish `cT` using `ch.W.cart_is (.grid i D.R.m) ⟨by omega, le_rfl⟩`. Establish `eS` using `GlobalTheory.FockPos.cart_one _ hS cS`. Establish `eT` using `GlobalTheory.FockPos.cart_one _ hT cT`. Establish `hW` using `ch.W.om_is (.chi i D.R.m) ⟨hi, le_rfl⟩`.

Establish `hj` using `fun f => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m)) (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m)) (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std hθ`. Express the relevant statement in the definitionally equal form `IsVacO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m)) (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ at hv hv'`. Express the relevant statement in the definitionally equal form `∀ k, pureTensorO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m)) (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ _ _ = _ at hJ`. Express the relevant statement in the definitionally equal form `∃ ε : ℂ, _ ∧ _ ∧ ∀ k, pureTensorO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m)) (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ _ _ = _`. Rewrite `hv`, `hv'`, `hJ`, `cS`, `hj`, the goal using `[eS]`.

Rewrite `hv`, `hv'`, `hJ`, `cT`, `hj`, the goal using `[eT]`. Establish `hγ : negGA _ γ' ∈ GQ (negSp (ch.G.V (.grid (i + 1) D.R.m)))`. Take `⟨x, hx, e⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h1)`. Use `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)` and prove the remaining obligations. Establish `hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * (ch.G.V (.grid (i + 1) D.R.m)).gram * (x : Matrix _ _ _) = (ch.G.V (.grid (i + 1) D.R.m)).gram` using `hx`.

Use `show Formalism.UG.cT _ (x : Matrix _ _ _) * (-(ch.G.V (.grid (i + 1) D.R.m)).gram) * (x : Matrix _ _ _) = -(ch.G.V (.grid (i + 1) D.R.m)).gram`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hx']`. Take `⟨c, hc, hn⟩` from `move_fin (r := negGA _ r'.1) (g := negGA _ b.1) (r' := r.1) (h := a.1) (f := f) hθ hW (Or.inr rfl) (fun τ => isCartanInv_neg (cS τ)) cT hγ r'.2 h2 g1 r.2 g2 hv.2.theta hv'.2.theta hv'.2.fock`. Establish `hn'` using `fun (F : Type) [NormedField F] (lam : Qbar →+* F) (a1 : ∀ τ, NormOne lam (tauE D τ U.1.det)) (a2 : ∀ τ, NormOne lam (tauE D τ U'.1.det)) => hn F lam (fun τ => (h5 τ).symm ▸ a2 τ) (fun τ => (g5 τ).symm ▸ a1 τ)`. Take `⟨m1, m2, m3⟩` from `arith U U' hn'`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; simp at m2`. Establish `hcc : (starRingEnd ℂ c)⁻¹ = c`. Use `inv_eq_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj', m2]`. Simplify using the standard rewrite rules.

Use `⟨c, m1, fun q _ => m3 _ _ q, fun k => ?_⟩` and prove the remaining obligations. Establish `key` using `jets_subst _ _ hS hT (GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ (fun _ => 1) _ _ _ _ hv) (GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ (fun _ => 1) _ _ _ _ hv') U' U ((_root_.map_ne_zero (starRingEnd ℂ)).2 hc0) g4 h3 (fun w => by rw [← map_mul]; exact …`. Establish `e` using `congrArg (starRingEnd ℂ) ((hj _ k 0).symm.trans (hJ k))`. Rewrite `e` using `[Complex.conj_conj, map_mul]`. Conclude with `e.trans (congrArg _ (Complex.conj_conj _))) k`.

Rewrite `key` using `[hcc]`. Use `(hj _ k 0).trans ((congrArg (starRingEnd ℂ) key).trans ?_)` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj]`. Both sides reduce to the same expression.
-/
theorem fock_jetTheta_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ), Differentiable ℂ Θ → GlobalTheory.RatMoveJets.JetTh ch p x y Θ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big) (U : Matrix.unitaryGroup (Fin (ch.G.V p.small).rank) D.host.E)
      (U' : Matrix.unitaryGroup (Fin (ch.G.V p.big).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord _ (ch.S.N.fr p.small) r U → GlobalTheory.RatMoveJets.RatCoord _ (ch.S.N.fr p.big) r' U' →
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      GlobalTheory.RatMoveJets.JetTh ch p (r * x) (r' * y) (fun z => ε * Θ (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.RatMoveJets.srcU p U U').1 (GlobalTheory.RatMoveJets.tgtU p U U').1 z)) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y Θ hΘ hJ r r' U U' hU hU'
  have hθ := ch.W.θ_is
  have hv := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
  have hv' := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp (r * x) (r' * y)
  have hlx := latAt_rat ch.S.toGridChoice _ r U hU x
  have hly := latAt_rat ch.S.toGridChoice _ r' U' hU' y
  obtain ⟨γ, g1, g2, g3, g4, g5⟩ := coord_data hθ hU
  obtain ⟨γ', h1, h2, h3, h4, h5⟩ := coord_data hθ hU'
  rw [hlx, hly]
  unfold JetTh at hJ ⊢
  rw [mul_assoc r, mul_assoc r'] at hv' ⊢
  generalize x * ch.S.N.u p.small = a at hv hv' hJ ⊢
  generalize y * ch.S.N.u p.big = b at hv hv' hJ ⊢
  generalize ch.S.Z.vac p = f at hv hv' hJ ⊢
  cases p with
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    have hS := ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)
    have hT := ch.S.N.fr_on (.top (j + 1)) hj1
    have cS := ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)
    have cT := ch.W.cart_is (.top (j + 1)) hj1
    have eS := GlobalTheory.FockPos.cart_one _ hS cS
    have eT := GlobalTheory.FockPos.cart_one _ hT cT
    have hW := ch.W.om_is (.top t j) hj1
    change IsVacO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ at hv hv'
    change ∀ k, pureTensorO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ _ _ = _ at hJ
    change ∃ ε : ℂ, _ ∧ _ ∧ ∀ k, pureTensorO _ _ _ _ (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) _ _ _ _ _ = _
    rw [eS] at hv hv' hJ cS ⊢
    rw [eT] at hv hv' hJ cT ⊢
    obtain ⟨c, hc, hn⟩ := move_fin hθ hW (Or.inl rfl) cS cT g1 r.2 g2 h1 r'.2 h2 hv.2.theta hv'.2.theta hv'.2.fock
    have hn' := fun (F : Type) [NormedField F] (lam : Qbar →+* F) (a1 : ∀ τ, NormOne lam (tauE D τ U.1.det))
      (a2 : ∀ τ, NormOne lam (tauE D τ U'.1.det)) => NormOne.inv' (hn F lam (fun τ => (g5 τ).symm ▸ a1 τ) (fun τ => (h5 τ).symm ▸ a2 τ))
    obtain ⟨m1, m2, m3⟩ := arith U U' hn'
    have hc0 : c ≠ 0 := by rintro rfl; simp at m2
    exact ⟨c⁻¹, m1, fun q _ => m3 _ _ q, jets_subst _ _ hS hT hv hv' U U' hc0 h4 g3 hc _ _ _ hΘ hJ⟩
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hS := ch.S.N.fr_on (.grid (i + 1) D.R.m) ⟨hi, rfl⟩
    have hT := ch.S.N.fr_on (.grid i D.R.m) ⟨by omega, rfl⟩
    have cS := ch.W.cart_is (.grid (i + 1) D.R.m) ⟨hi, le_rfl⟩
    have cT := ch.W.cart_is (.grid i D.R.m) ⟨by omega, le_rfl⟩
    have eS := GlobalTheory.FockPos.cart_one _ hS cS
    have eT := GlobalTheory.FockPos.cart_one _ hT cT
    have hW := ch.W.om_is (.chi i D.R.m) ⟨hi, le_rfl⟩
    have hj := fun f => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std hθ
    change IsVacO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m)) (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ at hv hv'
    change ∀ k, pureTensorO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m))
      (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ _ _ = _ at hJ
    change ∃ ε : ℂ, _ ∧ _ ∧ ∀ k, pureTensorO _ _ (negSp (ch.G.V (.grid (i + 1) D.R.m))) (ch.G.V (.grid i D.R.m))
      (fun τ => -ch.W.cart (.grid (i + 1) D.R.m) τ) (ch.W.cart (.grid i D.R.m)) _ _ _ _ _ = _
    rw [eS] at hv hv' hJ cS hj ⊢
    rw [eT] at hv hv' hJ cT hj ⊢
    have hγ : negGA _ γ' ∈ GQ (negSp (ch.G.V (.grid (i + 1) D.R.m))) := by
      obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h1)
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
      have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * (ch.G.V (.grid (i + 1) D.R.m)).gram * (x : Matrix _ _ _) =
        (ch.G.V (.grid (i + 1) D.R.m)).gram := hx
      show Formalism.UG.cT _ (x : Matrix _ _ _) * (-(ch.G.V (.grid (i + 1) D.R.m)).gram) * (x : Matrix _ _ _) =
        -(ch.G.V (.grid (i + 1) D.R.m)).gram
      rw [Matrix.mul_neg, Matrix.neg_mul, hx']
    obtain ⟨c, hc, hn⟩ := move_fin (r := negGA _ r'.1) (g := negGA _ b.1) (r' := r.1) (h := a.1) (f := f) hθ hW (Or.inr rfl)
      (fun τ => isCartanInv_neg (cS τ)) cT hγ r'.2 h2 g1 r.2 g2 hv.2.theta hv'.2.theta hv'.2.fock
    have hn' := fun (F : Type) [NormedField F] (lam : Qbar →+* F) (a1 : ∀ τ, NormOne lam (tauE D τ U.1.det))
      (a2 : ∀ τ, NormOne lam (tauE D τ U'.1.det)) => hn F lam (fun τ => (h5 τ).symm ▸ a2 τ) (fun τ => (g5 τ).symm ▸ a1 τ)
    obtain ⟨m1, m2, m3⟩ := arith U U' hn'
    have hc0 : c ≠ 0 := by rintro rfl; simp at m2
    have hcc : (starRingEnd ℂ c)⁻¹ = c := by
      refine inv_eq_of_mul_eq_one_left ?_
      rw [Complex.mul_conj', m2]; simp
    refine ⟨c, m1, fun q _ => m3 _ _ q, fun k => ?_⟩
    have key := jets_subst _ _ hS hT (GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ (fun _ => 1) _ _ _ _ hv) (GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ (fun _ => 1) _ _ _ _ hv') U' U
      ((_root_.map_ne_zero (starRingEnd ℂ)).2 hc0) g4 h3 (fun w => by rw [← map_mul]; exact congrArg _ (hc w)) D.host.ccK ch.S.Z.δ
      (starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ)) hΘ (fun k => by
        have e := congrArg (starRingEnd ℂ) ((hj _ k 0).symm.trans (hJ k))
        rw [Complex.conj_conj, map_mul] at e
        exact e.trans (congrArg _ (Complex.conj_conj _))) k
    rw [hcc] at key
    refine (hj _ k 0).trans ((congrArg (starRingEnd ℂ) key).trans ?_)
    rw [map_mul, Complex.conj_conj]
    rfl
end GlobalTheory.RatMoveFock
end
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.RatMoveFock.fock_jetTheta_rational`.
-/
theorem _root_.GlobalTheory.T.twist_fock_jetTheta_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ), Differentiable ℂ Θ → GlobalTheory.RatMoveJets.JetTh ch p x y Θ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big) (U : Matrix.unitaryGroup (Fin (ch.G.V p.small).rank) D.host.E)
      (U' : Matrix.unitaryGroup (Fin (ch.G.V p.big).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord _ (ch.S.N.fr p.small) r U → GlobalTheory.RatMoveJets.RatCoord _ (ch.S.N.fr p.big) r' U' →
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      GlobalTheory.RatMoveJets.JetTh ch p (r * x) (r' * y) (fun z => ε * Θ (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.RatMoveJets.srcU p U U').1 (GlobalTheory.RatMoveJets.tgtU p U U').1 z)) := _root_.GlobalTheory.RatMoveFock.fock_jetTheta_rational
end
