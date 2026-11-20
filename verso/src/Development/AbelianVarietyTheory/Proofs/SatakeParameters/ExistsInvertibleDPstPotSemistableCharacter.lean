import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToAStRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAlStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section
open Module

namespace GlobalTheory.NormBC

/- English proof (translation)
Establish `h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B`. Apply `TensorProduct.AlgebraTensorModule.ext` to reduce the goal to its premises. Introduce `b z`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]`.
-/
theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

/- English proof (translation)
Rewrite `h` using `[Algebra.norm_apply]`. Establish `hu : IsUnit (LinearMap.mul B A z)` using `(LinearMap.isUnit_iff_isUnit_det _).2 h`. Take `⟨y, hy⟩` from `((Module.End.isUnit_iff _).1 hu).2 1`. Conclude with `IsUnit.of_mul_eq_one y (by simpa using hy)`.
-/
theorem isUnit_of_isUnit_norm {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Free B A]
    [Module.Finite B A] {z : A} (h : IsUnit (Algebra.norm B z)) : IsUnit z := by
  rw [Algebra.norm_apply] at h
  have hu : IsUnit (LinearMap.mul B A z) := (LinearMap.isUnit_iff_isUnit_det _).2 h
  obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
  exact IsUnit.of_mul_eq_one y (by simpa using hy)

end GlobalTheory.NormBC

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def toAlg (L : FinExt l) : Bst P ⊗[ℚ_[l]] (Fin 1 → ↥L.1) ≃ₗ[Bst P] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Bst P) (Bst P))
    (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => rfl`. Consider the case `add x x' hx hx' => simp only [map_add, hx, hx']`.
-/
theorem toAlg_comm (L : FinExt l) (z : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toAlg P L (TensorProduct.comm ℚ_[l] (Fin 1 → ↥L.1) (Bst P) z) = toA P L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x x' hx hx' => simp only [map_add, hx, hx']

/- English proof (translation)
Establish `h` using `b.linearIndependent.map' (((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) (LinearMap.ker_eq_bot.mpr ((toAlg P L).injective.comp (GlobalTheory.PstRank.toB_injective P ρ)))`. Establish `hf : (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) = ⇑(((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) ∘ ⇑b`. Use function extensionality and compare the values at `fun i => (toAlg_comm P L _).symm`. Rewrite using `[hf]`. Conclude with `h`.
-/
theorem linearIndependent_toA {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (b : Basis (Fin d) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) :
    LinearIndependent ↥(MaximalUnramifiedExtension l)
      (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
  have h := b.linearIndependent.map' (((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ
    GlobalTheory.PstRank.toB P ρ) (LinearMap.ker_eq_bot.mpr ((toAlg P L).injective.comp (GlobalTheory.PstRank.toB_injective P ρ)))
  have hf : (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) =
      ⇑(((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) ∘ ⇑b :=
    funext fun i => (toAlg_comm P L _).symm
  rw [hf]
  exact h

end GlobalTheory.Pst.UnitLetter

namespace GlobalTheory.Pst.UnitLetter

open GlobalTheory.NormBC

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

/- English proof (translation)
It suffices to establish `h : ∀ s : Finset (Fin d), ∃ K' : FinExt l, ∀ i ∈ s, ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' → stRep P ρ g (y i) = y i by`. Take `⟨K', hK'⟩` from `h Finset.univ`. Conclude with `⟨K', fun i => hK' i (Finset.mem_univ i)⟩`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact ⟨K, by simp⟩`. Consider the case `insert j s hj ih`. Take `⟨K₁, h₁⟩` from `ih`. Take `⟨K₂, h₂⟩` from `(mem_Dpst P ρ).mp (hy j)`. Use `⟨supExt K₁ K₂, fun i hi g hg => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)`. Conclude with `h₁ i hi g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)`.
-/
theorem exists_common_fixed {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (hy : ∀ i, y i ∈ Dpst P ρ) :
    ∃ K' : FinExt l, ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' → stRep P ρ g (y i) = y i := by
  suffices h : ∀ s : Finset (Fin d), ∃ K' : FinExt l, ∀ i ∈ s, ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g (y i) = y i by
    obtain ⟨K', hK'⟩ := h Finset.univ
    exact ⟨K', fun i => hK' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨K, by simp⟩
  | insert j s hj ih =>
    obtain ⟨K₁, h₁⟩ := ih
    obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (hy j)
    refine ⟨supExt K₁ K₂, fun i hi g hg => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    · exact h₁ i hi g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)

end GlobalTheory.Pst.UnitLetter

set_option maxHeartbeats 1000000 in
open GlobalTheory.Pst.UnitLetter GlobalTheory.NormBC in

/- English proof (translation)
Introduce `l _ P AI hT K L ρm χ hm hpst`. Use `haveI := L.2`. Take `⟨hdom, hfrac, hline⟩` from `GlobalTheory.Pst.stRegular l P AI hT`. Take `⟨hfd, hrank⟩` from `(isPst_iff P ρm).mp hpst`. Use `set d := finrank ℚ_[l] ↥L.1 with hddef`.

Establish `hd : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) = d`. Rewrite using `[hrank]`. Conclude with `(LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1).finrank_eq`. Set `bD` to `Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) hd`. Set `y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P` to `fun i => ((toUr P ρm).symm (bD i) : ↥(Dpst P ρm)).1`.

Establish `hyD : ∀ i, y i ∈ Dpst P ρm` using `fun i => ((toUr P ρm).symm (bD i)).2`. Take `⟨K', hK'⟩` from `exists_common_fixed P ρm y hyD`. Set `w : Fin d → Bst P ⊗[ℚ_[l]] ↥L.1` to `fun i => toA P L (y i)`. Set `G` to `{g : ↥(GK K) // (g : GQ l) ∈ GK K'}`. Set `σ : G → (Bst P ⊗[ℚ_[l]] ↥L.1) →+ (Bst P ⊗[ℚ_[l]] ↥L.1)` to `fun g => AddMonoidHom.mk' (fun z => Algebra.TensorProduct.map (actSt P ((g.1 : ↥(GK K)) : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) z * ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g.1)) (fun a b => by simp [map_add, add_mul])`.

Establish `hσ : ∀ (g : G) (b : Bst P) (z : Bst P ⊗[ℚ_[l]] ↥L.1), σ g (b • z) = actSt P ((g.1 : ↥(GK K)) : GQ l) b • σ g z`. Introduce `g b z`. Simplify using `only [σ, AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, mul_assoc]`. Use `congr 1`. Establish `hreg : ∀ b b' : Bst P, b ≠ 0 → (∀ g : G, b * actSt P ((g.1 : ↥(GK K)) : GQ l) b' = actSt P ((g.1 : ↥(GK K)) : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b`.

Introduce `b b' hb h`. Take `⟨c, -, hc⟩` from `hfrac (supExt K K') b b' hb fun g => h ⟨⟨g, GK_le (K' := supExt K K') le_sup_left g.2⟩, GK_le (K' := supExt K K') le_sup_right g.2⟩`. Conclude with `⟨c, hc⟩`. Establish `hv : ∀ (g : G) i, σ g (w i) = w i`. Introduce `g i`.

Simplify using `only [σ, w, AddMonoidHom.mk'_apply]`. Rewrite using `[← toA_stRep ρm χ hm, hK' i g.1 g.2]`. Establish `hK : LinearIndependent ↥(MaximalUnramifiedExtension l) w` using `linearIndependent_toA P ρm bD`. Establish `hB : LinearIndependent (Bst P) w`. Use `GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (W := Bst P ⊗[ℚ_[l]] ↥L.1) (G := G) (fun g => actSt P ((g.1 : ↥(GK K)) : GQ l)) σ hσ hreg w hv Finset.univ (hK.linearIndepOn _)` as an intermediate fact.

Rewrite `this` using `[Finset.coe_univ]`. Conclude with `linearIndepOn_univ.mp this`. Establish `hfin : finrank (Bst P) (Bst P ⊗[ℚ_[l]] ↥L.1) = d` using `Module.finrank_baseChange`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero (k := ↥(MaximalUnramifiedExtension l)) w (GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent hfin w hB)`. Set `ys` to `∑ i, mulV P ↥L.1 (Fin 1 → ↥L.1) (a i) (y i)`.

Establish `hys : ys ∈ Dpst P ρm` using `Submodule.sum_mem _ fun i _ => mulV_mem_Dpst P ρm (a i) (y i) (hyD i)`. Establish `hysA : toA P L ys = ∑ i, algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (a i) • w i`. Simplify using `only [ys, map_sum, toA_mulV, w]`. Establish `hn : Algebra.norm (Bst P) (toA P L ys) ≠ 0` using `by rw [hysA]; exact ha`. Take `⟨K₂, hK₂⟩` from `(mem_Dpst P ρm).mp hys`.

Establish `hχ : ∀ g : ↥(GK K), χ g ≠ 0`. Introduce `g h0`. Establish `h1 : ρm (g * g⁻¹) (fun _ => (1 : ↥L.1)) = fun _ => 1` using `by rw [mul_inv_cancel, map_one]; rfl`. Rewrite `h1` using `[map_mul, Module.End.mul_apply, hm g, h0, zero_smul]`. Conclude with `zero_ne_one (congrFun h1 0)`.

Establish `hunit : IsUnit (Algebra.norm (Bst P) (toA P L ys))`. Use `hline (supExt K K₂) _ hn fun g => ?_` and prove the remaining obligations. Set `g0 : ↥(GK K)` to `⟨g, GK_le (K' := supExt K K₂) le_sup_left g.2⟩`. Establish `hfix` using `hK₂ g0 (GK_le (K' := supExt K K₂) le_sup_right g.2)`. Establish `h1 : Algebra.norm (Bst P) (toA P L (stRep P ρm g0 ys)) = Algebra.norm (Bst P) (toA P L ys)`.

Rewrite using `[hfix]`. Rewrite `h1` using `[toA_stRep ρm χ hm, map_mul, GlobalTheory.T.norm_tensorProduct_map_id_right, norm_one_tmul]`. Establish `hν : Algebra.norm ℚ_[l] (χ g0) ≠ 0` using `Algebra.norm_ne_zero_iff.mpr (hχ g0)`. Use `⟨(Algebra.norm ℚ_[l] (χ g0))⁻¹, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `actSt P ((g0 : ↥(GK K)) : GQ l) _ = _`.

Use `conv_rhs => rw [← h1]`. Rewrite using `[mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, mul_one]`. Take `⟨v, hv'⟩` from `(isUnit_of_isUnit_norm hunit).exists_right_inv`. Use `⟨ys, hys, (toA P L).symm v, ?_⟩` and prove the remaining obligations. Apply `(toA P L).injective` to reduce the goal to its premises.

Rewrite using `[toA_mulB, LinearEquiv.apply_symm_apply, toA_tmul, mul_comm, hv']`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.Pst.UnitLetter.exists_unit_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  intro l _ P AI hT K L ρm χ hm hpst
  haveI := L.2
  obtain ⟨hdom, hfrac, hline⟩ := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hfd, hrank⟩ := (isPst_iff P ρm).mp hpst
  set d := finrank ℚ_[l] ↥L.1 with hddef
  have hd : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) = d := by
    rw [hrank]; exact (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1).finrank_eq
  let bD := Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) hd
  let y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρm).symm (bD i) : ↥(Dpst P ρm)).1
  have hyD : ∀ i, y i ∈ Dpst P ρm := fun i => ((toUr P ρm).symm (bD i)).2

  obtain ⟨K', hK'⟩ := exists_common_fixed P ρm y hyD
  let w : Fin d → Bst P ⊗[ℚ_[l]] ↥L.1 := fun i => toA P L (y i)
  let G := {g : ↥(GK K) // (g : GQ l) ∈ GK K'}
  let σ : G → (Bst P ⊗[ℚ_[l]] ↥L.1) →+ (Bst P ⊗[ℚ_[l]] ↥L.1) := fun g => AddMonoidHom.mk' (fun z =>
      Algebra.TensorProduct.map (actSt P ((g.1 : ↥(GK K)) : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) z *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g.1)) (fun a b => by simp [map_add, add_mul])
  have hσ : ∀ (g : G) (b : Bst P) (z : Bst P ⊗[ℚ_[l]] ↥L.1),
      σ g (b • z) = actSt P ((g.1 : ↥(GK K)) : GQ l) b • σ g z := by
    intro g b z
    simp only [σ, AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, mul_assoc]
    congr 1
  have hreg : ∀ b b' : Bst P, b ≠ 0 → (∀ g : G, b * actSt P ((g.1 : ↥(GK K)) : GQ l) b' =
      actSt P ((g.1 : ↥(GK K)) : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b := by
    intro b b' hb h
    obtain ⟨c, -, hc⟩ := hfrac (supExt K K') b b' hb fun g =>
      h ⟨⟨g, GK_le (K' := supExt K K') le_sup_left g.2⟩, GK_le (K' := supExt K K') le_sup_right g.2⟩
    exact ⟨c, hc⟩
  have hv : ∀ (g : G) i, σ g (w i) = w i := by
    intro g i
    simp only [σ, w, AddMonoidHom.mk'_apply]
    rw [← toA_stRep ρm χ hm, hK' i g.1 g.2]
  have hK : LinearIndependent ↥(MaximalUnramifiedExtension l) w := linearIndependent_toA P ρm bD
  have hB : LinearIndependent (Bst P) w := by
    have := GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P)
      (W := Bst P ⊗[ℚ_[l]] ↥L.1)
      (G := G) (fun g => actSt P ((g.1 : ↥(GK K)) : GQ l)) σ hσ hreg w hv Finset.univ
      (hK.linearIndepOn _)
    rw [Finset.coe_univ] at this
    exact linearIndepOn_univ.mp this
  have hfin : finrank (Bst P) (Bst P ⊗[ℚ_[l]] ↥L.1) = d := Module.finrank_baseChange
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero (k := ↥(MaximalUnramifiedExtension l)) w (GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent hfin w hB)
  let ys := ∑ i, mulV P ↥L.1 (Fin 1 → ↥L.1) (a i) (y i)
  have hys : ys ∈ Dpst P ρm := Submodule.sum_mem _ fun i _ => mulV_mem_Dpst P ρm (a i) (y i) (hyD i)
  have hysA : toA P L ys = ∑ i, algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (a i) • w i := by
    simp only [ys, map_sum, toA_mulV, w]
  have hn : Algebra.norm (Bst P) (toA P L ys) ≠ 0 := by rw [hysA]; exact ha
  obtain ⟨K₂, hK₂⟩ := (mem_Dpst P ρm).mp hys
  have hχ : ∀ g : ↥(GK K), χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g * g⁻¹) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by rw [mul_inv_cancel, map_one]; rfl
    rw [map_mul, Module.End.mul_apply, hm g, h0, zero_smul] at h1
    exact zero_ne_one (congrFun h1 0)
  have hunit : IsUnit (Algebra.norm (Bst P) (toA P L ys)) := by
    refine hline (supExt K K₂) _ hn fun g => ?_
    let g0 : ↥(GK K) := ⟨g, GK_le (K' := supExt K K₂) le_sup_left g.2⟩
    have hfix := hK₂ g0 (GK_le (K' := supExt K K₂) le_sup_right g.2)
    have h1 : Algebra.norm (Bst P) (toA P L (stRep P ρm g0 ys)) = Algebra.norm (Bst P) (toA P L ys) := by
      rw [hfix]
    rw [toA_stRep ρm χ hm, map_mul, GlobalTheory.T.norm_tensorProduct_map_id_right, norm_one_tmul] at h1
    have hν : Algebra.norm ℚ_[l] (χ g0) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hχ g0)
    refine ⟨(Algebra.norm ℚ_[l] (χ g0))⁻¹, ?_⟩
    change actSt P ((g0 : ↥(GK K)) : GQ l) _ = _
    conv_rhs => rw [← h1]
    rw [mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, mul_one]
  obtain ⟨v, hv'⟩ := (isUnit_of_isUnit_norm hunit).exists_right_inv
  refine ⟨ys, hys, (toA P L).symm v, ?_⟩
  apply (toA P L).injective
  rw [toA_mulB, LinearEquiv.apply_symm_apply, toA_tmul, mul_comm, hv']
  rfl
