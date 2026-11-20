import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPolynomialDegreeLeRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPolynomialCoefficientsEqStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEigenvalueAtBaseFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFramesStatement

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open scoped TensorProduct

namespace GlobalTheory.FiniteRingMultiplication

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def multN (N : ℕ) : AddSubgroup (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∃ s ∈ Formalism.L2.Herm.intAf F E, z = (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s}
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, add_mem hs ht, (mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, zero_mem _, (mul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨-s, neg_mem hs, (mul_neg _ _).symm⟩

/- English proof (translation)
Establish `h` using `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) (fun v => Valued.isOpen_valuationSubring _)`. Conclude with `h`.
-/
theorem isOpen_intAd : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have h := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

/- English proof (translation)
Establish `h : IsAlgebraic ℤ e` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)`. Take `⟨y, hy, hi⟩` from `h.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩` and prove the remaining obligations. Establish `h2 : IsIntegral ℤ ((y.natAbs : E) * e)`. Break down `Int.natAbs_eq y with h3 | h3` into its components or cases.

Establish `: (y.natAbs : E) * e = y • e` using `by conv_rhs => rw [h3]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hi`. Establish `: (y.natAbs : E) * e = -(y • e)` using `by conv_rhs => rw [h3]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hi.neg`. Conclude with `⟨⟨_, h2⟩, rfl⟩`.
-/
theorem exists_nat_mul_int (e : E) : ∃ m : ℕ, m ≠ 0 ∧ (m : E) * e ∈ Formalism.UG.intOE E := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * e) := by
    rcases Int.natAbs_eq y with h3 | h3
    · have : (y.natAbs : E) * e = y • e := by
        conv_rhs => rw [h3]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * e = -(y • e) := by
        conv_rhs => rw [h3]
        simp
      rw [this]; exact hi.neg
  exact ⟨⟨_, h2⟩, rfl⟩

variable {F E}

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => exact Eventually.of_forall fun a => by rw [zero_mul]; exact zero_mem _`. Consider the case `add c d hc hd => filter_upwards [hc, hd] with a h1 h2`. Rewrite using `[add_mul]`. Conclude with `add_mem h1 h2`.

Consider the case `tmul e u`. Take `⟨m, hm, hme⟩` from `exists_nat_mul_int E e`. Use `set w : F := ((N : F) * (m : F))⁻¹ with hw`. Establish `hc : Continuous fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a` using `continuous_const.mul continuous_id`. Establish `h0 : (fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a) ⁻¹' (Formalism.UG.intAd F : Set _) ∈ 𝓝 0` using `((isOpen_intAd F).preimage hc).mem_nhds (by show (algebraMap F _ w * u) * 0 ∈ Formalism.UG.intAd F`.

Rewrite using `[mul_zero]`. Conclude with `zero_mem _)`. Use `filter_upwards [h0] with a ha`. Use `⟨(((m : E) * e) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] ((algebraMap F _ w * u) * a)), mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hme⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, ha⟩, rfl⟩)), ?_⟩` and prove the remaining obligations. Establish `hN' : (N : F) ≠ 0` using `by exact_mod_cast hN`.

Establish `hm' : (m : F) ≠ 0` using `by exact_mod_cast hm`. Establish `e1 : (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (N : F)` using `(map_natCast _ _).symm`. Establish `e2 : (m : E) * e = (m : F) • e` using `by rw [Algebra.smul_def, map_natCast]`. Rewrite using `[e1, e2, ← Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc, ← Algebra.smul_def, mul_one, mul_one, one_mul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul]`. Establish `: (N : F) * (m : F) * w = 1` using `by rw [hw]; field_simp`.

Rewrite using `[this, one_smul]`.
-/
theorem eventually_mul_right (N : ℕ) (hN : N ≠ 0) (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ a in 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), c * ((1 : E) ⊗ₜ[F] a) ∈ multN F E N := by
  induction c using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun a => by rw [zero_mul]; exact zero_mem _
  | add c d hc hd =>
    filter_upwards [hc, hd] with a h1 h2
    rw [add_mul]; exact add_mem h1 h2
  | tmul e u =>
    obtain ⟨m, hm, hme⟩ := exists_nat_mul_int E e
    set w : F := ((N : F) * (m : F))⁻¹ with hw
    have hc : Continuous fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a := continuous_const.mul continuous_id
    have h0 : (fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a) ⁻¹' (Formalism.UG.intAd F : Set _) ∈ 𝓝 0 :=
      ((isOpen_intAd F).preimage hc).mem_nhds (by
        show (algebraMap F _ w * u) * 0 ∈ Formalism.UG.intAd F
        rw [mul_zero]; exact zero_mem _)
    filter_upwards [h0] with a ha
    refine ⟨(((m : E) * e) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] ((algebraMap F _ w * u) * a)),
      mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hme⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, ha⟩, rfl⟩)), ?_⟩
    have hN' : (N : F) ≠ 0 := by exact_mod_cast hN
    have hm' : (m : F) ≠ 0 := by exact_mod_cast hm
    have e1 : (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (N : F) := (map_natCast _ _).symm
    have e2 : (m : E) * e = (m : F) • e := by rw [Algebra.smul_def, map_natCast]
    rw [e1, e2, ← Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc,
      ← Algebra.smul_def, mul_one, mul_one, one_mul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul]
    have : (N : F) * (m : F) * w = 1 := by rw [hw]; field_simp
    rw [this, one_smul]

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set B := Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) (Module.finBasis F E) with hB`. Establish `h1 : ∀ i, ∀ᶠ b in 𝓝 (0 : AdeleRing (𝓞 F) F ⊗[F] E), (c * (Module.finBasis F E i ⊗ₜ[F] 1)) * ((1 : E) ⊗ₜ[F] (B.coord i b).2) ∈ multN F E N`. Introduce `i`. Establish `hc : Continuous (B.coord i)` using `IsModuleTopology.continuous_of_linearMap _`.

Establish `hs : Continuous fun a : AdeleRing (𝓞 F) F => a.2` using `continuous_snd`. Establish `ht : Tendsto (fun b => (B.coord i b).2) (𝓝 0) (𝓝 0)`. Use `(hs.comp hc).tendsto' 0 0 ?_` and prove the remaining obligations. Use `show (B.coord i 0).2 = 0`. Rewrite using `[map_zero]`.

Both sides reduce to the same expression. Conclude with `ht.eventually (eventually_mul_right N hN _)`. Use `filter_upwards [eventually_all.2 h1] with b hb`. Rewrite using `[← B.sum_repr b, map_sum, Finset.mul_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Use `hb i` as an intermediate fact. Rewrite `this` using `[mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hφ]`. Conclude with `this`.
-/
theorem eventually_mul_hom (N : ℕ) (hN : N ≠ 0)
    [TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E)] [IsModuleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)]
    (φ : AdeleRing (𝓞 F) F ⊗[F] E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hφ : ∀ a e, φ (a ⊗ₜ[F] e) = e ⊗ₜ[F] a.2) (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ b in 𝓝 (0 : AdeleRing (𝓞 F) F ⊗[F] E), c * φ b ∈ multN F E N := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set B := Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) (Module.finBasis F E) with hB
  have h1 : ∀ i, ∀ᶠ b in 𝓝 (0 : AdeleRing (𝓞 F) F ⊗[F] E),
      (c * (Module.finBasis F E i ⊗ₜ[F] 1)) * ((1 : E) ⊗ₜ[F] (B.coord i b).2) ∈ multN F E N := by
    intro i
    have hc : Continuous (B.coord i) := IsModuleTopology.continuous_of_linearMap _
    have hs : Continuous fun a : AdeleRing (𝓞 F) F => a.2 := continuous_snd
    have ht : Tendsto (fun b => (B.coord i b).2) (𝓝 0) (𝓝 0) := by
      refine (hs.comp hc).tendsto' 0 0 ?_
      show (B.coord i 0).2 = 0
      rw [map_zero]; rfl
    exact ht.eventually (eventually_mul_right N hN _)
  filter_upwards [eventually_all.2 h1] with b hb
  rw [← B.sum_repr b, map_sum, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  have := hb i
  rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hφ]
  exact this

end General

/- English proof (translation)
Establish `h1 : ∀ i j k l, ∀ᶠ g in 𝓝 (1 : GL (Fin n) A), ((β⁻¹).val i k * β.val l j) * φ ((g.val - 1) k l) ∈ W`. Introduce `i j k l`. Establish `hc : Continuous fun g : GL (Fin n) A => (g.val - 1) k l` using `(Units.continuous_val.sub continuous_const).matrix_elem k l`. Establish `ht : Tendsto (fun g : GL (Fin n) A => (g.val - 1) k l) (𝓝 1) (𝓝 0)` using `hc.tendsto' 1 0 (by simp)`. Conclude with `ht.eventually (hφ _)`.

Use `filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k => eventually_all.2 fun l => h1 i j k l] with g hg x hx i j`. Establish `e : (β⁻¹ * x * β).val - 1 = (β⁻¹).val * (g.val - 1).map φ * β.val`. Establish `: (g.val - 1).map φ = x.val - 1`. Rewrite using `[hx]`. Conclude with `(map_sub φ.mapMatrix _ _).trans (by rw [map_one]; rfl)`.

Rewrite using `[this, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]`. Rewrite using `[e, Matrix.mul_apply]`. Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations.

Use `hg i j k l` as an intermediate fact. Rewrite using `[Matrix.map_apply, mul_right_comm]`. Conclude with `this`.
-/
theorem eventually_conj {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] {n : ℕ}
    (φ : A →+* B) (W : AddSubgroup B) (hφ : ∀ c, ∀ᶠ a in 𝓝 (0 : A), c * φ a ∈ W) (β : GL (Fin n) B) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin n) A), ∀ x : GL (Fin n) B, x.val = g.val.map φ → ∀ i j, ((β⁻¹ * x * β).val - 1) i j ∈ W := by
  have h1 : ∀ i j k l, ∀ᶠ g in 𝓝 (1 : GL (Fin n) A), ((β⁻¹).val i k * β.val l j) * φ ((g.val - 1) k l) ∈ W := by
    intro i j k l
    have hc : Continuous fun g : GL (Fin n) A => (g.val - 1) k l :=
      (Units.continuous_val.sub continuous_const).matrix_elem k l
    have ht : Tendsto (fun g : GL (Fin n) A => (g.val - 1) k l) (𝓝 1) (𝓝 0) := hc.tendsto' 1 0 (by simp)
    exact ht.eventually (hφ _)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    eventually_all.2 fun l => h1 i j k l] with g hg x hx i j
  have e : (β⁻¹ * x * β).val - 1 = (β⁻¹).val * (g.val - 1).map φ * β.val := by
    have : (g.val - 1).map φ = x.val - 1 := by
      rw [hx]
      exact (map_sub φ.mapMatrix _ _).trans (by rw [map_one]; rfl)
    rw [this, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun k _ => ?_
  have := hg i j k l
  rw [Matrix.map_apply, mul_right_comm]
  exact this

section Group

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def finRing (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finRing_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    finRing D (a ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] a.2 := rfl

variable {D : D7} {V : HSp D}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finE_val (g : GA D V) : (finE V g).val = (matHom V g).val.map (finRing D) := rfl

/- English proof (translation)
Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Consider the case `add c d hc hd => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hc, hd]`. Consider the case `tmul a e => rfl`.
-/
theorem finRing_sig (b : AF D.host.F ⊗[D.host.F] D.host.E) :
    finRing D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig b) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finRing D b) := by
  induction b using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add c d hc hd => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hc, hd]
  | tmul a e => rfl

/- English proof (translation)
Establish `h : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val * JR (AF D.host.F) V.gram * (matHom V g).val = JR (AF D.host.F) V.gram` using `g.2`. Establish `h2` using `congrArg (finRing D).mapMatrix h`. Rewrite `h2` using `[map_mul, map_mul]`. Establish `e1 : (finRing D).mapMatrix (JR (AF D.host.F) V.gram) = V.gram.map (Formalism.UG.inclE (F` using `D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `e2 : (finRing D).mapMatrix (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val) = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (finE V g).val`. Use extensionality with `i j`. Conclude with `finRing_sig _`. Rewrite `h2` using `[e1, e2]`.

Conclude with `h2`.
-/
theorem finE_mem_UA (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val * JR (AF D.host.F) V.gram *
    (matHom V g).val = JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (finRing D).mapMatrix h
  rw [map_mul, map_mul] at h2
  have e1 : (finRing D).mapMatrix (JR (AF D.host.F) V.gram) =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
    ext i j; rfl
  have e2 : (finRing D).mapMatrix (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (finE V g).val := by
    ext i j; exact finRing_sig _
  rw [e1, e2] at h2
  exact h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModTop : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩

/- English proof (translation)
Use `haveI := isModTop (D := D)`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Conclude with `IsModuleTopology.isTopologicalRing (AF D.host.F) _`.
-/
theorem isTopRing : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := by
  haveI := isModTop (D := D)
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact IsModuleTopology.isTopologicalRing (AF D.host.F) _

/- English proof (translation)
Use `haveI := isTopRing (D := D)`. Conclude with `(inferInstance : IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`.
-/
theorem isTopGroup : IsTopologicalGroup (GA D V) := by
  haveI := isTopRing (D := D)
  exact (inferInstance : IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

/- English proof (translation)
Use `haveI := isModTop (D := D)`. Use `haveI := isTopRing (D := D)`. Establish `h1 : Continuous fun g : GA D V => matHom V g` using `continuous_subtype_val`. Establish `ht : Tendsto (fun g : GA D V => matHom V g) (𝓝 1) (𝓝 1)` using `h1.tendsto' 1 1 rfl`. Establish `h2` using `ht.eventually (eventually_conj (finRing D) (multN D.host.F D.host.E N) (eventually_mul_hom N hN (finRing D) (finRing_tmul D)) β)`.

Use `filter_upwards [h2] with g hg`. Conclude with `hg _ (finE_val g)`.
-/
theorem eventually_entry (β : GL (Fin V.rank) (EAf D)) (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ g in 𝓝 (1 : GA D V), ∀ i j, ((β⁻¹ * finE V g * β).val - 1) i j ∈ multN D.host.F D.host.E N := by
  haveI := isModTop (D := D)
  haveI := isTopRing (D := D)
  have h1 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have ht : Tendsto (fun g : GA D V => matHom V g) (𝓝 1) (𝓝 1) := h1.tendsto' 1 1 rfl
  have h2 := ht.eventually (eventually_conj (finRing D) (multN D.host.F D.host.E N)
    (eventually_mul_hom N hN (finRing D) (finRing_tmul D)) β)
  filter_upwards [h2] with g hg
  exact hg _ (finE_val g)

end Group

section Princ

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Take `⟨s, hs, e⟩` from `h i j`. Establish `: m i j = (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s + (1 : Matrix (Fin n) (Fin n) _) i j`. Rewrite using `[← e, Matrix.sub_apply, sub_add_cancel]`. Rewrite using `[this]`. Use `add_mem (mul_mem (natCast_mem _ _) hs) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem entry_int {N : ℕ} {m : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ i j, (m - 1) i j ∈ multN F E N) (i j : Fin n) : m i j ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, hs, e⟩ := h i j
  have : m i j = (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s + (1 : Matrix (Fin n) (Fin n) _) i j := by
    rw [← e, Matrix.sub_apply, sub_add_cancel]
  rw [this]
  refine add_mem (mul_mem (natCast_mem _ _) hs) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Use `set S := Formalism.L2.Herm.intAf F E with hS`. Set `a : Matrix (Fin n) (Fin n) S` to `fun i j => ⟨_, entry_int h i j⟩`. Set `b : Matrix (Fin n) (Fin n) S` to `fun i j => ⟨_, entry_int h' i j⟩`. Establish `ha : S.subtype.mapMatrix a = (β⁻¹ * x * β).val` using `rfl`. Establish `hb : S.subtype.mapMatrix b = (β⁻¹ * x⁻¹ * β).val` using `rfl`.

Establish `hinj : Function.Injective (S.subtype.mapMatrix : Matrix (Fin n) (Fin n) S → _)`. Introduce `u v huv`. Use extensionality with `i j`. Conclude with `congrFun (congrFun huv i) j`. Set `y : GL (Fin n) S` to `⟨a, b, hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group), hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group)⟩`.

Establish `hy : frGL β y = x`. Establish `h1 : intGL F E n y = β⁻¹ * x * β` using `Units.ext rfl`. Use `show β * intGL F E n y * β⁻¹ = x`. Rewrite using `[h1]`. Use `group`.

Use `⟨⟨y, hy⟩, fun PP hP => ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, redFn_frGL]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show resS F PP (a i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j`.

Take `⟨s, hs, e⟩` from `h i j`. Establish `h2 : a i j = (N : S) * ⟨s, hs⟩ + (1 : Matrix (Fin n) (Fin n) S) i j`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h3 : (((1 : Matrix (Fin n) (Fin n) S) i j : S) : E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl`.

Rewrite using `[Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, h3]`. Use `show (β⁻¹ * x * β).val i j = _ * s + _`. Rewrite using `[← e, Matrix.sub_apply, sub_add_cancel]`. Establish `h4 : (N : kP PP) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk PP.asIdeal)]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hP`. Rewrite using `[h2, map_add, map_mul, map_natCast, h4, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `map_one _`. Conclude with `map_zero _`.
-/
theorem mem_St_red {N : ℕ} (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : ∀ i j, ((β⁻¹ * x * β).val - 1) i j ∈ multN F E N)
    (h' : ∀ i j, ((β⁻¹ * x⁻¹ * β).val - 1) i j ∈ multN F E N) :
    x ∈ St β ∧ ∀ PP : Pl E, (N : 𝓞 E) ∈ PP.asIdeal → redFn β PP x = 1 := by
  set S := Formalism.L2.Herm.intAf F E with hS
  let a : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, entry_int h i j⟩
  let b : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, entry_int h' i j⟩
  have ha : S.subtype.mapMatrix a = (β⁻¹ * x * β).val := rfl
  have hb : S.subtype.mapMatrix b = (β⁻¹ * x⁻¹ * β).val := rfl
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix (Fin n) (Fin n) S → _) := by
    intro u v huv
    ext i j
    exact congrFun (congrFun huv i) j
  let y : GL (Fin n) S :=
    ⟨a, b, hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group),
      hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group)⟩
  have hy : frGL β y = x := by
    have h1 : intGL F E n y = β⁻¹ * x * β := Units.ext rfl
    show β * intGL F E n y * β⁻¹ = x
    rw [h1]; group
  refine ⟨⟨y, hy⟩, fun PP hP => ?_⟩
  rw [← hy, redFn_frGL]
  apply Units.ext
  ext i j
  show resS F PP (a i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  obtain ⟨s, hs, e⟩ := h i j
  have h2 : a i j = (N : S) * ⟨s, hs⟩ + (1 : Matrix (Fin n) (Fin n) S) i j := by
    apply Subtype.ext
    have h3 : (((1 : Matrix (Fin n) (Fin n) S) i j : S) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, h3]
    show (β⁻¹ * x * β).val i j = _ * s + _
    rw [← e, Matrix.sub_apply, sub_add_cancel]
  have h4 : (N : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hP
  rw [h2, map_add, map_mul, map_natCast, h4, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

/- English proof (translation)
Use `⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_ne_zero_iff.2 fun PP _ h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP hP => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun PP : Pl E => Ideal.absNorm PP.asIdeal) hP`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`.
-/
theorem exists_nat_mem (T : Finset (Pl E)) : ∃ N : ℕ, N ≠ 0 ∧ ∀ PP ∈ T, (N : 𝓞 E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_ne_zero_iff.2 fun PP _ h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h),
    fun PP hP => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl E => Ideal.absNorm PP.asIdeal) hP
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

end Princ

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

/- English proof (translation)
Use `haveI := isTopGroup (D := D) (V := V)`. Take `⟨N, hN, hT⟩` from `exists_nat_mem T`. Apply the tactic sequence `have h1 := eventually_entry β N hN`. Establish `ht : Tendsto (fun g : GA D V => g⁻¹) (𝓝 1) (𝓝 1)` using `continuous_inv.tendsto' 1 1 inv_one`. Use `filter_upwards [h1, ht.eventually h1] with g hg hg'`.

Rewrite `hg'` using `[map_inv]`. Take `⟨h2, h3⟩` from `mem_St_red β (finE V g) hg hg'`. Conclude with `⟨h2, fun PP hP => h3 PP (hT PP hP)⟩`.
-/
theorem eventually_princ (β : GL (Fin V.rank) (EAf D)) (T : Finset (Pl D.host.E)) :
    ∀ᶠ g in 𝓝 (1 : GA D V), finE V g ∈ St β ∧ ∀ PP ∈ T, redFn β PP (finE V g) = 1 := by
  haveI := isTopGroup (D := D) (V := V)
  obtain ⟨N, hN, hT⟩ := exists_nat_mem T
  have h1 := eventually_entry β N hN
  have ht : Tendsto (fun g : GA D V => g⁻¹) (𝓝 1) (𝓝 1) := continuous_inv.tendsto' 1 1 inv_one
  filter_upwards [h1, ht.eventually h1] with g hg hg'
  rw [map_inv] at hg'
  obtain ⟨h2, h3⟩ := mem_St_red β (finE V g) hg hg'
  exact ⟨h2, fun PP hP => h3 PP (hT PP hP)⟩

/- English proof (translation)
Use `haveI := isTopGroup (D := D) (V := V)`. Set `S : Subgroup (GfC V)` to `{ carrier := {g | ρ g x = x} one_mem' := by show ρ 1 x = x; rw [map_one]; rfl mul_mem' := by`. Introduce `a b ha hb`. Use `show ρ (a * b) x = x`. Rewrite using `[map_mul, Module.End.mul_apply, show ρ b x = x from hb]`.

Conclude with `ha`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Use `show ρ a⁻¹ x = x`. Use `conv_lhs => rw [← show ρ a x = x from ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Use `rfl }`. Use `S.isOpen_of_mem_nhds (g := 1) ?_` and prove the remaining obligations. Establish `ht : Tendsto (fun g : GfC V => (g : GA D V)) (𝓝 1) (𝓝 1)` using `continuous_subtype_val.tendsto' 1 1 rfl`. Use `filter_upwards [ht.eventually (eventually_princ β L.Pg)] with k hk`.

Establish `hK : finE V k ∈ Kg D.sp.cm V.gram β L.Pg` using `⟨⟨finE_mem_UA _, hk.1⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hk.1, hk.2 PP hP⟩⟩`. Establish `hlev : (k : GA D V) ∈ levG V β (withP L P)` using `⟨k.2, Kg_le_lev (D := withP L P) (Finset.Subset.refl _) (by show L.Q ⊆ _; rw [hQ]; exact Finset.empty_subset _) hK⟩`. Establish `hr : rTup β (withP L P) (finE V k) = 1`. Use function extensionality and compare the values at `PP`. Use `show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1`.

Rewrite using `[hk.2 PP.1 PP.2]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`. Establish `hchi : levChi V β (withP L P) k = 1`. Establish `h1 : levFn β (withP L P) (finE V k) = 1`. Unfold `levFn`.

Rewrite using `[hr, blockDiagonalExtendByOnePrimeField_one, show (withP L P).s = 0 from hs, show (withP L P).Q = ∅ from hQ]`. Simplify using the standard rewrite rules. Unfold `levChi`. Rewrite using `[h1, Units.val_one]`. Establish `h0` using `GlobalTheory.CuspMult.mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, hlev, rfl⟩))`.

Rewrite `h0` using `[hchi, map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul, one_smul, map_one, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `h0`.
-/
theorem isOpen_stabiliser {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (EAf D)}
    {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G] {eG : G ≃* G0 L.Pg L.r} {c : G → ℂ}
    {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → Polynomial ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X} (hs : L.s = 0) (hQ : L.Q = ∅) {x : X}
    (hx : x ∈ GlobalTheory.CuspMult.killed ρ (GlobalTheory.CuspMult.eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  haveI := isTopGroup (D := D) (V := V)
  let S : Subgroup (GfC V) :=
    { carrier := {g | ρ g x = x}
      one_mem' := by show ρ 1 x = x; rw [map_one]; rfl
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, show ρ b x = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ x = x
        conv_lhs => rw [← show ρ a x = x from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have ht : Tendsto (fun g : GfC V => (g : GA D V)) (𝓝 1) (𝓝 1) := continuous_subtype_val.tendsto' 1 1 rfl
  filter_upwards [ht.eventually (eventually_princ β L.Pg)] with k hk
  have hK : finE V k ∈ Kg D.sp.cm V.gram β L.Pg :=
    ⟨⟨finE_mem_UA _, hk.1⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hk.1, hk.2 PP hP⟩⟩
  have hlev : (k : GA D V) ∈ levG V β (withP L P) :=
    ⟨k.2, Kg_le_lev (D := withP L P) (Finset.Subset.refl _) (by show L.Q ⊆ _; rw [hQ]; exact Finset.empty_subset _) hK⟩
  have hr : rTup β (withP L P) (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk.2 PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  have hchi : levChi V β (withP L P) k = 1 := by
    have h1 : levFn β (withP L P) (finE V k) = 1 := by
      unfold levFn
      rw [hr, blockDiagonalExtendByOnePrimeField_one, show (withP L P).s = 0 from hs, show (withP L P).Q = ∅ from hQ]
      simp
    unfold levChi
    rw [h1, Units.val_one]
  have h0 := GlobalTheory.CuspMult.mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, hlev, rfl⟩))
  rw [hchi, map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul, one_smul, map_one,
    LinearMap.sub_apply, sub_eq_zero] at h0
  exact h0

end Main

end GlobalTheory.FiniteRingMultiplication

end
