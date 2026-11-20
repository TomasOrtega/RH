import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.SymplHAddRight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsResolution

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rTensor_eq_self {F M N ι : Type} {P : ι → Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [∀ t, AddCommGroup (P t)] [∀ t, Module F (P t)]
    (f : ∀ t, M →ₗ[F] P t) (g : M →ₗ[F] M) (h : ∀ m, (∀ t, f t m = 0) → g m = m)
    (z : M ⊗[F] N) (hz : ∀ t, (f t).rTensor N z = 0) : g.rTensor N z = z := by
  classical
  let b := Module.Free.chooseBasis F N
  have key : ∀ {Q : Type} [AddCommGroup Q] [Module F Q] (u : M →ₗ[F] Q) (z : M ⊗[F] N) i,
      TensorProduct.equivFinsuppOfBasisRight b (u.rTensor N z) i = u (TensorProduct.equivFinsuppOfBasisRight b z i) := by
    intro Q _ _ u z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key]
  refine h _ fun t => ?_
  rw [← key, hz t]
  simp

open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

open Classical in

def idemOff : Af F :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_idemOff (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemOff F S) = if v ∈ S then 0 else 1 := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idemOff_int : idemOff F S ∈ intAf F := by
  intro v
  rw [evalV_idemOff]
  split_ifs
  · exact zero_mem _
  · exact one_mem _

variable {F} in
/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intAf_one : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

variable {F} in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Af_ext {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) : a = b :=
  RestrictedProduct.ext _ _ h

def liftOff : Af F →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)) ∘ₗ LinearMap.mulLeft F (idemOff F S)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftOff_apply (α : Af F) : liftOff F S α = pairA F 0 (idemOff F S * α) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem liftOff_snd {E : Type} [AddCommGroup E] [Module F E] (z : AF F ⊗[F] E)
    (h1 : (fstA F).toLinearMap.rTensor E z = 0)
    (h2 : ∀ v ∈ S, (evalV F v).toLinearMap.rTensor E ((sndA F).toLinearMap.rTensor E z) = 0) :
    (liftOff F S).rTensor E ((sndA F).toLinearMap.rTensor E z) = z := by
  classical
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  refine rTensor_eq_self (ι := Option S) (P := fun t => Ainf F × (∀ v, Fv F v))
    (fun t => t.elim ((LinearMap.inl _ _ _) ∘ₗ (fstA F).toLinearMap) fun v =>
      (LinearMap.inr _ _ _) ∘ₗ (LinearMap.single F (fun v => Fv F v) v.1) ∘ₗ
        (evalV F v.1).toLinearMap ∘ₗ (sndA F).toLinearMap) _ ?_ z ?_
  · intro m hm
    have a1 : fstA F m = 0 := congrArg Prod.fst (hm none)
    have a2 : ∀ v ∈ S, evalV F v (sndA F m) = 0 := by
      intro v hv
      have h3 : (Pi.single v (evalV F v (sndA F m)) : ∀ v, Fv F v) v = 0 :=
        congrFun (congrArg Prod.snd (hm (some ⟨v, hv⟩))) v
      rwa [Pi.single_eq_same] at h3
    refine Prod.ext a1.symm (Af_ext fun v => ?_)
    change evalV F v (idemOff F S * sndA F m) = evalV F v (sndA F m)
    rw [map_mul, evalV_idemOff]
    split_ifs with hv
    · rw [a2 v hv, mul_zero]
    · rw [one_mul]
  · rintro (_ | ⟨v, hv⟩)
    · simp only [Option.elim, LinearMap.rTensor_comp, LinearMap.comp_apply, h1, map_zero]
    · simp only [Option.elim, LinearMap.rTensor_comp, LinearMap.comp_apply, h2 v hv, map_zero]

def liftMul {E : Type} [Field E] [Algebra F E] (c : E) : Af F ⊗[F] E →+ AF F ⊗[F] E :=
  ((liftOff F S).rTensor E).toAddMonoidHom.comp (AddMonoidHom.mulLeft ((1 : Af F) ⊗ₜ[F] c))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftMul_apply {E : Type} [Field E] [Algebra F E] (c : E) (z : Af F ⊗[F] E) :
    liftMul F S c z = (liftOff F S).rTensor E (((1 : Af F) ⊗ₜ[F] c) * z) := rfl

end Adeles

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem liftOff_finPart (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (z : AE D) (h1 : infPart D z = 0)
    (h2 : ∀ v ∈ S, locPart D v z = 0) :
    (liftOff D.host.F S).rTensor D.host.E (finPart D z) = z :=
  liftOff_snd D.host.F S z h1 h2

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem selfDualLattice_frame_span_integral_coordinates (V : HSp D) {x y : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (hy : y ∈ L0c D V) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  obtain ⟨o, ho⟩ := (mem_hermitianStandardLattice_iff_pairing_integral V _).1 hy _ hx
  exact ⟨o, ho.trans (hT_coord V x y)⟩

def latRankOne (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA A B) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v ∈ S, evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D A, ∃ y ∈ L0c D B,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * star (x i) * y j)}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mapUp_mulVec (A B : HSp D) (x : WA A B) (y : Fin A.rank → AEf D) (j : Fin B.rank) :
    (mapUp A B x).mulVec y j = ∑ i, finPart D (x i j) * ∑ l, ((1 : Af D.host.F) ⊗ₜ[D.host.F] A.gram i l) * y l := by
  simp only [mapUp, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, gramFin,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc]
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Supply the required witnesses or components. Treat this case separately. A detailed English derivation is pending.
-/
theorem latRankOne_maps (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {x : WA A B}
    (hx : x ∈ latRankOne A B S) : x ∈ offS A B S ∧ ∀ y ∈ latFin A, (mapUp A B x).mulVec y ∈ latFinAA B := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hS, a, ha, x, hx, y, hy, rfl⟩ := hw
    refine ⟨⟨fun i j => ?_, fun v hv i j => ?_⟩, fun z hz => ?_⟩
    · exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F v α ⊗ₜ[D.host.F] _ = 0
      rw [hS v hv, TensorProduct.zero_tmul]
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, u, hu, rfl⟩ := hz
        obtain ⟨o, ho⟩ := selfDualLattice_frame_span_integral_coordinates A hx hu
        refine AddSubgroup.subset_closure ⟨α * β, intAf_mul hα hβ, (o • a) • y,
          ⟨o • a, Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, y, hy, rfl⟩, ?_⟩
        funext j
        rw [mapUp_mulVec]
        have : (((o • a) • y) j) = ∑ i, ∑ l, (a * star (x i) * y j) * (A.gram i l * u l) := by
          rw [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, show algebraMap _ _ o = (o : D.host.E) from rfl, ho]
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
        rw [this]
        simp only [TensorProduct.tmul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        change (α ⊗ₜ[D.host.F] (a * star (x i) * y j)) * _ = _
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
      | neg z _ h => rw [Matrix.mulVec_neg]; exact neg_mem h
  | zero => exact ⟨zero_mem _, fun y _ => by rw [mapUp_zero, Matrix.zero_mulVec]; exact zero_mem _⟩
  | add x x' _ _ h h' =>
    exact ⟨add_mem h.1 h'.1, fun y hy => by rw [mapUp_add, Matrix.add_mulVec]; exact add_mem (h.2 y hy) (h'.2 y hy)⟩
  | neg x _ h => exact ⟨neg_mem h.1, fun y hy => by rw [mapUp_neg, Matrix.neg_mulVec]; exact neg_mem (h.2 y hy)⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem rankOne_mem (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {q : Fin A.rank → D.host.E}
    (hq : q ∈ L0c D A) {z : Fin B.rank → AEf D} (hz : z ∈ latFinAA B) :
    (Matrix.of fun i j => liftMul D.host.F S (star (q i)) (z j) : WA A B) ∈ latRankOne A B S := by
  let Φ : (Fin B.rank → AEf D) →+ WA A B := AddMonoidHom.mk'
    (fun z => Matrix.of fun i j => liftMul D.host.F S (star (q i)) (z j))
    fun z z' => Matrix.ext fun i j => (liftMul D.host.F S (star (q i))).map_add (z j) (z' j)
  have hle : latFinAA B ≤ (latRankOne A B S).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, u, ⟨a, ha, y, hy, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨idemOff D.host.F S * β, intAf_mul (idemOff_int _ _) hβ, fun v hv => ?_,
      a, ha, q, hq, y, hy, ?_⟩
    · rw [map_mul, evalV_idemOff, if_pos hv, zero_mul]
    · ext i j
      change liftMul D.host.F S (star (q i)) (β ⊗ₜ[D.host.F] (a * y j)) = _
      simp only [liftMul_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        liftOff_apply]
      congr 1
      ring
  exact hle hz

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eq_sum_rankOne (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {x : WA A B}
    (hx : x ∈ offS A B S) {n : ℕ} {p q : Fin n → Fin A.rank → D.host.E}
    (hpq : ∀ i i', ∑ k, star (q k i) * ∑ l, A.gram i' l * p k l = if i = i' then 1 else 0) :
    x = ∑ k, (Matrix.of fun i j => liftMul D.host.F S (star (q k i))
      ((mapUp A B x).mulVec (fun l => (1 : Af D.host.F) ⊗ₜ[D.host.F] p k l) j) : WA A B) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.of_apply, liftMul_apply]
  refine (liftOff_finPart S (x i j) (hx.1 i j) fun v hv => hx.2 v hv i j).symm.trans
    (Eq.trans (congrArg _ ?_) (map_sum ((liftOff D.host.F S).rTensor D.host.E) _ _))
  simp only [mapUp_mulVec, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Finset.sum_comm]
  have : ∀ i', ∑ k, ∑ l, ((1 : Af D.host.F) ⊗ₜ[D.host.F] star (q k i)) *
      (finPart D (x i' j) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (A.gram i' l * p k l))) =
      if i = i' then finPart D (x i' j) else 0 := by
    intro i'
    have e : ∑ k, ∑ l, ((1 : Af D.host.F) ⊗ₜ[D.host.F] star (q k i)) *
        (finPart D (x i' j) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (A.gram i' l * p k l))) =
        finPart D (x i' j) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (∑ k, star (q k i) * ∑ l, A.gram i' l * p k l)) := by
      simp only [Finset.mul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, hpq]
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, mul_one]
    · rw [TensorProduct.tmul_zero, mul_zero]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem unramOutside_iff (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.Theta.UnramOutside D χ S ↔ GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S χ := Iff.rfl

def HalfIntegral (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ u ∈ homLat V W S, ∀ u' ∈ homLat V W S, ψ (symplH V W u u') = 1

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem theta0_isIntegral (D : D7) : IsIntegral ℤ (theta0 D) := by
  have h : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
    exact D.host.sqd_sq
  obtain ⟨-, -, -, hd, -⟩ := D.host.hyp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((4 * k + 2 : ℕ) : ℤ), ?_, ?_⟩
  · monicity!
  · rw [hk] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, theta0]
    rw [eq_intCast]
    push_cast at h ⊢
    linear_combination (1 / 4 : D.host.E) * h

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem smul_mem_latVWS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (o : 𝓞 D.host.E) {l : WA V W}
    (hl : l ∈ latVWS V W S) : incA D (o : D.host.E) • l ∈ latVWS V W S := by
  induction hl using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hS, a, ha, x, hx, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, hS, o • a,
      Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, x, hx, y, hy, ?_⟩
    ext i j
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def,
      show algebraMap _ _ o = (o : D.host.E) from rfl]
    congr 1
    split_ifs <;> ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hHom_smul_right (V W : HSp D) (c : AE D) (x y : WA V W) : hHom V W x (c • y) = c * hHom V W x y := by
  unfold hHom
  split_ifs
  all_goals
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem vacSignOf_eq (ψ : AddChar (AF D.host.F) ℂ) (θ : D.host.E) (V W : HSp D) (l : WA V W) :
    vacSignOf ψ θ V W l = ψ (symplH V W (incA D θ • l) l) := by
  rw [vacSignOf, symplH, sympl, hHom_smul_right, RingHom.map_mul, ← mul_assoc (incA D D.host.xi0),
    mul_comm (incA D D.host.xi0)]

variable {X : ThetaX D} {T : ThetaTied D X}

def FixesVacuumWhere (Wl : WeilTied D X T)
    (P : ∀ _ _ : HSp D, Finset (HeightOneSpectrum (𝓞 D.host.F)) → Prop) : Prop :=
  ∀ (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), P V W S →
      GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S (T.eChr χ) → GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S (T.eChr χ') →
      ∀ g ∈ KsphC V S, ∀ h ∈ KsphC W S, ∀ Φ : X.Sch V W, GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.IsVacuum Wl V W S Φ →
        Wl.om V W χ χ' (g, h) Φ = Φ

def halfA (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Rewrite the conclusion using the stated equalities.
-/
theorem symplH_eq (V W : HSp D) (u u' : WA V W) : symplH V W u u' = sympl V W (halfA D • u) u' := by
  rw [symplH, sympl, sympl, hHom_smul_right, mul_left_comm, halfA]
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = r
  rw [← Algebra.smul_def r, LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem half_mem_integers {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F := by
  have h2 : v.valuation F (2 : F) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v (algebraMap F (Fv F v) (1 / 2)) = v.valuation F (1 / 2) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [this, map_div₀, h2, map_one, div_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfIntegral_iff_of_selfDual (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hd : ∀ x ∈ offS V W S, x ∈ homLat V W S ↔ ∀ l ∈ homLat V W S, ψ (sympl V W x l) = 1) :
    HalfIntegral ψ V W S ↔ ∀ u ∈ homLat V W S, halfA D • u ∈ homLat V W S := by
  constructor
  · intro h u hu
    refine (hd _ ⟨fun i j => ?_, fun v hv i j => ?_⟩).2 fun l hl => ?_
    · rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hu.1.1 i j]; exact MulZeroClass.mul_zero _
    · rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hu.1.2 v hv i j]; exact MulZeroClass.mul_zero _
    · rw [← symplH_eq]; exact h u hu l hl
  · intro h u hu u' hu'
    rw [symplH_eq]
    exact (hd _ (h u hu).1).1 (h u hu) u' hu'

end GlobalTheory.WeilUnramifiedCompare

end
