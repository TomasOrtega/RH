import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KStabBridge

variable {D : D7}

/- English proof (translation)
The claim follows from `GlobalTheory.SplitIdem.evalV_singleV_same _ _ _`.
-/
theorem evalV_sv_same (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 :=
  GlobalTheory.SplitIdem.evalV_singleV_same _ _ _

/- English proof (translation)
The claim follows from `GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ h`.
-/
theorem evalV_sv_ne {v w : Pl D} (h : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 :=
  GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ h

/- English proof (translation)
Introduce `w` and use `by rw [map_mul]; exact mul_mem (ha w) (hb w)`.
-/
theorem intAf_mul {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := fun w => by rw [map_mul]; exact mul_mem (ha w) (hb w)

/- English proof (translation)
Introduce `w` and use `by by_cases h : w = v · subst h; rw [evalV_sv_same]; exact one_mem _ · rw [evalV_sv_ne h]; exact zero_mem _`.
-/
theorem sv_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases h : w = v
  · subst h; rw [evalV_sv_same]; exact one_mem _
  · rw [evalV_sv_ne h]; exact zero_mem _

/- English proof (translation)
Introduce `w` and use `by rw [map_sub, map_one] by_cases h : w = v · subst h; rw [evalV_sv_same, sub_self]; exact zero_mem _ · rw [evalV_sv_ne h, sub_zero]; exact one_mem _`.
-/
theorem one_sub_sv_int (v : Pl D) : 1 - singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  rw [map_sub, map_one]
  by_cases h : w = v
  · subst h; rw [evalV_sv_same, sub_self]; exact zero_mem _
  · rw [evalV_sv_ne h, sub_zero]; exact one_mem _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `evalV D.host.F v (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) = 1`. Rewrite using `[evalV_sv_same]`. Both sides reduce to the same expression.
-/
theorem compFin_e_same (v : Pl D) :
    compFin D v (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
  change evalV D.host.F v (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
  rw [evalV_sv_same]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `evalV D.host.F w (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Rewrite using `[evalV_sv_ne h]`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem compFin_e_ne {v w : Pl D} (h : w ≠ v) :
    compFin D w (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
  change evalV D.host.F w (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [evalV_sv_ne h]; exact TensorProduct.zero_tmul _ _

/- English proof (translation)
The claim follows from `TensorProduct.zero_tmul _ _`.
-/
theorem infPart_pair (x : Af D.host.F) (c : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] c) = 0 :=
  TensorProduct.zero_tmul _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_pair (x : Af D.host.F) (c : D.host.E) :
    finPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] c) = x ⊗ₜ[D.host.F] c := rfl

/- English proof (translation)
Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, (infPart D).map_zero, (finPart D).map_zero⟩`. Consider the case `tmul x c => exact ⟨pairA D.host.F 0 x ⊗ₜ c, infPart_pair x c, finPart_pair x c⟩`. Consider the case `add x y hx hy`. Take `⟨a, ha1, ha2⟩` from `hx`.

Take `⟨b, hb1, hb2⟩` from `hy`. Conclude with `⟨a + b, by rw [(infPart D).map_add, ha1, hb1, add_zero], by rw [(finPart D).map_add, ha2, hb2]⟩`.
-/
theorem exists_fin_lift (b : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ a : AE D, infPart D a = 0 ∧ finPart D a = b := by
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨0, (infPart D).map_zero, (finPart D).map_zero⟩
  | tmul x c => exact ⟨pairA D.host.F 0 x ⊗ₜ c, infPart_pair x c, finPart_pair x c⟩
  | add x y hx hy =>
    obtain ⟨a, ha1, ha2⟩ := hx
    obtain ⟨b, hb1, hb2⟩ := hy
    exact ⟨a + b, by rw [(infPart D).map_add, ha1, hb1, add_zero], by rw [(finPart D).map_add, ha2, hb2]⟩

end GlobalTheory.KStabBridge

namespace GlobalTheory.KStabBridge
variable {D : D7}

/- English proof (translation)
Unfold `FinPl.latV FinPl.latMul at hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, -, a, ha, x, hx, rfl⟩` from `hy`. Rewrite using `[Set.mem_singleton_iff.1 ha]`.

Use `AddSubgroup.subset_closure ⟨α, hα, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = α ⊗ₜ[D.host.F] x i`. Rewrite using `[one_mul]`. Both sides reduce to the same expression.

Consider the case `zero`. Use `zero_mem (latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `(finPart D).map_zero`. Consider the case `add y z _ _ hy hz`.

Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `(finPart D).map_add _ _`. Consider the case `neg y _ hy`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Conclude with `(finPart D).map_neg _`.
-/
theorem fin_mem_latHat (S : HSp D) (L : Lat S) (P : Pl D → Prop) {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) := by
  unfold FinPl.latV FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff.1 ha]
    refine AddSubgroup.subset_closure ⟨α, hα, x, hx, ?_⟩
    funext i
    show finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = α ⊗ₜ[D.host.F] x i
    rw [one_mul]; rfl
  | zero =>
    convert zero_mem (latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) using 1
    funext i; exact (finPart D).map_zero
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    funext i; exact (finPart D).map_add _ _
  | neg y _ hy =>
    convert neg_mem hy using 1
    funext i; exact (finPart D).map_neg _

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨t * a, intAf_mul ht ha, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `add_mem hy hz`.

Consider the case `neg y _ hy => rw [smul_neg]`. Conclude with `neg_mem hy`.
-/
theorem latHat_smul {n : ℕ} (Ls : Set (Fin n → D.host.E)) {t : Af D.host.F} (ht : t ∈ intAf D.host.F)
    {y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ latHat D.host.F D.host.E Ls) :
    (t ⊗ₜ[D.host.F] (1 : D.host.E)) • y ∈ latHat D.host.F D.host.E Ls := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨t * a, intAf_mul ht ha, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Use `⟨fun i => pairA D.host.F 0 (singleV D.host.F v 1 * a) ⊗ₜ[D.host.F] (1 * x i), AddSubgroup.subset_closure ⟨_, intAf_mul (sv_int v) ha, fun w hw => ?_, 1, rfl, x, hx, rfl⟩, fun i => infPart_pair _ _, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, evalV_sv_ne hw, zero_mul]`.

Rewrite using `[finPart_pair, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero`. Use `⟨0, zero_mem (latV S L (· = v)), fun i => (infPart D).map_zero, fun i => ?_⟩` and prove the remaining obligations. Use `show finPart D 0 = (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * 0`. Rewrite using `[mul_zero]`.

Conclude with `(finPart D).map_zero`. Consider the case `add z z' _ _ h h'`. Take `⟨y, hy, h1, h2⟩` from `h`. Take `⟨y', hy', h1', h2'⟩` from `h'`. Conclude with `⟨y + y', add_mem hy hy', fun i => by rw [Pi.add_apply, (infPart D).map_add, h1, h1', add_zero], fun i => by rw [Pi.add_apply, (finPart D).map_add, h2, h2', Pi.add_apply, mul_add]⟩`.

Consider the case `neg z _ h`. Take `⟨y, hy, h1, h2⟩` from `h`. Use `⟨-y, neg_mem hy, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `show infPart D (-(y i)) = 0`. Rewrite using `[(infPart D).map_neg, h1, neg_zero]`.

Use `show finPart D (-(y i)) = (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * -(z i)`. Rewrite using `[(finPart D).map_neg, h2, mul_neg]`.
-/
theorem exists_lift_latV (S : HSp D) (L : Lat S) (v : Pl D) {z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    ∃ y ∈ latV S L (· = v), (∀ i, infPart D (y i) = 0) ∧
      ∀ i, finPart D (y i) = (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * z i := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine ⟨fun i => pairA D.host.F 0 (singleV D.host.F v 1 * a) ⊗ₜ[D.host.F] (1 * x i),
      AddSubgroup.subset_closure ⟨_, intAf_mul (sv_int v) ha, fun w hw => ?_, 1, rfl, x, hx, rfl⟩,
      fun i => infPart_pair _ _, fun i => ?_⟩
    · rw [map_mul, evalV_sv_ne hw, zero_mul]
    · rw [finPart_pair, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    refine ⟨0, zero_mem (latV S L (· = v)), fun i => (infPart D).map_zero, fun i => ?_⟩
    show finPart D 0 = (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * 0
    rw [mul_zero]; exact (finPart D).map_zero
  | add z z' _ _ h h' =>
    obtain ⟨y, hy, h1, h2⟩ := h
    obtain ⟨y', hy', h1', h2'⟩ := h'
    exact ⟨y + y', add_mem hy hy', fun i => by rw [Pi.add_apply, (infPart D).map_add, h1, h1', add_zero],
      fun i => by rw [Pi.add_apply, (finPart D).map_add, h2, h2', Pi.add_apply, mul_add]⟩
  | neg z _ h =>
    obtain ⟨y, hy, h1, h2⟩ := h
    refine ⟨-y, neg_mem hy, fun i => ?_, fun i => ?_⟩
    · show infPart D (-(y i)) = 0
      rw [(infPart D).map_neg, h1, neg_zero]
    · show finPart D (-(y i)) = (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * -(z i)
      rw [(finPart D).map_neg, h2, mul_neg]

end GlobalTheory.KStabBridge

namespace GlobalTheory.KStabBridge
variable {D : D7}

/- English proof (translation)
Use `GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `compFin D w _ = compFin D w _`. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[compFin_e_same, one_mul]`. Rewrite using `[h w hw, mul_zero]`.
-/
theorem e_mul_of_supp (v : Pl D) (X : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, w ≠ v → compFin D w X = 0) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * X = X := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  change compFin D w _ = compFin D w _
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [compFin_e_same, one_mul]
  · rw [h w hw, mul_zero]

/- English proof (translation)
The claim follows from `e_mul_of_supp v _ fun _ hw => compFin_e_ne hw`.
-/
theorem e_idem (v : Pl D) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) =
      singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E) :=
  e_mul_of_supp v _ fun _ hw => compFin_e_ne hw

/- English proof (translation)
Rewrite using `[TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]`.
-/
theorem one_sub_e (v : Pl D) :
    1 - singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E) = (1 - singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]

/- English proof (translation)
Establish `h0 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S)) κ = 1` using `MonoidHom.mem_ker.1 hg`. Establish `h1'` using `congrArg (fun g : GL (Fin S.rank) (AE D ⧸ idAt D P) => g.val i j) h0`. Establish `h1 : Ideal.Quotient.mk (idAt D P) (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idAt D P)) i j` using `h1'`. Rewrite using `[← Ideal.Quotient.mk_eq_mk_iff_sub_mem, h1, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem entries_mem {S : HSp D} {P : Pl D → Prop} {κ : GA D S} (hg : κ ∈ grpAt S P) (i j : Fin S.rank) :
    mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D P := by
  have h0 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S)) κ = 1 :=
    MonoidHom.mem_ker.1 hg
  have h1' := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ idAt D P) => g.val i j) h0
  have h1 : Ideal.Quotient.mk (idAt D P) (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idAt D P)) i j :=
    h1'
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.KStabBridge

namespace GlobalTheory.KStabBridge
open scoped Matrix
variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Generalize the expression as in `he : singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E) = e at hN hcore`. Establish `hee : e * e = e` using `by rw [← he]; exact e_idem v`. Establish `hN' : ∀ i j, (1 - e) * M i j = (1 - e) * (1 : Matrix (Fin n) (Fin n) _) i j`. Introduce `i j`. Use `hN i j` as an intermediate fact.

Rewrite using `[← sub_eq_zero, ← mul_sub]`. Take the linear combination `(-1 : Af D.host.F ⊗[D.host.F] D.host.E) * this`. Establish `hsplit : ∀ z, z ∈ latHat D.host.F D.host.E Ls ↔ e • z ∈ latHat D.host.F D.host.E Ls ∧ (1 - e) • z ∈ latHat D.host.F D.host.E Ls`. Introduce `z`. Use `⟨fun hz => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩` and prove the remaining obligations.

Rewrite using `[← he]`. Conclude with `latHat_smul _ (sv_int v) hz`. Rewrite using `[← he, one_sub_e]`. Conclude with `latHat_smul _ (one_sub_sv_int v) hz`. Use `add_mem h1 h2` as an intermediate fact.

Rewrite `this` using `[← add_smul, add_sub_cancel, one_smul]`. Then use the resulting hypothesis. Establish `hcomm : ∀ z, M *ᵥ (e • z) = e • (M *ᵥ z)` using `fun z => by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _`.

Establish `hoff : ∀ z, (1 - e) • (M *ᵥ z) = (1 - e) • z`. Introduce `z`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, ← mul_assoc, hN']`. Simplify using `[Matrix.one_apply]`.

Establish `hey : e • e • y = e • y` using `by rw [smul_smul, hee]`. Establish `h2 : M *ᵥ y ∈ latHat D.host.F D.host.E Ls ↔ M *ᵥ (e • y) ∈ latHat D.host.F D.host.E Ls ∧ (1 - e) • y ∈ latHat D.host.F D.host.E Ls`. Establish `h` using `hsplit (M *ᵥ y)`. Rewrite `h` using `[hoff y, ← hcomm y]`. Then use the resulting hypothesis. Establish `h3` using `hcore (e • y) hey`.

Conclude with `(hsplit y).trans ((and_congr_left' h3).trans h2.symm)`.
-/
theorem keeps_of_core (v : Pl D) {n : ℕ} (Ls : Set (Fin n → D.host.E))
    (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hN : ∀ i j, (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (M i j - (1 : Matrix (Fin n) (Fin n) _) i j) =
      M i j - (1 : Matrix (Fin n) (Fin n) _) i j)
    (hcore : ∀ z, (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) • z = z →
      (z ∈ latHat D.host.F D.host.E Ls ↔ M *ᵥ z ∈ latHat D.host.F D.host.E Ls))
    (y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E Ls ↔ M *ᵥ y ∈ latHat D.host.F D.host.E Ls := by
  generalize he : singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E) = e at hN hcore
  have hee : e * e = e := by rw [← he]; exact e_idem v
  have hN' : ∀ i j, (1 - e) * M i j = (1 - e) * (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro i j
    have := hN i j
    rw [← sub_eq_zero, ← mul_sub]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * this
  have hsplit : ∀ z, z ∈ latHat D.host.F D.host.E Ls ↔
      e • z ∈ latHat D.host.F D.host.E Ls ∧ (1 - e) • z ∈ latHat D.host.F D.host.E Ls := by
    intro z
    refine ⟨fun hz => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
    · rw [← he]; exact latHat_smul _ (sv_int v) hz
    · rw [← he, one_sub_e]; exact latHat_smul _ (one_sub_sv_int v) hz
    · have := add_mem h1 h2
      rwa [← add_smul, add_sub_cancel, one_smul] at this
  have hcomm : ∀ z, M *ᵥ (e • z) = e • (M *ᵥ z) := fun z => by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
  have hoff : ∀ z, (1 - e) • (M *ᵥ z) = (1 - e) • z := by
    intro z
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, ← mul_assoc, hN']
    simp [Matrix.one_apply]
  have hey : e • e • y = e • y := by rw [smul_smul, hee]
  have h2 : M *ᵥ y ∈ latHat D.host.F D.host.E Ls ↔
      M *ᵥ (e • y) ∈ latHat D.host.F D.host.E Ls ∧ (1 - e) • y ∈ latHat D.host.F D.host.E Ls := by
    have h := hsplit (M *ᵥ y)
    rwa [hoff y, ← hcomm y] at h
  have h3 := hcore (e • y) hey
  exact (hsplit y).trans ((and_congr_left' h3).trans h2.symm)

end GlobalTheory.KStabBridge

namespace GlobalTheory.KStabBridge
open scoped Matrix
variable {D : D7}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hzL`. Take `⟨y', hy', h1', h2'⟩` from `exists_lift_latV S L v hzL`. Establish `: y' = y` using `funext fun i => GlobalTheory.VacStabFixed.parts_ext (by rw [h1', h1]) (by rw [h2', h2]; exact congrFun hz i)`. Rewrite using `[← this]` and apply the resulting hypothesis.

Introduce `hy`. Use `fin_mem_latHat S L _ hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `(h2 i).symm`.
-/
theorem mem_latHat_iff_lift (S : HSp D) (L : Lat S) (v : Pl D) (z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) • z = z) (y : Fin S.rank → AE D)
    (h1 : ∀ i, infPart D (y i) = 0) (h2 : ∀ i, finPart D (y i) = z i) :
    z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) ↔ y ∈ latV S L (· = v) := by
  constructor
  · intro hzL
    obtain ⟨y', hy', h1', h2'⟩ := exists_lift_latV S L v hzL
    have : y' = y := funext fun i => GlobalTheory.VacStabFixed.parts_ext (by rw [h1', h1])
      (by rw [h2', h2]; exact congrFun hz i)
    rwa [← this]
  · intro hy
    have := fin_mem_latHat S L _ hy
    convert this using 1
    funext i; exact (h2 i).symm

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨hg, hmv⟩` from `hκ`. Establish `hI` using `entries_mem hg`. Establish `hone : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (i j : Fin S.rank), f ((1 : Matrix (Fin S.rank) (Fin S.rank) R) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) R') i j` using `fun f i j => congrFun (congrFun (Matrix.map_one _ (map_zero f) (map_one f)) i) j`. Establish `hinf : ∀ i j, infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j` using `fun i j => by`. Establish `h` using `(Ideal.mem_inf.1 (hI i j)).1`.

Rewrite `h` using `[RingHom.mem_ker, (infPart D).map_sub, sub_eq_zero, hone]`. Conclude with `h`. Establish `hcomp : ∀ w, w ≠ v → ∀ i j, compAt D w (mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0` using `fun w hw i j => by`. Establish `h` using `(Ideal.mem_iInf.1 (Ideal.mem_inf.1 (hI i j)).2) ⟨w, hw⟩`. Rewrite `h` using `[RingHom.mem_ker]`. Then use the resulting hypothesis.

Establish `hfin : ∀ i j, finPart D (mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (mt S κ).map (finPart D) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j` using `fun i j => by`. Rewrite using `[(finPart D).map_sub, hone]`. Both sides reduce to the same expression. Use `⟨?_, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Conclude with `hinf i j`. Use extensionality with `i j`. Establish `h` using `hcomp w hw i j`. Express the relevant statement in the definitionally equal form `compFin D w (finPart D _) = 0 at h`. Rewrite `h` using `[hfin, (compFin D w).map_sub, sub_eq_zero, hone]`.

Conclude with `h`. Use `keeps_of_core v _ _ (fun i j => by` and prove the remaining obligations. Rewrite using `[← hfin]`. Conclude with `e_mul_of_supp v _ fun w hw => hcomp w hw i j) ?_`. Introduce `z hz`.

Use `choose lift hl1 hl2 using exists_fin_lift (D := D)`. Set `y : Fin S.rank → AE D` to `fun i => lift (z i)`. Establish `hsupp : ∀ i, y i ∈ idAt D (· = v)` using `fun i => Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (hl1 _), Ideal.mem_iInf.2 fun w => RingHom.mem_ker.2 (by`. Express the relevant statement in the definitionally equal form `compFin D w (finPart D (lift (z i))) = 0`. Rewrite using `[hl2, ← congrFun hz i]`.

Express the relevant statement in the definitionally equal form `compFin D w ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * z i) = 0`. Rewrite using `[(compFin D w).map_mul, compFin_e_ne w.2, zero_mul])⟩`. Establish `hMz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) • ((mt S κ).map (finPart D) *ᵥ z) = (mt S κ).map (finPart D) *ᵥ z` using `by conv_rhs => rw [← hz]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `k1 : ∀ i, infPart D ((mt S κ *ᵥ y) i) = 0` using `fun i => by`. Rewrite using `[RingHom.map_mulVec]`. Establish `: (infPart D ∘ y) = 0` using `funext fun j => hl1 _`. Rewrite using `[this, Matrix.mulVec_zero]`.

Both sides reduce to the same expression. Establish `k2 : ∀ i, finPart D ((mt S κ *ᵥ y) i) = ((mt S κ).map (finPart D) *ᵥ z) i` using `fun i => by`. Rewrite using `[RingHom.map_mulVec]`. Establish `: (finPart D ∘ y) = z` using `funext fun j => hl2 _`. Rewrite using `[this]`.

Conclude with `(mem_latHat_iff_lift S L v z hz y (fun i => hl1 _) (fun i => hl2 _)).trans ((hmv y hsupp).trans (mem_latHat_iff_lift S L v _ hMz _ k1 k2).symm)`.
-/
theorem inStabAt_of_inK (D : D7) (S : HSp D) (L : Lat S) (v : Pl D) (κ : GA D S) (_hL : IsSelfDualC S L)
    (hκ : InK S L (· = v) κ) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.InStabAt S L v κ := by
  obtain ⟨hg, hmv⟩ := hκ
  have hI := entries_mem hg
  have hone : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (i j : Fin S.rank),
      f ((1 : Matrix (Fin S.rank) (Fin S.rank) R) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) R') i j :=
    fun f i j => congrFun (congrFun (Matrix.map_one _ (map_zero f) (map_one f)) i) j
  have hinf : ∀ i j, infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j := fun i j => by
    have h := (Ideal.mem_inf.1 (hI i j)).1
    rw [RingHom.mem_ker, (infPart D).map_sub, sub_eq_zero, hone] at h
    exact h
  have hcomp : ∀ w, w ≠ v → ∀ i j,
      compAt D w (mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := fun w hw i j => by
    have h := (Ideal.mem_iInf.1 (Ideal.mem_inf.1 (hI i j)).2) ⟨w, hw⟩
    rwa [RingHom.mem_ker] at h
  have hfin : ∀ i j, finPart D (mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (mt S κ).map (finPart D) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) _) i j := fun i j => by
    rw [(finPart D).map_sub, hone]; rfl
  refine ⟨?_, fun w hw => ?_, ?_⟩
  · ext i j
    exact hinf i j
  · ext i j
    have h := hcomp w hw i j
    change compFin D w (finPart D _) = 0 at h
    rw [hfin, (compFin D w).map_sub, sub_eq_zero, hone] at h
    exact h
  refine keeps_of_core v _ _ (fun i j => by
    rw [← hfin]; exact e_mul_of_supp v _ fun w hw => hcomp w hw i j) ?_
  intro z hz
  choose lift hl1 hl2 using exists_fin_lift (D := D)
  let y : Fin S.rank → AE D := fun i => lift (z i)
  have hsupp : ∀ i, y i ∈ idAt D (· = v) := fun i => Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (hl1 _),
    Ideal.mem_iInf.2 fun w => RingHom.mem_ker.2 (by
      change compFin D w (finPart D (lift (z i))) = 0
      rw [hl2, ← congrFun hz i]
      change compFin D w ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * z i) = 0
      rw [(compFin D w).map_mul, compFin_e_ne w.2, zero_mul])⟩
  have hMz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) • ((mt S κ).map (finPart D) *ᵥ z) =
      (mt S κ).map (finPart D) *ᵥ z := by
    conv_rhs => rw [← hz]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have k1 : ∀ i, infPart D ((mt S κ *ᵥ y) i) = 0 := fun i => by
    rw [RingHom.map_mulVec]
    have : (infPart D ∘ y) = 0 := funext fun j => hl1 _
    rw [this, Matrix.mulVec_zero]; rfl
  have k2 : ∀ i, finPart D ((mt S κ *ᵥ y) i) = ((mt S κ).map (finPart D) *ᵥ z) i := fun i => by
    rw [RingHom.map_mulVec]
    have : (finPart D ∘ y) = z := funext fun j => hl2 _
    rw [this]
  exact (mem_latHat_iff_lift S L v z hz y (fun i => hl1 _) (fun i => hl2 _)).trans
    ((hmv y hsupp).trans (mem_latHat_iff_lift S L v _ hMz _ k1 k2).symm)

end GlobalTheory.KStabBridge
