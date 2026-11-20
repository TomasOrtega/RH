import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `[Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`.
-/
theorem repr_map {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing B]
    [Algebra F B] (b : Module.Basis ι F E) (f : A →ₐ[F] B) (x : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp [map_add, hx, hy]

open Classical in

def ePl (D : D7) (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun v => if P v then 1 else 0)
    (Filter.Eventually.of_forall fun v => by
      split_ifs
      · exact one_mem _
      · exact zero_mem _)

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_ePl (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (ePl D P) = if P v then 1 else 0 := rfl

def idem (D : D7) (P : Pl D → Prop) : AE D := pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)

/- English proof (translation)
Use `set b := Module.finBasis D.host.F D.host.E`. Apply `(Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h1` using `repr_map b (fstA D.host.F) x i`. Establish `h2 : ∀ w, evalV D.host.F w (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).repr x i)) = 0`.

Introduce `w`. Use `repr_map b (evalV D.host.F w) (finPart D x) i` as an intermediate fact. Establish `hf : finPart D x = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) x` using `rfl`. Rewrite `this` using `[hf, repr_map b (sndA D.host.F) x i]`. Rewrite using `[← this, ← hf]`.

Establish `hx : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (finPart D x) = 0` using `hw w`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Establish `h0' : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) x = 0` using `h0`. Rewrite `h1` using `[h0']`.

Rewrite `h1` using `[LinearEquiv.map_zero, Finsupp.zero_apply]`. Rewrite using `[LinearEquiv.map_zero, Finsupp.zero_apply]`. Use `Prod.ext h1.symm ?_` and prove the remaining obligations. Conclude with `RestrictedProduct.ext _ _ fun w => h2 w`.
-/
theorem eq_zero_of_comp (x : AE D) (h0 : infPart D x = 0) (hw : ∀ w, compAt D w x = 0) : x = 0 := by
  set b := Module.finBasis D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  ext i
  have h1 := repr_map b (fstA D.host.F) x i
  have h2 : ∀ w, evalV D.host.F w (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).repr x i)) = 0 := by
    intro w
    have := repr_map b (evalV D.host.F w) (finPart D x) i
    have hf : finPart D x = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) x := rfl
    rw [hf, repr_map b (sndA D.host.F) x i] at this
    rw [← this, ← hf]
    have hx : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (finPart D x) = 0 := hw w
    rw [hx]; simp
  have h0' : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) x = 0 := h0
  rw [h0'] at h1
  rw [LinearEquiv.map_zero, Finsupp.zero_apply] at h1
  rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  refine Prod.ext h1.symm ?_
  exact RestrictedProduct.ext _ _ fun w => h2 w

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Introduce `v`. Rewrite using `[evalV_ePl]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem ePl_int (P : Pl D → Prop) : ePl D P ∈ intAf D.host.F := by
  classical
  intro v
  rw [evalV_ePl]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Use `show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Use `show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e = 0`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem infPart_pair (α : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e = 0
  exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Use `show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem finPart_pair (α : Af D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Unfold `GlobalTheory.FinPl.compAt`. Rewrite using `[RingHom.comp_apply, finPart_pair]`. Use `show Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (α ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem compAt_pair (w : Pl D) (α : Af D.host.F) (e : D.host.E) :
    compAt D w (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = evalV D.host.F w α ⊗ₜ[D.host.F] e := by
  unfold GlobalTheory.FinPl.compAt
  rw [RingHom.comp_apply, finPart_pair]
  show Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (α ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

open Classical in
/- English proof (translation)
Unfold `idem`. Rewrite using `[compAt_pair, evalV_ePl]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem compAt_idem (P : Pl D → Prop) (w : Pl D) : compAt D w (idem D P) = if P w then 1 else 0 := by
  classical
  unfold idem
  rw [compAt_pair, evalV_ePl]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Unfold `idAt`. Use `Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_pair _ _), ?_⟩` and prove the remaining obligations. Use `Submodule.mem_iInf _ |>.2 fun w => RingHom.mem_ker.2 ?_` and prove the remaining obligations. Rewrite using `[compAt_idem, if_neg w.2]`.
-/
theorem idem_mem_idAt (P : Pl D → Prop) : idem D P ∈ idAt D P := by
  unfold idAt
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_pair _ _), ?_⟩
  refine Submodule.mem_iInf _ |>.2 fun w => RingHom.mem_ker.2 ?_
  rw [compAt_idem, if_neg w.2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Unfold `idAt at ha`. Take `⟨ha0, haw⟩` from `Ideal.mem_inf.1 ha`. Establish `haw'` using `Submodule.mem_iInf _ |>.1 haw`.

Establish `h : (1 - idem D P) * a = 0`. Apply `eq_zero_of_comp` to reduce the goal to its premises. Rewrite using `[map_mul, RingHom.mem_ker.1 ha0, mul_zero]`. Introduce `w`. Rewrite using `[map_mul]`.

Distinguish the cases in `hw : P w`. Rewrite using `[map_sub, map_one, compAt_idem, if_pos hw, sub_self, zero_mul]`. Rewrite using `[RingHom.mem_ker.1 (haw' ⟨w, hw⟩), mul_zero]`. Rewrite `h` using `[sub_mul, one_mul, sub_eq_zero]`. Conclude with `h.symm`.

Introduce `h`. Rewrite using `[← h]`. Conclude with `Ideal.mul_mem_right _ _ (idem_mem_idAt P)`.
-/
theorem mem_idAt_iff (P : Pl D → Prop) (a : AE D) : a ∈ idAt D P ↔ idem D P * a = a := by
  constructor
  · intro ha
    unfold idAt at ha
    obtain ⟨ha0, haw⟩ := Ideal.mem_inf.1 ha
    have haw' := Submodule.mem_iInf _ |>.1 haw
    have h : (1 - idem D P) * a = 0 := by
      apply eq_zero_of_comp
      · rw [map_mul, RingHom.mem_ker.1 ha0, mul_zero]
      · intro w
        rw [map_mul]
        by_cases hw : P w
        · rw [map_sub, map_one, compAt_idem, if_pos hw, sub_self, zero_mul]
        · rw [RingHom.mem_ker.1 (haw' ⟨w, hw⟩), mul_zero]
    rw [sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  · intro h
    rw [← h]
    exact Ideal.mul_mem_right _ _ (idem_mem_idAt P)

/- English proof (translation)
Unfold `idOff`. Rewrite using `[Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Apply `eq_zero_of_comp` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Unfold `idem`. Rewrite using `[infPart_pair, zero_mul]`. Introduce `w`. Rewrite using `[map_mul]`.

Distinguish the cases in `hw : P w`. Rewrite using `[RingHom.mem_ker.1 (ha ⟨w, hw⟩), mul_zero]`. Rewrite using `[compAt_idem, if_neg hw, zero_mul]`. Introduce `h w`. Apply `RingHom.mem_ker.2` to reduce the goal to its premises.

Use `congrArg (compAt D w.1) h` as an intermediate fact. Rewrite `this` using `[map_mul, compAt_idem, if_pos w.2, one_mul, map_zero]`. Conclude with `this`.
-/
theorem mem_idOff_iff (P : Pl D → Prop) (a : AE D) : a ∈ idOff D P ↔ idem D P * a = 0 := by
  unfold idOff
  rw [Submodule.mem_iInf]
  constructor
  · intro ha
    apply eq_zero_of_comp
    · rw [map_mul]; unfold idem; rw [infPart_pair, zero_mul]
    · intro w
      rw [map_mul]
      by_cases hw : P w
      · rw [RingHom.mem_ker.1 (ha ⟨w, hw⟩), mul_zero]
      · rw [compAt_idem, if_neg hw, zero_mul]
  · intro h w
    apply RingHom.mem_ker.2
    have := congrArg (compAt D w.1) h
    rw [map_mul, compAt_idem, if_pos w.2, one_mul, map_zero] at this
    exact this

/- English proof (translation)
Use `⟨idem_mem_idAt P, ?_⟩` and prove the remaining obligations. Unfold `idem`. Rewrite using `[finPart_pair]`. Conclude with `AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, 1, by simp⟩`.
-/
theorem idem_mem_intAt (P : Pl D → Prop) : idem D P ∈ intAt D P := by
  refine ⟨idem_mem_idAt P, ?_⟩
  unfold idem
  rw [finPart_pair]
  exact AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, 1, by simp⟩

/- English proof (translation)
Use `(mem_idAt_iff P (idem D P)).1 (idem_mem_idAt P)` as an intermediate fact. Conclude with `this`.
-/
theorem idem_mul_self (P : Pl D → Prop) : idem D P * idem D P = idem D P := by
  have := (mem_idAt_iff P (idem D P)).1 (idem_mem_idAt P)
  exact this

/- English proof (translation)
Unfold `idem`. Use `show Algebra.TensorProduct.map (AlgHom.id _ _) _ (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression.
-/
theorem cA_idem (P : Pl D → Prop) : cA D (idem D P) = idem D P := by
  unfold idem
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨idem D P, idem_mul_self P, cA_idem P, idem_mem_intAt P, mem_idAt_iff P, mem_idOff_iff P⟩`.
-/
theorem part_idem (P : Pl D → Prop) : ∃ ε : AE D, ε * ε = ε ∧ cA D ε = ε ∧ ε ∈ intAt D P ∧
    (∀ a, a ∈ idAt D P ↔ ε * a = a) ∧ (∀ a, a ∈ idOff D P ↔ ε * a = 0) :=
  ⟨idem D P, idem_mul_self P, cA_idem P, idem_mem_intAt P, mem_idAt_iff P, mem_idOff_iff P⟩

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

section Mix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def mix (e : A) (X Y : Matrix n n A) : Matrix n n A := e • X + (1 - e) • Y

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Simplify using `only [mix, add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]`.
-/
theorem mix_mul {e : A} (he : e * e = e) (X Y X' Y' : Matrix n n A) :
    mix e X Y * mix e X' Y' = mix e (X * X') (Y * Y') := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[mix, ← add_smul, add_sub_cancel, one_smul]`.
-/
theorem mix_self (e : A) (X : Matrix n n A) : mix e X X = X := by
  rw [mix, ← add_smul, add_sub_cancel, one_smul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, mix, hσ]`.
-/
theorem cT_mix (σ : A →+* A) {e : A} (hσ : σ e = e) (X Y : Matrix n n A) :
    Formalism.UG.cT σ (mix e X Y) = mix e (Formalism.UG.cT σ X) (Formalism.UG.cT σ Y) := by
  ext i j
  simp [Formalism.UG.cT, mix, hσ]

def mixGL {e : A} (he : e * e = e) (g h : GL n A) : GL n A where
  val := mix e g h
  inv := mix e (↑g⁻¹ : Matrix n n A) (↑h⁻¹ : Matrix n n A)
  val_inv := by rw [mix_mul he]; simp [mix_self]
  inv_val := by rw [mix_mul he]; simp [mix_self]

/- English proof (translation)
Establish `hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * g = J` using `hg`. Establish `hh' : Formalism.UG.cT σ (h : Matrix n n A) * J * h = J` using `hh`. Use `show Formalism.UG.cT σ (mix e g h) * J * mix e g h = J`. Rewrite using `[cT_mix σ hσ]`. Use `conv_lhs => rw [← mix_self e J]`.

Rewrite using `[mix_mul he, mix_mul he, hg', hh', mix_self]`.
-/
theorem mixGL_mem (σ : A →+* A) (J : Matrix n n A) {e : A} (he : e * e = e) (hσ : σ e = e) {g h : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J) (hh : h ∈ Formalism.UG.UJ σ J) : mixGL he g h ∈ Formalism.UG.UJ σ J := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * g = J := hg
  have hh' : Formalism.UG.cT σ (h : Matrix n n A) * J * h = J := hh
  show Formalism.UG.cT σ (mix e g h) * J * mix e g h = J
  rw [cT_mix σ hσ]
  conv_lhs => rw [← mix_self e J]
  rw [mix_mul he, mix_mul he, hg', hh', mix_self]

end Mix

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Unfold `congGrp`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]`. Use `show (mt V x).map (Ideal.Quotient.mk I) = 1 ↔ _`. Rewrite using `[← Matrix.map_one (Ideal.Quotient.mk I) (map_zero _) (map_one _), ← Matrix.ext_iff]`. Simplify using `only [Matrix.map_apply, Ideal.Quotient.eq]`.
-/
theorem mem_congGrp {V : HSp D} (I : Ideal (AE D)) (x : GA D V) :
    x ∈ congGrp V I ↔ ∀ i j, mt V x i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  show (mt V x).map (Ideal.Quotient.mk I) = 1 ↔ _
  rw [← Matrix.map_one (Ideal.Quotient.mk I) (map_zero _) (map_one _), ← Matrix.ext_iff]
  simp only [Matrix.map_apply, Ideal.Quotient.eq]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem mt_inj {V : HSp D} {a b : GA D V} (h : mt V a = mt V b) : a = b := Subtype.ext (Units.ext h)

def mixGA (P : Pl D → Prop) {V : HSp D} (g h : GA D V) : GA D V :=
  ⟨mixGL (idem_mul_self P) g.1 h.1, by exact mixGL_mem _ _ (idem_mul_self P) (cA_idem P) g.2 h.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mixGA (P : Pl D → Prop) {V : HSp D} (g h : GA D V) :
    mt V (mixGA P g h) = mix (idem D P) (mt V g) (mt V h) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_one (V : HSp D) : mt V 1 = 1 := rfl

/- English proof (translation)
Unfold `grpAt`. Rewrite using `[mem_congGrp, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[mem_idAt_iff]`. Simplify using `only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take the linear combination `h`. Introduce `h`. Take the linear combination `h`.
-/
theorem mem_grpAt_iff (P : Pl D → Prop) {V : HSp D} (x : GA D V) :
    x ∈ grpAt V P ↔ mix (idem D P) (mt V x) 1 = mt V x := by
  unfold grpAt
  rw [mem_congGrp, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [mem_idAt_iff]
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/- English proof (translation)
Unfold `grpOff`. Rewrite using `[mem_congGrp, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[mem_idOff_iff]`. Simplify using `only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take the linear combination `(-1 : AE D) * h`. Introduce `h`. Take the linear combination `(-1 : AE D) * h`.
-/
theorem mem_grpOff_iff (P : Pl D → Prop) {V : HSp D} (x : GA D V) :
    x ∈ grpOff V P ↔ mix (idem D P) 1 (mt V x) = mt V x := by
  unfold grpOff
  rw [mem_congGrp, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [mem_idOff_iff]
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · intro h; linear_combination (-1 : AE D) * h
  · intro h; linear_combination (-1 : AE D) * h

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`. Simplify using `only [mix, smul_add, smul_smul, he, h1, zero_smul, add_zero]`.
-/
theorem mix_mix_left {e : AE D} (he : e * e = e) {n : Type} [Fintype n] [DecidableEq n] (X Y Z : Matrix n n (AE D)) :
    mix e (mix e X Y) Z = mix e X Z := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  simp only [mix, smul_add, smul_smul, he, h1, zero_smul, add_zero]

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Simplify using `only [mix, smul_add, smul_smul, h2, h3, zero_smul, zero_add]`.
-/
theorem mix_mix_right {e : AE D} (he : e * e = e) {n : Type} [Fintype n] [DecidableEq n] (X Y Z : Matrix n n (AE D)) :
    mix e X (mix e Y Z) = mix e X Z := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, smul_add, smul_smul, h2, h3, zero_smul, zero_add]

/- English proof (translation)
Establish `he` using `idem_mul_self P`. Use `⟨fun h => ⟨mixGA P h 1, ?_, mixGA P 1 h, ?_, ?_⟩, fun x hx y hy => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_grpAt_iff, mt_mixGA, mt_one, mix_mix_left he]`. Rewrite using `[mem_grpOff_iff, mt_mixGA, mt_one, mix_mix_right he]`. Apply `mt_inj` to reduce the goal to its premises.

Rewrite using `[mt_mul, mt_mixGA, mt_mixGA, mt_one, mix_mul he, mul_one, one_mul, mix_self]`. Rewrite `hx` using `[mem_grpAt_iff]`. Rewrite `hy` using `[mem_grpOff_iff]`. Apply `mt_inj` to reduce the goal to its premises. Rewrite using `[mt_mul, mt_mul, ← hx, ← hy, mix_mul he, mix_mul he]`.

Simplify using `only [mul_one, one_mul]`. Rewrite using `[eq_bot_iff]`. Introduce `x hxy`. Take `⟨hx, hy⟩` from `Subgroup.mem_inf.1 hxy`. Rewrite using `[Subgroup.mem_bot]`.

Rewrite `hx` using `[mem_grpAt_iff]`. Rewrite `hy` using `[mem_grpOff_iff]`. Apply `mt_inj` to reduce the goal to its premises. Rewrite using `[mt_one]`. Use extensionality with `i j`.

Establish `h1` using `congrFun (congrFun hx i) j`. Establish `h2` using `congrFun (congrFun hy i) j`. Simplify using `only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2`. Take the linear combination `(-1 : AE D) * h1 + (-1 : AE D) * h2`.
-/
theorem part_grp (P : Pl D → Prop) (S : HSp D) :
    (∀ h : GA D S, ∃ x ∈ grpAt S P, ∃ y ∈ grpOff S P, h = x * y) ∧
      (∀ x ∈ grpAt S P, ∀ y ∈ grpOff S P, x * y = y * x) ∧ grpAt S P ⊓ grpOff S P = ⊥ := by
  have he := idem_mul_self P
  refine ⟨fun h => ⟨mixGA P h 1, ?_, mixGA P 1 h, ?_, ?_⟩, fun x hx y hy => ?_, ?_⟩
  · rw [mem_grpAt_iff, mt_mixGA, mt_one, mix_mix_left he]
  · rw [mem_grpOff_iff, mt_mixGA, mt_one, mix_mix_right he]
  · apply mt_inj
    rw [mt_mul, mt_mixGA, mt_mixGA, mt_one, mix_mul he, mul_one, one_mul, mix_self]
  · rw [mem_grpAt_iff] at hx
    rw [mem_grpOff_iff] at hy
    apply mt_inj
    rw [mt_mul, mt_mul, ← hx, ← hy, mix_mul he, mix_mul he]
    simp only [mul_one, one_mul]
  · rw [eq_bot_iff]
    intro x hxy
    obtain ⟨hx, hy⟩ := Subgroup.mem_inf.1 hxy
    rw [Subgroup.mem_bot]
    rw [mem_grpAt_iff] at hx
    rw [mem_grpOff_iff] at hy
    apply mt_inj
    rw [mt_one]
    ext i j
    have h1 := congrFun (congrFun hx i) j
    have h2 := congrFun (congrFun hy i) j
    simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    linear_combination (-1 : AE D) * h1 + (-1 : AE D) * h2

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Conclude with `Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (add_zero (0 : Ainf D.host.F)).symm rfl`.
-/
theorem pairA_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b := by
  exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (add_zero (0 : Ainf D.host.F)).symm rfl

/- English proof (translation)
Conclude with `Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (neg_zero (G := Ainf D.host.F)).symm rfl`.
-/
theorem pairA_neg (a : Af D.host.F) : pairA D.host.F 0 (-a) = -pairA D.host.F 0 a := by
  exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (neg_zero (G := Ainf D.host.F)).symm rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairA_zero : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl

/- English proof (translation)
Conclude with `Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (mul_zero (0 : Ainf D.host.F)).symm rfl`.
-/
theorem pairA_mul (a b : Af D.host.F) : pairA D.host.F 0 (a * b) = pairA D.host.F 0 a * pairA D.host.F 0 b := by
  exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (mul_zero (0 : Ainf D.host.F)).symm rfl

/- English proof (translation)
Conclude with `Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (smul_zero (A := Ainf D.host.F) c).symm rfl`.
-/
theorem pairA_zsmul (c : ℤ) (a : Af D.host.F) : pairA D.host.F 0 (c • a) = c • pairA D.host.F 0 a := by
  exact Prod.ext (α := Ainf D.host.F) (β := Af D.host.F) (smul_zero (A := Ainf D.host.F) c).symm rfl

/- English proof (translation)
Unfold `idAt`. Use `Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_pair _ _), ?_⟩` and prove the remaining obligations. Use `Submodule.mem_iInf _ |>.2 fun w => RingHom.mem_ker.2 ?_` and prove the remaining obligations. Rewrite using `[compAt_pair, hα w.1 w.2]`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem pair_mem_idAt (P : Pl D → Prop) (α : Af D.host.F) (hα : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (e : D.host.E) : pairA D.host.F 0 α ⊗ₜ[D.host.F] e ∈ idAt D P := by
  unfold idAt
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_pair _ _), ?_⟩
  refine Submodule.mem_iInf _ |>.2 fun w => RingHom.mem_ker.2 ?_
  rw [compAt_pair, hα w.1 w.2]
  exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, -, hα, a, -, x, -, rfl⟩` from `hy`. Conclude with `fun i => pair_mem_idAt P α hα _`. Consider the case `zero => exact fun i => zero_mem _`.

Consider the case `add y z _ _ hy hz => exact fun i => add_mem (hy i) (hz i)`. Consider the case `neg y _ hy => exact fun i => neg_mem (hy i)`.
-/
theorem latV_idAt {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ∀ i, y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hy
    exact fun i => pair_mem_idAt P α hα _
  | zero => exact fun i => zero_mem _
  | add y z _ _ hy hz => exact fun i => add_mem (hy i) (hz i)
  | neg y _ hy => exact fun i => neg_mem (hy i)

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 D.host.E) L := Module.Finite.iff_fg.mpr hL`. Use `haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 D.host.E) L`. Take `⟨t, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`. Use `⟨t, fun k => s k, fun k => (s k).2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmem : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; trivial`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hc` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem exists_gens {S : HSp D} (L : Lat S) (hL : L.FG) : ∃ (t : ℕ) (g : Fin t → Fin S.rank → D.host.E),
    (∀ k, g k ∈ L) ∧ ∀ x ∈ L, ∃ c : Fin t → ℤ, x = ∑ k, c k • g k := by
  haveI : Module.Finite (𝓞 D.host.E) L := Module.Finite.iff_fg.mpr hL
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 D.host.E) L
  obtain ⟨t, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  refine ⟨t, fun k => s k, fun k => (s k).2, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this.symm

/- English proof (translation)
Introduce `v`. Rewrite using `[map_zsmul]`. Conclude with `zsmul_mem (h v) c`.
-/
theorem intAf_zsmul (c : ℤ) {α : Af D.host.F} (h : α ∈ intAf D.host.F) : c • α ∈ intAf D.host.F := by
  intro v
  rw [map_zsmul]
  exact zsmul_mem (h v) c

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hαi, hα, a, ha, x, hx, rfl⟩` from `hy`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality.

Take `⟨c, rfl⟩` from `hgen x hx`. Use `⟨fun k => c k • α, fun k => ⟨intAf_zsmul _ hαi, fun w hw => by rw [map_zsmul, hα w hw, smul_zero]⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [one_mul, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, pairA_zsmul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Consider the case `zero`. Use `⟨0, fun k => ⟨fun v => by rw [Pi.zero_apply, map_zero]; exact zero_mem _, fun w _ => map_zero _⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[pairA_zero]`.

Consider the case `add y z _ _ hy hz`. Take `⟨β, hβ, rfl⟩` from `hy`. Take `⟨γ, hγ, rfl⟩` from `hz`. Use `⟨β + γ, fun k => ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, map_add]`.

Conclude with `add_mem ((hβ k).1 v) ((hγ k).1 v)`. Rewrite using `[Pi.add_apply, map_add, (hβ k).2 w hw, (hγ k).2 w hw, add_zero]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, pairA_add, TensorProduct.add_tmul, Finset.sum_add_distrib]`. Consider the case `neg y _ hy`.

Take `⟨β, hβ, rfl⟩` from `hy`. Use `⟨-β, fun k => ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.neg_apply, map_neg]`. Conclude with `neg_mem ((hβ k).1 v)`. Rewrite using `[Pi.neg_apply, map_neg, (hβ k).2 w hw, neg_zero]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.neg_apply, pairA_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]`.
-/
theorem latV_repr {S : HSp D} {L : Lat S} {Q : Pl D → Prop} {t : ℕ} (g : Fin t → Fin S.rank → D.host.E)
    (hgen : ∀ x ∈ L, ∃ c : Fin t → ℤ, x = ∑ k, c k • g k) {z : Fin S.rank → AE D} (hz : z ∈ latV S L Q) :
    ∃ β : Fin t → Af D.host.F, (∀ k, β k ∈ intAf D.host.F ∧ ∀ w, ¬ Q w → evalV D.host.F w (β k) = 0) ∧
      z = fun i => ∑ k, pairA D.host.F 0 (β k) ⊗ₜ[D.host.F] g k i := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := hgen x hx
    refine ⟨fun k => c k • α, fun k => ⟨intAf_zsmul _ hαi, fun w hw => by rw [map_zsmul, hα w hw, smul_zero]⟩, ?_⟩
    funext i
    simp only [one_mul, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, pairA_zsmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | zero =>
    refine ⟨0, fun k => ⟨fun v => by rw [Pi.zero_apply, map_zero]; exact zero_mem _, fun w _ => map_zero _⟩, ?_⟩
    funext i
    simp [pairA_zero]
  | add y z _ _ hy hz =>
    obtain ⟨β, hβ, rfl⟩ := hy
    obtain ⟨γ, hγ, rfl⟩ := hz
    refine ⟨β + γ, fun k => ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩
    · rw [Pi.add_apply, map_add]; exact add_mem ((hβ k).1 v) ((hγ k).1 v)
    · rw [Pi.add_apply, map_add, (hβ k).2 w hw, (hγ k).2 w hw, add_zero]
    · funext i
      simp only [Pi.add_apply, pairA_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨β, hβ, rfl⟩ := hy
    refine ⟨-β, fun k => ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩
    · rw [Pi.neg_apply, map_neg]; exact neg_mem ((hβ k).1 v)
    · rw [Pi.neg_apply, map_neg, (hβ k).2 w hw, neg_zero]
    · funext i
      simp only [Pi.neg_apply, pairA_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

variable {D : D7}

def finIn (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finIn_tmul (a : Af D.host.F) (e : D.host.E) : finIn D (a ⊗ₜ[D.host.F] e) = pairA D.host.F 0 a ⊗ₜ[D.host.F] e := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a e => rw [finIn_tmul, infPart_pair]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`.
-/
theorem infPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (finIn D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [finIn_tmul, infPart_pair]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero]`. Consider the case `tmul a e`. Rewrite using `[finIn_tmul, compAt_pair]`. Use `show _ = Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] e)`.

Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`.
-/
theorem compAt_finIn (w : Pl D) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    compAt D w (finIn D z) = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [finIn_tmul, compAt_pair]
    show _ = Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] e)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/- English proof (translation)
The claim follows from `RingHom.mem_ker.1 (Ideal.mem_inf.1 h).1`.
-/
theorem infPart_of_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) : infPart D a = 0 :=
  RingHom.mem_ker.1 (Ideal.mem_inf.1 h).1

/- English proof (translation)
The claim follows from `RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h).2 ⟨w, hw⟩)`.
-/
theorem compAt_of_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) {w : Pl D} (hw : ¬ P w) : compAt D w a = 0 :=
  RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h).2 ⟨w, hw⟩)

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_comp` to reduce the goal to its premises. Rewrite using `[map_sub, h, infPart_finIn, sub_zero]`. Introduce `w`. Rewrite using `[map_sub, compAt_finIn]`.

Unfold `GlobalTheory.FinPl.compAt`. Rewrite using `[RingHom.comp_apply, sub_self]`.
-/
theorem eq_finIn {a : AE D} (h : infPart D a = 0) : a = finIn D (finPart D a) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [map_sub, h, infPart_finIn, sub_zero]
  · intro w
    rw [map_sub, compAt_finIn]
    unfold GlobalTheory.FinPl.compAt
    rw [RingHom.comp_apply, sub_self]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, o, rfl⟩` from `hz`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨α, hαi, hα, a', ha', x, hx, rfl⟩` from `hy`. Rewrite `ha'` using `[Set.mem_singleton_iff]`. Substitute `ha'` using the available equality. Use `AddSubgroup.subset_closure ⟨ePl D (· = v) * a * α, fun w => ?_, fun w hw => ?_, 1, rfl, o • x, L.smul_mem o hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`.

Conclude with `mul_mem (mul_mem (ePl_int _ w) (ha w)) (hαi w)`. Rewrite using `[map_mul, map_mul, evalV_ePl, if_neg hw, zero_mul, zero_mul]`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Unfold `idem`.

Rewrite using `[finIn_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, ← pairA_mul]`. Use `congr 1`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Simplify using `only [one_mul]`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [smul_add]`. Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.

Consider the case `zero => rw [map_zero, mul_zero, zero_smul]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ h h' => rw [map_add, mul_add, add_smul]`. Conclude with `add_mem h h'`. Consider the case `neg z _ h => rw [map_neg, mul_neg, neg_smul]`.

Conclude with `neg_mem h`.
-/
theorem placeIdempotent_integral_smul_mem_latticeCompletionAtPlace {S : HSp D} {L : Lat S} {P : Pl D → Prop} (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (idem D (· = v) * finIn D z) • y ∈ latV S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a', ha', x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      refine AddSubgroup.subset_closure ⟨ePl D (· = v) * a * α, fun w => ?_, fun w hw => ?_, 1, rfl, o • x,
        L.smul_mem o hx, ?_⟩
      · rw [map_mul, map_mul]
        exact mul_mem (mul_mem (ePl_int _ w) (ha w)) (hαi w)
      · rw [map_mul, map_mul, evalV_ePl, if_neg hw, zero_mul, zero_mul]
      · funext i
        rw [Pi.smul_apply, smul_eq_mul]
        unfold idem
        rw [finIn_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul,
          ← pairA_mul]
        congr 1
        rw [Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add, mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

/- English proof (translation)
Establish `he1 : idem D (· = v) * e = e` using `(mem_idAt_iff _ e).1 he.1`. Establish `he2 : e = finIn D (finPart D e)` using `eq_finIn (infPart_of_idAt he.1)`. Establish `: e = idem D (· = v) * finIn D (finPart D e)` using `by rw [← he2, he1]`. Rewrite using `[this]`. Conclude with `placeIdempotent_integral_smul_mem_latticeCompletionAtPlace v he.2 hy`.
-/
theorem smul_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} (v : Pl D) {e : AE D} (he : e ∈ intAt D (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : e • y ∈ latV S L (· = v) := by
  have he1 : idem D (· = v) * e = e := (mem_idAt_iff _ e).1 he.1
  have he2 : e = finIn D (finPart D e) := eq_finIn (infPart_of_idAt he.1)
  have : e = idem D (· = v) * finIn D (finPart D e) := by rw [← he2, he1]
  rw [this]
  exact placeIdempotent_integral_smul_mem_latticeCompletionAtPlace v he.2 hy

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨latV_idAt hy, fun v _ e he => smul_latV v he hy⟩`. Introduce and unpack `⟨hid, hloc⟩`. Take `⟨t, g, hgL, hgen⟩` from `exists_gens L hL.fg`.

Establish `hrep : ∀ v, P v → ∃ β : Fin t → Af D.host.F, (∀ k, β k ∈ intAf D.host.F ∧ ∀ w, ¬ w = v → evalV D.host.F w (β k) = 0) ∧ idem D (· = v) • y = fun i => ∑ k, pairA D.host.F 0 (β k) ⊗ₜ[D.host.F] g k i` using `fun v hv => latV_repr g hgen (hloc v hv _ (idem_mem_intAt _))`. Use `choose! B hB hBy using hrep`. Set `β : Fin t → Af D.host.F` to `fun k => RestrictedProduct.mk (fun w => if P w then evalV D.host.F w (B w k) else 0) (Filter.Eventually.of_forall fun w => by`. Distinguish the cases in `hw : P w`. Rewrite using `[if_pos hw]`.

Conclude with `((hB w hw) k).1 w`. Rewrite using `[if_neg hw]`. Conclude with `zero_mem _)`. Establish `hβ : ∀ k w, evalV D.host.F w (β k) = if P w then evalV D.host.F w (B w k) else 0` using `fun k w => rfl`. Establish `hyeq : y = fun i => ∑ k, pairA D.host.F 0 (β k) ⊗ₜ[D.host.F] g k i`.

Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_comp` to reduce the goal to its premises. Rewrite using `[map_sub, map_sum]`. Simplify using `only [infPart_pair, Finset.sum_const_zero, sub_zero]`.

Conclude with `infPart_of_idAt (hid i)`. Introduce `w`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [compAt_pair, hβ]`. Distinguish the cases in `hw : P w`.

Establish `h1 : compAt D w (y i) = compAt D w ((idem D (· = w) • y) i)`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, compAt_idem, if_pos rfl, one_mul]`. Rewrite using `[h1, hBy w hw, map_sum]`. Simplify using `only [compAt_pair, if_pos hw, sub_self]`. Rewrite using `[compAt_of_idAt (hid i) hw]`.

Simplify using `only [if_neg hw, TensorProduct.zero_tmul, Finset.sum_const_zero, sub_zero]`. Rewrite using `[hyeq, ← Finset.sum_fn]`. Use `AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨β k, fun w => ?_, fun w hw => ?_, 1, rfl, g k, hgL k, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ]`. Distinguish the cases in `hw : P w`.

Rewrite using `[if_pos hw]`. Conclude with `((hB w hw) k).1 w`. Rewrite using `[if_neg hw]`. Conclude with `zero_mem _`. Rewrite using `[hβ, if_neg hw]`.

Use function extensionality and compare the values at `i`. Rewrite using `[one_mul]`.
-/
theorem part_lat (P : Pl D → Prop) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D)
    (hL : Submodule.IsLattice D.host.E L) :
    y ∈ latV S L P ↔ (∀ i, y i ∈ idAt D P) ∧ ∀ v, P v → ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v) := by
  classical
  constructor
  · intro hy
    exact ⟨latV_idAt hy, fun v _ e he => smul_latV v he hy⟩
  · rintro ⟨hid, hloc⟩
    obtain ⟨t, g, hgL, hgen⟩ := exists_gens L hL.fg
    have hrep : ∀ v, P v → ∃ β : Fin t → Af D.host.F,
        (∀ k, β k ∈ intAf D.host.F ∧ ∀ w, ¬ w = v → evalV D.host.F w (β k) = 0) ∧
          idem D (· = v) • y = fun i => ∑ k, pairA D.host.F 0 (β k) ⊗ₜ[D.host.F] g k i :=
      fun v hv => latV_repr g hgen (hloc v hv _ (idem_mem_intAt _))
    choose! B hB hBy using hrep
    let β : Fin t → Af D.host.F := fun k => RestrictedProduct.mk (fun w => if P w then evalV D.host.F w (B w k) else 0)
      (Filter.Eventually.of_forall fun w => by
        by_cases hw : P w
        · rw [if_pos hw]; exact ((hB w hw) k).1 w
        · rw [if_neg hw]; exact zero_mem _)
    have hβ : ∀ k w, evalV D.host.F w (β k) = if P w then evalV D.host.F w (B w k) else 0 := fun k w => rfl
    have hyeq : y = fun i => ∑ k, pairA D.host.F 0 (β k) ⊗ₜ[D.host.F] g k i := by
      funext i
      rw [← sub_eq_zero]
      apply eq_zero_of_comp
      · rw [map_sub, map_sum]
        simp only [infPart_pair, Finset.sum_const_zero, sub_zero]
        exact infPart_of_idAt (hid i)
      · intro w
        rw [map_sub, map_sum]
        simp only [compAt_pair, hβ]
        by_cases hw : P w
        · have h1 : compAt D w (y i) = compAt D w ((idem D (· = w) • y) i) := by
            rw [Pi.smul_apply, smul_eq_mul, map_mul, compAt_idem, if_pos rfl, one_mul]
          rw [h1, hBy w hw, map_sum]
          simp only [compAt_pair, if_pos hw, sub_self]
        · rw [compAt_of_idAt (hid i) hw]
          simp only [if_neg hw, TensorProduct.zero_tmul, Finset.sum_const_zero, sub_zero]
    rw [hyeq, ← Finset.sum_fn]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure
      ⟨β k, fun w => ?_, fun w hw => ?_, 1, rfl, g k, hgL k, ?_⟩
    · rw [hβ]
      by_cases hw : P w
      · rw [if_pos hw]; exact ((hB w hw) k).1 w
      · rw [if_neg hw]; exact zero_mem _
    · rw [hβ, if_neg hw]
    · funext i
      rw [one_mul]

end GlobalTheory.FinPlLoc

open GlobalTheory.FinPlLoc in
/- English proof (translation)
Introduce `D P` and use `⟨part_idem P, fun S => ⟨(part_grp P S).1, (part_grp P S).2.1, (part_grp P S).2.2, fun L y hL => part_lat P S L y hL⟩⟩`.
-/
theorem GlobalTheory.FinPl.localComponents : ∀ (D : D7) (P : Pl D → Prop), (∃ ε : AE D, ε * ε = ε ∧ cA D ε = ε ∧ ε ∈ intAt D P ∧
    (∀ a, a ∈ idAt D P ↔ ε * a = a) ∧ (∀ a, a ∈ idOff D P ↔ ε * a = 0)) ∧ ∀ S : HSp D,
    (∀ h : GA D S, ∃ x ∈ grpAt S P, ∃ y ∈ grpOff S P, h = x * y) ∧ (∀ x ∈ grpAt S P, ∀ y ∈ grpOff S P, x * y = y * x) ∧
    grpAt S P ⊓ grpOff S P = ⊥ ∧ (∀ (L : Lat S) (y : Fin S.rank → AE D), (Submodule.IsLattice D.host.E L) →
      (y ∈ latV S L P ↔ (∀ i, y i ∈ idAt D P) ∧ ∀ v, P v → ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v))) :=
  fun D P => ⟨part_idem P, fun S => ⟨(part_grp P S).1, (part_grp P S).2.1, (part_grp P S).2.2,
    fun L y hL => part_lat P S L y hL⟩⟩
