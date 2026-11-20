import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Dil

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hs : Function.Surjective (prV (E` using `E) v) := fun x => ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩`. Establish `hk : RingHom.ker (prV (E` using `E) v) ≤ RingHom.ker (adAt F w) := fun z hz => ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v z).1.1 hz) w hw`. Conclude with `⟨RingHom.liftOfSurjective (prV (E := E) v) hs ⟨adAt F w, hk⟩, fun z => RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩`.
-/
theorem exists_psi (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v) :
    ∃ ψ : E ⊗[F] v.adicCompletion F →+* w.adicCompletion E, ∀ z, ψ (prV (E := E) v z) = adAt F w z := by
  have hs : Function.Surjective (prV (E := E) v) := fun x => ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩
  have hk : RingHom.ker (prV (E := E) v) ≤ RingHom.ker (adAt F w) := fun z hz =>
    ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v z).1.1 hz) w hw
  exact ⟨RingHom.liftOfSurjective (prV (E := E) v) hs ⟨adAt F w, hk⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩

def psi (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v) :
    E ⊗[F] v.adicCompletion F →+* w.adicCompletion E := (exists_psi v w hw).choose

/- English proof (translation)
The claim follows from `(exists_psi v w hw).choose_spec z`.
-/
theorem psi_prV (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v) (z : AfE F E) :
    psi v w hw (prV (E := E) v z) = adAt F w z := (exists_psi v w hw).choose_spec z

/- English proof (translation)
Rewrite using `[← adAt_inclE F w x, ← psi_prV v w hw]`. Use `congr 1`.
-/
theorem psi_inclE (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v) (x : E) :
    psi v w hw (Formalism.UG.inclE (F := F) (v.adicCompletion F) x) = algebraMap E _ x := by
  rw [← adAt_inclE F w x, ← psi_prV v w hw]
  congr 1

/- English proof (translation)
Take `⟨z, rfl⟩ : ∃ z, prV (E` from `E) v z = x := ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩`. Rewrite using `[(GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v z).2]`. Conclude with `forall₂_congr fun w hw => by rw [psi_prV]`.
-/
theorem mem_intV_iff (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    x ∈ intV E v ↔ ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v), Valued.v (psi v w hw x) ≤ 1 := by
  obtain ⟨z, rfl⟩ : ∃ z, prV (E := E) v z = x := ⟨_, Formalism.UG.P.afsplit_prV_IE v x⟩
  rw [(GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v z).2]
  exact forall₂_congr fun w hw => by rw [psi_prV]

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨_, ⟨o, rfl⟩⟩, rfl⟩)`.
-/
theorem incl_mem_intV (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E o) ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨o, rfl⟩⟩, rfl⟩)

def kap (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : 𝓞 E →+* intV E v :=
  ((Formalism.UG.inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E v)
    fun o => incl_mem_intV v o

/- English proof (translation)
Rewrite using `[valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h3 : ¬ P.intValuation π ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => h2 ((P.intValuation_le_pow_iff_mem π 2).1 h)`. Rewrite `h3` using `[not_le]`. Break down `eq_or_ne (Valued.v z) 0 with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Conclude with `zero_le'`. Establish `hp : P.intValuation π ≠ 0` using `(lt_of_le_of_lt zero_le' h3).ne'`. Rewrite `hz`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h3`, the goal using `[← WithZero.exp_log hp]`. Rewrite `h3` using `[WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Establish `h4 : WithZero.log (Valued.v z) < 0`. Rewrite using `[← WithZero.exp_lt_exp, WithZero.exp_zero]`. Conclude with `hz`. Move the coercions through the operations in `at h3`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_val_pi {P : HeightOneSpectrum (𝓞 E)} {π : 𝓞 E} (h2 : π ∉ P.asIdeal ^ 2) {z : P.adicCompletion E}
    (hz : Valued.v z < 1) : Valued.v z ≤ Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E π)) := by
  rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have h3 : ¬ P.intValuation π ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((P.intValuation_le_pow_iff_mem π 2).1 h)
  rw [not_le] at h3
  rcases eq_or_ne (Valued.v z) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  have hp : P.intValuation π ≠ 0 := (lt_of_le_of_lt zero_le' h3).ne'
  rw [← WithZero.exp_log h0] at hz ⊢
  rw [← WithZero.exp_log hp] at h3 ⊢
  rw [WithZero.exp_lt_exp] at h3
  rw [WithZero.exp_le_exp]
  have h4 : WithZero.log (Valued.v z) < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_zero]; exact hz
  push_cast at h3
  omega

/- English proof (translation)
Rewrite using `[valued_algebraMap]`. Conclude with `le_antisymm (P.valuation_le_one π) (not_lt.1 fun h' => h ((P.valuation_lt_one_iff_mem π).1 h'))`.
-/
theorem val_eq_one {P : HeightOneSpectrum (𝓞 E)} {π : 𝓞 E} (h : π ∉ P.asIdeal) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E π)) = 1 := by
  rw [valued_algebraMap]
  exact le_antisymm (P.valuation_le_one π) (not_lt.1 fun h' => h ((P.valuation_lt_one_iff_mem π).1 h'))

/- English proof (translation)
Rewrite using `[valued_algebraMap]`. Conclude with `(P.valuation_lt_one_iff_mem π).2 h`.
-/
theorem val_lt_one {P : HeightOneSpectrum (𝓞 E)} {π : 𝓞 E} (h : π ∈ P.asIdeal) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E π)) < 1 := by
  rw [valued_algebraMap]
  exact (P.valuation_lt_one_iff_mem π).2 h

/- English proof (translation)
Rewrite using `[valued_algebraMap]`. Conclude with `P.valuation_le_one π`.
-/
theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E π)) ≤ 1 := by
  rw [valued_algebraMap]
  exact P.valuation_le_one π

/- English proof (translation)
Establish `hz : PtExist.idem F P * z ∈ RInt F E` using `(mem_rInt_iff F E _).2 fun w => by`. Rewrite using `[← adAt_apply, map_mul, PtExist.adAt_idem]`. Use `split_ifs with hw`. Substitute `hw` using the available equality. Simplify using `using h`.

Simplify using the standard rewrite rules. Take `⟨c, -, hc⟩` from `PtExist.hasRes_redA P hz`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[map_mul, PtExist.adAt_idem, if_pos rfl, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_res [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (z : AfE F E) (h : Valued.v (adAt F P z) ≤ 1) :
    ∃ c : 𝓞 E, Valued.v (adAt F P z - algebraMap E _ (algebraMap (𝓞 E) E c)) < 1 := by
  classical
  have hz : PtExist.idem F P * z ∈ RInt F E := (mem_rInt_iff F E _).2 fun w => by
    rw [← adAt_apply, map_mul, PtExist.adAt_idem]
    split_ifs with hw
    · subst hw; simpa using h
    · simp
  obtain ⟨c, -, hc⟩ := PtExist.hasRes_redA P hz
  refine ⟨c, ?_⟩
  rwa [map_mul, PtExist.adAt_idem, if_pos rfl, one_mul] at hc

/- English proof (translation)
Establish `e : prV (E` using `E) (w.under (𝓞 F)) ((G : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0 := by`. Use `congrArg (fun M : GL (Fin n) (E ⊗[F] (w.under (𝓞 F)).adicCompletion F) => M.1 i j) h` as an intermediate fact. Simplify using `only [Units.val_one, Matrix.one_apply] at this`. Conclude with `this`. Establish `e2 : prV (E` using `E) (w.under (𝓞 F)) ((G : Matrix (Fin n) (Fin n) (AfE F E)) i j - if i = j then 1 else 0) = 0 := by`.

Rewrite using `[map_sub, e]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `e3` using `(GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (w.under (𝓞 F)) _).1.1 e2 w rfl`. Rewrite `e3` using `[map_sub, sub_eq_zero]`. Rewrite using `[e3]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem adAt_of_bc_eq_one {n : ℕ} (G : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (h : bc (prV (E := E) (w.under (𝓞 F))) G = 1) (i j : Fin n) :
    adAt F w ((G : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0 := by
  have e : prV (E := E) (w.under (𝓞 F)) ((G : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0 := by
    have := congrArg (fun M : GL (Fin n) (E ⊗[F] (w.under (𝓞 F)).adicCompletion F) => M.1 i j) h
    simp only [Units.val_one, Matrix.one_apply] at this
    exact this
  have e2 : prV (E := E) (w.under (𝓞 F)) ((G : Matrix (Fin n) (Fin n) (AfE F E)) i j - if i = j then 1 else 0) = 0 := by
    rw [map_sub, e]
    split_ifs <;> simp
  have e3 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (w.under (𝓞 F)) _).1.1 e2 w rfl
  rw [map_sub, sub_eq_zero] at e3
  rw [e3]
  split_ifs <;> simp

end Comp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {S : Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f bad}
  {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)}

local notation "ι" => Formalism.UG.inclE (F := F) (v.adicCompletion F)

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same, Matrix.one_apply_eq, mul_one]`. Both sides reduce to the same expression. Introduce `b _ hb`.

Simplify using `[Matrix.one_apply, hb.symm]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules.
-/
theorem hform_single_left (c : E) (y : Fin n → E) (j : Fin n) :
    hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (Pi.single j c) y = star c * y j := by
  classical
  unfold hform
  rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, Matrix.one_apply_eq, mul_one]; rfl
  · intro b _ hb; simp [Matrix.one_apply, hb.symm]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same, Matrix.one_apply_eq, mul_one]`. Both sides reduce to the same expression. Introduce `b _ hb`.

Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Simplify using `[Matrix.one_apply, hb]`. Simplify using `[Pi.single_apply, hk]`. Simplify using the standard rewrite rules.
-/
theorem hform_single_right (c : E) (x : Fin n → E) (j : Fin n) :
    hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x (Pi.single j c) = star (x j) * c := by
  classical
  unfold hform
  rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, Matrix.one_apply_eq, mul_one]; rfl
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = j
    · subst hk; simp [Matrix.one_apply, hb]
    · simp [Pi.single_apply, hk]
  · simp

def IsBase (S : Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f bad) (π : 𝓞 E) : Prop :=
  ∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)

/- English proof (translation)
Use `(hLb _).2 fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Conclude with `⟨t, by simp, ht⟩`. Conclude with `⟨0, by simp [Pi.single_apply, hk], fun _ => dvd_zero _⟩`.
-/
theorem single_mem_Lb (hLb : IsBase S π) (j : Fin n) (t : 𝓞 E) (ht : j.1 + 1 = n → π ∣ t) :
    (Pi.single j (algebraMap (𝓞 E) E t) : Fin n → E) ∈ S.Lb := by
  classical
  refine (hLb _).2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    exact ⟨t, by simp, ht⟩
  · exact ⟨0, by simp [Pi.single_apply, hk], fun _ => dvd_zero _⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Prove the components needed by the constructor for the conclusion. Introduce `hj`. Establish `h` using `hx _ (single_mem_Lb hLb j 1 fun h => absurd h hj)`.

Rewrite `h` using `[hform_single_left, map_one, star_one, one_mul]`. Then use the resulting hypothesis. Introduce `hj`. Establish `h` using `hx _ (single_mem_Lb hLb j π fun _ => dvd_rfl)`. Rewrite `h` using `[hform_single_left]`. Then use the resulting hypothesis. Consider the case `zero => simp [zero_mem]`.

Consider the case `add a b _ _ ha hb`. Use `⟨fun h => add_mem (ha.1 h) (hb.1 h), fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `add_mem (ha.2 h) (hb.2 h)`. Consider the case `smul c a _ ha`.

Establish `e : (c • a) j = algebraMap (𝓞 E) E c * a j`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `mul_mem ⟨c, rfl⟩ (ha.1 h)`.

Rewrite using `[e, mul_left_comm]`. Conclude with `mul_mem ⟨c, rfl⟩ (ha.2 h)`.
-/
theorem coord_of_mem_span (hLb : IsBase S π) {x : Fin n → E}
    (hx : x ∈ Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)) (j : Fin n) :
    (j.1 + 1 ≠ n → x j ∈ (algebraMap (𝓞 E) E).range) ∧
      (j.1 + 1 = n → star (algebraMap (𝓞 E) E π) * x j ∈ (algebraMap (𝓞 E) E).range) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    constructor
    · intro hj
      have h := hx _ (single_mem_Lb hLb j 1 fun h => absurd h hj)
      rwa [hform_single_left, map_one, star_one, one_mul] at h
    · intro hj
      have h := hx _ (single_mem_Lb hLb j π fun _ => dvd_rfl)
      rwa [hform_single_left] at h
  | zero => simp [zero_mem]
  | add a b _ _ ha hb =>
    refine ⟨fun h => add_mem (ha.1 h) (hb.1 h), fun h => ?_⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha.2 h) (hb.2 h)
  | smul c a _ ha =>
    have e : (c • a) j = algebraMap (𝓞 E) E c * a j := by
      rw [Pi.smul_apply, Algebra.smul_def]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [e]
      exact mul_mem ⟨c, rfl⟩ (ha.1 h)
    · rw [e, mul_left_comm]
      exact mul_mem ⟨c, rfl⟩ (ha.2 h)

/- English proof (translation)
Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Establish `h` using `coord_of_mem_span hLb hy j`. Prove the components needed by the constructor for the conclusion.

Introduce `hj`. Take `⟨o, ho⟩` from `h.1 hj`. Use `show ι (y j) ∈ intV E v`. Rewrite using `[← ho]`. Conclude with `incl_mem_intV v o`.

Introduce `hj`. Take `⟨o, ho⟩` from `h.2 hj`. Use `show ι _ * ι (y j) ∈ intV E v`. Rewrite using `[← map_mul, ← ho]`. Conclude with `incl_mem_intV v o`.

Consider the case `zero => simp [zero_mem]`. Consider the case `add a b _ _ ha hb`. Use `⟨fun h => add_mem (ha.1 h) (hb.1 h), fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `add_mem (ha.2 h) (hb.2 h)`.

Consider the case `smul c a _ ha`. Establish `e : (c • a) j = (c : E ⊗[F] v.adicCompletion F) * a j` using `rfl`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `mul_mem c.2 (ha.1 h)`.

Rewrite using `[e, mul_left_comm]`. Conclude with `mul_mem c.2 (ha.2 h)`.
-/
theorem coord_of_mem (hLb : IsBase S π) {s : Fin n → E ⊗[F] v.adicCompletion F}
    (hs : s ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) (j : Fin n) :
    (j.1 + 1 ≠ n → s j ∈ intV E v) ∧ (j.1 + 1 = n → ι (star (algebraMap (𝓞 E) E π)) * s j ∈ intV E v) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have h := coord_of_mem_span hLb hy j
    constructor
    · intro hj
      obtain ⟨o, ho⟩ := h.1 hj
      show ι (y j) ∈ intV E v
      rw [← ho]
      exact incl_mem_intV v o
    · intro hj
      obtain ⟨o, ho⟩ := h.2 hj
      show ι _ * ι (y j) ∈ intV E v
      rw [← map_mul, ← ho]
      exact incl_mem_intV v o
  | zero => simp [zero_mem]
  | add a b _ _ ha hb =>
    refine ⟨fun h => add_mem (ha.1 h) (hb.1 h), fun h => ?_⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha.2 h) (hb.2 h)
  | smul c a _ ha =>
    have e : (c • a) j = (c : E ⊗[F] v.adicCompletion F) * a j := rfl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [e]
      exact mul_mem c.2 (ha.1 h)
    · rw [e, mul_left_comm]
      exact mul_mem c.2 (ha.2 h)

def ee (n : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (j : Fin n) : Fin n → E ⊗[F] v.adicCompletion F :=
  fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single j 1 : Fin n → E) i)

/- English proof (translation)
Use `Submodule.subset_span ⟨_, Submodule.subset_span fun x hx => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hform_single_right]`. Take `⟨r, hr, -⟩` from `(hLb x).1 hx j`. Use `⟨cO E r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, algebraMap_cO, mul_one]`.
-/
theorem ee_mem (hLb : IsBase S π) (j : Fin n) :
    ee n F E v j ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)) := by
  refine Submodule.subset_span ⟨_, Submodule.subset_span fun x hx => ?_, rfl⟩
  rw [hform_single_right]
  obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
  refine ⟨cO E r, ?_⟩
  rw [hr, algebraMap_cO, mul_one]

/- English proof (translation)
Establish `e : ee n F E v j = Pi.single j 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[ee]`.

Simplify using `[ee, Pi.single_apply, hk]`. Rewrite using `[e, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem mulVec_ee (G : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (j i : Fin n) :
    (G *ᵥ ee n F E v j) i = G i j := by
  classical
  have e : ee n F E v j = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [ee]
    · simp [ee, Pi.single_apply, hk]
  rw [e, Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Establish `e : y = ∑ j, u j • (fun i => ι ((Pi.single j (algebraMap (𝓞 E) E (t j)) : Fin n → E) i))`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Use `show _ = (u i : E ⊗[F] v.adicCompletion F) * ι _`. Rewrite using `[hy i, Pi.single_eq_same]`.

Introduce `b _ hb show (u b : E ⊗[F] v.adicCompletion F) * ι _ = 0`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hb), map_zero, mul_zero]`. Conclude with `fun h => absurd (Finset.mem_univ i) h`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht j, rfl⟩)`.
-/
theorem mem_latS_of_coords {y : Fin n → E ⊗[F] v.adicCompletion F} (u : Fin n → intV E v) (t : Fin n → 𝓞 E)
    (ht : ∀ j, (Pi.single j (algebraMap (𝓞 E) E (t j)) : Fin n → E) ∈ S.Lb)
    (hy : ∀ j, y j = (u j : E ⊗[F] v.adicCompletion F) * ι (algebraMap (𝓞 E) E (t j))) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  classical
  have e : y = ∑ j, u j • (fun i => ι ((Pi.single j (algebraMap (𝓞 E) E (t j)) : Fin n → E) i)) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (u i : E ⊗[F] v.adicCompletion F) * ι _
      rw [hy i, Pi.single_eq_same]
    · intro b _ hb
      show (u b : E ⊗[F] v.adicCompletion F) * ι _ = 0
      rw [Pi.single_eq_of_ne (Ne.symm hb), map_zero, mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht j, rfl⟩)

end Loc

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {S : Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f bad}
  {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)}

local notation "ι" => Formalism.UG.inclE (F := F) (v.adicCompletion F)

/- English proof (translation)
Establish `h` using `coord_of_mem (v := v) hLb hs j`. Distinguish the cases in `hj : j.1 + 1 = n`. Establish `h4` using `(mem_intV_iff v _).1 (h.2 hj) P hP`. Establish `h5 : cO E π ∉ P.asIdeal` using `h3`. Rewrite `h4` using `[map_mul, psi_inclE, map_mul, ← algebraMap_cO, val_eq_one h5, one_mul]`.

Conclude with `h4`. Conclude with `(mem_intV_iff v _).1 (h.1 hj) P hP`.
-/
theorem val_coord_le (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    {s : Fin n → E ⊗[F] v.adicCompletion F}
    (hs : s ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) (j : Fin n) :
    Valued.v (psi v P hP (s j)) ≤ 1 := by
  have h := coord_of_mem (v := v) hLb hs j
  by_cases hj : j.1 + 1 = n
  · have h4 := (mem_intV_iff v _).1 (h.2 hj) P hP
    have h5 : cO E π ∉ P.asIdeal := h3
    rw [map_mul, psi_inclE, map_mul, ← algebraMap_cO, val_eq_one h5, one_mul] at h4
    exact h4
  · exact (mem_intV_iff v _).1 (h.1 hj) P hP

/- English proof (translation)
Establish `h` using `val_coord_le hLb hP h3 ((hG _).1 (ee_mem hLb j)) i`. Rewrite `h` using `[mulVec_ee]`. Then use the resulting hypothesis.
-/
theorem val_entry_le (hLb : IsBase S π) (hP : P.under (𝓞 F) = v) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    {G : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hG : G ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)))) (i j : Fin n) :
    Valued.v (psi v P hP ((G : Matrix (Fin n) (Fin n) _) i j)) ≤ 1 := by
  have h := val_coord_le hLb hP h3 ((hG _).1 (ee_mem hLb j)) i
  rwa [mulVec_ee] at h

/- English proof (translation)
Establish `hπ0 : (algebraMap (𝓞 E) E π) ≠ 0` using `fun h => h3 (by`. Establish `: π = 0` using `RingOfIntegers.ext h`. Rewrite using `[this]`. Conclude with `zero_mem _)`. Establish `hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = r` using `fun j => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hr⟩`.

Take `⟨y, i, hi, hyi⟩ : ∃ y, ∃ i ∈ P.asIdeal, y * cO E π + i = 1` from `P.isMaximal.exists_inv h3`. Establish `hA : S.fT v hv (kap F v (y * cO E π) • s) = 0`. Use `S.fT_L v hv _ ?_` and prove the remaining obligations. Establish `hc2` using `(coord_of_mem (v := v) hLb s.2 r).2 hr`. Establish `hu : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E (y * cO E π)) * s.1 r ∈ intV E v`.

Use `(mem_intV_iff v _).2 fun w hw' => ?_` and prove the remaining obligations. Break down `hw w hw' with rfl | rfl` into its components or cases. Establish `e : psi v w hw' = psi v w hP` using `rfl`. Rewrite using `[map_mul, psi_inclE, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, e, mul_assoc]`. Use `inv_mul_le_one_of_le₀ ?_ zero_le'` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `(mem_intV_iff v _).1 hc2 _ hw'`. Establish `e : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E (y * cO E π)) * s.1 r = ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E y) * (ι (star (algebraMap (𝓞 E) E π)) * s.1 r)`. Rewrite using `[← mul_assoc, ← map_mul, map_mul (algebraMap (𝓞 E) E) y, algebraMap_cO, mul_assoc]`. Rewrite using `[e, map_mul, map_mul, psi_inclE, map_mul, map_mul, map_inv₀, map_inv₀, val_eq_one h3, inv_one, one_mul]`.

Conclude with `mul_le_one' (val_le_one _ _) h4`. Establish `hjm : ∀ j, ι (algebraMap (𝓞 E) E (y * cO E π)) * s.1 j ∈ intV E v ∨ j = r` using `fun j => by`. Distinguish the cases in `hj : j = r`. Conclude with `Or.inr hj`. Conclude with `Or.inl (mul_mem (incl_mem_intV v _) ((coord_of_mem (v := v) hLb s.2 j).1 fun h => hj ((hlast j).1 h)))`.

Use `mem_latS_of_coords (S := S) (fun j => if hj : j = r then ⟨_, hu⟩ else ⟨_, (hjm j).resolve_right hj⟩) (fun j => if j = r then π else 1) (fun j => single_mem_Lb hLb j _ fun h => ?_) fun j => ?_` and prove the remaining obligations. Rewrite using `[if_pos ((hlast j).1 h)]`. Distinguish the cases in `hj : j = r`. Substitute `hj` using the available equality. Simplify using `only [dif_pos, if_pos]`.

Use `show ι _ * s.1 j = ι _ * s.1 j * ι _`. Rewrite using `[mul_right_comm, ← map_mul, mul_right_comm, inv_mul_cancel₀ hπ0, one_mul]`. Simplify using `only [dif_neg hj, if_neg hj, map_one, mul_one]`. Both sides reduce to the same expression. Establish `hB : S.fT v hv (kap F v i • s) = 0`.

Establish `hm : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E i) ∈ intV E v`. Use `(mem_intV_iff v _).2 fun w hw' => ?_` and prove the remaining obligations. Rewrite using `[psi_inclE, map_mul, map_mul, map_inv₀, map_inv₀]`. Break down `hw w hw' with rfl | rfl` into its components or cases. Conclude with `inv_mul_le_one_of_le₀ (le_val_pi h2 (val_lt_one hi)) zero_le'`.

Rewrite using `[val_eq_one h3, inv_one, one_mul]`. Conclude with `val_le_one _ _`. Use `hk ((⟨_, hm⟩ : intV E v) • s) _ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Use `show ι (algebraMap (𝓞 E) E i) * s.1 j = ι (algebraMap (𝓞 E) E π) * (ι _ * s.1 j)`.

Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel_left₀ hπ0]`. Establish `e : s = kap F v (y * cO E π) • s + kap F v i • s`. Rewrite using `[← add_smul, ← map_add, hyi, map_one, one_smul]`. Rewrite using `[e, map_add, hA, hB, add_zero]`.
-/
theorem fT_kill (hLb : IsBase S π) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    (r : Fin n) (hr : r.1 + 1 = n)
    (s : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)))
    (hs : Valued.v (psi v P hP (s.1 r)) < 1) : S.fT v hv s = 0 := by
  classical
  have hπ0 : (algebraMap (𝓞 E) E π) ≠ 0 := fun h => h3 (by
    have : π = 0 := RingOfIntegers.ext h
    rw [this]; exact zero_mem _)
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = r := fun j =>
    ⟨fun h => Fin.ext (by omega), fun h => h ▸ hr⟩
  obtain ⟨y, i, hi, hyi⟩ : ∃ y, ∃ i ∈ P.asIdeal, y * cO E π + i = 1 := P.isMaximal.exists_inv h3

  have hA : S.fT v hv (kap F v (y * cO E π) • s) = 0 := by
    refine S.fT_L v hv _ ?_
    have hc2 := (coord_of_mem (v := v) hLb s.2 r).2 hr
    have hu : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E (y * cO E π)) * s.1 r ∈ intV E v := by
      refine (mem_intV_iff v _).2 fun w hw' => ?_
      rcases hw w hw' with rfl | rfl
      · have e : psi v w hw' = psi v w hP := rfl
        rw [map_mul, psi_inclE, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, e, mul_assoc]
        refine inv_mul_le_one_of_le₀ ?_ zero_le'
        calc _ ≤ Valued.v (psi v w hP (s.1 r)) := mul_le_of_le_one_left' (val_le_one _ _)
          _ ≤ _ := le_val_pi h2 hs
      · have h4 := (mem_intV_iff v _).1 hc2 _ hw'
        have e : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E (y * cO E π)) * s.1 r =
            ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E y) * (ι (star (algebraMap (𝓞 E) E π)) * s.1 r) := by
          rw [← mul_assoc, ← map_mul, map_mul (algebraMap (𝓞 E) E) y, algebraMap_cO, mul_assoc]
        rw [e, map_mul, map_mul, psi_inclE, map_mul, map_mul, map_inv₀, map_inv₀, val_eq_one h3, inv_one, one_mul]
        exact mul_le_one' (val_le_one _ _) h4
    have hjm : ∀ j, ι (algebraMap (𝓞 E) E (y * cO E π)) * s.1 j ∈ intV E v ∨ j = r := fun j => by
      by_cases hj : j = r
      · exact Or.inr hj
      · exact Or.inl (mul_mem (incl_mem_intV v _) ((coord_of_mem (v := v) hLb s.2 j).1 fun h => hj ((hlast j).1 h)))
    refine mem_latS_of_coords (S := S) (fun j => if hj : j = r then ⟨_, hu⟩ else ⟨_, (hjm j).resolve_right hj⟩)
      (fun j => if j = r then π else 1) (fun j => single_mem_Lb hLb j _ fun h => ?_) fun j => ?_
    · rw [if_pos ((hlast j).1 h)]
    · by_cases hj : j = r
      · subst hj
        simp only [dif_pos, if_pos]
        show ι _ * s.1 j = ι _ * s.1 j * ι _
        rw [mul_right_comm, ← map_mul, mul_right_comm, inv_mul_cancel₀ hπ0, one_mul]
      · simp only [dif_neg hj, if_neg hj, map_one, mul_one]
        rfl

  have hB : S.fT v hv (kap F v i • s) = 0 := by
    have hm : ι ((algebraMap (𝓞 E) E π)⁻¹ * algebraMap (𝓞 E) E i) ∈ intV E v := by
      refine (mem_intV_iff v _).2 fun w hw' => ?_
      rw [psi_inclE, map_mul, map_mul, map_inv₀, map_inv₀]
      rcases hw w hw' with rfl | rfl
      · exact inv_mul_le_one_of_le₀ (le_val_pi h2 (val_lt_one hi)) zero_le'
      · rw [val_eq_one h3, inv_one, one_mul]
        exact val_le_one _ _
    refine hk ((⟨_, hm⟩ : intV E v) • s) _ ?_
    funext j
    show ι (algebraMap (𝓞 E) E i) * s.1 j = ι (algebraMap (𝓞 E) E π) * (ι _ * s.1 j)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel_left₀ hπ0]
  have e : s = kap F v (y * cO E π) • s + kap F v i • s := by
    rw [← add_smul, ← map_add, hyi, map_one, one_smul]
  rw [e, map_add, hA, hB, add_zero]

/- English proof (translation)
Simplify using `[ee]`.
-/
theorem ee_self (r : Fin n) : ee n F E v r r = 1 := by
  simp [ee]

/- English proof (translation)
Simplify using `[ee, Pi.single_apply, h.symm]`.
-/
theorem ee_ne {j r : Fin n} (h : j ≠ r) : ee n F E v j r = 0 := by
  simp [ee, Pi.single_apply, h.symm]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_conjP, mem_conjP, cO_cO])`.
-/
theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_conjP, mem_conjP, cO_cO])

/- English proof (translation)
Assume the negation of the conclusion as `hdn`. Take `⟨y, i, hi, hyi⟩` from `P.isMaximal.exists_inv hdn`. Apply `hm` to reduce the goal to its premises. Establish `e : κ (y * d + i) • m = m` using `by rw [hyi, map_one, one_smul]`. Rewrite using `[← e, map_add, add_smul, map_mul, mul_smul, hd, smul_zero, hP i hi, zero_add]`.
-/
theorem mem_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (κ : 𝓞 E →+* A) {m : M} (hm : m ≠ 0)
    (hP : ∀ i ∈ P.asIdeal, κ i • m = 0) {d : 𝓞 E} (hd : κ d • m = 0) : d ∈ P.asIdeal := by
  by_contra hdn
  obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hdn
  apply hm
  have e : κ (y * d + i) • m = m := by rw [hyi, map_one, one_smul]
  rw [← e, map_add, add_smul, map_mul, mul_smul, hd, smul_zero, hP i hi, zero_add]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `kill` using `fT_kill hLb hv hP hw h2 h3 hk r hr`. Take `⟨eL, heL⟩ : ∃ e : latS (F` from `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), e.1 = ee n F E v r := ⟨⟨ee n F E v r, ee_mem hLb r⟩, rfl⟩`. Establish `key : ∀ (t : latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) (c : 𝓞 E), Valued.v (psi v P hP (t.1 r) - algebraMap E _ (algebraMap (𝓞 E) E c)) < 1 → S.fT v hv t = kap F v c • S.fT v hv eL := by`. Introduce `t c h`. Establish `e` using `kill (t - kap F v c • eL) (by`.

Establish `e1 : (t - kap F v c • eL).1 r = t.1 r - Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (algebraMap (𝓞 E) E c) := by show t.1 r - Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E c) * eL.1 r = _`. Rewrite using `[heL, ee_self, mul_one]`. Rewrite using `[e1, map_sub, psi_inclE]`. Conclude with `h)`. Rewrite `e` using `[map_sub, map_smul, sub_eq_zero]`.

Conclude with `e`. Establish `hne0 : S.fT v hv eL ≠ 0`. Introduce `h0`. Apply `S.fT_ne v hv` to reduce the goal to its premises. Use `LinearMap.ext fun t => ?_` and prove the remaining obligations.

Take `⟨y, hy⟩ : ∃ y, prV (E` from `E) v y = t.1 r := ⟨_, Formalism.UG.P.afsplit_prV_IE v _⟩`. Establish `hvz : Valued.v (adAt F P y) ≤ 1`. Rewrite using `[← psi_prV v P hP, hy]`. Conclude with `val_coord_le hLb hP h3 t.2 r`. Take `⟨c, hc'⟩` from `exists_res P y hvz`.

Rewrite using `[key t c (by rw [← hy, psi_prV]; exact hc'), h0, smul_zero, LinearMap.zero_apply]`. Establish `hker : ∀ i ∈ P.asIdeal, kap F v i • S.fT v hv eL = 0`. Introduce `i hi`. Rewrite using `[← map_smul]`. Use `kill _ ?_` and prove the remaining obligations.

Establish `e2 : (kap F v i • eL).1 r = Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (algebraMap (𝓞 E) E i) := by show Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E i) * eL.1 r = _`. Rewrite using `[heL, ee_self, mul_one]`. Rewrite using `[e2, psi_inclE]`. Conclude with `val_lt_one hi`. Establish `hdiv : ∀ d : 𝓞 E, kap F v d • S.fT v hv eL = 0 → d ∈ P.asIdeal` using `fun d hd => mem_of_smul_eq_zero (kap F v) hne0 hker hd`.

Take `⟨ej, hej⟩ : ∃ e : latS (F` from `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), e.1 = ee n F E v j := ⟨⟨ee n F E v j, ee_mem hLb j⟩, rfl⟩`. Take `⟨x, hx1⟩ : ∃ x : latS (F` from `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), x.1 = g'.1 *ᵥ ee n F E v j := ⟨⟨g'.1 *ᵥ ee n F E v j, (hg' _).1 (ee_mem hLb j)⟩, rfl⟩`. Establish `hx` using `hfun x`. Establish `e2 : (⟨g.1 *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) = ej := by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show g.1 *ᵥ x.1 = ej.1`. Rewrite using `[hx1, hej, Matrix.mulVec_mulVec, ← Units.val_mul, hgg, Units.val_one, Matrix.one_mulVec]`. Rewrite `hx` using `[e2]`. Take `⟨c, hc'⟩` from `exists_res P z hzv`. Establish `hfx : S.fT v hv x = kap F v c • S.fT v hv eL` using `key x c (by`.

Establish `e3 : x.1 r = prV (E` using `E) v z := by rw [hx1, mulVec_ee, hz]`. Rewrite using `[e3, psi_prV]`. Conclude with `hc')`. Use `⟨c, ?_, hc'⟩` and prove the remaining obligations. Distinguish the cases in `hjr : j = r`.

Substitute `hjr` using the available equality. Rewrite using `[if_pos rfl]`. Establish `hee : ej = eL` using `Subtype.ext (hej.trans heL.symm)`. Establish `e4 : kap F v (c - (a : 𝓞 E)) • S.fT v hv eL = 0`. Rewrite using `[map_sub, sub_smul, ← hfx, ← hx, hee, map_intCast, Int.cast_smul_eq_zsmul, sub_self]`.

Establish `e5` using `hdiv _ e4`. Rewrite using `[← map_intCast (Ideal.Quotient.mk P.asIdeal) a]`. Conclude with `Ideal.Quotient.eq.2 e5`. Rewrite using `[if_neg hjr]`. Establish `e6` using `kill ej (by`.

Rewrite using `[hej, ee_ne hjr, map_zero]`. Use the proof step `simp)`. Rewrite `hx` using `[e6, smul_zero, hfx]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hdiv c hx.symm)`.
-/
theorem last_row (hLb : IsBase S π) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hP : P.under (𝓞 F) = v)
    (hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (h2 : π ∉ P.asIdeal ^ 2) (h3 : π ∉ (conjPrime₂ P).asIdeal)
    (hk : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)),
      t'.1 = Formalism.UG.inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0)
    {g g' : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))))
    (hg' : g' ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))))
    (hgg : g * g' = 1) {a : ℤ}
    (hfun : ∀ x : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)),
      a • S.fT v hv ⟨g.1 *ᵥ x.1, (hg x.1).1 x.2⟩ = S.fT v hv x)
    (r j : Fin n) (hr : r.1 + 1 = n) (z : AfE F E) (hz : prV (E := E) v z = g'.1 r j)
    (hzv : Valued.v (adAt F P z) ≤ 1) :
    HasRes P (adAt F P z) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  have kill := fT_kill hLb hv hP hw h2 h3 hk r hr
  obtain ⟨eL, heL⟩ : ∃ e : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), e.1 = ee n F E v r :=
    ⟨⟨ee n F E v r, ee_mem hLb r⟩, rfl⟩
  have key : ∀ (t : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) (c : 𝓞 E),
      Valued.v (psi v P hP (t.1 r) - algebraMap E _ (algebraMap (𝓞 E) E c)) < 1 →
      S.fT v hv t = kap F v c • S.fT v hv eL := by
    intro t c h
    have e := kill (t - kap F v c • eL) (by
      have e1 : (t - kap F v c • eL).1 r = t.1 r - Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E c) := by
        show t.1 r - Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E c) * eL.1 r = _
        rw [heL, ee_self, mul_one]
      rw [e1, map_sub, psi_inclE]
      exact h)
    rw [map_sub, map_smul, sub_eq_zero] at e
    exact e
  have hne0 : S.fT v hv eL ≠ 0 := by
    intro h0
    apply S.fT_ne v hv
    refine LinearMap.ext fun t => ?_
    obtain ⟨y, hy⟩ : ∃ y, prV (E := E) v y = t.1 r := ⟨_, Formalism.UG.P.afsplit_prV_IE v _⟩
    have hvz : Valued.v (adAt F P y) ≤ 1 := by
      rw [← psi_prV v P hP, hy]
      exact val_coord_le hLb hP h3 t.2 r
    obtain ⟨c, hc'⟩ := exists_res P y hvz
    rw [key t c (by rw [← hy, psi_prV]; exact hc'), h0, smul_zero, LinearMap.zero_apply]
  have hker : ∀ i ∈ P.asIdeal, kap F v i • S.fT v hv eL = 0 := by
    intro i hi
    rw [← map_smul]
    refine kill _ ?_
    have e2 : (kap F v i • eL).1 r = Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E i) := by
      show Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E i) * eL.1 r = _
      rw [heL, ee_self, mul_one]
    rw [e2, psi_inclE]
    exact val_lt_one hi
  have hdiv : ∀ d : 𝓞 E, kap F v d • S.fT v hv eL = 0 → d ∈ P.asIdeal := fun d hd =>
    mem_of_smul_eq_zero (kap F v) hne0 hker hd
  obtain ⟨ej, hej⟩ : ∃ e : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), e.1 = ee n F E v j :=
    ⟨⟨ee n F E v j, ee_mem hLb j⟩, rfl⟩
  obtain ⟨x, hx1⟩ : ∃ x : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)), x.1 = g'.1 *ᵥ ee n F E v j :=
    ⟨⟨g'.1 *ᵥ ee n F E v j, (hg' _).1 (ee_mem hLb j)⟩, rfl⟩
  have hx := hfun x
  have e2 : (⟨g.1 *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) = ej := by
    apply Subtype.ext
    show g.1 *ᵥ x.1 = ej.1
    rw [hx1, hej, Matrix.mulVec_mulVec, ← Units.val_mul, hgg, Units.val_one, Matrix.one_mulVec]
  rw [e2] at hx
  obtain ⟨c, hc'⟩ := exists_res P z hzv
  have hfx : S.fT v hv x = kap F v c • S.fT v hv eL := key x c (by
    have e3 : x.1 r = prV (E := E) v z := by rw [hx1, mulVec_ee, hz]
    rw [e3, psi_prV]
    exact hc')
  refine ⟨c, ?_, hc'⟩
  by_cases hjr : j = r
  · subst hjr
    rw [if_pos rfl]
    have hee : ej = eL := Subtype.ext (hej.trans heL.symm)
    have e4 : kap F v (c - (a : 𝓞 E)) • S.fT v hv eL = 0 := by
      rw [map_sub, sub_smul, ← hfx, ← hx, hee, map_intCast, Int.cast_smul_eq_zsmul, sub_self]
    have e5 := hdiv _ e4
    rw [← map_intCast (Ideal.Quotient.mk P.asIdeal) a]
    exact Ideal.Quotient.eq.2 e5
  · rw [if_neg hjr]
    have e6 := kill ej (by
      rw [hej, ee_ne hjr, map_zero]
      simp)
    rw [e6, smul_zero, hfx] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv c hx.symm)

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n T f bad J S π P v hv a δ hJ hP hw h1 h2 h3 hLb0 hk hD`. Substitute `hJ` using the available equality. Establish `hLb : IsBase S π` using `hLb0`. Take `⟨hoff, -, hg, hfun⟩` from `hD`. Establish `hg' : bc (prV (E` using `E) v) δ.1⁻¹ ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) := by`.

Rewrite using `[map_inv]`. Conclude with `inv_mem hg`. Establish `eP : ∀ i j, Valued.v (adAt F P (δ.1.1 i j)) ≤ 1` using `fun i j => by`. Establish `h` using `val_entry_le hLb hP h3 hg i j`. Rewrite `h` using `[show ((bc (prV (E := E) v) δ.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j = prV (E := E) v (δ.1.1 i j) from rfl, psi_prV]`.

Conclude with `h`. Establish `eP' : ∀ i j, Valued.v (adAt F P ((δ.1⁻¹).1 i j)) ≤ 1` using `fun i j => by`. Establish `h` using `val_entry_le hLb hP h3 hg' i j`. Rewrite `h` using `[show ((bc (prV (E := E) v) δ.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j = prV (E := E) v ((δ.1⁻¹).1 i j) from rfl, psi_prV]`. Conclude with `h`.

Establish `off : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w (δ.1.1 i j) = if i = j then 1 else 0` using `fun w hwv i j => adAt_of_bc_eq_one _ w (hoff _ hwv) i j`. Establish `off' : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0` using `fun w hwv i j => adAt_of_bc_eq_one _ w (by rw [map_inv, hoff _ hwv, inv_one]) i j`. Establish `hQ : ∀ Q ∈ ({P} : Finset (HeightOneSpectrum (𝓞 E))), conjPrime₂ Q ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E)))`. Introduce `Q hQ hQ'`. Rewrite `hQ`, `hQ'` using `[Finset.mem_singleton]`.

Substitute `hQ` using the available equality. Conclude with `h3 (by rw [hQ']; exact h1)`. Establish `hi1 : ∀ w, conjPrime₂ w ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E))) → ∀ i j, Valued.v (adAt F w (δ.1.1 i j)) ≤ 1`. Introduce `w hcw i j`. Distinguish the cases in `hwv : w.under (𝓞 F) = v`.

Break down `hw w hwv with rfl | rfl` into its components or cases. Conclude with `eP i j`. Conclude with `absurd (Finset.mem_singleton.2 (conjP_conjP' P)) hcw`. Apply the tactic sequence `rw [off w hwv] split_ifs <;> simp`. Establish `hi2 : ∀ w, conjPrime₂ w ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E))) → ∀ i j, Valued.v (adAt F w ((δ.1⁻¹).1 i j)) ≤ 1`.

Introduce `w hcw i j`. Distinguish the cases in `hwv : w.under (𝓞 F) = v`. Break down `hw w hwv with rfl | rfl` into its components or cases. Conclude with `eP' i j`. Conclude with `absurd (Finset.mem_singleton.2 (conjP_conjP' P)) hcw`.

Apply the tactic sequence `rw [off' w hwv] split_ifs <;> simp`. Establish `hU : δ.1 ∈ UAd hc n` using `δ.2`. Use `⟨PtExist.int_of_uni hQ hU hi1 hi2, PtExist.int_of_uni hQ (inv_mem hU) hi2 (by rwa [inv_inv]), off', fun r j hr => ?_⟩` and prove the remaining obligations. Conclude with `last_row hLb hv hP hw h2 h3 hk hg hg' (by rw [← map_mul, mul_inv_cancel, map_one]) hfun r j hr _ rfl (eP' r j)`.
-/
theorem dia_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  intro F E _ _ _ _ _ _ hc n T f bad J S π P v hv a δ hJ hP hw h1 h2 h3 hLb0 hk hD
  subst hJ
  have hLb : IsBase S π := hLb0
  obtain ⟨hoff, -, hg, hfun⟩ := hD
  have hg' : bc (prV (E := E) v) δ.1⁻¹ ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb))) := by
    rw [map_inv]; exact inv_mem hg
  have eP : ∀ i j, Valued.v (adAt F P (δ.1.1 i j)) ≤ 1 := fun i j => by
    have h := val_entry_le hLb hP h3 hg i j
    rw [show ((bc (prV (E := E) v) δ.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j =
      prV (E := E) v (δ.1.1 i j) from rfl, psi_prV] at h
    exact h
  have eP' : ∀ i j, Valued.v (adAt F P ((δ.1⁻¹).1 i j)) ≤ 1 := fun i j => by
    have h := val_entry_le hLb hP h3 hg' i j
    rw [show ((bc (prV (E := E) v) δ.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j =
      prV (E := E) v ((δ.1⁻¹).1 i j) from rfl, psi_prV] at h
    exact h
  have off : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j,
      adAt F w (δ.1.1 i j) = if i = j then 1 else 0 := fun w hwv i j =>
    adAt_of_bc_eq_one _ w (hoff _ hwv) i j
  have off' : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j,
      adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0 := fun w hwv i j =>
    adAt_of_bc_eq_one _ w (by rw [map_inv, hoff _ hwv, inv_one]) i j
  have hQ : ∀ Q ∈ ({P} : Finset (HeightOneSpectrum (𝓞 E))), conjPrime₂ Q ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E))) := by
    intro Q hQ hQ'
    rw [Finset.mem_singleton] at hQ hQ'
    subst hQ
    exact h3 (by rw [hQ']; exact h1)
  have hi1 : ∀ w, conjPrime₂ w ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E))) → ∀ i j, Valued.v (adAt F w (δ.1.1 i j)) ≤ 1 := by
    intro w hcw i j
    by_cases hwv : w.under (𝓞 F) = v
    · rcases hw w hwv with rfl | rfl
      · exact eP i j
      · exact absurd (Finset.mem_singleton.2 (conjP_conjP' P)) hcw
    · rw [off w hwv]
      split_ifs <;> simp
  have hi2 : ∀ w, conjPrime₂ w ∉ ({P} : Finset (HeightOneSpectrum (𝓞 E))) → ∀ i j, Valued.v (adAt F w ((δ.1⁻¹).1 i j)) ≤ 1 := by
    intro w hcw i j
    by_cases hwv : w.under (𝓞 F) = v
    · rcases hw w hwv with rfl | rfl
      · exact eP' i j
      · exact absurd (Finset.mem_singleton.2 (conjP_conjP' P)) hcw
    · rw [off' w hwv]
      split_ifs <;> simp
  have hU : δ.1 ∈ UAd hc n := δ.2
  refine ⟨PtExist.int_of_uni hQ hU hi1 hi2, PtExist.int_of_uni hQ (inv_mem hU) hi2 (by rwa [inv_inv]), off', fun r j hr => ?_⟩
  exact last_row hLb hv hP hw h2 h3 hk hg hg' (by rw [← map_mul, mul_inv_cancel, map_one]) hfun r j hr _ rfl (eP' r j)

end GlobalTheory.Mem.Dil
