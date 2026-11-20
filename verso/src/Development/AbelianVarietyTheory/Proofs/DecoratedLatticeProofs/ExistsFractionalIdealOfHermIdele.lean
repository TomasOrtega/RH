import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

local notation "ZF" => Af D.host.F ⊗[D.host.F] D.host.E

/- English proof (translation)
The claim follows from `GlobalTheory.FinPl.Conductor.tmul_mem (fun v => by rw [map_one]; exact one_mem _) o`.
-/
theorem one_tmul_mem (o : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  GlobalTheory.FinPl.Conductor.tmul_mem (fun v => by rw [map_one]; exact one_mem _) o

/- English proof (translation)
Establish `h : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[← h]`.

Conclude with `(GlobalTheory.SplitDec.int_iff (incA D e)).trans (GlobalTheory.SplitDec.rat_int_iff e)`.
-/
theorem one_tmul_mem_iff (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] e ∈ intAE D ↔ e ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have h : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [← h]
  exact (GlobalTheory.SplitDec.int_iff (incA D e)).trans (GlobalTheory.SplitDec.rat_int_iff e)

/- English proof (translation)
Take `⟨x, u, hu, rfl⟩` from `GlobalTheory.FinPl.Conductor.approx y`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) x`. Establish `hb0 : (b : D.host.E) ≠ 0`. Use `nonZeroDivisors.ne_zero hb` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Use `⟨b, nonZeroDivisors.ne_zero hb, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `add_mem ?_ (GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem b) hu)` and prove the remaining obligations. Establish `e : (b : D.host.E) * x = (a : D.host.E)`. Rewrite using `[← hab]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `one_tmul_mem a`.
-/
theorem exists_int_mul (y : ZF) : ∃ N : 𝓞 D.host.E, N ≠ 0 ∧
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y ∈ intAE D := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.FinPl.Conductor.approx y
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  refine add_mem ?_ (GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem b) hu)
  have e : (b : D.host.E) * x = (a : D.host.E) := by
    rw [← hab]; field_simp
  rw [e]
  exact one_tmul_mem a

/- English proof (translation)
Establish `hN' : (N : D.host.E) ≠ 0` using `by exact_mod_cast hN`. Take `⟨x, u, hu, e⟩` from `GlobalTheory.FinPl.Conductor.approx (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z)`. Use `⟨N * x, u, hu, ?_⟩` and prove the remaining obligations. Establish `h1 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) = 1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hN']`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem approx_mul (z : ZF) {N : 𝓞 D.host.E} (hN : N ≠ 0) : ∃ x : D.host.E, ∃ u ∈ intAE D,
    z = (1 : Af D.host.F) ⊗ₜ[D.host.F] x + ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u := by
  have hN' : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.FinPl.Conductor.approx
    (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z)
  refine ⟨N * x, u, hu, ?_⟩
  have h1 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hN']; rfl
  calc z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z) := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.SeeSaw.IdeleIdeal

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

def subOf (y : Af D.host.F ⊗[D.host.F] D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {d | y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D}
  add_mem' {a b} ha hb := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a + b)) ∈ intAE D
    rw [TensorProduct.tmul_add, mul_add]; exact add_mem ha hb
  zero_mem' := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (0 : D.host.E)) ∈ intAE D
    rw [TensorProduct.tmul_zero, mul_zero]; exact zero_mem _
  smul_mem' c d hd := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) ∈ intAE D
    have e : y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) =
        ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
      rw [Algebra.smul_def, ← mul_assoc, mul_comm _ y, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem c) hd

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_subOf {y : Af D.host.F ⊗[D.host.F] D.host.E} {d : D.host.E} :
    d ∈ subOf y ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

/- English proof (translation)
Take `⟨N, hN, hNy⟩` from `exists_int_mul y'`. Use `⟨N, mem_nonZeroDivisors_of_ne_zero hN, fun d hd => ?_⟩` and prove the remaining obligations. Establish `e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • d) = (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y') * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d))`. Rewrite using `[mul_assoc, ← mul_assoc y', h, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]`. Use `GlobalTheory.FinPl.Conductor.mul_mem_int hNy (mem_subOf.1 hd)` as an intermediate fact.

Rewrite `this` using `[← e, one_tmul_mem_iff, Submodule.mem_one]`. Take `⟨r, hr⟩` from `this`. Conclude with `⟨r, hr⟩`.
-/
theorem isFractional_subOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) :
    IsFractional (𝓞 D.host.E)⁰ (subOf y) := by
  obtain ⟨N, hN, hNy⟩ := exists_int_mul y'
  refine ⟨N, mem_nonZeroDivisors_of_ne_zero hN, fun d hd => ?_⟩
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • d) =
      (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y') * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
    rw [mul_assoc, ← mul_assoc y', h, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  have := GlobalTheory.FinPl.Conductor.mul_mem_int hNy (mem_subOf.1 hd)
  rw [← e, one_tmul_mem_iff, Submodule.mem_one] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr⟩

def idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) : FI D := ⟨subOf y, isFractional_subOf h⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) {d : D.host.E} :
    d ∈ idealOf h ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

end GlobalTheory.SeeSaw.IdeleIdeal

open GlobalTheory.SeeSaw.IdeleIdeal GlobalTheory.FinPlLoc in

/- English proof (translation)
Introduce `D m`. Use `set mi := finPart D ((m⁻¹ : (AE D)ˣ) : AE D) with hmi`. Use `set mf := finPart D (m : AE D) with hmf`. Establish `hmm : mf * mi = 1`. Rewrite using `[hmf, hmi, ← map_mul, Units.mul_inv, map_one]`.

Use `⟨idealOf hmm, fun x a ha => ?_⟩` and prove the remaining obligations. Establish `hmemA : ∀ d : D.host.E, d ∈ (idealOf hmm) ↔ mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D` using `fun d => mem_idealOf hmm`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use `⟨Ideal.mul_mem_left _ _ ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← hmi]`. Use `clear ha`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, -, d, hd, rfl⟩` from `hy`.

Rewrite using `[finPart_pair]`. Establish `e : mi * (α ⊗ₜ[D.host.F] d) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d))`. Rewrite using `[mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[e]`. Establish `h1 : α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D`.

Simplify using `using GlobalTheory.FinPl.Conductor.tmul_mem hα (1 : 𝓞 D.host.E)`. Conclude with `GlobalTheory.FinPl.Conductor.mul_mem_int h1 ((hmemA d).1 hd)`. Consider the case `zero => rw [map_zero, mul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add, mul_add]`.

Conclude with `add_mem hy hz`. Consider the case `neg y _ hy => rw [map_neg, mul_neg]`. Conclude with `neg_mem hy`. Introduce `hi`. Establish `hz : mi * finPart D a ∈ intAE D`.

Use `hi.2` as an intermediate fact. Rewrite `this` using `[map_mul, ← hmi]`. Then use the resulting hypothesis. Take `⟨N, hN, hNm⟩` from `exists_int_mul mi`. Take `⟨d, u, hu, e⟩` from `approx_mul (finPart D a) hN`. Establish `hd : d ∈ (idealOf hmm)`.

Rewrite using `[hmemA]`. Establish `e2 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) = mi * finPart D a - (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * u`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `sub_mem hz (GlobalTheory.FinPl.Conductor.mul_mem_int hNm hu)`. Establish `hidem : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a` using `GlobalTheory.FinPl.Conductor.idem_mul x _ fun w hw => (Submodule.mem_iInf _).1 (Ideal.mem_inf.1 ha).2 ⟨w, hw⟩`. Establish `hε : singleV D.host.F x 1 ∈ intAf D.host.F`. Use `GlobalTheory.FinPl.Conductor.idem_mul_mem (v := x) (α := 1) (by rw [map_one]; exact one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.

Establish `hsupp : ∀ (β : Af D.host.F) w, w ≠ x → evalV D.host.F w (singleV D.host.F x 1 * β) = 0` using `fun β w hw => by`. Rewrite using `[map_mul, GlobalTheory.FinPl.Conductor.ev_ne hw, zero_mul]`. Establish `hrest : ∀ u ∈ intAE D, finIn D ((singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u)) ∈ idV (idealOf hmm) x`. Introduce `u hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨β, hβ, o, rfl⟩` from `hy`. Establish `e3 : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * (β ⊗ₜ[D.host.F] (o : D.host.E))) = (singleV D.host.F x 1 * β) ⊗ₜ[D.host.F] ((N : D.host.E) * o)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]`. Rewrite using `[e3, finIn_tmul]`.

Use `AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.Conductor.idem_mul_mem (hβ x), hsupp β, _, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hmemA]`. Establish `e4 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * o)) = (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))`. Rewrite using `[mul_comm _ mi, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[e4]`.

Conclude with `GlobalTheory.FinPl.Conductor.mul_mem_int hNm (one_tmul_mem o)`. Consider the case `zero => rw [mul_zero, mul_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [mul_add, mul_add, map_add]`. Conclude with `add_mem hy hz`.

Consider the case `neg y _ hy => rw [mul_neg, mul_neg, map_neg]`. Conclude with `neg_mem hy`. Rewrite using `[eq_finIn (infPart_of_idAt ha), ← hidem, e, mul_add, map_add]`. Use `add_mem ?_ (hrest u hu)` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, finIn_tmul]`.

Conclude with `AddSubgroup.subset_closure ⟨_, hε, fun w hw => GlobalTheory.FinPl.Conductor.ev_ne hw, d, hd, rfl⟩`.
-/
theorem GlobalTheory.SeeSaw.exists_idealOfIdele : ∀ (D : D7) (m : (AE D)ˣ), ∃ 𝔞 : FI D, ∀ x : Pl D, ∀ a ∈ idAt D (· = x),
    a ∈ idV 𝔞 x ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D m
  set mi := finPart D ((m⁻¹ : (AE D)ˣ) : AE D) with hmi
  set mf := finPart D (m : AE D) with hmf
  have hmm : mf * mi = 1 := by
    rw [hmf, hmi, ← map_mul, Units.mul_inv, map_one]
  refine ⟨idealOf hmm, fun x a ha => ?_⟩
  have hmemA : ∀ d : D.host.E, d ∈ (idealOf hmm) ↔
      mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := fun d => mem_idealOf hmm
  constructor
  · intro hv
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [map_mul, ← hmi]
    clear ha
    induction hv using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, -, d, hd, rfl⟩ := hy
      rw [finPart_pair]
      have e : mi * (α ⊗ₜ[D.host.F] d) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
        rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      have h1 : α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D := by
        simpa using GlobalTheory.FinPl.Conductor.tmul_mem hα (1 : 𝓞 D.host.E)
      exact GlobalTheory.FinPl.Conductor.mul_mem_int h1 ((hmemA d).1 hd)
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, mul_neg]; exact neg_mem hy
  · intro hi
    have hz : mi * finPart D a ∈ intAE D := by
      have := hi.2
      rwa [map_mul, ← hmi] at this
    obtain ⟨N, hN, hNm⟩ := exists_int_mul mi
    obtain ⟨d, u, hu, e⟩ := approx_mul (finPart D a) hN
    have hd : d ∈ (idealOf hmm) := by
      rw [hmemA]
      have e2 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) =
          mi * finPart D a - (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * u := by
        rw [e]; ring
      rw [e2]
      exact sub_mem hz (GlobalTheory.FinPl.Conductor.mul_mem_int hNm hu)
    have hidem : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
      GlobalTheory.FinPl.Conductor.idem_mul x _ fun w hw => (Submodule.mem_iInf _).1 (Ideal.mem_inf.1 ha).2 ⟨w, hw⟩
    have hε : singleV D.host.F x 1 ∈ intAf D.host.F := by
      have := GlobalTheory.FinPl.Conductor.idem_mul_mem (v := x) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    have hsupp : ∀ (β : Af D.host.F) w, w ≠ x → evalV D.host.F w (singleV D.host.F x 1 * β) = 0 := fun β w hw => by
      rw [map_mul, GlobalTheory.FinPl.Conductor.ev_ne hw, zero_mul]

    have hrest : ∀ u ∈ intAE D, finIn D ((singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u)) ∈ idV (idealOf hmm) x := by
      intro u hu
      induction hu using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨β, hβ, o, rfl⟩ := hy
        have e3 : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * (β ⊗ₜ[D.host.F] (o : D.host.E))) =
            (singleV D.host.F x 1 * β) ⊗ₜ[D.host.F] ((N : D.host.E) * o) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
        rw [e3, finIn_tmul]
        refine AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.Conductor.idem_mul_mem (hβ x), hsupp β, _, ?_, rfl⟩
        rw [hmemA]
        have e4 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * o)) =
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) := by
          rw [mul_comm _ mi, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e4]
        exact GlobalTheory.FinPl.Conductor.mul_mem_int hNm (one_tmul_mem o)
      | zero => rw [mul_zero, mul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add, mul_add, map_add]; exact add_mem hy hz
      | neg y _ hy => rw [mul_neg, mul_neg, map_neg]; exact neg_mem hy
    rw [eq_finIn (infPart_of_idAt ha), ← hidem, e, mul_add, map_add]
    refine add_mem ?_ (hrest u hu)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, finIn_tmul]
    exact AddSubgroup.subset_closure ⟨_, hε, fun w hw => GlobalTheory.FinPl.Conductor.ev_ne hw, d, hd, rfl⟩
