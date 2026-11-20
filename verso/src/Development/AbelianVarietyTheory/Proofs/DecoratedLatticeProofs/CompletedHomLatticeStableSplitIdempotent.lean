import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitVac

open GlobalTheory.LatVac NumberField

variable {D : D7}

def finIncl (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finIncl_tmul (β : Af D.host.F) (x : D.host.E) :
    finIncl D (β ⊗ₜ[D.host.F] x) = pairA D.host.F 0 β ⊗ₜ[D.host.F] x := rfl

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul β x => rw [finIncl_tmul]`. Conclude with `infPart_pair β x`. Consider the case `add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz, add_zero]`.
-/
theorem infPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (finIncl D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact infPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz, add_zero]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul β x => rw [finIncl_tmul]`. Conclude with `finPart_pair β x`. Consider the case `add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz]`.
-/
theorem finPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finIncl D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact finPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_parts` to reduce the goal to its premises. Rewrite using `[RingHom.map_sub, hz, infPart_finIncl, sub_zero]`. Rewrite using `[RingHom.map_sub, finPart_finIncl, sub_self]`.
-/
theorem eq_finIncl {z : AE D} (hz : infPart D z = 0) : z = finIncl D (finPart D z) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, hz, infPart_finIncl, sub_zero]
  · rw [RingHom.map_sub, finPart_finIncl, sub_self]

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨β, hβ, x, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨β * α, mul_mem_intAf hβ hα, fun w hw => ?_, a, ha, s, hs, x • t, LT.smul_mem x ht, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hsupp w hw, mul_zero]`.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, finIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, pair_mul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(x : D.host.E) * (a * t i * _) = a * ((x : D.host.E) * t i) * _`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero`. Use `(latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v)).zero_mem using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz`.

Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.add_apply, LinearMap.map_add, add_mul]`. Consider the case `neg y _ hy`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.neg_apply, LinearMap.map_neg, neg_mul]`.
-/
theorem finIncl_mul_mem {S T : HSp D} (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (v : GlobalTheory.FinPl.Pl D)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ LT) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    (Matrix.of fun i j => finIncl D y *
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, x, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨β * α, mul_mem_intAf hβ hα, fun w hw => ?_, a, ha, s, hs, x • t,
      LT.smul_mem x ht, ?_⟩
    · rw [map_mul, hsupp w hw, mul_zero]
    · ext i j
      simp only [Matrix.of_apply, finIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, pair_mul]
      congr 1
      change (x : D.host.E) * (a * t i * _) = a * ((x : D.host.E) * t i) * _
      ring
  | zero =>
    convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v)).zero_mem using 1
    ext i j; simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, LinearMap.map_add, add_mul]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, LinearMap.map_neg, neg_mul]

/- English proof (translation)
Introduce `D k _ _ _ _ q S T LS LT u hu`. Take `⟨ε, ⟨α₀, rfl, h1, h0⟩, hε⟩` from `q.above`. Establish `hee : q.e * q.e = q.e` using `q.split.1`. Establish `hec : q.e * cA D q.e = 0` using `q.split.2.1`. Establish `hεinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α₀)) = 0` using `infPart_pair α₀ 1`.

Establish `hinf : infPart D q.e = 0`. Establish `: q.e = q.e * (q.e + cA D q.e)` using `by rw [mul_add, hee, hec, add_zero]`. Rewrite using `[this, RingHom.map_mul, hε, hεinf, mul_zero]`. Establish `hfin : finPart D q.e ∈ intAE D`. Establish `h` using `q.sec_pr 1`.

Rewrite `h` using `[map_one, mul_one]`. Rewrite using `[← h]`. Conclude with `(q.int_iff 1).1 (one_mem _)`. Establish `he` using `eq_finIncl hinf`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Establish `h` using `finIncl_mul_mem LS LT q.v hα hsupp ha hs ht hfin`. Rewrite `h` using `[← he]`.

Simplify `h` using `only [Matrix.of_apply]`. Consider the case `zero`. Use `(latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v)).zero_mem using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.add_apply, mul_add]`. Consider the case `neg x _ hx`.

Use `neg_mem hx using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.neg_apply, mul_neg]`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`.

Take `⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Introduce `i j`. Establish `hmul : α₀ * α = α`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`.

Express the relevant statement in the definitionally equal form `evalV D.host.F w (α₀ * α) = evalV D.host.F w α`. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = q.v`. Substitute `hw` using the available equality. Rewrite using `[h1, one_mul]`.

Rewrite using `[hsupp w hw, mul_zero]`. Rewrite using `[hε, Matrix.of_apply]`. Express the relevant statement in the definitionally equal form `(pairA D.host.F 0 α₀ ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, pair_mul, hmul]`. Consider the case `zero => intro i j`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro i j`. Rewrite using `[Matrix.add_apply, mul_add, hx, hy]`. Consider the case `neg x _ hx => intro i j`. Rewrite using `[Matrix.neg_apply, mul_neg, hx]`.
-/
theorem idem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  intro D k _ _ _ _ q S T LS LT u hu
  obtain ⟨ε, ⟨α₀, rfl, h1, h0⟩, hε⟩ := q.above
  have hee : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hεinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α₀)) = 0 := infPart_pair α₀ 1
  have hinf : infPart D q.e = 0 := by
    have : q.e = q.e * (q.e + cA D q.e) := by rw [mul_add, hee, hec, add_zero]
    rw [this, RingHom.map_mul, hε, hεinf, mul_zero]
  have hfin : finPart D q.e ∈ intAE D := by
    have h := q.sec_pr 1
    rw [map_one, mul_one] at h
    rw [← h]
    exact (q.int_iff 1).1 (one_mem _)
  have he := eq_finIncl hinf
  refine ⟨?_, ?_⟩
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have h := finIncl_mul_mem LS LT q.v hα hsupp ha hs ht hfin
      rw [← he] at h
      simpa only [Matrix.of_apply] using h
    | zero =>
      convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v)).zero_mem using 1
      ext i j; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
    | neg x _ hx =>
      convert neg_mem hx using 1
      ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have hmul : α₀ * α = α := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α₀ * α) = evalV D.host.F w α
        rw [map_mul]
        by_cases hw : w = q.v
        · subst hw; rw [h1, one_mul]
        · rw [hsupp w hw, mul_zero]
      rw [hε, Matrix.of_apply]
      change (pairA D.host.F 0 α₀ ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pair_mul, hmul]
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; rw [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => intro i j; rw [Matrix.neg_apply, mul_neg, hx]

end GlobalTheory.SplitVac
