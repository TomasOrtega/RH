import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasureImageCosets
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def lamA (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def lamP (a : ℕ) (ϖ : Fv F v) : AddSubgroup (TupV (E := E) v n a) :=
  (lamA v Λ a).map (DistribMulAction.toAddMonoidHom (TupV (E := E) v n a) (sc (E := E) v ϖ))

def clsU (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_add_smul (s : Fv F v ⊗[F] E) (x z y w : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + s • z) (y + s • w) = hR (Fv F v) σ J x y + s * hR (Fv F v) σ J x w +
      sigR (Fv F v) σ s * hR (Fv F v) σ J z y + sigR (Fv F v) σ s * s * hR (Fv F v) σ J z w := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[sigR, sc]`.
-/
theorem sigR_sc (x : Fv F v) : sigR (Fv F v) σ (sc (E := E) v x) = sc (E := E) v x := by
  simp [sigR, sc]

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, hϖ]`. Conclude with `(show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by` after adjusting the coercions. Rewrite using `[← ofAdd_zero, Multiplicative.ofAdd_le]`. Use the proof step `norm_num)`.
-/
theorem unif_int {ϖ : Fv F v} (hϖ : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ]
  exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by
    rw [← ofAdd_zero, Multiplicative.ofAdd_le]; norm_num)

/- English proof (translation)
Establish `h` using `(Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).smul_mem (⟨x, hx⟩ : v.adicCompletionIntegers F) hc`. Establish `e : (⟨x, hx⟩ : v.adicCompletionIntegers F) • c = sc (E` using `E) v x * c := by show x • c = sc (E := E) v x * c`. Rewrite using `[Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem sc_mul_mem {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : sc (E := E) v x * c ∈ OEv (E := E) v := by
  have h := (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).smul_mem
    (⟨x, hx⟩ : v.adicCompletionIntegers F) hc
  have e : (⟨x, hx⟩ : v.adicCompletionIntegers F) • c = sc (E := E) v x * c := by
    show x • c = sc (E := E) v x * c
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e] at h
  exact h

/- English proof (translation)
The claim follows from `(Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).add_mem hc hd`.
-/
theorem oev_add {c d : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v) (hd : d ∈ OEv (E := E) v) :
    c + d ∈ OEv (E := E) v :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).add_mem hc hd

/- English proof (translation)
Introduce `i j`. Take `⟨c, hc, hce⟩` from `hN i j`. Establish `hh : ∀ p q : Fin a, ∀ P Q : TupV (E` using `E) v n a, P ∈ LamT v Λ a → Q ∈ LamT v Λ a → hR (Fv F v) σ J (P p) (Q q) ∈ OEv (E := E) v := fun p q P Q hP hQ => (hSD (Q q)).1 (hQ q) (P p) (hP p)`. Establish `hi` using `unif_int v hϖ`. Use `⟨c + (hR (Fv F v) σ J (X i) (Z j) + hR (Fv F v) σ J (Z i) (X j) + sc (E := E) v ϖ * hR (Fv F v) σ J (Z i) (Z j)), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `oev_add v hc (oev_add v (oev_add v (hh i j X Z hX hZ) (hh i j Z X hZ hX)) (sc_mul_mem v hi (hh i j Z Z hZ hZ)))`. Establish `e1 : gramR (Fv F v) σ J (X + sc (E` using `E) v ϖ • Z) i j = hR (Fv F v) σ J (X i + sc (E := E) v ϖ • Z i) (X j + sc (E := E) v ϖ • Z j) := rfl`. Establish `e2 : gramR (Fv F v) σ J X i j = hR (Fv F v) σ J (X i) (X j)` using `rfl`. Rewrite using `[e1, hR_add_smul, sigR_sc]`. Rewrite `hce` using `[e2]`.

Take the linear combination `hce`.
-/
theorem nearT_add {a : ℕ} (hSD : IsSDLoc σ J v Λ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ)
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (X Z : TupV (E := E) v n a)
    (hX : X ∈ LamT v Λ a) (hZ : Z ∈ LamT v Λ a) (hN : X ∈ NearT v σ J ϖ T) :
    X + sc (E := E) v ϖ • Z ∈ NearT v σ J ϖ T := by
  intro i j
  obtain ⟨c, hc, hce⟩ := hN i j
  have hh : ∀ p q : Fin a, ∀ P Q : TupV (E := E) v n a, P ∈ LamT v Λ a → Q ∈ LamT v Λ a →
      hR (Fv F v) σ J (P p) (Q q) ∈ OEv (E := E) v :=
    fun p q P Q hP hQ => (hSD (Q q)).1 (hQ q) (P p) (hP p)
  have hi := unif_int v hϖ
  refine ⟨c + (hR (Fv F v) σ J (X i) (Z j) + hR (Fv F v) σ J (Z i) (X j) +
      sc (E := E) v ϖ * hR (Fv F v) σ J (Z i) (Z j)), ?_, ?_⟩
  · exact oev_add v hc (oev_add v (oev_add v (hh i j X Z hX hZ) (hh i j Z X hZ hX))
      (sc_mul_mem v hi (hh i j Z Z hZ hZ)))
  · have e1 : gramR (Fv F v) σ J (X + sc (E := E) v ϖ • Z) i j =
        hR (Fv F v) σ J (X i + sc (E := E) v ϖ • Z i) (X j + sc (E := E) v ϖ • Z j) := rfl
    have e2 : gramR (Fv F v) σ J X i j = hR (Fv F v) σ J (X i) (X j) := rfl
    rw [e1, hR_add_smul, sigR_sc]
    rw [e2] at hce
    linear_combination hce

/- English proof (translation)
Introduce `hG hμ ϖ hϖ`. Take `⟨hMA, hL, hP⟩` from `hM hG ϖ hϖ`. Establish `hSD : IsSDLoc σ J v Λ` using `hG.2.2.1`. Establish `ha : a ≤ n` using `hG.2.2.2.2.1`. Establish `hq` using `qv_pos v`.

Use `set μ := dX σ J ψ v a with hμdef`. Establish `: μ.IsAddHaarMeasure`. Rewrite using `[hμdef, dX, dif_pos hμ]`. Conclude with `hμ.choose_spec.1`. Establish `hPL : lamP v Λ a ϖ ≤ lamA v Λ a`.

Introduce and unpack `_ ⟨Z, hZ, rfl⟩ i`. Establish `: (sc (E` using `E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl`. Use `show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ`. Rewrite using `[this]`. Establish `e : sc (E` using `E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by`.

Use extensionality with `p`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `show _ = ϖ • Z i p`. Rewrite using `[Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(latLoc (E := E) v Λ).smul_mem _ (hZ i)`. Establish `hIdx` using `hI hG ϖ hϖ`. Establish `hN0 : Ideal.absNorm v.asIdeal ≠ 0`. Introduce `h0`.

Establish `: qv v = 0` using `by simp [qv, h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0`. Rewrite using `[hIdx]`. Conclude with `pow_ne_zero _ hN0`.

Establish `eL` using `PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin`. Establish `eS` using `measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} (by`. Introduce and unpack `x hx y ⟨Z, hZ, hZe⟩`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[AddSubgroup.coe_add, ← hZe]`.

Conclude with `nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx)`. Establish `himg : ((↑) : lamA v Λ a → TupV (E` using `E) v n a) '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} = LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x.2, hx⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨X, h1⟩, h2, rfl⟩`. Rewrite `eS` using `[himg]`. Establish `eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) * μ (lamP v Λ a ϖ)` using `eL`.

Rewrite using `[eS, eL', ← mul_assoc]`. Use `congr 1`. Establish `hcard` using `hC hG ϖ hϖ`. Express the relevant statement in the definitionally equal form `(Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _`. Rewrite using `[← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]`.

Use `congr 1`. Establish `hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a)`. Simplify using `[qv]`. Rewrite using `[hqv]`. Establish `hle : a ^ 2 ≤ 2 * n * a` using `by nlinarith`.

Establish `e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2)`. Rewrite using `[← pow_add, Nat.sub_add_cancel hle]`. Rewrite using `[e3]`. Establish `e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1`. Rewrite using `[zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]`.

Conclude with `inv_mul_cancel₀ (pow_ne_zero _ hq.ne')`. Take the linear combination `(-(qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a)) * e4`. Establish `hP0 : 0 ≤ prodEta (E` using `E) v n a := by`. Unfold `prodEta`. Use `Finset.prod_nonneg fun j _ => ?_` and prove the remaining obligations.

Establish `hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)`. Conclude with `Nat.one_le_iff_ne_zero.2 hN0` after adjusting the coercions. Establish `habs : |((etaV (E` using `E) v : ℤ) : ℝ)| = 1 := by`. Apply the tactic sequence `unfold etaV; split_ifs <;> norm_num`. Establish `h1 : ((etaV (E` using `E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]`. Use `_ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_nonneg (zpow_nonneg hq.le _) hP0`.
-/
theorem countU_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasU σ J ψ v Λ a Y)
    (hI : IdxU σ J ψ v Λ a Y) (hC : ClsU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  set μ := dX σ J ψ v a with hμdef
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, dX, dif_pos hμ]
    exact hμ.choose_spec.1
  have hPL : lamP v Λ a ϖ ≤ lamA v Λ a := by
    rintro _ ⟨Z, hZ, rfl⟩ i
    have : (sc (E := E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl
    show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ
    rw [this]
    have e : sc (E := E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by
      ext p
      simp only [Pi.smul_apply, smul_eq_mul]
      show _ = ϖ • Z i p
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]
    exact (latLoc (E := E) v Λ).smul_mem _ (hZ i)
  have hIdx := hI hG ϖ hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h0
    have : qv v = 0 := by simp [qv, h0]
    linarith
  have hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0 := by
    rw [hIdx]; exact pow_ne_zero _ hN0
  have eL := PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin
  have eS := measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin
    {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)}
    (by
      rintro x hx y ⟨Z, hZ, hZe⟩
      simp only [Set.mem_setOf_eq]
      rw [AddSubgroup.coe_add, ← hZe]
      exact nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx)
  have himg : ((↑) : lamA v Λ a → TupV (E := E) v n a) ''
      {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X, h1⟩, h2, rfl⟩
  rw [himg] at eS
  have eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) *
      μ (lamP v Λ a ϖ) := eL
  rw [eS, eL', ← mul_assoc]
  congr 1
  have hcard := hC hG ϖ hϖ
  change (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _
  rw [← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a) := by
      simp [qv]
    rw [hqv]
    have hle : a ^ 2 ≤ 2 * n * a := by nlinarith
    have e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e3]
    have e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1 := by
      rw [zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')
    linear_combination (-(qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a)) * e4
  · have hP0 : 0 ≤ prodEta (E := E) v n a := by
      unfold prodEta
      refine Finset.prod_nonneg fun j _ => ?_
      have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
      have habs : |((etaV (E := E) v : ℤ) : ℝ)| = 1 := by
        unfold etaV; split_ifs <;> norm_num
      have h1 : ((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
        calc _ ≤ |((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))| :=
              le_abs_self _
          _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
              rw [abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]
          _ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
      linarith
    exact mul_nonneg (zpow_nonneg hq.le _) hP0

end PI.OmLocU
