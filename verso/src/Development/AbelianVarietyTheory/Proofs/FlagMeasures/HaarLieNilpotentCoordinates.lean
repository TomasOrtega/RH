import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgueStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.SnMass.NEntry

variable {k r : ℕ}

/- English proof (translation)
Establish `hp : ∀ n v, P n ((N ^ n) v)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact fun v => h0 _`. Consider the case `succ n ih => intro v`. Rewrite using `[pow_succ']`.

Conclude with `h1 _ _ (ih v)`. Establish `hK : IsNilpotent N` using `⟨m, LinearMap.ext fun v => h2 _ (hp m v)⟩`. Establish `hd : LinearMap.det (1 + N) = 1`. Establish `h` using `(hK.neg).charpoly_eq_X_pow_finrank`. Establish `h2` using `LinearMap.eval_charpoly (-N) 1`.

Rewrite `h2` using `[h]`. Simplify using `using h2.symm`. Use `⟨?_, (Module.End.isUnit_iff (1 + N)).1 hK.isUnit_one_add⟩` and prove the remaining obligations. Use `⟨(LinearMap.continuous_of_finiteDimensional (1 + N)).measurable, ?_⟩` and prove the remaining obligations. Use `Measure.map_linearMap_addHaar_eq_smul_addHaar μ (f := 1 + N) (by rw [hd]; exact one_ne_zero)` as an intermediate fact.

Rewrite `this` using `[hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul]`. Conclude with `this`.
-/
theorem unip {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (N : V →ₗ[ℝ] V) (P : ℕ → V → Prop) (m : ℕ)
    (h0 : ∀ v, P 0 v) (h1 : ∀ n v, P n v → P (n + 1) (N v)) (h2 : ∀ v, P m v → v = 0) :
    MeasurePreserving (fun v => v + N v) μ μ ∧ Function.Bijective fun v => v + N v := by
  have hp : ∀ n v, P n ((N ^ n) v) := fun n => by
    induction n with
    | zero => exact fun v => h0 _
    | succ n ih => intro v; rw [pow_succ']; exact h1 _ _ (ih v)
  have hK : IsNilpotent N := ⟨m, LinearMap.ext fun v => h2 _ (hp m v)⟩
  have hd : LinearMap.det (1 + N) = 1 := by
    have h := (hK.neg).charpoly_eq_X_pow_finrank
    have h2 := LinearMap.eval_charpoly (-N) 1
    rw [h] at h2
    simpa using h2.symm
  refine ⟨?_, (Module.End.isUnit_iff (1 + N)).1 hK.isUnit_one_add⟩
  refine ⟨(LinearMap.continuous_of_finiteDimensional (1 + N)).measurable, ?_⟩
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar μ (f := 1 + N) (by rw [hd]; exact one_ne_zero)
  rw [hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at this
  exact this

/- English proof (translation)
Simplify using `[upper, h.not_gt, Matrix.one_apply]`.
-/
theorem upper_sub (x : UT r → ℂ) (a c : Fin r) (h : c ≤ a) : (upper x - 1) a c = 0 := by
  simp [upper, h.not_gt, Matrix.one_apply]

def NB (k : ℕ) (x : UT r → ℂ) : (Fin r → Fin (k + 1) → ℂ) →ₗ[ℝ] (Fin r → Fin (k + 1) → ℂ) where
  toFun C a j := ∑ c, (upper x - 1) a c * C c j
  map_add' C D := by ext a j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' t C := by ext a j; simp [Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Use `haveI : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `unip _ _ (fun n C => ∀ a : Fin r, r ≤ a.val + n → C a = 0) r (fun v a h => by omega) ?_ fun v h => funext fun a => h a (by omega)` and prove the remaining obligations. Introduce `n C h a ha`. Use function extensionality and compare the values at `j`. Use `show ∑ c, (upper x - 1) a c * C c j = 0`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c ≤ a`. Rewrite using `[upper_sub x a c hc, zero_mul]`. Rewrite using `[h c (by have : a.val < c.val := not_le.1 hc; omega)]; simp`.
-/
theorem unip_NB (x : UT r → ℂ) :
    MeasurePreserving (fun v => v + NB k x v) volume volume ∧ Function.Bijective fun v => v + NB k x v := by
  haveI : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine unip _ _ (fun n C => ∀ a : Fin r, r ≤ a.val + n → C a = 0) r (fun v a h => by omega) ?_
    fun v h => funext fun a => h a (by omega)
  intro n C h a ha
  funext j
  show ∑ c, (upper x - 1) a c * C c j = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c ≤ a
  · rw [upper_sub x a c hc, zero_mul]
  · rw [h c (by have : a.val < c.val := not_le.1 hc; omega)]; simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [skewM, Matrix.smul_apply, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp [mul_assoc]`.
-/
theorem skewM_smul (c : ℝ) (s : UT r → ℂ) (t : Fin r → ℝ) : skewM (c • s) (c • t) = c • skewM s t := by
  ext a b
  simp only [skewM, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp [mul_assoc]

def co (S : Matrix (Fin r) (Fin r) ℂ) : (UT r → ℂ) × (Fin r → ℝ) := (fun p => S p.1.1 p.1.2, fun a => (S a a).im)

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [co]`.
-/
theorem co_add (S S' : Matrix (Fin r) (Fin r) ℂ) : co (S + S') = co S + co S' := by
  ext <;> simp [co]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [co]`.
-/
theorem co_smul (c : ℝ) (S : Matrix (Fin r) (Fin r) ℂ) : co (c • S) = c • co S := by
  ext <;> simp [co]

/- English proof (translation)
Use extensionality with `p`. Simplify using `[co, skewM, p.2]`. Simplify using `[co, skewM]`.
-/
theorem co_skewM (v : (UT r → ℂ) × (Fin r → ℝ)) : co (skewM v.1 v.2) = v := by
  ext p
  · simp [co, skewM, p.2]
  · simp [co, skewM]

def NS (x : UT r → ℂ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun v := co ((upper x - 1) * skewM v.1 v.2)
  map_add' v w := by rw [Prod.fst_add, Prod.snd_add, NHaar.skewM_add, Matrix.mul_add, co_add]
  map_smul' t v := by rw [Prod.smul_fst, Prod.smul_snd, skewM_smul, Matrix.mul_smul, co_smul]; rfl

/- English proof (translation)
Use `haveI : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`. Use `unip _ _ (fun n v => (∀ p : UT r, 2 * r ≤ 2 * p.1.1.val + 1 + n → v.1 p = 0) ∧ ∀ a : Fin r, 2 * r ≤ 2 * a.val + n → v.2 a = 0) (2 * r) (fun v => ⟨fun p h => by have := p.1.1.2; omega, fun a h => by omega⟩) ?_ fun v h => Prod.ext (funext fun a => h.1 a (by omega)) (funext fun a => …` and prove the remaining obligations. Introduce and unpack `n v ⟨h1, h2⟩`. Establish `key : ∀ a b : Fin r, a ≤ b → 2 * r ≤ 2 * a.val + 1 + n ∨ (a < b ∧ 2 * r ≤ 2 * a.val + 2 + n) → ((upper x - 1) * skewM v.1 v.2) a b = 0`. Introduce `a b hab h`.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c ≤ a`. Rewrite using `[upper_sub x a c hc, zero_mul]`. Establish `hc' : a.val < c.val` using `not_le.1 hc`.

Establish `hab' : a.val ≤ b.val` using `hab`. Rewrite `h` using `[Fin.lt_def]`. Unfold `skewM`. Use `split_ifs with g1 g2`. Rewrite using `[h1 _ (by simp only; omega), mul_zero]`.

Rewrite using `[h1 _ (by simp only; omega)]; simp`. Rewrite using `[h2 _ (by omega)]; simp`. Use `⟨fun p hp => key _ _ p.2.le (Or.inr ⟨p.2, by omega⟩), fun a ha => ?_⟩` and prove the remaining obligations. Use `show (((upper x - 1) * skewM v.1 v.2) a a).im = 0`. Rewrite using `[key a a le_rfl (Or.inl (by omega)), Complex.zero_im]`.
-/
theorem unip_NS (x : UT r → ℂ) :
    MeasurePreserving (fun v => v + NS x v) volume volume ∧ Function.Bijective fun v => v + NS x v := by
  haveI : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine unip _ _ (fun n v => (∀ p : UT r, 2 * r ≤ 2 * p.1.1.val + 1 + n → v.1 p = 0) ∧
    ∀ a : Fin r, 2 * r ≤ 2 * a.val + n → v.2 a = 0) (2 * r)
    (fun v => ⟨fun p h => by have := p.1.1.2; omega, fun a h => by omega⟩) ?_
    fun v h => Prod.ext (funext fun a => h.1 a (by omega)) (funext fun a => h.2 a (by omega))
  rintro n v ⟨h1, h2⟩
  have key : ∀ a b : Fin r, a ≤ b → 2 * r ≤ 2 * a.val + 1 + n ∨ (a < b ∧ 2 * r ≤ 2 * a.val + 2 + n) →
      ((upper x - 1) * skewM v.1 v.2) a b = 0 := by
    intro a b hab h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c ≤ a
    · rw [upper_sub x a c hc, zero_mul]
    have hc' : a.val < c.val := not_le.1 hc
    have hab' : a.val ≤ b.val := hab
    rw [Fin.lt_def] at h
    unfold skewM
    split_ifs with g1 g2
    · rw [h1 _ (by simp only; omega), mul_zero]
    · rw [h1 _ (by simp only; omega)]; simp
    · rw [h2 _ (by omega)]; simp
  refine ⟨fun p hp => key _ _ p.2.le (Or.inr ⟨p.2, by omega⟩), fun a ha => ?_⟩
  show (((upper x - 1) * skewM v.1 v.2) a a).im = 0
  rw [key a a le_rfl (Or.inl (by omega)), Complex.zero_im]

def cj (B : Fin r → Fin (k + 1) → ℂ) : Fin r → Fin (k + 1) → ℂ := fun a j => -(star (B a j) * Rad.sg k j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `volume_preserving_pi (f := fun (_ : Fin r) (v : Fin (k + 1) → ℂ) j => -(star (v j) * Rad.sg k j)) fun a => ?_` and prove the remaining obligations. Use `volume_preserving_pi (f := fun j (z : ℂ) => -(star z * Rad.sg k j)) fun j => ?_` and prove the remaining obligations. Establish `h` using `Complex.conjLIE.measurePreserving`. Unfold `Rad.sg`.

Use `split_ifs`. Simplify using `only [mul_neg, mul_one, neg_neg]`. Conclude with `h`. Simplify using `only [mul_one]`. Conclude with `(Measure.measurePreserving_neg volume).comp h`.

Use `Function.Involutive.bijective fun B => ?_` and prove the remaining obligations. Use extensionality with `a j`. Simplify using `only [cj, Rad.sg]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem cj_mp : MeasurePreserving (cj (k := k) (r := r)) volume volume ∧ Function.Bijective (cj (k := k) (r := r)) := by
  constructor
  · refine volume_preserving_pi (f := fun (_ : Fin r) (v : Fin (k + 1) → ℂ) j => -(star (v j) * Rad.sg k j)) fun a => ?_
    refine volume_preserving_pi (f := fun j (z : ℂ) => -(star z * Rad.sg k j)) fun j => ?_
    have h := Complex.conjLIE.measurePreserving
    unfold Rad.sg
    split_ifs
    · simp only [mul_neg, mul_one, neg_neg]
      exact h
    · simp only [mul_one]
      exact (Measure.measurePreserving_neg volume).comp h
  · refine Function.Involutive.bijective fun B => ?_
    ext a j
    simp only [cj, Rad.sg]
    split_ifs <;> simp

abbrev Idx (k r : ℕ) := {p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) // p.1.val < r ∧ p.1 < p.2 ∧ p.2.val ≤ r + k}

def idx (k r : ℕ) : UT r ⊕ Fin r × Fin (k + 1) ≃ Idx k r :=
  Equiv.ofBijective (Sum.elim
    (fun p => ⟨(eI k r p.1.1, eI k r p.1.2), p.1.1.2, p.2, by have := p.1.2.2; simp only [eI]; omega⟩)
    fun p => ⟨(eI k r p.1, wI k r p.2), p.1.2, by have := p.1.2; simp only [eI, wI, Fin.lt_def]; omega,
      by have := p.2.2; simp only [wI]; omega⟩) (by
    constructor
    · rintro (p | p) (q | q) h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq, Rad.eI_inj, Rad.wI_inj, Rad.eI_ne_wI,
          Rad.wI_ne_eI, and_false] at h
      · exact congrArg _ (Subtype.ext (Prod.ext h.1 h.2))
      · exact congrArg _ (Prod.ext h.1 h.2)
    · rintro ⟨⟨i, j⟩, h1, h2, h3⟩
      by_cases h : j.val < r
      · exact ⟨.inl ⟨(⟨i.val, h1⟩, ⟨j.val, h⟩), h2⟩, rfl⟩
      · refine ⟨.inr (⟨i.val, h1⟩, ⟨j.val - r, by simp only at h3; omega⟩), Subtype.ext (Prod.ext rfl (Fin.ext ?_))⟩
        simp only [Sum.elim_inr, wI]; omega)

def glue (q : (UT r → ℂ) × (Fin r → Fin (k + 1) → ℂ)) : Idx k r → ℂ := fun p =>
  Sum.elim q.1 (fun y => q.2 y.1 y.2) ((idx k r).symm p)

/- English proof (translation)
Establish `hm : Measurable (glue (k` using `k) (r := r)) := by`. Use `measurable_pi_lambda _ fun p => ?_` and prove the remaining obligations. Unfold `glue`. Apply the tactic sequence `rcases (idx k r).symm p with y | y <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop`. Use `⟨⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩, fun q q' h => ?_, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.map_apply hm (MeasurableSet.univ_pi hs)]`. Establish `e : glue ⁻¹' Set.univ.pi s = (Set.univ.pi fun p => s (idx k r (.inl p))) ×ˢ Set.univ.pi (fun i => Set.univ.pi (fun j => s (idx k r (.inr (i, j)))))`. Use extensionality with `f`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]`. Rewrite using `[← (idx k r).forall_congr_right]`.

Simplify using `[glue]`. Rewrite using `[e, Measure.volume_eq_prod, Measure.prod_prod, volume_pi, Measure.pi_pi, volume_pi, Measure.pi_pi]`. Repeatedly rewrite using `[volume_pi, Measure.pi_pi]`. Rewrite using `[← (idx k r).prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]`. Use `Prod.ext (funext fun p => ?_) (funext fun a => funext fun j => ?_)` and prove the remaining obligations.

Simplify `congrFun h (idx k r (.inl p))` using `[glue]`. Simplify `congrFun h (idx k r (.inr (a, j)))` using `[glue]`. Use `⟨(fun p => y (idx k r (.inl p)), fun a j => y (idx k r (.inr (a, j)))), funext fun p => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `(idx k r).surjective p`. Apply the tactic sequence `rcases p with p | p <;> simp [glue]`.
-/
theorem glue_mp : MeasurePreserving (glue (k := k) (r := r)) volume volume ∧
    Function.Bijective (glue (k := k) (r := r)) := by
  have hm : Measurable (glue (k := k) (r := r)) := by
    refine measurable_pi_lambda _ fun p => ?_
    unfold glue
    rcases (idx k r).symm p with y | y <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  refine ⟨⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩, fun q q' h => ?_, fun y => ?_⟩
  · rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have e : glue ⁻¹' Set.univ.pi s = (Set.univ.pi fun p => s (idx k r (.inl p))) ×ˢ
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (idx k r (.inr (i, j))))) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
      rw [← (idx k r).forall_congr_right]
      simp [glue]
    rw [e, Measure.volume_eq_prod, Measure.prod_prod, volume_pi, Measure.pi_pi, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [← (idx k r).prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  · refine Prod.ext (funext fun p => ?_) (funext fun a => funext fun j => ?_)
    · simpa [glue] using congrFun h (idx k r (.inl p))
    · simpa [glue] using congrFun h (idx k r (.inr (a, j)))
  · refine ⟨(fun p => y (idx k r (.inl p)), fun a j => y (idx k r (.inr (a, j)))), funext fun p => ?_⟩
    obtain ⟨p, rfl⟩ := (idx k r).surjective p
    rcases p with p | p <;> simp [glue]

/- English proof (translation)
Rewrite using `[NHaar.coord, Matrix.mul_apply, UEmb.sum_idx]`. Simplify using `only [UEmb.u_ee, UEmb.u_em, UEmb.u_es, zero_mul, Finset.sum_const_zero, add_zero]`.
-/
theorem coord_e (q : (UT r → ℂ) × PPar k r) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    NHaar.coord k r q (eI k r a) j = ∑ c, upper q.1 a c * pOf k r q.2 (eI k r c) j := by
  rw [NHaar.coord, Matrix.mul_apply, UEmb.sum_idx]
  simp only [UEmb.u_ee, UEmb.u_em, UEmb.u_es, zero_mul, Finset.sum_const_zero, add_zero]

def shift (x : UT r → ℂ) (B : Fin r → Fin (k + 1) → ℂ) : (UT r → ℂ) × (Fin r → ℝ) :=
  co (upper x * Matrix.of fun c b => -(herm (Hb k) (B b) (B c) / 2))

def tri (x : UT r → ℂ) (q : PPar k r) : PPar k r :=
  (cj q.1 + NB k x (cj q.1), shift x q.1 + (q.2 + NS x q.2))

/- English proof (translation)
Use `Prod.ext (funext fun p => ?_) ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `(idx k r).surjective p`. Break down `p with p | p` into its components or cases. Simplify using `only [glue, Equiv.symm_apply_apply, Sum.elim_inl] show NHaar.coord k r q (eI k r p.1.1) (eI k r p.1.2) = _`. Simplify using `[coord_e, pOf, Rad.pEl_ee, upper, p.2]`.

Simplify using `only [glue, Equiv.symm_apply_apply, Sum.elim_inr] show NHaar.coord k r q (eI k r p.1) (wI k r p.2) = cj q.2.1 p.1 p.2 + ∑ c, (upper q.1 - 1) p.1 c * cj q.2.1 c p.2`. Simplify using `only [coord_e, pOf, Rad.pEl_ew, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, cj]`. Expand and normalize the polynomial expressions, which then agree. Use `show co (Matrix.of fun a b => NHaar.coord k r q (eI k r a) (esI k r b)) = shift q.1 q.2.1 + (q.2.2 + co ((upper q.1 - 1) * skewM q.2.2.1 q.2.2.2))`. Establish `e : ∀ S, q.2.2 + co S = co (skewM q.2.2.1 q.2.2.2 + S)` using `fun S => by rw [co_add, co_skewM]`.

Rewrite using `[shift, e, ← co_add]`. Use `congr 1`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, add_sub_cancel, ← Matrix.mul_add]`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, coord_e]`.

Simplify using `only [Matrix.of_apply, pOf, Rad.pEl_es, Matrix.mul_apply, Matrix.add_apply]`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.
-/
theorem nCoords_coord (q : (UT r → ℂ) × PPar k r) :
    nCoords k r (Matrix.of.symm (NHaar.coord k r q)) = (glue (q.1, (tri q.1 q.2).1), (tri q.1 q.2).2) := by
  refine Prod.ext (funext fun p => ?_) ?_
  · obtain ⟨p, rfl⟩ := (idx k r).surjective p
    rcases p with p | p
    · simp only [glue, Equiv.symm_apply_apply, Sum.elim_inl]
      show NHaar.coord k r q (eI k r p.1.1) (eI k r p.1.2) = _
      simp [coord_e, pOf, Rad.pEl_ee, upper, p.2]
    · simp only [glue, Equiv.symm_apply_apply, Sum.elim_inr]
      show NHaar.coord k r q (eI k r p.1) (wI k r p.2) = cj q.2.1 p.1 p.2 + ∑ c, (upper q.1 - 1) p.1 c * cj q.2.1 c p.2
      simp only [coord_e, pOf, Rad.pEl_ew, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, cj]
      ring
  · show co (Matrix.of fun a b => NHaar.coord k r q (eI k r a) (esI k r b)) = shift q.1 q.2.1 + (q.2.2 + co ((upper q.1 - 1) * skewM q.2.2.1 q.2.2.2))
    have e : ∀ S, q.2.2 + co S = co (skewM q.2.2.1 q.2.2.2 + S) := fun S => by rw [co_add, co_skewM]
    rw [shift, e, ← co_add]
    congr 1
    rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel, ← Matrix.mul_add]
    ext a b
    rw [Matrix.of_apply, coord_e]
    simp only [Matrix.of_apply, pOf, Rad.pEl_es, Matrix.mul_apply, Matrix.add_apply]
    exact Finset.sum_congr rfl fun c _ => by ring

/- English proof (translation)
Establish `hB` using `(unip_NB (k := k) x).2.comp cj_mp.2`. Establish `hS` using `(unip_NS x).2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, v⟩ ⟨B', v'⟩ h`. Take `rfl : B = B'` from `hB.1 (congrArg Prod.fst h)`.

Conclude with `congrArg _ (hS.1 (add_left_cancel (congrArg Prod.snd h)))`. Introduce and unpack `⟨C, w⟩`. Take `⟨B, rfl⟩` from `hB.2 C`. Take `⟨v, hv⟩` from `hS.2 (w - shift x B)`. Conclude with `⟨(B, v), Prod.ext rfl (by simp only [tri] at hv ⊢; rw [hv, add_sub_cancel])⟩`.
-/
theorem tri_bij (x : UT r → ℂ) : Function.Bijective (tri (k := k) x) := by
  have hB := (unip_NB (k := k) x).2.comp cj_mp.2
  have hS := (unip_NS x).2
  constructor
  · rintro ⟨B, v⟩ ⟨B', v'⟩ h
    obtain rfl : B = B' := hB.1 (congrArg Prod.fst h)
    exact congrArg _ (hS.1 (add_left_cancel (congrArg Prod.snd h)))
  · rintro ⟨C, w⟩
    obtain ⟨B, rfl⟩ := hB.2 C
    obtain ⟨v, hv⟩ := hS.2 (w - shift x B)
    exact ⟨(B, v), Prod.ext rfl (by simp only [tri] at hv ⊢; rw [hv, add_sub_cancel])⟩

/- English proof (translation)
Unfold `nCoords`. Use `fun_prop`.
-/
theorem cont_nCoords : Continuous (nCoords k r) := by
  unfold nCoords
  fun_prop

/- English proof (translation)
Establish `h` using `cont_nCoords.comp (f := fun q => Matrix.of.symm (NHaar.coord k r q)) (NCoord.coord_homeo k r).2.1`. Simplify using `only [Function.comp_def, nCoords_coord] at h`. Use `Continuous.prodMk (continuous_pi fun a => continuous_pi fun j => ?_) h.snd` and prove the remaining obligations. Use `((continuous_apply (idx k r (.inr (a, j)))).comp h.fst).congr fun q => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, glue, Equiv.symm_apply_apply, Sum.elim_inr]`.

Both sides reduce to the same expression.
-/
theorem cont_tri : Continuous fun q : (UT r → ℂ) × PPar k r => tri q.1 q.2 := by
  have h := cont_nCoords.comp (f := fun q => Matrix.of.symm (NHaar.coord k r q)) (NCoord.coord_homeo k r).2.1
  simp only [Function.comp_def, nCoords_coord] at h
  refine Continuous.prodMk (continuous_pi fun a => continuous_pi fun j => ?_) h.snd
  refine ((continuous_apply (idx k r (.inr (a, j)))).comp h.fst).congr fun q => ?_
  simp only [Function.comp_apply, glue, Equiv.symm_apply_apply, Sum.elim_inr]
  rfl

/- English proof (translation)
Establish `hI : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddLeftInvariant` using `Measure.prod.instIsAddLeftInvariant`. Conclude with `((unip_NB (k := k) x).1.comp cj_mp.1).skew_product (g := fun B v => shift x B + (v + NS x v)) (cont_tri.comp (Continuous.prodMk_right x)).snd.measurable (Filter.Eventually.of_forall fun B => ((measurePreserving_add_left volume (shift x B)).comp (unip_NS x).1).map_eq)`.
-/
theorem tri_mp (x : UT r → ℂ) : MeasurePreserving (tri (k := k) x) volume volume := by
  have hI : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddLeftInvariant :=
    Measure.prod.instIsAddLeftInvariant
  exact ((unip_NB (k := k) x).1.comp cj_mp.1).skew_product (g := fun B v => shift x B + (v + NS x v))
    (cont_tri.comp (Continuous.prodMk_right x)).snd.measurable
    (Filter.Eventually.of_forall fun B => ((measurePreserving_add_left volume (shift x B)).comp (unip_NS x).1).map_eq)

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun q : (UT r → ℂ) × PPar k r => (q.1, tri q.1 q.2)) volume volume` using `(MeasurePreserving.id volume).skew_product (g := tri) cont_tri.measurable (Filter.Eventually.of_forall fun x => (tri_mp x).map_eq)`. Establish `h2` using `(volume_preserving_prodAssoc (α₁ := UT r → ℂ) (β₁ := Fin r → Fin (k + 1) → ℂ) (γ₁ := (UT r → ℂ) × (Fin r → ℝ))).symm`. Establish `h3` using `(glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))))`. Simplify using `only [nCoords_coord]`. Conclude with `(h3.comp h2).comp h1`.
-/
theorem entries_mp : MeasurePreserving
    (fun q : (UT r → ℂ) × PPar k r => nCoords k r (Matrix.of.symm (NHaar.coord k r q))) volume volume := by
  have h1 : MeasurePreserving (fun q : (UT r → ℂ) × PPar k r => (q.1, tri q.1 q.2)) volume volume :=
    (MeasurePreserving.id volume).skew_product (g := tri) cont_tri.measurable
      (Filter.Eventually.of_forall fun x => (tri_mp x).map_eq)
  have h2 := (volume_preserving_prodAssoc (α₁ := UT r → ℂ) (β₁ := Fin r → Fin (k + 1) → ℂ)
    (γ₁ := (UT r → ℂ) × (Fin r → ℝ))).symm
  have h3 := (glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))))
  simp only [nCoords_coord]
  exact (h3.comp h2).comp h1

/- English proof (translation)
Introduce `k r`. Take `⟨hbij, hΦ, -⟩` from `NCoord.coord_homeo k r`. Use `⟨GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top, fun x hx y hy h => ?_, fun y _ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨q, -, hq⟩` from `hbij.surjOn hx`. Take `⟨q', -, hq'⟩` from `hbij.surjOn hy`.

Take `rfl : Matrix.of.symm (NHaar.coord k r q) = x` from `hq`. Take `rfl : Matrix.of.symm (NHaar.coord k r q') = y` from `hq'`. Rewrite `h` using `[nCoords_coord, nCoords_coord, Prod.mk.injEq]`. Establish `h1` using `glue_mp.2.1 h.1`. Rewrite `h1` using `[Prod.mk.injEq]`.

Establish `h2 : tri q.1 q.2 = tri q'.1 q'.2` using `Prod.ext h1.2 h.2`. Rewrite `h2` using `[h1.1]`. Rewrite using `[show q = q' from Prod.ext h1.1 ((tri_bij _).1 h2)]`. Take `⟨⟨x, C⟩, hx⟩` from `glue_mp.2.2 y.1`. Take `⟨q, hq⟩` from `(tri_bij x).2 (C, y.2)`.

Use `⟨Matrix.of.symm (NHaar.coord k r (x, q)), hbij.mapsTo (Set.mem_univ (x, q)), ?_⟩` and prove the remaining obligations. Rewrite using `[nCoords_coord, hq, hx]`. Establish `hΦ' : Continuous fun q => (Matrix.of.symm (NHaar.coord k r q) : Mt k r)` using `hΦ`. Rewrite using `[GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, Measure.map_smul, add_comm (r * (k + 1)), lebN, Measure.map_map cont_nCoords.measurable hΦ'.measurable]`. Conclude with `congrArg _ entries_mp.map_eq`.
-/
theorem haarLie_entries : ∀ (k r : ℕ), IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧
    Set.InjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} ∧
    Set.SurjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} Set.univ ∧
    (haarLie (Nset k r) 1).map (nCoords k r) = (2 : ℝ≥0∞) ^ (r * (r - 1) + r * (k + 1)) • volume := by
  intro k r
  obtain ⟨hbij, hΦ, -⟩ := NCoord.coord_homeo k r
  refine ⟨GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top, fun x hx y hy h => ?_, fun y _ => ?_, ?_⟩
  · obtain ⟨q, -, hq⟩ := hbij.surjOn hx
    obtain ⟨q', -, hq'⟩ := hbij.surjOn hy
    obtain rfl : Matrix.of.symm (NHaar.coord k r q) = x := hq
    obtain rfl : Matrix.of.symm (NHaar.coord k r q') = y := hq'
    rw [nCoords_coord, nCoords_coord, Prod.mk.injEq] at h
    have h1 := glue_mp.2.1 h.1
    rw [Prod.mk.injEq] at h1
    have h2 : tri q.1 q.2 = tri q'.1 q'.2 := Prod.ext h1.2 h.2
    rw [h1.1] at h2
    rw [show q = q' from Prod.ext h1.1 ((tri_bij _).1 h2)]
  · obtain ⟨⟨x, C⟩, hx⟩ := glue_mp.2.2 y.1
    obtain ⟨q, hq⟩ := (tri_bij x).2 (C, y.2)
    refine ⟨Matrix.of.symm (NHaar.coord k r (x, q)), hbij.mapsTo (Set.mem_univ (x, q)), ?_⟩
    rw [nCoords_coord, hq, hx]
  · have hΦ' : Continuous fun q => (Matrix.of.symm (NHaar.coord k r q) : Mt k r) := hΦ
    rw [GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, Measure.map_smul, add_comm (r * (k + 1)), lebN, Measure.map_map cont_nCoords.measurable hΦ'.measurable]
    exact congrArg _ entries_mp.map_eq

end GlobalTheory.SnMass.NEntry
