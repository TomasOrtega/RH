import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteType
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSumStatement
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open Formalism.REAL (GlRel qdet qminor Tm)

namespace GlobalTheory.CompanionTheory.PairMult.CenScal

variable {n : ℕ}

section Regular

variable {U : Type} [Ring U] [Algebra ℂ U]

def leftMulLetter (x : Fin n → Fin n → U) (p q : Fin n) : Module.End ℂ U := LinearMap.mulLeft ℂ (x p q)

def negRightMulLetterShift (x : Fin n → Fin n → U) (τ : Fin n → ℂ) (p q : Fin n) : Module.End ℂ U :=
  -LinearMap.mulRight ℂ (x p q) + if p = q then τ p • (1 : Module.End ℂ U) else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leftMulLetter_apply (x : Fin n → Fin n → U) (p q : Fin n) (u : U) : leftMulLetter x p q u = x p q * u := rfl

/- English proof (translation)
Unfold `negRightMulLetterShift`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem negRightMulLetterShift_apply (x : Fin n → Fin n → U) (τ : Fin n → ℂ) (p q : Fin n) (u : U) :
    negRightMulLetterShift x τ p q u = -(u * x p q) + if p = q then τ p • u else 0 := by
  unfold negRightMulLetterShift
  split_ifs <;> simp

def LevRel (lev : Fin n → ℕ) (x : Fin n → Fin n → U) : Prop :=
  ∀ p q r v, lev p = lev q → lev r = lev v →
    x p q * x r v - x r v * x p q = (if q = r then x p v else 0) - (if v = p then x r q else 0)

/- English proof (translation)
Use `⟨fun p q r v h1 h2 => LinearMap.ext fun u => ?_, fun p q r v h1 h2 => LinearMap.ext fun u => ?_, fun p q r v _ _ => LinearMap.ext fun u => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (· * u) (hx p q r v h1 h2)`. Simplify using `only [sub_mul, mul_assoc] at e`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, leftMulLetter_apply]`. Rewrite using `[e]`.

Apply the tactic sequence `split_ifs <;> simp [leftMulLetter_apply]`. Establish `e` using `congrArg (u * ·) (hx p q r v h1 h2)`. Simplify using `only [mul_sub, ← mul_assoc] at e`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, negRightMulLetterShift_apply]`. Establish `key : ∀ c c' : ℂ, (-((-(u * x r v) + c' • u) * x p q) + c • (-(u * x r v) + c' • u)) - (-((-(u * x p q) + c • u) * x r v) + c' • (-(u * x p q) + c • u)) = -(u * x p q * x r v - u * x r v * x p q)`.

Introduce `c c'`. Simplify using `only [add_mul, neg_mul, smul_mul_assoc, smul_add, smul_neg, smul_smul, neg_add, neg_neg]`. Rewrite using `[mul_comm c c']`. Normalize the expressions using the abelian group laws. Establish `ea : ∀ (a b : Fin n) (w : U), (if a = b then τ a • w else 0) = (if a = b then τ a else 0) • w`.

Introduce `a b w`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [ea]`. Rewrite using `[key, e]`. Apply the tactic sequence `by_cases h3 : q = r <;> by_cases h4 : v = p`.

Substitute `h3 h4` using the available equality. Simplify using `[negRightMulLetterShift_apply, hτ _ _ h1]`. Normalize the expressions using the abelian group laws. Simplify using `[h3, h4, negRightMulLetterShift_apply, Ne.symm h4]`. Simplify using `[h3, h4, negRightMulLetterShift_apply, Ne.symm h3]`.

Simplify using `[h3, h4]`. Apply the tactic sequence `simp only [Module.End.mul_apply, leftMulLetter_apply, negRightMulLetterShift_apply] split_ifs <;> simp [mul_add, mul_assoc]`.
-/
theorem lRel_regular {lev : Fin n → ℕ} {x : Fin n → Fin n → U} (hx : LevRel lev x) {τ : Fin n → ℂ}
    (hτ : ∀ a c, lev a = lev c → τ a = τ c) : LRel lev (leftMulLetter x) (negRightMulLetterShift x τ) := by
  refine ⟨fun p q r v h1 h2 => LinearMap.ext fun u => ?_, fun p q r v h1 h2 => LinearMap.ext fun u => ?_,
    fun p q r v _ _ => LinearMap.ext fun u => ?_⟩
  · have e := congrArg (· * u) (hx p q r v h1 h2)
    simp only [sub_mul, mul_assoc] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, leftMulLetter_apply]
    rw [e]
    split_ifs <;> simp [leftMulLetter_apply]
  · have e := congrArg (u * ·) (hx p q r v h1 h2)
    simp only [mul_sub, ← mul_assoc] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, negRightMulLetterShift_apply]
    have key : ∀ c c' : ℂ, (-((-(u * x r v) + c' • u) * x p q) + c • (-(u * x r v) + c' • u)) -
        (-((-(u * x p q) + c • u) * x r v) + c' • (-(u * x p q) + c • u)) = -(u * x p q * x r v - u * x r v * x p q) := by
      intro c c'
      simp only [add_mul, neg_mul, smul_mul_assoc, smul_add, smul_neg, smul_smul, neg_add, neg_neg]
      rw [mul_comm c c']
      abel
    have ea : ∀ (a b : Fin n) (w : U), (if a = b then τ a • w else 0) = (if a = b then τ a else 0) • w := by
      intro a b w
      split_ifs <;> simp
    simp only [ea]
    rw [key, e]
    by_cases h3 : q = r <;> by_cases h4 : v = p
    · subst h3 h4
      simp [negRightMulLetterShift_apply, hτ _ _ h1]
      abel
    · simp [h3, h4, negRightMulLetterShift_apply, Ne.symm h4]
    · simp [h3, h4, negRightMulLetterShift_apply, Ne.symm h3]
    · simp [h3, h4]
  · simp only [Module.End.mul_apply, leftMulLetter_apply, negRightMulLetterShift_apply]
    split_ifs <;> simp [mul_add, mul_assoc]

/- English proof (translation)
Establish `e` using `LinearMap.congr_fun (hb U (leftMulLetter x) (negRightMulLetterShift x τ) (lRel_regular hx hτ) p q hpq).eq 1`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, leftMulLetter_apply, negRightMulLetterShift_apply] at e`. Establish `e1 : x p q * (1 : U) + (-((1 : U) * x p q) + (if p = q then τ p • (1 : U) else 0)) = if p = q then τ p • (1 : U) else 0`. Simplify using the standard rewrite rules. Rewrite `e` using `[e1]`.

Use `split_ifs at e with h`. Rewrite `e` using `[← add_assoc, map_smul]`. Conclude with `add_neg_eq_zero.1 (add_eq_right.1 e)`. Rewrite `e` using `[add_zero, map_zero]`. Conclude with `add_neg_eq_zero.1 e`.
-/
theorem central_letters {lev : Fin n → ℕ} {x : Fin n → Fin n → U} (hx : LevRel lev x) {τ : Fin n → ℂ}
    (hτ : ∀ a c, lev a = lev c → τ a = τ c) {b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hb : InvLev lev b)
    (p q : Fin n) (hpq : lev p = lev q) :
    x p q * evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b 1 = evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b 1 * x p q := by
  have e := LinearMap.congr_fun (hb U (leftMulLetter x) (negRightMulLetterShift x τ) (lRel_regular hx hτ) p q hpq).eq 1
  simp only [Module.End.mul_apply, LinearMap.add_apply, leftMulLetter_apply, negRightMulLetterShift_apply] at e
  have e1 : x p q * (1 : U) + (-((1 : U) * x p q) + (if p = q then τ p • (1 : U) else 0)) = if p = q then τ p • (1 : U) else 0 := by
    simp
  rw [e1] at e
  split_ifs at e with h
  · rw [← add_assoc, map_smul] at e
    exact add_neg_eq_zero.1 (add_eq_right.1 e)
  · rw [add_zero, map_zero] at e
    exact add_neg_eq_zero.1 e

/- English proof (translation)
Proceed by induction on `b using FreeAlgebra.induction generalizing u with`. Consider the case `grade0 r => simp [Module.algebraMap_end_apply]`. Consider the case `grade1 l`. Take `⟨s, p, q⟩` from `l`. Simplify using `only [evB, FreeAlgebra.lift_ι_apply]`.

Distinguish the cases in `hpq : lev p = lev q`. Consider the cases of `s`. Simplify using `only [if_true, hpq, Bool.false_eq_true, if_false, negRightMulLetterShift_apply]`. Establish `e1 : X2 p q (ρ u t) = ρ u (X2 p q t)` using `(LinearMap.congr_fun (hc p q hpq u).eq t).symm`. Establish `e2 : X2 p q t = -(X1 p q t) + if p = q then τ p • t else 0`.

Rewrite using `[← ht p q hpq, LinearMap.add_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, e2]`. Apply the tactic sequence `split_ifs <;> simp [map_add, map_neg, map_mul, hρ p q hpq, Module.End.mul_apply, LinearMap.add_apply]`. Simplify using `only [if_true, hpq, leftMulLetter_apply, map_mul, Module.End.mul_apply, hρ p q hpq]`.

Simplify using `[hpq]`. Consider the case `mul a c ha hc'`. Simplify using `only [map_mul, Module.End.mul_apply]`. Rewrite using `[hc', ha]`. Consider the case `add a c ha hc'`.

Simplify using `only [map_add, LinearMap.add_apply, ha, hc']`.
-/
theorem evB_intertwine {W : Type} [AddCommGroup W] [Module ℂ W] {lev : Fin n → ℕ} {x : Fin n → Fin n → U}
    {τ : Fin n → ℂ} (ρ : U →ₐ[ℂ] Module.End ℂ W) (X1 X2 : Fin n → Fin n → Module.End ℂ W) (t : W)
    (hρ : ∀ p q, lev p = lev q → ρ (x p q) = X1 p q)
    (hc : ∀ p q, lev p = lev q → ∀ u, Commute (ρ u) (X2 p q))
    (ht : ∀ p q, lev p = lev q → (X1 p q + X2 p q) t = if p = q then τ p • t else 0)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (u : U) :
    evB lev X1 X2 b (ρ u t) = ρ (evB lev (leftMulLetter x) (negRightMulLetterShift x τ) b u) t := by
  induction b using FreeAlgebra.induction generalizing u with
  | grade0 r => simp [Module.algebraMap_end_apply]
  | grade1 l =>
    obtain ⟨s, p, q⟩ := l
    simp only [evB, FreeAlgebra.lift_ι_apply]
    by_cases hpq : lev p = lev q
    · cases s
      · simp only [if_true, hpq, Bool.false_eq_true, if_false, negRightMulLetterShift_apply]
        have e1 : X2 p q (ρ u t) = ρ u (X2 p q t) := (LinearMap.congr_fun (hc p q hpq u).eq t).symm
        have e2 : X2 p q t = -(X1 p q t) + if p = q then τ p • t else 0 := by
          rw [← ht p q hpq, LinearMap.add_apply]; abel
        rw [e1, e2]
        split_ifs <;> simp [map_add, map_neg, map_mul, hρ p q hpq, Module.End.mul_apply, LinearMap.add_apply]
      · simp only [if_true, hpq, leftMulLetter_apply, map_mul, Module.End.mul_apply, hρ p q hpq]
    · simp [hpq]
  | mul a c ha hc' =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hc', ha]
  | add a c ha hc' =>
    simp only [map_add, LinearMap.add_apply, ha, hc']

end Regular

section Blocks

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

abbrev Gl (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

def eu (m : ℕ) (p q : Fin m) : UniversalEnvelopingAlgebra ℂ (Gl m) := ι ℂ (Matrix.single p q (1 : ℂ) : Gl m)

/- English proof (translation)
Rewrite using `[LieRing.of_associative_ring_bracket]`. Use `congr 1`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ h _`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ h _`.
-/
theorem single_lie {m : ℕ} (a b c d : Fin m) :
    (⁅(Matrix.single a b (1 : ℂ) : Gl m), (Matrix.single c d (1 : ℂ) : Gl m)⁆ : Gl m) =
      (if b = c then Matrix.single a d (1 : ℂ) else 0) - (if d = a then Matrix.single c b (1 : ℂ) else 0) := by
  rw [LieRing.of_associative_ring_bracket]
  congr 1
  · split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  · split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

/- English proof (translation)
Introduce `a b c d`. Establish `e` using `(ι ℂ : Gl m →ₗ⁅ℂ⁆ _).map_lie (Matrix.single a b (1 : ℂ) : Gl m) (Matrix.single c d (1 : ℂ) : Gl m)`. Rewrite `e` using `[single_lie, LieRing.of_associative_ring_bracket]`. Simplify using `only [eu]`. Rewrite using `[← e, map_sub]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glRel_eu (m : ℕ) : GlRel (eu m) := by
  intro a b c d
  have e := (ι ℂ : Gl m →ₗ⁅ℂ⁆ _).map_lie (Matrix.single a b (1 : ℂ) : Gl m) (Matrix.single c d (1 : ℂ) : Gl m)
  rw [single_lie, LieRing.of_associative_ring_bracket] at e
  simp only [eu]
  rw [← e, map_sub]
  split_ifs <;> simp

/- English proof (translation)
Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Simplify using the standard rewrite rules.
-/
theorem gl_eq_sum {m : ℕ} (Z : Gl m) : Z = ∑ a, ∑ b, Z a b • (Matrix.single a b (1 : ℂ) : Gl m) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp

/- English proof (translation)
Use `GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun Z => ?_) a` and prove the remaining obligations. Rewrite using `[gl_eq_sum Z, map_sum]`. Simplify using `only [map_sum, map_smul, AlgHom.id_apply]`. Conclude with `sum_mem fun p _ => sum_mem fun q _ => Subalgebra.smul_mem _ (h p q) _`.
-/
theorem mem_of_eu {m : ℕ} (S : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ (Gl m))) (h : ∀ p q, eu m p q ∈ S)
    (a : UniversalEnvelopingAlgebra ℂ (Gl m)) : a ∈ S := by
  refine GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun Z => ?_) a
  rw [gl_eq_sum Z, map_sum]
  simp only [map_sum, map_smul, AlgHom.id_apply]
  exact sum_mem fun p _ => sum_mem fun q _ => Subalgebra.smul_mem _ (h p q) _

/- English proof (translation)
Establish `hgen : Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2) = ⊤` using `eq_top_iff.2 fun a _ => mem_of_eu (Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2)) (fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩) a`. Rewrite using `[GlobalTheory.SmoothForms.center_eq_adjoin (glRel_eu m) hgen, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[← GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_succ_eq_gelfA']`. Conclude with `GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_mem_adjoin_qdet' _ _ _ (glRel_eu m) _`.
-/
theorem center_gl_le (m : ℕ) :
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Gl m)) ≤ Algebra.adjoin ℂ (Set.range (qdet (eu m))) := by
  have hgen : Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2) = ⊤ :=
    eq_top_iff.2 fun a _ => mem_of_eu (Algebra.adjoin ℂ (Set.range fun p : Fin m × Fin m => eu m p.1 p.2))
      (fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩) a
  rw [GlobalTheory.SmoothForms.center_eq_adjoin (glRel_eu m) hgen, Algebra.adjoin_le_iff]
  rintro _ ⟨k, rfl⟩
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_succ_eq_gelfA']
  exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.etr_mem_adjoin_qdet' _ _ _ (glRel_eu m) _

def glLin {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) : Gl m →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z Z' := by simp [add_smul, sum_add_distrib]
  map_smul' c Z := by simp [smul_sum, mul_smul]

/- English proof (translation)
Simplify using `[glLin, Matrix.single_apply, ite_and]`.
-/
theorem glLin_single {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (p q : Fin m) :
    glLin E (Matrix.single p q (1 : ℂ) : Gl m) = E p q := by
  simp [glLin, Matrix.single_apply, ite_and]

/- English proof (translation)
Establish `key : ∀ a b c d : Fin m, glLin E ⁅(Matrix.single a b (1 : ℂ) : Gl m), (Matrix.single c d (1 : ℂ) : Gl m)⁆ = ⁅glLin E (Matrix.single a b (1 : ℂ) : Gl m), glLin E (Matrix.single c d (1 : ℂ) : Gl m)⁆`. Introduce `a b c d`. Rewrite using `[single_lie, map_sub, glLin_single, glLin_single, LieRing.of_associative_ring_bracket, hE a b c d]`. Apply the tactic sequence `split_ifs <;> simp [glLin_single]`. Rewrite using `[gl_eq_sum Z, gl_eq_sum Z']`.

Simplify using `only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, key]`.
-/
theorem glLin_lie {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} {E : Fin m → Fin m → A} (hE : GlRel E) (Z Z' : Gl m) :
    glLin E ⁅Z, Z'⁆ = ⁅glLin E Z, glLin E Z'⁆ := by
  have key : ∀ a b c d : Fin m, glLin E ⁅(Matrix.single a b (1 : ℂ) : Gl m), (Matrix.single c d (1 : ℂ) : Gl m)⁆ =
      ⁅glLin E (Matrix.single a b (1 : ℂ) : Gl m), glLin E (Matrix.single c d (1 : ℂ) : Gl m)⁆ := by
    intro a b c d
    rw [single_lie, map_sub, glLin_single, glLin_single, LieRing.of_associative_ring_bracket, hE a b c d]
    split_ifs <;> simp [glLin_single]
  rw [gl_eq_sum Z, gl_eq_sum Z']
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, key]

def glHom {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) : Gl m →ₗ⁅ℂ⁆ A :=
  { glLin E with map_lie' := fun {Z Z'} => glLin_lie hE Z Z' }

/- English proof (translation)
The claim follows from `glLin_single E p q`.
-/
theorem glHom_single {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (p q : Fin m) :
    glHom E hE (Matrix.single p q (1 : ℂ) : Gl m) = E p q := glLin_single E p q

variable {M : ℕ} (d : Fin M → ℕ)

abbrev Ds : Type := DirectSum (Fin M) fun i => Gl (d i)

abbrev UD : Type := UniversalEnvelopingAlgebra ℂ (Ds d)

def mi (i : Fin M) : UniversalEnvelopingAlgebra ℂ (Gl (d i)) →ₐ[ℂ] UD d :=
  lift ℂ ((ι ℂ).comp (DirectSum.lieAlgebraOf ℂ (Fin M) (fun i => Gl (d i)) i))

/- English proof (translation)
Simplify using `only [mi, lift_ι_apply]`. Both sides reduce to the same expression.
-/
theorem mi_ι (i : Fin M) (Z : Gl (d i)) : mi d i (ι ℂ Z) = ι ℂ (DirectSum.of (fun i => Gl (d i)) i Z) := by
  simp only [mi, lift_ι_apply]
  rfl

def eb (i : Fin M) (p q : Fin (d i)) : UD d := mi d i (eu (d i) p q)

/- English proof (translation)
Use `GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun z => ?_) a` and prove the remaining obligations. Proceed by induction on `z using DirectSum.induction_on with`. Consider the case `zero => simp`. Consider the case `of i Z`. Establish `: ∀ b, mi d i b ∈ S` using `fun b => mem_of_eu (S.comap (mi d i)) (fun p q => h i p q) b`.

Rewrite using `[AlgHom.id_apply, ← mi_ι]`. Conclude with `this _`. Consider the case `add y z hy hz`. Simplify using `only [map_add]`. Conclude with `add_mem hy hz`.
-/
theorem mem_of_eb (S : Subalgebra ℂ (UD d)) (h : ∀ i p q, eb d i p q ∈ S) (a : UD d) : a ∈ S := by
  refine GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S (fun z => ?_) a
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i Z =>
    have : ∀ b, mi d i b ∈ S := fun b => mem_of_eu (S.comap (mi d i)) (fun p q => h i p q) b
    rw [AlgHom.id_apply, ← mi_ι]
    exact this _
  | add y z hy hz =>
    simp only [map_add]
    exact add_mem hy hz

/- English proof (translation)
Rewrite using `[GlobalTheory.EnvCentre.center_directSum (Fin M) (fun i => Gl (d i)) (mi d) (mi_ι d), Algebra.adjoin_le_iff]`. Introduce `z hz`. Take `⟨i, c, hc, rfl⟩` from `Set.mem_iUnion.1 hz`. Establish `hle : Algebra.adjoin ℂ (Set.range (qdet (eu (d i)))) ≤ (Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi d i (qdet (eu (d i)) u))).comap (mi d i)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, u, rfl⟩)`. Conclude with `hle (center_gl_le _ hc)`.
-/
theorem center_UD_le : Subalgebra.center ℂ (UD d) ≤
    Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi d i (qdet (eu (d i)) u)) := by
  rw [GlobalTheory.EnvCentre.center_directSum (Fin M) (fun i => Gl (d i)) (mi d) (mi_ι d), Algebra.adjoin_le_iff]
  intro z hz
  obtain ⟨i, c, hc, rfl⟩ := Set.mem_iUnion.1 hz
  have hle : Algebra.adjoin ℂ (Set.range (qdet (eu (d i)))) ≤
      (Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi d i (qdet (eu (d i)) u))).comap (mi d i) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, u, rfl⟩)
  exact hle (center_gl_le _ hc)

/- English proof (translation)
Establish `e` using `(ι ℂ : Ds d →ₗ⁅ℂ⁆ _).map_lie (DirectSum.of (fun i => Gl (d i)) i (Matrix.single p q (1 : ℂ))) (DirectSum.of (fun i => Gl (d i)) k (Matrix.single r v (1 : ℂ)))`. Rewrite `e` using `[DirectSum.lie_of_of_ne _ hik, map_zero, LieRing.of_associative_ring_bracket]`. Simplify using `only [eb, eu, mi_ι]`. Conclude with `sub_eq_zero.1 e.symm`.
-/
theorem eb_comm {i k : Fin M} (hik : i ≠ k) (p q : Fin (d i)) (r v : Fin (d k)) : Commute (eb d i p q) (eb d k r v) := by
  have e := (ι ℂ : Ds d →ₗ⁅ℂ⁆ _).map_lie (DirectSum.of (fun i => Gl (d i)) i (Matrix.single p q (1 : ℂ)))
    (DirectSum.of (fun i => Gl (d i)) k (Matrix.single r v (1 : ℂ)))
  rw [DirectSum.lie_of_of_ne _ hik, map_zero, LieRing.of_associative_ring_bracket] at e
  simp only [eb, eu, mi_ι]
  exact sub_eq_zero.1 e.symm

/- English proof (translation)
Introduce `a b c e`. Establish `h` using `congrArg (mi d i) (glRel_eu (d i) a b c e)`. Simplify using `only [map_sub, map_mul] at h`. Simplify using `only [eb]`. Rewrite using `[h]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eb_rel (i : Fin M) : GlRel (eb d i) := by
  intro a b c e
  have h := congrArg (mi d i) (glRel_eu (d i) a b c e)
  simp only [map_sub, map_mul] at h
  simp only [eb]
  rw [h]
  split_ifs <;> simp

end Blocks

section Final

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm`. Simplify using `only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 3`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem qdet_map {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A'] (φ : A →ₐ[ℂ] A') {m : ℕ}
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

variable {M : ℕ} {d : Fin M → ℕ}

def xs (a b : Σ i, Fin (d i)) : UD d := if h : a.1 = b.1 then eb d a.1 a.2 (h ▸ b.2) else 0

/- English proof (translation)
Simplify using `[xs]`.
-/
theorem xs_same (i : Fin M) (p q : Fin (d i)) : xs (d := d) ⟨i, p⟩ ⟨i, q⟩ = eb d i p q := by
  simp [xs]

def xl {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) (p q : Fin n) : UD d := xs (e.symm p) (e.symm q)

/- English proof (translation)
Simplify using `[xl]`.
-/
theorem xl_apply {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) (a b : Σ i, Fin (d i)) : xl e (e a) (e b) = xs a b := by
  simp [xl]

/- English proof (translation)
Introduce `p q r v h1 h2`. Take `⟨⟨i, p⟩, rfl⟩` from `e.surjective p`. Take `⟨⟨i', q⟩, rfl⟩` from `e.surjective q`. Take `⟨⟨k, r⟩, rfl⟩` from `e.surjective r`. Take `⟨⟨k', v⟩, rfl⟩` from `e.surjective v`.

Rewrite `h1`, `h2` using `[he, he]`. Take `rfl : i = i'` from `Fin.ext h1`. Take `rfl : k = k'` from `Fin.ext h2`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using `only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]`. Conclude with `eb_rel d i p q r v`. Establish `n1 : (⟨i, q⟩ : Σ i, Fin (d i)) ≠ ⟨k, r⟩` using `fun h => hik (congrArg Sigma.fst h)`. Establish `n2 : (⟨k, v⟩ : Σ i, Fin (d i)) ≠ ⟨i, p⟩` using `fun h => hik (congrArg Sigma.fst h).symm`. Simplify using `only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, n1, n2, if_false, sub_zero]`.

Conclude with `sub_eq_zero.2 (eb_comm d hik p q r v).eq`.
-/
theorem levRel_xl {n : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) {lev : Fin n → ℕ} (he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ)) :
    LevRel lev (xl e) := by
  intro p q r v h1 h2
  obtain ⟨⟨i, p⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨i', q⟩, rfl⟩ := e.surjective q
  obtain ⟨⟨k, r⟩, rfl⟩ := e.surjective r
  obtain ⟨⟨k', v⟩, rfl⟩ := e.surjective v
  rw [he, he] at h1 h2
  obtain rfl : i = i' := Fin.ext h1
  obtain rfl : k = k' := Fin.ext h2
  by_cases hik : i = k
  · subst hik
    simp only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact eb_rel d i p q r v
  · have n1 : (⟨i, q⟩ : Σ i, Fin (d i)) ≠ ⟨k, r⟩ := fun h => hik (congrArg Sigma.fst h)
    have n2 : (⟨k, v⟩ : Σ i, Fin (d i)) ≠ ⟨i, p⟩ := fun h => hik (congrArg Sigma.fst h).symm
    simp only [xl_apply, xs_same, EmbeddingLike.apply_eq_iff_eq, n1, n2, if_false, sub_zero]
    exact sub_eq_zero.2 (eb_comm d hik p q r v).eq

/- English proof (translation)
Express the relevant statement in the definitionally equal form `⁅glLin E Z, glLin E' Z'⁆ = 0`. Rewrite using `[gl_eq_sum Z, gl_eq_sum Z']`. Establish `h0 : ∀ p q r v, ⁅E p q, E' r v⁆ = 0` using `fun p q r v => by`. Rewrite using `[LieRing.of_associative_ring_bracket, (hc p q r v).eq, sub_self]`. Simplify using `only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, glLin_single, h0, smul_zero, sum_const_zero]`.
-/
theorem glHom_comm {A : Type} [Ring A] [Algebra ℂ A] {m m' : ℕ} {E : Fin m → Fin m → A} {E' : Fin m' → Fin m' → A}
    (hE : GlRel E) (hE' : GlRel E') (hc : ∀ p q r v, Commute (E p q) (E' r v)) (Z : Gl m) (Z' : Gl m') :
    ⁅glHom E hE Z, glHom E' hE' Z'⁆ = 0 := by
  change ⁅glLin E Z, glLin E' Z'⁆ = 0
  rw [gl_eq_sum Z, gl_eq_sum Z']
  have h0 : ∀ p q r v, ⁅E p q, E' r v⁆ = 0 := fun p q r v => by
    rw [LieRing.of_associative_ring_bracket, (hc p q r v).eq, sub_self]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, glLin_single, h0, smul_zero, sum_const_zero]

end Final

end GlobalTheory.CompanionTheory.PairMult.CenScal

namespace GlobalTheory.CompanionTheory.PairMult

end GlobalTheory.CompanionTheory.PairMult
end
