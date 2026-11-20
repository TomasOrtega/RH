import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenBigCellSet

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)`. Use `next p q hp hq =>`. Simplify using `using hp.add hq`.

Use `next p n hp =>`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Use `hp.mul ?_` and prove the remaining obligations. Break down `n with ⟨i, j⟩ | ⟨i, j⟩` into its components or cases. Simplify using `only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl] fun_prop`.

Simplify using `only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]`. Establish `h : ContDiff ℝ ∞ fun g : Mat k r => g i j` using `by fun_prop`. Conclude with `Complex.conjCLE.contDiff.comp h`.
-/
lemma cd_eval (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => eval (vars g) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)
  next p q hp hq =>
    simpa using hp.add hq
  next p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases n with ⟨i, j⟩ | ⟨i, j⟩
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl]
      fun_prop
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]
      have h : ContDiff ℝ ∞ fun g : Mat k r => g i j := by fun_prop
      exact Complex.conjCLE.contDiff.comp h

/- English proof (translation)
Take `⟨q, -, hq⟩` from `dminPoly (k := k) z z' l`. Establish `h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q` using `funext hq`. Rewrite using `[h]`. Conclude with `cd_eval q`.
-/
lemma cd_dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ∞ (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, -, hq⟩ := dminPoly (k := k) z z' l
  have h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

/- English proof (translation)
Take `⟨q, -, hq⟩` from `gfPoly (k := k) z z'`. Establish `h : (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g => eval (vars g) q` using `funext hq`. Rewrite using `[h]`. Conclude with `cd_eval q`.
-/
lemma cd_gf (z z' : Fin (2 * r + k + 1) → ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  obtain ⟨q, -, hq⟩ := gfPoly (k := k) z z'
  have h : (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

/- English proof (translation)
Break down `h with rfl | h` into its components or cases. Simplify using `using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)`. Conclude with `(hf.contDiffAt.inv h).pow a`.
-/
lemma cda_invpow {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) {x : Mat k r} (a : ℕ) (h : a = 0 ∨ f x ≠ 0) :
    ContDiffAt ℝ ∞ (fun g => (f g)⁻¹ ^ a) x := by
  rcases h with rfl | h
  · simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  · exact (hf.contDiffAt.inv h).pow a

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.prod_insert hi]`. Conclude with `(h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))`.
-/
lemma cda_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/- English proof (translation)
Take `⟨hab, -, -⟩` from `he`. Establish `hx0 : 0 < Gf k r D.z D.z' x` using `hx.1`. Establish `hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0` using `fun l hl => Set.mem_iInter₂.1 hx.2 l hl`. Establish `hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0`. Introduce `h0`.

Establish `hG` using `hx0`. Simplify using `only [Gf, h0, Complex.normSq_zero, zero_sub] at hG`. Use `mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0` using `fun l hl => by`.

Break down `hab l hl with hl | rfl` into its components or cases. Conclude with `hxL l hl`. Conclude with `hlast`. Establish `hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0` using `fun l => by`. Distinguish the cases in `h : e.1.a l = 0`.

Conclude with `Or.inl h`. Conclude with `Or.inr (hnz l (Or.inl h))`. Establish `hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0` using `fun l => by`. Distinguish the cases in `h : e.1.b l = 0`. Conclude with `Or.inl h`.

Use `right`. Simplify using `using hnz l (Or.inr h)`. Use `show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x`. Use `(cd_eval _).contDiffAt.mul ?_` and prove the remaining obligations. Use `(cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_` and prove the remaining obligations.

Conclude with `(cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))`. Conclude with `cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))`.
-/
lemma cda_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) {x : Mat k r} (hx : x ∈ V0 D L) : ContDiffAt ℝ ∞ (cvs D e.1) x := by
  obtain ⟨hab, -, -⟩ := he
  have hx0 : 0 < Gf k r D.z D.z' x := hx.1
  have hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0 := fun l hl => Set.mem_iInter₂.1 hx.2 l hl
  have hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG := hx0
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))
    linarith
  have hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0 := fun l hl => by
    rcases hab l hl with hl | rfl
    · exact hxL l hl
    · exact hlast
  have hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0 := fun l => by
    by_cases h : e.1.a l = 0
    · exact Or.inl h
    · exact Or.inr (hnz l (Or.inl h))
  have hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0 := fun l => by
    by_cases h : e.1.b l = 0
    · exact Or.inl h
    · right
      simpa using hnz l (Or.inr h)
  show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x
  refine (cd_eval _).contDiffAt.mul ?_
  refine (cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l *
      (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_
  · exact (cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul
      (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))
  · exact cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f, hU, hgU, hf, hfe⟩` from `hA g₀ hg₀`. Take `⟨V, f', hV, hgV, hf', hfe'⟩` from `hB g₀ hg₀`. Use `⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)`.

Introduce `g hg hgG`. Simplify using `only [hfe g hg.1 hgG, hfe' g hg.2 hgG]`.
-/
lemma ckOn_mul {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hA g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hfe'⟩ := hB g₀ hg₀
  refine ⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩
  · exact (hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)
  · intro g hg hgG
    simp only [hfe g hg.1 hgG, hfe' g hg.2 hgG]

/- English proof (translation)
Introduce `es`. Proceed by induction on `es with`. Consider the case `nil`. Introduce `_ g₀ _`. Use `⟨univ, fun _ => 1, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩` and prove the remaining obligations.

Introduce `g _ _`. Simplify using `[C6.Epart]`. Consider the case `cons e es ih`. Introduce `hes`. Establish `h1` using `ckOn_Rw_top (hfib e.1) (hes e (by simp))`.

Establish `h2` using `ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))`. Conclude with `ckOn_mul h1 h2`.
-/
lemma ckOn_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) → CkOn ⊤ (GPos D) (C6.Epart fib es) := by
  intro es
  induction es with
  | nil =>
    intro _ g₀ _
    refine ⟨univ, fun _ => 1, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩
    intro g _ _
    simp [C6.Epart]
  | cons e es ih =>
    intro hes
    have h1 := ckOn_Rw_top (hfib e.1) (hes e (by simp))
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    exact ckOn_mul h1 h2

/- English proof (translation)
Introduce `g₀ hg₀`. Establish `hgpos : g₀ ∈ GPos D` using `domL_gpos hg₀`. Take `⟨U, f, hU, hgU, hf, hfe⟩` from `ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos`. Establish `hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L)` using `(isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)`. Use `⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)`. Introduce `g hg hgG`. Simplify using `only [cv, hfe g hg.1 hgG]`.
-/
lemma ckOn_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) : CkOn ⊤ (C6.domL D L) (cv D fib e.1) := by
  intro g₀ hg₀
  have hgpos : g₀ ∈ GPos D := domL_gpos hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos
  have hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L) :=
    (isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)
  refine ⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩
  · exact (hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)
  · intro g hg hgG
    simp only [cv, hfe g hg.1 hgG]

def mulCT {nf : ℕ} (t₁ t₂ : CT k r nf) : CT k r nf :=
  ⟨t₁.q * t₂.q, t₁.a + t₂.a, t₁.b + t₂.b, t₁.c + t₂.c, t₁.es ++ t₂.es⟩

/- English proof (translation)
Simplify using `only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Rewrite using `[smul_mul_smul_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma cv_mul (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t₁ t₂ : CT k r nf)
    (g : Mat k r) : cv D fib (mulCT t₁ t₂) g = cv D fib t₁ g * cv D fib t₂ g := by
  simp only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply,
    pow_add, Finset.prod_mul_distrib]
  rw [smul_mul_smul_comm]
  congr 1
  ring

/- English proof (translation)
Unfold `Good at h₁ h ⊢`. Take `⟨ha1, hs1, -⟩` from `h₁`. Take `⟨ha, hs, hw⟩` from `h`. Use `⟨fun l hl => ?_, fun x hx => ?_, hw⟩` and prove the remaining obligations. Distinguish the cases in `h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0`.

Conclude with `ha1 l h1`. Apply `ha l push_neg at h1` to reduce the goal to its premises. Simplify `hl` using `[mulCT, h1.1, h1.2]`. Simplify using `only [mulCT, List.mem_append] at hx`. Break down `hx with hx | hx` into its components or cases.

Conclude with `hs1 x hx`. Conclude with `hs x hx`.
-/
lemma good_mul {nf : ℕ} {L : Finset (Fin (r + 2))} {e₁ e : CT k r nf × List (Mat k r)} (h₁ : Good L e₁)
    (h : Good L e) : Good L (mulCT e₁.1 e.1, e.2) := by
  unfold Good at h₁ h ⊢
  obtain ⟨ha1, hs1, -⟩ := h₁
  obtain ⟨ha, hs, hw⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_, hw⟩
  · by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
    · exact ha1 l h1
    · apply ha l
      push_neg at h1
      simpa [mulCT, h1.1, h1.2] using hl
  · simp only [mulCT, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs1 x hx
    · exact hs x hx

def fo {nf : ℕ} (es : List (Fin nf × List (Mat k r))) : ℕ := (es.map fun e => e.2.length).sum

/- English proof (translation)
Introduce `es`. Proceed by induction on `es with`. Consider the case `nil => intro i`. Conclude with `i.elim0`. Consider the case `cons e es ih`.

Introduce `i`. Break down `i with ⟨_ | j, hj⟩` into its components or cases. Simplify using `[fo]`. Use linear arithmetic over natural numbers and integers. Establish `hj' : j < es.length` using `by simpa using hj`.

Use `ih ⟨j, hj'⟩` as an intermediate fact. Establish `e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) = e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2)` using `rfl`. Use `show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) = fo (e :: es) + 1`. Rewrite using `[e2]`. Simplify using `only [fo, List.map_cons, List.sum_cons] at this ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
lemma fo_set {nf : ℕ} (X : Mat k r) :
    ∀ (es : List (Fin nf × List (Mat k r))) (i : Fin es.length),
      fo (es.set i ((es.get i).1, X :: (es.get i).2)) = fo es + 1 := by
  intro es
  induction es with
  | nil => intro i; exact i.elim0
  | cons e es ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · simp [fo]
      omega
    · have hj' : j < es.length := by simpa using hj
      have := ih ⟨j, hj'⟩
      have e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) =
          e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2) := rfl
      show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) =
        fo (e :: es) + 1
      rw [e2]
      simp only [fo, List.map_cons, List.sum_cons] at this ⊢
      omega

/- English proof (translation)
Introduce `e' he'`. Simplify using `only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'`. Break down `he' with ⟨t', ht', rfl⟩ | rfl` into its components or cases. Break down `ht' with ht' | ht'` into its components or cases. Establish `hes` using `dscal_es D X e.1 t' ht'`.

Use `⟨?_, by simp [hes]⟩` and prove the remaining obligations. Simplify using `only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'`. Break down `ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl` into its components or cases. Conclude with `(PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)`. Use `split_ifs`.

Simplify using the standard rewrite rules. Conclude with `(deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)`. Use `split_ifs`. Simplify using the standard rewrite rules. Conclude with `(deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)`.

Use `split_ifs`. Simplify using the standard rewrite rules. Conclude with `(deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)`. Simplify using `only [dfib, List.mem_ofFn] at ht'`. Take `⟨i, rfl⟩` from `ht'`.

Use `⟨Nat.le_add_right _ _, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[fo_set]`. Use linear arithmetic over natural numbers and integers. Use `⟨Nat.le_add_right _ _, by simp; omega⟩` and prove the remaining obligations.
-/
lemma bound_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) :
    ∀ e' ∈ stepOne D X e, e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + 1 := by
  intro e' he'
  simp only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · rcases ht' with ht' | ht'
    · have hes := dscal_es D X e.1 t' ht'
      refine ⟨?_, by simp [hes]⟩
      simp only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'
      rcases ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl
      · exact (PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)
    · simp only [dfib, List.mem_ofFn] at ht'
      obtain ⟨i, rfl⟩ := ht'
      refine ⟨Nat.le_add_right _ _, ?_⟩
      simp only
      rw [fo_set]; omega
  · refine ⟨Nat.le_add_right _ _, by simp; omega⟩

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `Lf e' he'`. Conclude with `⟨e', he', by simp, by simp⟩`.

Consider the case `cons X w ih`. Introduce `Lf e' he'`. Simplify using `only [steps, List.foldr_cons, step, List.mem_flatMap] at he'`. Take `⟨e'', he'', he'⟩` from `he'`. Take `⟨e, he, hd, ho⟩` from `ih Lf e'' he''`.

Take `⟨hd', ho'⟩` from `bound_step D X e'' e' he'`. Use `⟨e, he, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [List.length_cons]`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [List.length_cons]`.

Use linear arithmetic over natural numbers and integers.
-/
lemma bound_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by
  intro w
  induction w with
  | nil =>
    intro Lf e' he'
    exact ⟨e', he', by simp, by simp⟩
  | cons X w ih =>
    intro Lf e' he'
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨e, he, hd, ho⟩ := ih Lf e'' he''
    obtain ⟨hd', ho'⟩ := bound_step D X e'' e' he'
    refine ⟨e, he, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      omega

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => simp [steps]`. Consider the case `cons X w ih`. Simplify using `only [steps, List.foldr_cons, step, List.mem_flatMap, List.cons_append]`.

Conclude with `⟨_, ih, by simp [stepOne]⟩`.
-/
lemma mem_steps_full (D : RealPlaceData k r Wp Wq) {nf : ℕ} (e : CT k r nf × List (Mat k r)) :
    ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w [e] := by
  intro w
  induction w with
  | nil => simp [steps]
  | cons X w ih =>
    simp only [steps, List.foldr_cons, step, List.mem_flatMap, List.cons_append]
    exact ⟨_, ih, by simp [stepOne]⟩

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons X w ih => show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)`. Rewrite using `[ih]`. Simplify using `[step, List.flatMap_append]`.
-/
lemma steps_append (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L₁ L₂ : FS k r nf) :
    steps D w (L₁ ++ L₂) = steps D w L₁ ++ steps D w L₂ := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)
    rw [ih]
    simp [step, List.flatMap_append]

end Formalism.FourierDecayAlt.P.MinorPolynomials
