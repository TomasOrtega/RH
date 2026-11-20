import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobValue

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hf_comp {Q Q' : Obj l ↥(OL K)} (c : Hom Q Q') (g : Hom bk.prism Q) :
    BK.hf (c.comp g) = c.f.comp (BK.hf g) := rfl

/- English proof (translation)
Establish `e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i))`. Use function extensionality and compare the values at `i`. Rewrite using `[hy, RingHom.map_mulVec]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, S.ε_φ]`.
-/
theorem frob_change (S : Strat bk d) {Q : Obj l ↥(OL K)} (g g' : Hom bk.prism Q) (y y' : Fin d → Q.A)
    (hy : y = (S.ε g g').mulVec y') :
    BK.hf g' bk.E ^ S.a • (S.A.map (BK.hf g)).mulVec (fun i => Q.D.φ (y i)) =
      BK.hf g bk.E ^ S.a • (S.ε g g').mulVec ((S.A.map (BK.hf g')).mulVec (fun i => Q.D.φ (y' i))) := by
  have e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i)) := by
    funext i; rw [hy, RingHom.map_mulVec]; rfl
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
    S.ε_φ]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) = p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i)`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, map_pow]`. Establish `h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) = (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i`. Rewrite using `[RingHom.map_mulVec, Matrix.map_map, hf_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `p.f_φ (y j)`. Use `h1.trans ?_` and prove the remaining obligations. Simplify using `only [h2, Pi.smul_apply, smul_eq_mul]`.
-/
theorem push (S : Strat bk d) {C Q : Obj l ↥(OL K)} (p : Hom C Q) (f : Hom bk.prism C) (c : C.A)
    (y : Fin d → C.A) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i)) =
      p.f c ^ S.a • (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) := by
  funext i
  have h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) =
      p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) := by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  have h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) =
      (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i := by
    rw [RingHom.map_mulVec, Matrix.map_map, hf_comp]
    congr 1
    funext j
    exact p.f_φ (y j)
  refine h1.trans ?_
  simp only [h2, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
The claim follows from `funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)`.
-/
theorem vec_cancel {A : Type} [CommRing A] {r : A} (hr : r ∈ nonZeroDivisors A) {u w : Fin d → A}
    (e : r • u = r • w) : u = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)

/- English proof (translation)
Use `vec_cancel hr ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, smul_smul, mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]`. Use `_ = (e ^ a * e' ^ a) • (u' ^ a • R) := by`. Rewrite using `[smul_smul, smul_smul, mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_smul_transfer_of_regular {A : Type} [CommRing A] {a : ℕ} {e e' u u' : A} {L R : Fin d → A}
    (hr : e ^ a * e' ^ a ∈ nonZeroDivisors A) (hF : e' ^ a • L = e ^ a • R) (hT : u * e = u' * e') :
    u ^ a • L = u' ^ a • R := by
  refine vec_cancel hr ?_
  calc (e ^ a * e' ^ a) • (u ^ a • L) = (u * e) ^ a • (e' ^ a • L) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
    _ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]
    _ = (e ^ a * e' ^ a) • (u' ^ a • R) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring

/- English proof (translation)
Establish `hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j` using `fun j => (V.v_nat p h f x j).symm`. Establish `hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j`. Rewrite using `[hpq]`. Conclude with `fun j => (V.v_nat q h f x j).symm`. Establish `hF` using `frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)`.

Establish `hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E`. Establish `e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E)`. Rewrite using `[hc]`. Conclude with `congrArg (fun k : Hom B Q => k.f t) hpq`. Simplify `e1` using `only [map_mul, hf_comp, RingHom.comp_apply]`.

Rewrite using `[push S p f c, push S q f c, Matrix.mulVec_smul]`. Simplify using `only [hY, hY']`. Conclude with `pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT`.
-/
theorem compat (S : Strat bk d) {B C Q : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (hn : ∀ g : Hom bk.prism Q, BK.hf g bk.E ∈ nonZeroDivisors Q.A)
    (x : N) (p q : Hom C Q) (hpq : p.comp h = q.comp h) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) =
      (S.ε (p.comp f) (q.comp f)).mulVec
        (fun i => q.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) := by
  have hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j :=
    fun j => (V.v_nat p h f x j).symm
  have hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j := by
    rw [hpq]; exact fun j => (V.v_nat q h f x j).symm
  have hF := frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)
  have hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E := by
    have e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E) := by
      rw [hc]; exact congrArg (fun k : Hom B Q => k.f t) hpq
    simpa only [map_mul, hf_comp, RingHom.comp_apply] using e1
  rw [push S p f c, push S q f c, Matrix.mulVec_smul]
  simp only [hY, hY']
  exact pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]`.
-/
theorem pow_smul_matrix_swap_of_relation {A : Type} [CommRing A] {a : ℕ} {e e' u : A} {L M : Fin d → A} {P : Matrix (Fin d) (Fin d) A}
    (hF : e' ^ a • L = e ^ a • P.mulVec M) : e ^ a • P.mulVec (u ^ a • M) = (u * e') ^ a • L := by
  rw [Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]

/- English proof (translation)
Establish `nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j`. Introduce `y j`. Rewrite using `[hcomm]`. Conclude with `(V.v_nat h' a g y j).symm`. Establish `natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j` using `fun y j => (V.v_nat a' h f y j).symm`.

Establish `ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E`. Establish `e : h'.f (a.f t) = a'.f (h.f t)` using `congrArg (fun k : Hom B Q' => k.f t) hcomm.symm`. Rewrite using `[e, ← hc, map_mul]`. Both sides reduce to the same expression. Establish `e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) = BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']`. Both sides reduce to the same expression. Establish `e2 : V.v (a'.comp h) (a'.comp f) w = a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j)`. Establish `e` using `push S a' f c (V.v h f x)`.

Rewrite `e` using `[← hw]`. Simplify using `only [natC] at e`. Conclude with `e`. Establish `e3` using `push S h' g (a.f t) (V.v a g x)`. Simplify using `only [nat', ht] at e3`.

Establish `hF` using `frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)`. Establish `key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) = fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i)`. Establish `v1` using `(V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)`. Conclude with `e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))`. Use function extensionality and compare the values at `i`.

Conclude with `hinj' (congrFun key i)`.
-/
theorem coord (S : Strat bk d) {B C Q Q' : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (a : Hom B Q) (g : Hom bk.prism Q) (h' : Hom Q Q') (a' : Hom C Q') (hcomm : a'.comp h = h'.comp a)
    (hinj' : Function.Injective h'.f) (x w : N)
    (hw : V.v h f w = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))) :
    BK.hf g bk.E ^ S.a • V.v a g w = a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i) := by
  have nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j := by
    intro y j; rw [hcomm]; exact (V.v_nat h' a g y j).symm
  have natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j :=
    fun y j => (V.v_nat a' h f y j).symm
  have ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E := by
    have e : h'.f (a.f t) = a'.f (h.f t) := congrArg (fun k : Hom B Q' => k.f t) hcomm.symm
    rw [e, ← hc, map_mul]; rfl
  have e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']
    rfl
  have e2 : V.v (a'.comp h) (a'.comp f) w =
      a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j) := by
    have e := push S a' f c (V.v h f x)
    rw [← hw] at e
    simp only [natC] at e
    exact e
  have e3 := push S h' g (a.f t) (V.v a g x)
  simp only [nat', ht] at e3
  have hF := frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)
  have key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i) := by
    have v1 := (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)
    exact e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))
  funext i
  exact hinj' (congrFun key i)

/- English proof (translation)
Introduce `l _ K bk d S B N _ _ V t ht`. Take `⟨C, h, ⟨f⟩, hC⟩` from `GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B`. Establish `hIC` using `(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).1`. Establish `htC : h.f t ∈ Ideal.span {BK.hf f bk.E}` using `hIC ▸ h.f_I t ht`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 htC`.

Take `⟨hinj, hsurj⟩` from `GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC`. Establish `hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))` using `fun x => hsurj _ fun Q p q hpq => compat S V h f c t hc (fun g => (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2) x p q hpq`. Use `choose Ψf hΨf using hzc`. Establish `zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y`. Introduce `x y`.

Apply `hinj` to reduce the goal to its premises. Establish `e1 : V.v h f (x + y) = V.v h f x + V.v h f y` using `map_add (V.v h f) x y`. Establish `e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y)` using `map_add (V.v h f) _ _`. Establish `hφ : (fun i => C.D.φ (V.v h f (x + y) i)) = (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i))`. Use function extensionality and compare the values at `fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)`.

Use `(hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))` and prove the remaining obligations. Use `(congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)`. Establish `zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x`. Introduce `b x`.

Apply `hinj` to reduce the goal to its premises. Establish `e1 : V.v h f (b • x) = h.f b • V.v h f x` using `LinearMap.map_smulₛₗ (V.v h f) b x`. Establish `e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x)` using `LinearMap.map_smulₛₗ (V.v h f) _ _`. Establish `hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i))`. Use function extensionality and compare the values at `fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))`.

Use `(hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))` and prove the remaining obligations. Use `(congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)`. Use `⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩` and prove the remaining obligations. Introduce `Q a g x`.

Take `⟨Q', h', a', hcomm, hinj'⟩` from `GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hC Q a`. Conclude with `coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)`.
-/
theorem psi_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  intro l _ K bk d S B N _ _ V t ht
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hIC := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).1
  have htC : h.f t ∈ Ideal.span {BK.hf f bk.E} := hIC ▸ h.f_I t ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  have hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i)) :=
    fun x => hsurj _ fun Q p q hpq =>
      compat S V h f c t hc (fun g => (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2) x p q hpq
  choose Ψf hΨf using hzc
  have zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y := by
    intro x y
    apply hinj
    have e1 : V.v h f (x + y) = V.v h f x + V.v h f y := map_add (V.v h f) x y
    have e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y) := map_add (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (x + y) i)) =
        (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)
    refine (hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)
  have zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x := by
    intro b x
    apply hinj
    have e1 : V.v h f (b • x) = h.f b • V.v h f x := LinearMap.map_smulₛₗ (V.v h f) b x
    have e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x) := LinearMap.map_smulₛₗ (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans
        ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))
    refine (hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)
  refine ⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩
  intro Q a g x
  obtain ⟨Q', h', a', hcomm, hinj'⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hC Q a
  exact coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)

end GlobalTheory.BSP.FrobValue
