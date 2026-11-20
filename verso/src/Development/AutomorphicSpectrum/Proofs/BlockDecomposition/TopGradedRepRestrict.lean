import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLdlog

open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def ee {d : ℕ} (E : Frame Φ d) (k i : Fin d) : Φ.A.obj E.D := if i = k then 1 else 0

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `ℓ _`. Use `mem_FC.2 fun s => ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_zero, hF.top 0 le_rfl]`. Discharge the goal by the elementary cases of `trivial`. Consider the case `succ m ih`. Introduce `ℓ hl`. Conclude with `cup_mem hF rfl (ih _ fun k => hl _) (hl (Fin.last m))`.
-/
theorem cupList_mem (hF : IsFil Φ Fil) : ∀ (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m := by
  intro m
  induction m with
  | zero =>
    intro ℓ _
    refine mem_FC.2 fun s => ?_
    rw [Nat.cast_zero, hF.top 0 le_rfl]
    trivial
  | succ m ih =>
    intro ℓ hl
    exact cup_mem hF rfl (ih _ fun k => hl _) (hl (Fin.last m))

/- English proof (translation)
Rewrite using `[vl, Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `_ = (∑ I : Fin n → Fin n, vl (fc E σ I (∏ k, ee E k (I k))) u) * _`. Rewrite using `[Finset.sum_mul]`. Simplify using `only [← form_mul]`. Rewrite using `[Finset.sum_eq_single id]`.

Establish `e : ∏ k, ee E k (id k) = 1` using `Finset.prod_eq_one fun k _ => by simp [ee]`. Rewrite using `[e, mul_one]`. Introduce `I _ hI`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, I k ≠ k := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hI (funext hc)`. Establish `e : ∏ k, ee E k (I k) = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) (by simp [ee, hk])`. Rewrite using `[e, mul_zero]`. Simplify using `[Frame.form]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem form_id_eq {n : ℕ} (E : Frame Φ n) (σ : ∀ T : C, E.D ⟶ T) (w : Φ.A.obj E.D)
    (u : ComposableArrows C n) :
    E.form σ id w u = vl (∑ I : Fin n → Fin n, fc E σ I (∏ k, ee E k (I k))) u * (Φ.A.map (σ _)).hom w := by
  rw [vl, Finset.sum_apply]
  change _ = (∑ I : Fin n → Fin n, vl (fc E σ I (∏ k, ee E k (I k))) u) * _
  rw [Finset.sum_mul]
  simp only [← form_mul]
  rw [Finset.sum_eq_single id]
  · have e : ∏ k, ee E k (id k) = 1 := Finset.prod_eq_one fun k _ => by simp [ee]
    rw [e, mul_one]
  · intro I _ hI
    obtain ⟨k, hk⟩ : ∃ k, I k ≠ k := by
      by_contra hc
      push_neg at hc
      exact hI (funext hc)
    have e : ∏ k, ee E k (I k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (by simp [ee, hk])
    rw [e, mul_zero]
    simp [Frame.form]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Substitute `hr` using the available equality. Establish `hh : ∀ k, h0 (h k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0` using `fun k => mem_FC.2 fun s => by`. Use `hJ k (s.obj (Fin.last 0))` as an intermediate fact. Rewrite `this` using `[← hF.one]`. Rewrite using `[Nat.cast_one]`.

Conclude with `this`. Establish `he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k))) ∈ FC (Fil ((1 + 1 : ℕ) : ℤ)) 1` using `fun k => mem_FC.2 fun u => by`. Establish `e : vl (ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k)))) u = (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0))))`. Rewrite using `[← cech_d_h0_eval]`. Express the relevant statement in the definitionally equal form `_ - (vl (∑ i, fc E σ ![i] (ee E k i)) u + _) = _`.

Use `congr 2`. Rewrite using `[vl, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hl k u`.

Take `⟨g, hg, hn⟩` from `near E σ hF hc (n + 1) ℓ (ee E) (fun k => h0 (h k)) hh he`. Take `⟨H, hH, rfl⟩` from `hg`. Set `H' : CH.Cn (CH.modF Φ.A) n` to `fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w`. Establish `hH' : H' ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n` using `mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)`. Establish `h1` using `rep_add hx (rep_d (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))`.

Rewrite `h1` using `[add_zero]`. Use `rep_congr h1 fun u => ?_` and prove the remaining obligations. Establish `e1` using `mem_FC.1 hn u`. Establish `e2` using `d_mul E σ hF hc w hH u`. Establish `e3` using `hz u`.

Establish `e4 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1` using `by push_cast; ring`. Rewrite `e1`, `e2` using `[e4]`. Establish `e5` using `((Fil _).S _).neg_mem (((Fil _).S _).add_mem (((Fil _).S _).add_mem (Ideal.mul_mem_right ((Φ.A.map (σ _)).hom w) _ e1) e2) e3)`. Use `e5 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[form_id_eq]`.

Express the relevant statement in the definitionally equal form `_ + vl (CH.d (CH.modF Φ.A) n H') u - z u = -((vl (cupListC Φ.A ℓ) u - vl (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, ee E k (I k))) u - vl (CH.d (CH.modF Φ.A) n H) u) * _ + (vl (CH.d (CH.modF Φ.A) n H) u * _ - vl (CH.d (CH.modF Φ.A) n H') u) + (z u - _))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rep_back (hF : IsFil Φ Fil) {n : ℕ} (E : Frame Φ (n + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (ℓ : Fin (n + 1) → CH.Cn (CH.modF Φ.A) 1) (h : Fin (n + 1) → ∀ T : C, Φ.A.obj T)
    (hJ : ∀ k T, h k T ∈ Φ.J.S T)
    (hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows C 1), (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) -
        (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) ∈ (Fil 2).S _)
    (w : Φ.A.obj E.D) (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (x : CH.H (gr Fil r) (n + 1))
    (z : ∀ u : ComposableArrows C (n + 1), Φ.A.obj (u.obj (Fin.last (n + 1))))
    (hz : ∀ u, z u - vl (cupListC Φ.A ℓ) u * (Φ.A.map (σ _)).hom w ∈ (Fil (r + 1)).S _)
    (hx : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id w) x) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) z x := by
  subst hr
  have hh : ∀ k, h0 (h k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun s => by
    have := hJ k (s.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k))) ∈
      FC (Fil ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (ee E k i) + CH.d (CH.modF Φ.A) 0 (h0 (h k)))) u =
        (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (ee E k i) u +
          (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (ee E k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    exact hl k u
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ (ee E) (fun k => h0 (h k)) hh he
  obtain ⟨H, hH, rfl⟩ := hg
  let H' : CH.Cn (CH.modF Φ.A) n := fun u => (show Φ.A.obj (u.obj (Fin.last n)) from H u) * (Φ.A.map (σ _)).hom w
  have hH' : H' ∈ FC (Fil ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add hx (rep_d (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc w hH u
  have e3 := hz u
  have e4 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e4] at e1 e2
  have e5 := ((Fil _).S _).neg_mem (((Fil _).S _).add_mem (((Fil _).S _).add_mem
    (Ideal.mul_mem_right ((Φ.A.map (σ _)).hom w) _ e1) e2) e3)
  convert e5 using 1
  rw [form_id_eq]
  change _ + vl (CH.d (CH.modF Φ.A) n H') u - z u = -((vl (cupListC Φ.A ℓ) u -
    vl (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, ee E k (I k))) u - vl (CH.d (CH.modF Φ.A) n H) u) * _ +
    (vl (CH.d (CH.modF Φ.A) n H) u * _ - vl (CH.d (CH.modF Φ.A) n H') u) + (z u - _))
  ring

end Fr

section Term
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Substitute `e` using the available equality. Establish `e : ∀ (h : Fin.last n ⟶ Fin.last n) (z : A.obj (s.obj (Fin.last n))), (A.map (s.map h)).hom z = z`. Introduce `h z`. Establish `e1 : h = 𝟙 _` using `Subsingleton.elim _ _`. Establish `e2 : s.map h = 𝟙 _` using `(congrArg s.map e1).trans (s.map_id _)`.

Establish `e3 : A.map (s.map h) = 𝟙 _` using `(congrArg A.map e2).trans (A.map_id _)`. Rewrite using `[e3]`. Both sides reduce to the same expression. Conclude with `e _ _`.
-/
theorem term_id {n : ℕ} (f : CH.Cn (CH.modF A) n) (s : ComposableArrows C n) (g : Fin (n + 1) → Fin (n + 1))
    (hg : Monotone g) (e : g = id) : CH.term (CH.modF A) s f g hg = f s := by
  subst e
  have e : ∀ (h : Fin.last n ⟶ Fin.last n) (z : A.obj (s.obj (Fin.last n))), (A.map (s.map h)).hom z = z := by
    intro h z
    have e1 : h = 𝟙 _ := Subsingleton.elim _ _
    have e2 : s.map h = 𝟙 _ := (congrArg s.map e1).trans (s.map_id _)
    have e3 : A.map (s.map h) = 𝟙 _ := (congrArg A.map e2).trans (A.map_id _)
    rw [e3]
    rfl
  exact e _ _

end Term

section Loc
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

/- English proof (translation)
Take `⟨-, -, -, h4, -⟩` from `hL`. Conclude with `Ideal.Quotient.eq.1 ((Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) y))).trans (h4 T (σ T) y))`.
-/
theorem lift_sub_mem (s : ℕ) {V : X.Opens} {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (y : Γ(X, V))
    (T : (KS q s {V}).FullSubcategory) :
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) y) -
      ((sP (KS q s {V})).A.map (σ T)).hom (ε y) ∈ (sP (KS q s {V})).J.S T := by
  obtain ⟨-, -, -, h4, -⟩ := hL
  exact Ideal.Quotient.eq.1 ((Classical.choose_spec (Ideal.Quotient.mk_surjective
    (ev T.obj (ks_in q s V T.obj T.property) y))).trans (h4 T (σ T) y))

/- English proof (translation)
Establish `hF` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})`. Establish `hc : E.GrConst (sFil (KS q s {V}))` using `hL.1`. Establish `h5` using `hL.2.2.2.2`. Set `ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1` to `fun k => addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)`. Set `h : Fin (n + 1) → ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T` to `fun k T => (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) (t k)) - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))`.

Establish `hJ : ∀ k T, h k T ∈ (sP (KS q s {V})).J.S T` using `fun k T => lift_sub_mem q s t E ε hL σ (t k) T`. Establish `hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows (KS q s {V}).FullSubcategory 1), (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).h …`. Introduce `k u`. Simplify using `only [form_one]`. Establish `e1 : ∑ i, E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) * ((sP (KS q s {V})).A.map (σ _)).hom (ee E k i) = E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1))))`.

Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[show ee E k k = 1 from if_pos rfl, map_one, mul_one]`. Introduce `i _ hi`. Rewrite using `[show ee E k i = 0 from if_neg hi, map_zero, mul_zero]`. Introduce `hk`.

Conclude with `absurd (Finset.mem_univ _) hk`. Rewrite using `[e1]`. Establish `e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) = ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)))`. Unfold `Frame.a`. Rewrite using `[h5, GlobalTheory.CompanionTheory.CocProd.map_map]`.

Rewrite using `[e2]`. Express the relevant statement in the definitionally equal form `((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (show (sP (KS q s {V})).A.obj (u.obj 0) from _)) - (_ + (((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) - _) - ((sP (KS q s {V})). …`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hl'` using `fun k u => (hl k u).symm ▸ ((sFil (KS q s {V}) 2).S _).zero_mem`.

Establish `hlm : ∀ k, ℓ k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1`. Introduce `k`. Use `mem_FC.2 fun u => ?_` and prove the remaining obligations. Establish `e : vl (ℓ k) u = ((∑ i, E.form σ ![i] (ee E k i) u) + (h k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0))))` using `sub_eq_zero.1 (hl k u)`. Rewrite using `[e]`.

Use `((sFil _ _).S _).add_mem (((sFil _ _).S _).sum_mem fun i _ => mem_FC.1 (fc_mem E σ hF ![i] _) u) ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_one, hF.one]`. Conclude with `((sP (KS q s {V})).J.S _).sub_mem (hJ _ _) ((sP (KS q s {V})).J.map_mem _ (hJ _ _))`. Use `rep_back hF E σ hc ℓ h hJ hl' (ε y) r hr x _ (fun u => ?_) hx` and prove the remaining obligations. Substitute `hr` using the available equality.

Establish `hb` using `mem_FC.1 (cupList_mem hF (n + 1) ℓ hlm) u`. Establish `e0 : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) = (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + …`. Establish `e : CH.back (Nat.zero_add (n + 1)) = id`. Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `[CH.back]`. Use `term_id (cupListC (sP (KS q s {V})).A ℓ) u _ (CH.back_mono (Nat.zero_add (n + 1))) e` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ * (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u _ _ _) = _`. Rewrite using `[this]`. Establish `ha : ∀ p : Fin (n + 2), ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last p)))).hom (show (sP (KS q s {V})).A.obj (u.obj p) from liftV (u.obj p).obj (ks_in q s V (u.obj p).obj (u.obj p).property) y) - ((sP (KS q s {V})).A.map (σ _)).hom (ε y) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ …`.

Introduce `p`. Rewrite using `[Nat.cast_one, hF.one]`. Establish `e1` using `(sP (KS q s {V})).J.map_mem (u.map (homOfLE (Fin.le_last p))) (lift_sub_mem q s t E ε hL σ y (u.obj p))`. Establish `e2` using `const1 hF hc (σ (u.obj p) ≫ u.map (homOfLE (Fin.le_last p))) (σ _) (ε y)`. Establish `e3` using `((sP (KS q s {V})).J.S _).add_mem e1 e2`.

Rewrite `e3` using `[map_sub, GlobalTheory.CompanionTheory.CocProd.map_map, sub_add_sub_cancel]`. Conclude with `e3`. Establish `e4` using `hF.mul _ _ _ hb (ha (CH.front (Nat.zero_add (n + 1)) (Fin.last 0)))`. Establish `e5 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1` using `by push_cast; ring`. Rewrite `e4` using `[e5]`.

Use `e4 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) - _ = _`. Establish `ea : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) = ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last …` using `rfl`. Rewrite using `[e0, ea]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xdt_rep (s : ℕ) {V : X.Opens} {n : ℕ} (t : Fin (n + 1) → Γ(X, V)) (E : Frame (sP (KS q s {V})) (n + 1))
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (y : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (x : CH.H (gr (sFil (KS q s {V})) r) (n + 1))
    (hx : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε y)) x) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t y) x := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have h5 := hL.2.2.2.2
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k =>
    addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)
  let h : Fin (n + 1) → ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T := fun k T =>
    (show (sP (KS q s {V})).A.obj T from liftV T.obj (ks_in q s V T.obj T.property) (t k)) -
      ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hJ : ∀ k T, h k T ∈ (sP (KS q s {V})).J.S T := fun k T => lift_sub_mem q s t E ε hL σ (t k) T
  have hl : ∀ (k : Fin (n + 1)) (u : ComposableArrows (KS q s {V}).FullSubcategory 1),
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (ee E k i) u + (h k (u.obj (Fin.last 1)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) = 0 := by
    intro k u
    simp only [form_one]
    have e1 : ∑ i, E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) *
        ((sP (KS q s {V})).A.map (σ _)).hom (ee E k i) = E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
      rw [Finset.sum_eq_single k]
      · rw [show ee E k k = 1 from if_pos rfl, map_one, mul_one]
      · intro i _ hi
        rw [show ee E k i = 0 from if_neg hi, map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [e1]
    have e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) =
        ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
          (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) := by
      unfold Frame.a
      rw [h5, GlobalTheory.CompanionTheory.CocProd.map_map]
    rw [e2]
    change ((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (show (sP (KS q s {V})).A.obj (u.obj 0) from _)) -
      (_ + (((show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from _) - _) -
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom ((show (sP (KS q s {V})).A.obj (u.obj 0) from _) - _))) = 0
    rw [map_sub]
    ring
  have hl' := fun k u => (hl k u).symm ▸ ((sFil (KS q s {V}) 2).S _).zero_mem
  have hlm : ∀ k, ℓ k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
    intro k
    refine mem_FC.2 fun u => ?_
    have e : vl (ℓ k) u = ((∑ i, E.form σ ![i] (ee E k i) u) + (h k (u.obj (Fin.last 1)) -
        ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) :=
      sub_eq_zero.1 (hl k u)
    rw [e]
    refine ((sFil _ _).S _).add_mem (((sFil _ _).S _).sum_mem fun i _ => mem_FC.1 (fc_mem E σ hF ![i] _) u) ?_
    rw [Nat.cast_one, hF.one]
    exact ((sP (KS q s {V})).J.S _).sub_mem (hJ _ _) ((sP (KS q s {V})).J.map_mem _ (hJ _ _))
  refine rep_back hF E σ hc ℓ h hJ hl' (ε y) r hr x _ (fun u => ?_) hx
  subst hr
  have hb := mem_FC.1 (cupList_mem hF (n + 1) ℓ hlm) u
  have e0 : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) =
      (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
        (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) *
      vl (cupListC (sP (KS q s {V})).A ℓ) u := by
    have e : CH.back (Nat.zero_add (n + 1)) = id := by
      funext i
      apply Fin.ext
      simp [CH.back]
    have := term_id (cupListC (sP (KS q s {V})).A ℓ) u _ (CH.back_mono (Nat.zero_add (n + 1))) e
    change _ * (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u _ _ _) = _
    rw [this]
  have ha : ∀ p : Fin (n + 2), ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last p)))).hom
      (show (sP (KS q s {V})).A.obj (u.obj p) from liftV (u.obj p).obj (ks_in q s V (u.obj p).obj (u.obj p).property) y) -
      ((sP (KS q s {V})).A.map (σ _)).hom (ε y) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    intro p
    rw [Nat.cast_one, hF.one]
    have e1 := (sP (KS q s {V})).J.map_mem (u.map (homOfLE (Fin.le_last p))) (lift_sub_mem q s t E ε hL σ y (u.obj p))
    have e2 := const1 hF hc (σ (u.obj p) ≫ u.map (homOfLE (Fin.le_last p))) (σ _) (ε y)
    have e3 := ((sP (KS q s {V})).J.S _).add_mem e1 e2
    rw [map_sub, GlobalTheory.CompanionTheory.CocProd.map_map, sub_add_sub_cancel] at e3
    exact e3
  have e4 := hF.mul _ _ _ hb (ha (CH.front (Nat.zero_add (n + 1)) (Fin.last 0)))
  have e5 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e5] at e4
  convert e4 using 1
  change (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from xdtC s V t y u) - _ = _
  have ea : (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from CH.term (CH.modF (sP (KS q s {V})).A) u
        (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) y) (CH.front (Nat.zero_add (n + 1))) (CH.front_mono _)) =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0)))))).hom
        (show (sP (KS q s {V})).A.obj (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))) from
          liftV (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))).obj
            (ks_in q s V _ (u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))).property) y) := rfl
  rw [e0, ea]
  ring

end Loc

def i0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

/- English proof (translation)
Use `Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)` and prove the remaining obligations. Establish `h : Function.Surjective I.1` using `(Finite.injective_iff_surjective).1 I.2.injective`. Rewrite using `[h.range_eq, Function.surjective_id.range_eq]`.
-/
theorem idx_eq {m : ℕ} (I : Idx m m) : I = i0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

instance {m : ℕ} : Unique (Idx m m) := ⟨⟨i0 m⟩, idx_eq⟩

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Simplify using `only [sgn, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (⇑π)]`.

Simplify using `only [i0, Function.id_comp, if_true]`. Rewrite using `[Units.smul_def]`. Simplify using the standard rewrite rules. Introduce `J _ hJ`. Simplify using `[i0, hJ]`.

Simplify using the standard rewrite rules.
-/
theorem sgn_det {B : Type} [CommRing B] {m : ℕ} (c : Fin m → Fin m → B) :
    ∑ J : Fin m → Fin m, sgn (i0 m) J • ∏ k, c k (J k) = (Matrix.of fun i k => c k i).det := by
  rw [Matrix.det_apply]
  simp only [sgn, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (⇑π)]
  · simp only [i0, Function.id_comp, if_true]
    rw [Units.smul_def]
    simp
  · intro J _ hJ
    simp [i0, hJ]
  · simp

/- English proof (translation)
Distinguish the cases in `h : IsUnit a`. Take `⟨v, rfl⟩` from `h`. Establish `e1 : e (v : A) = ((Units.map e.toMonoidHom v : Bˣ) : B)` using `rfl`. Rewrite using `[e1, Ring.inverse_unit, Ring.inverse_unit]`. Both sides reduce to the same expression.

Establish `h' : ¬ IsUnit (e a)` using `fun hu => h ((MulEquiv.isUnit_map e).1 hu)`. Rewrite using `[Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]`.
-/
theorem inv_map {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) : Ring.inverse (e a) = e (Ring.inverse a) := by
  by_cases h : IsUnit a
  · obtain ⟨v, rfl⟩ := h
    have e1 : e (v : A) = ((Units.map e.toMonoidHom v : Bˣ) : B) := rfl
    rw [e1, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (e a) := fun hu => h ((MulEquiv.isUnit_map e).1 hu)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

/- English proof (translation)
Use `choose v hv using h`. Simplify using `only [← hv]`. Rewrite using `[← Units.coe_prod, Ring.inverse_unit, ← Finset.prod_inv_distrib, Units.coe_prod]`. Simplify using `only [Ring.inverse_unit]`.
-/
theorem inv_prod {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] (u : ι → A) (h : ∀ k, IsUnit (u k)) :
    Ring.inverse (∏ k, u k) = ∏ k, Ring.inverse (u k) := by
  choose v hv using h
  simp only [← hv]
  rw [← Units.coe_prod, Ring.inverse_unit, ← Finset.prod_inv_distrib, Units.coe_prod]
  simp only [Ring.inverse_unit]

/- English proof (translation)
Use `rep_congr h fun u => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_unique]`. Express the relevant statement in the definitionally equal form `E.form σ (i0 m).1 (w (i0 m)) u - _ ∈ _`. Rewrite using `[show (i0 m).1 = id from rfl, sub_self]`. Conclude with `Ideal.zero_mem _`.
-/
theorem rep_one {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {m : ℕ} (E : Frame Φ m)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (w : Idx m m → Φ.A.obj E.D) (cl : CH.H (gr Fil r) m)
    (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m m, E.form σ I.1 (w I) u) cl) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id (w (i0 m))) cl := by
  refine rep_congr h fun u => ?_
  rw [Fintype.sum_unique]
  change E.form σ (i0 m).1 (w (i0 m)) u - _ ∈ _
  rw [show (i0 m).1 = id from rfl, sub_self]
  exact Ideal.zero_mem _

/- English proof (translation)
Introduce `_ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD g hg ĝ hĝ x hx`. Use `left`. Take `⟨E, ε, hL⟩` from `GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)`. Set `σ : ∀ T, E.D ⟶ T` to `fun T => (E.ne T).some`. Establish `hF` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})`.

Establish `hc : E.GrConst (sFil (KS q s {V}))` using `hL.1`. Establish `hT` using `GlobalTheory.CompanionTheory.ConeLocal.taylor_loc q c s E ε hL D hD`. Establish `hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Establish `h1` using `rep_res (ks_le q s hVV) _ _ hx`. Use `choose h hh happ using fun k => GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main q s (by omega) hVV c.t E ε hL _ hT σ (g k) (hg k) (ĝ k) (hĝ k)`.

Set `ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1` to `fun k => resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s (ĝ k))`. Set `cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D` to `fun k i => Ring.inverse (ε (rs hVV (g k))) * ε (D i (ε.symm (ε (rs hVV (g k)))))`. Establish `h2 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from cupListC (sP (KS q s {V})).A ℓ u) * ((sP (KS q s {V})).A.map (σ _)).hom 1) (resKS q s hVV _ …`. Use `rep_congr h1 fun u => ?_` and prove the remaining obligations. Establish `e` using `congrFun (cup_resQ (ks_le q s hVV) (fun k => dlogC (KS q s {V'}) s (ĝ k))) u`.

Rewrite using `[map_one, mul_one]`. Conclude with `(sub_eq_zero.2 e) ▸ Ideal.zero_mem _`. Establish `h3` using `GlobalTheory.CompanionTheory.CupRep.cup_rep hF E σ hc (n + 1) ℓ cc h hh happ 1 _ hr _ h2`. Establish `h4` using `GlobalTheory.CompanionTheory.ConeLocal.rep_collapse hF E σ hc (n + 1) _ hr (fun I => I) (fun I => 1 * ∏ k, cc k (I k)) _ h3`. Establish `h5` using `rep_one E σ _ (fun I => ∑ J, sgn I J • (1 * ∏ k, cc k (J k))) _ h4`.

Establish `hu : ∀ k, IsUnit (rs hVV (g k))` using `fun k => (hg k).map (rs hVV)`. Establish `e : ∑ J : Fin (n + 1) → Fin (n + 1), sgn (i0 (n + 1)) J • (1 * ∏ k, cc k (J k)) = ε (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det)`. Simplify using `only [one_mul]`. Rewrite using `[sgn_det, inv_prod _ hu, ← Matrix.det_mul_row]`. Establish `e1` using `(ε : Γ(X, V) →+* (sP (KS q s {V})).A.obj E.D).map_det (Matrix.of fun k l => Ring.inverse (rs hVV (g l)) * D k (rs hVV (g l)))`.

Use `Eq.trans ?_ e1.symm` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i k`. Simplify using `[cc, inv_map]`. Rewrite `h5` using `[e]`.

Conclude with `xdt_rep q s c.t E ε hL σ _ _ hr _ h5`.
-/
theorem main : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' →
    ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, V')), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
    (∀ k T, Ideal.Quotient.mk _ (ĝ k T) = ev T.obj (ks_in q s V' T.obj T.property) (g k)) →
    ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (cupListC (sP (KS q s {V'})).A fun k => dlogC (KS q s {V'}) s (ĝ k)) (x) →
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det)) (resKS q s hVV _ _ _ x) ∨
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (-(Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det))) (resKS q s hVV _ _ _ x) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD g hg ĝ hĝ x hx
  left
  obtain ⟨E, ε, hL⟩ := GlobalTheory.CompanionTheory.ConeLocal.exists_loc q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.CompanionTheory.ConeLocal.taylor_loc q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have h1 := rep_res (ks_le q s hVV) _ _ hx
  choose h hh happ using fun k => GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main q s (by omega) hVV c.t E ε hL _ hT σ (g k) (hg k) (ĝ k) (hĝ k)
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s (ĝ k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i =>
    Ring.inverse (ε (rs hVV (g k))) * ε (D i (ε.symm (ε (rs hVV (g k)))))
  have h2 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from cupListC (sP (KS q s {V})).A ℓ u) *
        ((sP (KS q s {V})).A.map (σ _)).hom 1) (resKS q s hVV _ _ _ x) := by
    refine rep_congr h1 fun u => ?_
    have e := congrFun (cup_resQ (ks_le q s hVV) (fun k => dlogC (KS q s {V'}) s (ĝ k))) u
    rw [map_one, mul_one]
    exact (sub_eq_zero.2 e) ▸ Ideal.zero_mem _
  have h3 := GlobalTheory.CompanionTheory.CupRep.cup_rep hF E σ hc (n + 1) ℓ cc h hh happ 1 _ hr _ h2
  have h4 := GlobalTheory.CompanionTheory.ConeLocal.rep_collapse hF E σ hc (n + 1) _ hr (fun I => I) (fun I => 1 * ∏ k, cc k (I k)) _ h3
  have h5 := rep_one E σ _ (fun I => ∑ J, sgn I J • (1 * ∏ k, cc k (J k))) _ h4
  have hu : ∀ k, IsUnit (rs hVV (g k)) := fun k => (hg k).map (rs hVV)
  have e : ∑ J : Fin (n + 1) → Fin (n + 1), sgn (i0 (n + 1)) J • (1 * ∏ k, cc k (J k)) =
      ε (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det) := by
    simp only [one_mul]
    rw [sgn_det, inv_prod _ hu, ← Matrix.det_mul_row]
    have e1 := (ε : Γ(X, V) →+* (sP (KS q s {V})).A.obj E.D).map_det
      (Matrix.of fun k l => Ring.inverse (rs hVV (g l)) * D k (rs hVV (g l)))
    refine Eq.trans ?_ e1.symm
    congr 1
    ext i k
    simp [cc, inv_map]
  rw [e] at h5
  exact xdt_rep q s c.t E ε hL σ _ _ hr _ h5

end GlobalTheory.CompanionTheory.ConeLdlog
