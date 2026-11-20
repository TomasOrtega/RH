import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.LExact

open GlobalTheory.CompanionTheory.CupRep

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (V : X.Opens)
  {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
  (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (σ : ∀ T, E.D ⟶ T)

def lf (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) : (sP (KS q s {V})).A.obj T :=
  liftV T.obj (ks_in q s V T.obj T.property) g

variable {q s V t E ε}

/- English proof (translation)
Establish `a1 : Ideal.Quotient.mk T.obj.J (lf q s V g T) = ev T.obj (ks_in q s V T.obj T.property) g` using `Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) g))`. Establish `a2` using `hL.2.2.2.1 T u g`. Conclude with `Ideal.Quotient.eq.1 (a1.trans a2)`.
-/
theorem lf_sub_mem (hL : IsLoc q s t E ε) (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) (u : E.D ⟶ T) :
    lf q s V g T - ((sP (KS q s {V})).A.map u).hom (ε g) ∈ (sP (KS q s {V})).J.S T := by
  have a1 : Ideal.Quotient.mk T.obj.J (lf q s V g T) = ev T.obj (ks_in q s V T.obj T.property) g :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) g))
  have a2 := hL.2.2.2.1 T u g
  exact Ideal.Quotient.eq.1 (a1.trans a2)

/- English proof (translation)
Establish `e1 : ∑ i, E.form σ ![i] (if k = i then (1 : (sP (KS q s {V})).A.obj E.D) else 0) u = E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1))))`. Simplify using `only [DlogApprox.form_one]`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[if_pos rfl, map_one, mul_one]`. Introduce `b _ hb`.

Rewrite using `[if_neg (Ne.symm hb), map_zero, mul_zero]`. Simplify using the standard rewrite rules. Establish `e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) = ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) - ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k))` using `hL.2.2.2.2 k _ _`. Establish `e3 : ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) = ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)))`. Rewrite using `[Functor.map_comp]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, e3, map_sub]`. Express the relevant statement in the definitionally equal form `(lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (lf q s V (t k) (u.obj 0))) - _ = 0`. Normalize the expressions using the abelian group laws.
-/
theorem addC_eq (hL : IsLoc q s t E ε) (k : Fin d) (u : ComposableArrows (KS q s {V}).FullSubcategory 1) :
    (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from addC (KS q s {V}) (lf q s V (t k)) u) -
      (∑ i, E.form σ ![i] (if k = i then 1 else 0) u +
        ((lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) -
          ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
            (lf q s V (t k) (u.obj 0) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))))) = 0 := by
  have e1 : ∑ i, E.form σ ![i] (if k = i then (1 : (sP (KS q s {V})).A.obj E.D) else 0) u =
      E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
    simp only [DlogApprox.form_one]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, map_one, mul_one]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, mul_zero]
    · simp
  have e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) =
      ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
      ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) :=
    hL.2.2.2.2 k _ _
  have e3 : ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) := by
    rw [Functor.map_comp]; rfl
  rw [e1, e2, e3, map_sub]
  change (lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (lf q s V (t k) (u.obj 0))) - _ = 0
  abel
end

section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

/- English proof (translation)
Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `E.form σ I 0 s = 0`. Unfold `Frame.form`. Rewrite using `[map_zero, mul_zero]`.
-/
theorem fc_zero {j : ℕ} (I : Fin j → Fin d) : fc E σ I 0 = 0 := by
  funext s
  change E.form σ I 0 s = 0
  unfold Frame.form
  rw [map_zero, mul_zero]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single id]`. Simplify using the standard rewrite rules. Introduce `I _ hI`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, k ≠ I k := by`. Assume the negation of the conclusion as `hh`.

Use `push_neg at hh`. Conclude with `hI (funext fun k => (hh k).symm)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), fc_zero]`. Simplify using the standard rewrite rules.
-/
theorem sum_fc_delta (m : ℕ) (E : Frame Φ m) (σ : ∀ T : C, E.D ⟶ T) :
    ∑ I : Fin m → Fin m, fc E σ I (∏ k, if k = I k then (1 : Φ.A.obj E.D) else 0) = fc E σ id 1 := by
  rw [Finset.sum_eq_single id]
  · simp
  · intro I _ hI
    obtain ⟨k, hk⟩ : ∃ k, k ≠ I k := by
      by_contra hh
      push_neg at hh
      exact hI (funext fun k => (hh k).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), fc_zero]
  · simp
end

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {s : ℕ} {V : X.Opens}

/- English proof (translation)
Substitute `hr` using the available equality. Establish `hF` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})`. Establish `hc : E.GrConst (sFil (KS q s {V}))` using `hL.1`. Set `ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1` to `fun k => addC (KS q s {V}) (lf q s V (t k))`. Set `cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D` to `fun k i => if k = i then 1 else 0`.

Set `hh : Fin (n + 1) → ∀ T, (sP (KS q s {V})).A.obj T` to `fun k T => lf q s V (t k) T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))`. Establish `hJ : ∀ k T, hh k T ∈ (sP (KS q s {V})).J.S T` using `fun k T => lf_sub_mem hL _ T (σ T)`. Establish `hh0 : ∀ k, h0 (hh k) ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 0` using `fun k => mem_FC.2 fun u => by`. Use `hJ k (u.obj (Fin.last 0))` as an intermediate fact. Rewrite `this` using `[← hF.one]`.

Rewrite using `[Nat.cast_one]`. Conclude with `this`. Establish `he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k))) ∈ FC (sFil (KS q s {V}) ((1 + 1 : ℕ) : ℤ)) 1` using `fun k => mem_FC.2 fun u => by`. Establish `e : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k)))) u = (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (cc k i) u + (hh k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le ( …`. Rewrite using `[← cech_d_h0_eval]`.

Express the relevant statement in the definitionally equal form `_ - (vl (∑ i, fc E σ ![i] (cc k i)) u + _) = _`. Use `congr 2`. Rewrite using `[vl, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Establish `e0` using `addC_eq σ hL k u`. Conclude with `e0 ▸ Ideal.zero_mem _`. Take `⟨g, hg, hn⟩` from `near E σ hF hc (n + 1) ℓ cc (fun k => h0 (hh k)) hh0 he`. Take `⟨H, hH, rfl⟩` from `hg`. Rewrite `hn` using `[show (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, cc k (I k))) = fc E σ id 1 from sum_fc_delta _ E σ]`.

Establish `hcL : cupListC (sP (KS q s {V})).A ℓ ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1)`. Establish `h1` using `FC_anti hF (r := ((n + 1 : ℕ) : ℤ)) (by push_cast; omega) hn`. Establish `h2 : fc E σ id (1 : (sP (KS q s {V})).A.obj E.D) ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1)` using `fc_mem E σ hF id 1`. Establish `h3` using `d_mem hH`. Use `add_mem (add_mem h1 h3) h2` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, sub_add_cancel]`. Then use the resulting hypothesis. Set `H' : CH.Cn (CH.modF (sP (KS q s {V})).A) n` to `fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from H u) * ((sP (KS q s {V})).A.map (σ _)).hom (ε w)`. Establish `hH' : H' ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) n` using `mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)`. Establish `h1` using `rep_add h (rep_d (b := sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))`. Rewrite `h1` using `[add_zero]`.

Use `rep_congr h1 fun u => ?_` and prove the remaining obligations. Establish `e1` using `mem_FC.1 hn u`. Establish `e2` using `d_mul E σ hF hc (ε w) hH u`. Establish `e5` using `form_mul E σ id (ε w) 1 u`. Rewrite `e5` using `[mul_one]`.

Set `ψ` to `u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))))`. Set `T0` to `u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))`. Establish `a1 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0 - ((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) ∈ (sP (KS q s {V})).J.S _` using `(sP (KS q s {V})).J.map_mem ψ (lf_sub_mem hL w T0 (σ T0))`. Establish `a2` using `DlogApprox.const1 hF hc (σ T0 ≫ ψ) (σ (u.obj (Fin.last (n + 1)))) (ε w)`. Establish `a3 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) - ((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _`.

Rewrite using `[Nat.cast_one, hF.one]`. Establish `a4` using `((sP (KS q s {V})).J.S _).add_mem a1 a2`. Establish `e3 : ((sP (KS q s {V})).A.map (σ T0 ≫ ψ)).hom (ε w) = ((sP (KS q s {V})).A.map ψ).hom (((sP (KS q s {V})).A.map (σ T0)).hom (ε w))`. Rewrite using `[Functor.map_comp]`. Both sides reduce to the same expression.

Rewrite `a4` using `[e3, map_sub, sub_add_sub_cancel]`. Conclude with `a4`. Establish `ex : vl (xdtC (q` using `q) s V t w) u = ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * vl (cupListC (sP (KS q s {V})).A ℓ) u := congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) => ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * b) (CrystallineSemistableComparison.Auxff.term_id _ …`. Establish `e6` using `hF.mul 1 (n + 1) _ a3 (mem_FC.1 hcL u)`. Establish `e7 : ((1 + (n + 1) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1` using `by push_cast; ring`.

Establish `e8 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1` using `by push_cast; ring`. Rewrite `e6` using `[e7]`. Rewrite `e1`, `e2` using `[e8]`. Establish `e9` using `((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem (Ideal.mul_mem_right (((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w)) _ e1)) (((sFil …`. Express the relevant statement in the definitionally equal form `E.form σ id (ε w) u + vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u - vl (xdtC (q := q) s V t w) u ∈ _`.

Rewrite using `[ex, e5]`. Use `e9 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = -((vl (cupListC (sP (KS q s {V})).A ℓ) u - vl (fc E σ id 1) u - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u) * _) + -(vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u * _ - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u) + -(_ * _)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rep_xdt {n : ℕ} {t : Fin (n + 1) → Γ(X, V)} {E : Frame (sP (KS q s {V})) (n + 1)}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (w : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (cl : HQ (KS q s {V}) r (r + 1) (n + 1))
    (h : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε w)) cl) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t w) cl := by
  subst hr
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => addC (KS q s {V}) (lf q s V (t k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i => if k = i then 1 else 0
  let hh : Fin (n + 1) → ∀ T, (sP (KS q s {V})).A.obj T := fun k T =>
    lf q s V (t k) T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hJ : ∀ k T, hh k T ∈ (sP (KS q s {V})).J.S T := fun k T => lf_sub_mem hL _ T (σ T)
  have hh0 : ∀ k, h0 (hh k) ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun u => by
    have := hJ k (u.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k))) ∈
      FC (sFil (KS q s {V}) ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k)))) u =
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (cc k i) u +
          (hh k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (hh k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (cc k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    have e0 := addC_eq σ hL k u
    exact e0 ▸ Ideal.zero_mem _
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ cc (fun k => h0 (hh k)) hh0 he
  obtain ⟨H, hH, rfl⟩ := hg
  rw [show (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, cc k (I k))) = fc E σ id 1 from sum_fc_delta _ E σ] at hn
  have hcL : cupListC (sP (KS q s {V})).A ℓ ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := by
    have h1 := FC_anti hF (r := ((n + 1 : ℕ) : ℤ)) (by push_cast; omega) hn
    have h2 : fc E σ id (1 : (sP (KS q s {V})).A.obj E.D) ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := fc_mem E σ hF id 1
    have h3 := d_mem hH
    have := add_mem (add_mem h1 h3) h2
    rwa [sub_add_cancel, sub_add_cancel] at this
  let H' : CH.Cn (CH.modF (sP (KS q s {V})).A) n := fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from H u) * ((sP (KS q s {V})).A.map (σ _)).hom (ε w)
  have hH' : H' ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add h (rep_d (b := sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc (ε w) hH u
  have e5 := form_mul E σ id (ε w) 1 u
  rw [mul_one] at e5
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))))
  let T0 := u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))
  have a1 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0 - ((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) ∈
      (sP (KS q s {V})).J.S _ := (sP (KS q s {V})).J.map_mem ψ (lf_sub_mem hL w T0 (σ T0))
  have a2 := DlogApprox.const1 hF hc (σ T0 ≫ ψ) (σ (u.obj (Fin.last (n + 1)))) (ε w)
  have a3 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) - ((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w) ∈
      (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    have a4 := ((sP (KS q s {V})).J.S _).add_mem a1 a2
    have e3 : ((sP (KS q s {V})).A.map (σ T0 ≫ ψ)).hom (ε w) =
        ((sP (KS q s {V})).A.map ψ).hom (((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) := by
      rw [Functor.map_comp]; rfl
    rw [e3, map_sub, sub_add_sub_cancel] at a4
    exact a4
  have ex : vl (xdtC (q := q) s V t w) u = ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * vl (cupListC (sP (KS q s {V})).A ℓ) u :=
    congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) => ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * b)
      (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))
  have e6 := hF.mul 1 (n + 1) _ a3 (mem_FC.1 hcL u)
  have e7 : ((1 + (n + 1) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  have e8 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e7] at e6
  rw [e8] at e1 e2
  have e9 := ((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem
        (Ideal.mul_mem_right (((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w)) _ e1))
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e2))
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e6)
  change E.form σ id (ε w) u + vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u - vl (xdtC (q := q) s V t w) u ∈ _
  rw [ex, e5]
  convert e9 using 1
  change _ = -((vl (cupListC (sP (KS q s {V})).A ℓ) u - vl (fc E σ id 1) u - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u) * _) +
    -(vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u * _ - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u) + -(_ * _)
  ring
end

/- English proof (translation)
Introduce `_ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD f hf hdf x hx`. Use `haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q`. Take `⟨E, ε, hL⟩` from `GlobalTheory.T.exists_local_frame_of_coords q c s (by omega)`. Set `σ : ∀ T, E.D ⟶ T` to `fun T => (E.ne T).some`. Establish `hF` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})`.

Establish `hc : E.GrConst (sFil (KS q s {V}))` using `hL.1`. Establish `hT` using `GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD`. Establish `hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Take `⟨ξ, hξ⟩` from `rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf`. Establish `h1` using `rep_res (ks_le q s hVV) _ _ hξ`.

Establish `h2` using `rep_res (ks_le q s hVV) _ _ hx`. Take `⟨y, hy⟩` from `(GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)`. Establish `hmem` using `GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy`. Establish `h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x)`. Use `rep_congr h2 fun u => ?_` and prove the remaining obligations.

Establish `e` using `congrFun (d_resQ (ks_le q s hVV) f) u`. Conclude with `(sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _`. Establish `h3` using `GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'`. Establish `h4` using `GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3`. Establish `h5` using `rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4`.

Set `Ik : Fin (n + 1) → Idx n (n + 1)` to `fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩`. Set `sg : Fin (n + 1) → ℤ` to `fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)`. Use `⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.zsmul_mem _ (hmem (Ik k)) _`. Establish `e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α` using `fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) = ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by`.

Rewrite using `[Fintype.sum_prod_type_right, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (Ik k)]`. Establish `a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1` using `by rw [← mul_pow]; simp`. Rewrite using `[map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]`.

Use `push_cast`. Establish `a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) = (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k)))`. Take the linear combination `((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1`. Rewrite using `[a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]`. Introduce `I _ hI`.

Rewrite using `[sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `h5` using `[e]`. Conclude with `rep_xdt hL σ _ _ hr _ h5`.
-/
theorem main : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' →
    ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (f : CH.Cn (CH.modF (sP (KS q s {V'})).A) n), (∀ σ, f σ ∈ (sFil (KS q s {V'}) n).S _) →
      (∀ σ, CH.d _ n f σ ∈ (sFil (KS q s {V'}) ((n : ℤ) + 1)).S _) →
      ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (CH.d _ n f) (x) →
      ∃ η : Fin (n + 1) → Γ(X, V), (∀ k, η k ∈ jacSpan hVV (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
        Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k))) (resKS q s hVV _ _ _ x) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD f hf hdf x hx
  haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
  obtain ⟨E, ε, hL⟩ := GlobalTheory.T.exists_local_frame_of_coords q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨ξ, hξ⟩ := rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf
  have h1 := rep_res (ks_le q s hVV) _ _ hξ
  have h2 := rep_res (ks_le q s hVV) _ _ hx
  obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)
  have hmem := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy
  have h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x) := by
    refine rep_congr h2 fun u => ?_
    have e := congrFun (d_resQ (ks_le q s hVV) f) u
    exact (sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _
  have h3 := GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'
  have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2)
    (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3
  have h5 := rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4
  let Ik : Fin (n + 1) → Idx n (n + 1) := fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩
  let sg : Fin (n + 1) → ℤ := fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)
  refine ⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩
  · exact AddSubgroup.zsmul_mem _ (hmem (Ik k)) _
  · have e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) =
        ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by
      rw [Fintype.sum_prod_type_right, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single (Ik k)]
      · have a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; simp
        rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]
        push_cast
        have a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) =
            (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k))) := by
          linear_combination ((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1
        rw [a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]
      · intro I _ hI
        rw [sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [e] at h5
    exact rep_xdt hL σ _ _ hr _ h5

end GlobalTheory.CompanionTheory.ConeLocal.LExact
