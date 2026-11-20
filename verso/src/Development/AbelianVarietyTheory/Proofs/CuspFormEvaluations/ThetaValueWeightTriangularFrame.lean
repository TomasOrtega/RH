import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionLinearInSectionStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaValueWeight

/- English proof (translation)
Simplify using `[Scheme.Hom.appLE]`. Use `erw [Category.id_comp]`. Conclude with `Y.presheaf.map_id _`.
-/
theorem appLE_id {Y : Scheme.{0}} (U : Y.Opens) : Scheme.Hom.appLE (𝟙 Y) U U le_rfl = 𝟙 _ := by
  simp [Scheme.Hom.appLE]
  erw [Category.id_comp]
  exact Y.presheaf.map_id _

/- English proof (translation)
Establish `hs : Function.support (fun j => r * f j) = Function.support f`. Use extensionality with `j`. Simplify using `[hr.mul_right_eq_zero]`. Distinguish the cases in `h : (Function.support f).Finite`. Rewrite using `[finsum_eq_sum_of_support_subset f (s := h.toFinset) (by simp), finsum_eq_sum_of_support_subset (fun j => r * f j) (s := h.toFinset) (by rw [hs]; simp), Finset.mul_sum]`.

Rewrite using `[finsum_of_infinite_support h, finsum_of_infinite_support (hs ▸ h), mul_zero]`.
-/
theorem unit_mul_finsum {R J : Type} [CommRing R] {r : R} (hr : IsUnit r) (f : J → R) :
    r * ∑ᶠ j, f j = ∑ᶠ j, r * f j := by
  have hs : Function.support (fun j => r * f j) = Function.support f := by
    ext j
    simp [hr.mul_right_eq_zero]
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum_of_support_subset f (s := h.toFinset) (by simp),
      finsum_eq_sum_of_support_subset (fun j => r * f j) (s := h.toFinset) (by rw [hs]; simp),
      Finset.mul_sum]
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support (hs ▸ h), mul_zero]

section Scale

variable {X : Scheme.{0}} (A : Over X) [GrpObj A]

/- English proof (translation)
Unfold `liftFun`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_liftFun {T : Over X} {W W' : (T ⊗ A).left.Opens} (h : W' ≤ W) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom (liftFun A W r) = liftFun A W' r := by
  unfold liftFun
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Establish `e : ψ.left ≫ (fst T A).left = (fst T A).left` using `by rw [← Over.comp_left, hψ]`. Establish `h₁ : W ≤ (fst T A).left ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Establish `h₂ : W' ≤ (fst T A).left ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Express the relevant statement in the definitionally equal form `((fst T A).left.appLE ⊤ W h₁ ≫ ψ.left.appLE W W' h).hom r = ((fst T A).left.appLE ⊤ W' h₂).hom r`. Conclude with `congrArg (fun f => (CommRingCat.Hom.hom f) r) ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (FramedBaseChange.appLE_eq_of_eq e _ _ _ _))`.
-/
theorem pull_liftFun {T : Over X} (ψ : T ⊗ A ⟶ T ⊗ A) (hψ : ψ ≫ fst T A = fst T A)
    {W W' : (T ⊗ A).left.Opens} (h : W' ≤ ψ.left ⁻¹ᵁ W) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom ((ψ.left.app W).hom (liftFun A W r)) = liftFun A W' r := by
  have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
  have h₁ : W ≤ (fst T A).left ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h₂ : W' ≤ (fst T A).left ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change ((fst T A).left.appLE ⊤ W h₁ ≫ ψ.left.appLE W W' h).hom r = ((fst T A).left.appLE ⊤ W' h₂).hom r
  exact congrArg (fun f => (CommRingCat.Hom.hom f) r)
    ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (FramedBaseChange.appLE_eq_of_eq e _ _ _ _))

/- English proof (translation)
Rewrite using `[map_mul, map_mul, map_mul, hx, hx']`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma twist_lemma {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    (ρ : R₁ →+* R₄) (ψa : R₂ →+* R₃) (ρ₂ : R₃ →+* R₄) (x x' : R₁) (z z' : R₂) (c : R₄)
    (hx : ρ x = ρ₂ (ψa z)) (hx' : ρ x' = c * ρ₂ (ψa z')) :
    ρ (x * x') = c * ρ₂ (ψa (z * z')) := by
  rw [map_mul, map_mul, map_mul, hx, hx']
  ring

def scaleSec {L : LB A.left} {k : ℤ} {T : Over X} (r : Γ(T.left, ⊤)) (s : LB.Sec (LPow A L k T)) :
    LB.Sec (LPow A L k T) where
  f j := liftFun A _ r * s.f j
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, res_liftFun, res_liftFun]
    ring

/- English proof (translation)
Unfold `IsTwistPull at h ⊢`. Introduce `j`. Establish `e1 : (scaleSec A r s').f (fun _ => j 0) = liftFun A _ r * s'.f (fun _ => j 0)` using `rfl`. Establish `e2` using `hs (fun _ => j 1)`. Rewrite using `[e1, e2]`.

Conclude with `twist_lemma _ _ _ _ _ _ _ _ ((res_liftFun A _ r).trans (pull_liftFun A ψ hψ _ r).symm) (h j)`.
-/
theorem isTwistPull_scale {L : LB A.left} {T : Over X} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A}
    {hm : ψ ≫ snd T A = m} (hψ : ψ ≫ fst T A = fst T A) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s s₀ : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)} (r : Γ(T.left, ⊤))
    (hs : ∀ j, s₀.f j = liftFun A _ r * s.f j) (h : IsTwistPull A L ψ m hm a b α s s') :
    IsTwistPull A L ψ m hm a b α s₀ (scaleSec A r s') := by
  unfold IsTwistPull at h ⊢
  intro j
  have e1 : (scaleSec A r s').f (fun _ => j 0) = liftFun A _ r * s'.f (fun _ => j 0) := rfl
  have e2 := hs (fun _ => j 1)
  rw [e1, e2]
  exact twist_lemma _ _ _ _ _ _ _ _ ((res_liftFun A _ r).trans (pull_liftFun A ψ hψ _ r).symm) (h j)

variable [IsCommMonObj A] (L : RigLB A)

/- English proof (translation)
Take `⟨t', α₀, α, s₁, U, h1, h2, h3, h4, h5, h6, h7, h8⟩` from `h`. Use `⟨t', α₀, α, scaleSec A r s₁, U, h1, h2, h3, h4, h5, ?_, h7, ?_⟩` and prove the remaining obligations. Conclude with `isTwistPull_scale A (by simp [mulT]) r hs h6`. Conclude with `isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h8`.
-/
theorem isVtOver_scale {N : ℕ} {T : Over X} {ok : (T ⟶ A) → Prop} {s s₀ : LB.Sec (LPow A L.L 1 T)} {t : T ⟶ A}
    {F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)} (r : Γ(T.left, ⊤)) (hs : ∀ j, s₀.f j = liftFun A _ r * s.f j)
    (h : IsVtOver A L N ok s t F) : IsVtOver A L N ok s₀ t (scaleSec A r F) := by
  obtain ⟨t', α₀, α, s₁, U, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨t', α₀, α, scaleSec A r s₁, U, h1, h2, h3, h4, h5, ?_, h7, ?_⟩
  · exact isTwistPull_scale A (by simp [mulT]) r hs h6
  · exact isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h8

/- English proof (translation)
Take `⟨α₀, α, s₁, s₂, U₁, U₂, h1, h2, h3, h4, h5, h6, h7, h8⟩` from `h`. Use `⟨α₀, α, scaleSec A r s₁, scaleSec A r s₂, U₁, U₂, h1, h2, h3, ?_, h5, ?_, h7, ?_⟩` and prove the remaining obligations. Conclude with `isTwistPull_scale A (by simp [mulT]) r hs h4`. Conclude with `isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h6`. Conclude with `isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h8`.
-/
theorem isUUOver_scale {N : ℕ} {T : Over X} {s s₀ : LB.Sec (LPow A L.L 1 T)} {x₁ x₂ : T ⟶ A}
    {F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)} (r : Γ(T.left, ⊤)) (hs : ∀ j, s₀.f j = liftFun A _ r * s.f j)
    (h : IsUUOver A L N s x₁ x₂ F) : IsUUOver A L N s₀ x₁ x₂ (scaleSec A r F) := by
  obtain ⟨α₀, α, s₁, s₂, U₁, U₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨α₀, α, scaleSec A r s₁, scaleSec A r s₂, U₁, U₂, h1, h2, h3, ?_, h5, ?_, h7, ?_⟩
  · exact isTwistPull_scale A (by simp [mulT]) r hs h4
  · exact isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h6
  · exact isTwistPull_scale A (by simp [translT]) r (fun _ => rfl) h8

omit [IsCommMonObj A] in
/- English proof (translation)
Unfold `IsPullSec`. Introduce `j`. Establish `key : ∀ {Z : Scheme.{0}} (g : Z ⟶ Z) (_ : g = 𝟙 Z) (V : Z.Opens) (h' : V ≤ g ⁻¹ᵁ V) (x : Γ(Z, V)), (Z.presheaf.map (homOfLE h').op).hom ((g.app V).hom x) = x`. Introduce `Z g hg V h' x`. Substitute `hg` using the available equality.

Express the relevant statement in the definitionally equal form `(Scheme.Hom.appLE (𝟙 Z) V V le_rfl).hom x = x`. Simplify using `[appLE_id]`. Conclude with `(key _ (by rw [MonoidalCategory.id_whiskerRight, Over.id_left]) _ _ _).symm`.
-/
theorem isPullSec_id {L : LB A.left} {k : ℤ} {T : Over X} (s : LB.Sec (LPow A L k T)) :
    IsPullSec A L k (𝟙 T ▷ A) (whiskerRight_snd _ _) s s := by
  unfold IsPullSec
  intro j
  have key : ∀ {Z : Scheme.{0}} (g : Z ⟶ Z) (_ : g = 𝟙 Z) (V : Z.Opens) (h' : V ≤ g ⁻¹ᵁ V) (x : Γ(Z, V)),
      (Z.presheaf.map (homOfLE h').op).hom ((g.app V).hom x) = x := by
    intro Z g hg V h' x
    subst hg
    change (Scheme.Hom.appLE (𝟙 Z) V V le_rfl).hom x = x
    simp [appLE_id]
  exact (key _ (by rw [MonoidalCategory.id_whiskerRight, Over.id_left]) _ _ _).symm

end Scale

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Reframe {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Type where
  u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)
  tan : ∀ τ i, IsTanAt y.x (u τ i)
  eig : ∀ τ i, IsEigAt c τ (u τ i)
  basis : ∀ τ w, IsTanAt y.x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt y.x (u τ) a w
  s : LB.Sec (PPx y.x)
  gen : ∀ s' : LB.Sec (PPx y.x), ∃! a : S, ∀ i, s'.f i = scal y.x a i * s.f i

abbrev Reframe.pt {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (d : Reframe y) : FrPt Xo c S :=
  ⟨y.x, y.x_over, d.u, d.tan, d.eig, d.basis, d.s, d.gen⟩

/- English proof (translation)
Take `⟨x, xo, u, tan, eig, basis, s, gen⟩` from `y'`. Simplify using `only at h`. Substitute `h` using the available equality. Conclude with `⟨⟨u, tan, eig, basis, s, gen⟩, rfl⟩`.
-/
theorem exists_reframe {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (h : y'.x = y.x) :
    ∃ d : Reframe y, y' = d.pt := by
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := y'
  dsimp only at h
  subst h
  exact ⟨⟨u, tan, eig, basis, s, gen⟩, rfl⟩

/- English proof (translation)
Take `⟨-, -, pm, hs, hf, hpm⟩` from `hb`. Establish `e : pm = 𝟙 _` using `FramedBaseChange.pulledGroup_hom_ext pm (𝟙 _) (hs.trans (Category.id_comp _).symm) (hf.trans (Category.id_comp _).symm)`. Substitute `e` using the available equality. Use `hpm i le_rfl` as an intermediate fact. Rewrite `this` using `[appLE_id]`.

Rewrite using `[← this]`. Simplify using `only [CommRingCat.hom_id, RingHom.id_apply]`. Both sides reduce to the same expression.
-/
theorem gen_eq {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (d : Reframe y) {t : Ix Dw → Sˣ}
    (hb : FrBor t y d.pt) (i : Fin 1 → Xo.univ.t.PP.L.ι) :
    d.s.f i = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S (t none : S)) * y.s.f i := by
  obtain ⟨-, -, pm, hs, hf, hpm⟩ := hb
  have e : pm = 𝟙 _ := FramedBaseChange.pulledGroup_hom_ext pm (𝟙 _)
    (hs.trans (Category.id_comp _).symm) (hf.trans (Category.id_comp _).symm)
  subst e
  have := hpm i le_rfl
  rw [appLE_id] at this
  rw [← this]
  simp only [CommRingCat.hom_id, RingHom.id_apply]
  rfl

/- English proof (translation)
Unfold `wchar`. Simplify using `[map_prod, map_pow]`.
-/
theorem map_wchar {J : Type} [Fintype J] {K S T : Type} [Field K] [CommRing S] [Algebra K S] [CommRing T]
    [Algebra K T] (φ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    φ (wchar e t) = wchar e (fun i => Units.map (φ : S →* T) (t i)) := by
  unfold wchar
  simp [map_prod, map_pow]

/- English proof (translation)
Unfold `wchar`. Conclude with `⟨∏ i, t i ^ e i, by simp⟩`.
-/
theorem isUnit_wchar {J : Type} [Fintype J] {S : Type} [CommRing S] (e : J → ℕ) (t : J → Sˣ) :
    IsUnit (wchar e t) := by
  unfold wchar
  exact ⟨∏ i, t i ^ e i, by simp⟩

/- English proof (translation)
Establish `h1` using `_root_.GlobalTheory.T.harmonic_sum_triangular_frameChange hC E H Dw l Xo c nab hn S y d.pt t hb (𝟙 _) rfl n a P hP N F F (fun b => isPullSec_id _ (F b))`. Establish `h2 : ∀ b q, nab d.pt ((N : ℤ) ^ 2) (scaleSec Xo.univ.t.G (toΓ S (t none : S)) (F b)) q = (t none : S) * nab d.pt ((N : ℤ) ^ 2) (F b) q` using `fun b q => _root_.GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hn S d.pt N (F b) _ (t none : S) (fun _ => rfl) q`. Establish `hw : wchar (ex Dw a n) t = (t none : S) ^ n * ∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)`. Unfold `wchar ex`. Simplify using `[Fintype.prod_option]`.

Simplify using `only [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[hw, _root_.mul_assoc, ← h1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab : NabV Xo c} (hn : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (d : Reframe y) {t : Ix Dw → Sˣ}
    (hb : FrBor t y d.pt) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab d.pt ((N : ℤ) ^ 2) (scaleSec Xo.univ.t.G (toΓ S (t none : S)) (F b)) (colOf m b) =
      wchar (ex Dw a n) t * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  have h1 := _root_.GlobalTheory.T.harmonic_sum_triangular_frameChange hC E H Dw l Xo c nab hn S y d.pt t hb (𝟙 _) rfl n a P hP N F F
    (fun b => isPullSec_id _ (F b))
  have h2 : ∀ b q, nab d.pt ((N : ℤ) ^ 2) (scaleSec Xo.univ.t.G (toΓ S (t none : S)) (F b)) q =
      (t none : S) * nab d.pt ((N : ℤ) ^ 2) (F b) q :=
    fun b q => _root_.GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hn S d.pt N (F b) _ (t none : S) (fun _ => rfl) q
  have hw : wchar (ex Dw a n) t = (t none : S) ^ n * ∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2) := by
    unfold wchar ex
    simp [Fintype.prod_option]
  simp only [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hw, _root_.mul_assoc, ← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]`.
-/
private lemma dualMap_comp_epsMul_cusp_form_evaluations {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (a : S) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

/- English proof (translation)
Apply the tactic sequence `refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
private lemma dualMap_comp_algebraMap_cusp_form_evaluations {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) :
    (dualMap f).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp f := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Conclude with `congrArg (fun q => (CommRingCat.Hom.hom q) r) ((Scheme.Hom.appLE_comp_appLE p f₁ ⊤ W W' h₁ h).trans ((FramedBaseChange.appLE_eq_of_eq e ⊤ W' _ _).trans ((Scheme.Hom.appLE_comp_appLE f₂ g ⊤ (g ⁻¹ᵁ ⊤) W' le_rfl h₂).symm.trans (show g.appLE ⊤ (g ⁻¹ᵁ ⊤) le_rfl ≫ f₂.appLE (g ⁻¹ᵁ ⊤) W' …`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Use the proof step `rfl))))`.
-/
private lemma appLE_appLE_eq_of_comp_eq {X Y Z₁ Z₂ : Scheme.{0}} (p : X ⟶ Y) (f₁ : Y ⟶ Z₁) (f₂ : X ⟶ Z₂) (g : Z₂ ⟶ Z₁)
    (e : p ≫ f₁ = f₂ ≫ g) (W : Y.Opens) (W' : X.Opens) (h : W' ≤ p ⁻¹ᵁ W) (h₁ : W ≤ f₁ ⁻¹ᵁ ⊤)
    (h₂ : W' ≤ f₂ ⁻¹ᵁ ⊤) (r : Γ(Z₁, ⊤)) :
    (p.appLE W W' h).hom ((f₁.appLE ⊤ W h₁).hom r) = (f₂.appLE ⊤ W' h₂).hom (g.appTop.hom r) := by
  exact congrArg (fun q => (CommRingCat.Hom.hom q) r)
    ((Scheme.Hom.appLE_comp_appLE p f₁ ⊤ W W' h₁ h).trans ((FramedBaseChange.appLE_eq_of_eq e ⊤ W' _ _).trans
      ((Scheme.Hom.appLE_comp_appLE f₂ g ⊤ (g ⁻¹ᵁ ⊤) W' le_rfl h₂).symm.trans
        (show g.appLE ⊤ (g ⁻¹ᵁ ⊤) le_rfl ≫ f₂.appLE (g ⁻¹ᵁ ⊤) W' h₂ = g.app ⊤ ≫ f₂.appLE ⊤ W' h₂ by
          rw [Scheme.Hom.app_eq_appLE]
          rfl))))

/- English proof (translation)
Establish `hg` using `gen_eq d₀ hb`. Take `⟨-, hu, -⟩` from `hb`. Take `⟨zx, zu, pz, hzs, hzf, hzm⟩` from `hz`. Take `⟨-, zu', pz', hzs', hzf', hzm'⟩` from `hz'`. Establish `e : pz' = pz` using `FramedBaseChange.pulledGroup_hom_ext pz' pz (hzs'.trans hzs.symm) (hzf'.trans hzf.symm)`.

Substitute `e` using the available equality. Use `⟨rfl, ?_, 𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩` and prove the remaining obligations. Introduce `τ i`. Take `⟨cf, h1, h2, h3⟩` from `hu τ i`. Use `⟨fun j => φ (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩` and prove the remaining obligations.

Rewrite using `[zu' τ i]`. Take `⟨u, hu1, hu2⟩` from `h3`. Set `g : tEps z.x ⟶ tEps y.x` to `Over.homMk (spMap (dualMap φ.toRingHom)) (by show spMap (dualMap φ.toRingHom) ≫ spMap (algebraMap S (DualNumber S)) ≫ y.x = spMap (algebraMap T (DualNumber T)) ≫ z.x`. Rewrite using `[zx, ← Category.assoc, ← Category.assoc, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp, dualMap_comp_algebraMap_cusp_form_evaluations])`. Set `Fm : (tEps y.x ⟶ Xo.univ.t.G) →* (tEps z.x ⟶ Xo.univ.t.G)` to `{ toFun := fun v => g ≫ v map_one' := by simp map_mul' := fun a b => comp_mul g a b }`.

Use `⟨fun j => g ≫ u j, fun j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Over.comp_left, hu1 j, zu τ j]`. Express the relevant statement in the definitionally equal form `spMap (dualMap φ.toRingHom) ≫ _ = _`. Rewrite using `[← Category.assoc, ← Category.assoc, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp, dualMap_comp_epsMul_cusp_form_evaluations]`.

Establish `hprod : (List.ofFn fun j => g ≫ u j).prod = g ≫ (List.ofFn u).prod`. Use `map_list_prod Fm (List.ofFn u)` as an intermediate fact. Simplify `this.symm` using `[Fm, List.map_ofFn, Function.comp_def]`. Rewrite using `[hprod, Over.comp_left, hu2]`. Apply the tactic sequence `all_goals rfl`.

Introduce `i h`. Establish `k0` using `hzm i (FramedBaseChange.chart_le pz' hzs i)`. Establish `k1` using `hzm' i (FramedBaseChange.chart_le pz' hzs i)`. Simplify using `only [Reframe.pt] at k1 ⊢`. Rewrite `k1` using `[hg i, map_mul, k0]`.

Rewrite using `[appLE_id]`. Simplify using `only [CommRingCat.hom_id, RingHom.id_apply, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← k1]`. Use `congr 1`. Establish `nat` using `congrArg (fun q => CommRingCat.Hom.hom q (t none : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))`.

Conclude with `(congrArg (fun q => ((fst (Over.mk z.x) Xo.univ.t.G).left.appLE ⊤ ((PPx z.x).U i) (fun _ _ => trivial)).hom q) nat).trans (appLE_appLE_eq_of_comp_eq _ _ _ _ hzf _ _ _ _ _ _).symm`.
-/
private theorem frBor_units_map_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y : FrPt Xo c S} {z : FrPt Xo c T} (d₀ : Reframe y) (d : Reframe z)
    (hb : FrBor t y d₀.pt) (hz : FrMap φ y z) (hz' : FrMap φ d₀.pt d.pt) :
    FrBor (fun i => Units.map (φ : S →* T) (t i)) z d.pt := by
  have hg := gen_eq d₀ hb
  obtain ⟨-, hu, -⟩ := hb
  obtain ⟨zx, zu, pz, hzs, hzf, hzm⟩ := hz
  obtain ⟨-, zu', pz', hzs', hzf', hzm'⟩ := hz'
  have e : pz' = pz := FramedBaseChange.pulledGroup_hom_ext pz' pz (hzs'.trans hzs.symm) (hzf'.trans hzf.symm)
  subst e
  refine ⟨rfl, ?_, 𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · intro τ i
    obtain ⟨cf, h1, h2, h3⟩ := hu τ i
    refine ⟨fun j => φ (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩
    rw [zu' τ i]
    obtain ⟨u, hu1, hu2⟩ := h3
    let g : tEps z.x ⟶ tEps y.x := Over.homMk (spMap (dualMap φ.toRingHom)) (by
      show spMap (dualMap φ.toRingHom) ≫ spMap (algebraMap S (DualNumber S)) ≫ y.x =
        spMap (algebraMap T (DualNumber T)) ≫ z.x
      rw [zx, ← Category.assoc, ← Category.assoc, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp,
        dualMap_comp_algebraMap_cusp_form_evaluations])
    let Fm : (tEps y.x ⟶ Xo.univ.t.G) →* (tEps z.x ⟶ Xo.univ.t.G) :=
      { toFun := fun v => g ≫ v
        map_one' := by simp
        map_mul' := fun a b => comp_mul g a b }
    refine ⟨fun j => g ≫ u j, fun j => ?_, ?_⟩
    · dsimp only
      rw [Over.comp_left, hu1 j, zu τ j]
      change spMap (dualMap φ.toRingHom) ≫ _ = _
      rw [← Category.assoc, ← Category.assoc, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp,
        dualMap_comp_epsMul_cusp_form_evaluations]
    · have hprod : (List.ofFn fun j => g ≫ u j).prod = g ≫ (List.ofFn u).prod := by
        have := map_list_prod Fm (List.ofFn u)
        simpa [Fm, List.map_ofFn, Function.comp_def] using this.symm
      rw [hprod, Over.comp_left, hu2]
      all_goals rfl
  · intro i h
    have k0 := hzm i (FramedBaseChange.chart_le pz' hzs i)
    have k1 := hzm' i (FramedBaseChange.chart_le pz' hzs i)
    dsimp only [Reframe.pt] at k1 ⊢
    rw [hg i, map_mul, k0] at k1
    rw [appLE_id]
    simp only [CommRingCat.hom_id, RingHom.id_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [← k1]
    congr 1
    have nat := congrArg (fun q => CommRingCat.Hom.hom q (t none : S))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))
    exact (congrArg (fun q => ((fst (Over.mk z.x) Xo.univ.t.G).left.appLE ⊤ ((PPx z.x).U i)
      (fun _ _ => trivial)).hom q) nat).trans (appLE_appLE_eq_of_comp_eq _ _ _ _ hzf _ _ _ _ _ _).symm

end GlobalTheory.ThetaValueWeight

namespace GlobalTheory

open ThetaValueWeight in

/- English proof (translation)
Introduce `hL hC E _ _ _ H Dw l Xo c _ nab hn S _ _ y y' t hb n a P`. Take `⟨d₀, rfl⟩` from `exists_reframe y y' hb.1`. Use `⟨fun hP x v hv => ?_, fun hP w Λ β N v hv => ?_⟩` and prove the remaining obligations. Take `⟨S', _, _, φ, z, F, hff, hmap, hvt, hvv⟩` from `hv`. Establish `hP' : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))` using `hP.1`.

Take `⟨z', hz'⟩` from `_root_.GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S S' φ d₀.pt`. Take `⟨d, rfl⟩` from `exists_reframe z z' (hz'.1.trans hmap.1.symm)`. Establish `hb'` using `frBor_units_map_of_frMap φ d₀ d hb hmap hz'`. Use `⟨S', inferInstance, inferInstance, φ, d.pt, fun b => scaleSec Xo.univ.t.G (toΓ S' ((Units.map (φ : S →* S') (t none) : S'ˣ) : S')) (F b), hff, hz', fun b => isVtOver_scale _ _ _ (gen_eq d hb') (hvt b), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_wchar, hvv]`.

Unfold `thExpr`. Use `beta_reduce`. Rewrite using `[sum_eq hC hn d hb' hP' l.M F]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨S', _, _, φ, z, zz, tp, F, hff, hmap, hz1, hz2, hz3, hz4, hvv⟩` from `hv`.

Take `⟨z', hz'⟩` from `_root_.GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S S' φ d₀.pt`. Take `⟨d, rfl⟩` from `exists_reframe z z' (hz'.1.trans hmap.1.symm)`. Establish `hb'` using `frBor_units_map_of_frMap φ d₀ d hb hmap hz'`. Use `⟨S', inferInstance, inferInstance, φ, d.pt, zz, tp, fun q i b => scaleSec Xo.univ.t.G (toΓ S' ((Units.map (φ : S →* S') (t none) : S'ˣ) : S')) (F q i b), hff, hz', hz1, hz2, hz3, fun q i b => isUUOver_scale _ _ _ (gen_eq d hb') (hz4 q i b), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_wchar, hvv]`.

Simplify using `only [sum_eq hC hn d hb' hP N]`. Simplify using `only [← Finset.mul_sum, mul_left_comm (algebraMap c.F S' (w _))]`. Rewrite using `[← unit_mul_finsum (isUnit_wchar _ _) _]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaValue_weight : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), (P ∈ harmA c a n → ∀ (x : Fin n → Dw.La) (v : S), ThValAt Xo c nab y x P v → ThValAt Xo c nab y' x P (wchar (ex Dw a n) t * v)) ∧ (P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ β N P y' (wchar (ex Dw a n) t * v)) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hn S _ _ y y' t hb n a P
  obtain ⟨d₀, rfl⟩ := exists_reframe y y' hb.1
  refine ⟨fun hP x v hv => ?_, fun hP w Λ β N v hv => ?_⟩
  · obtain ⟨S', _, _, φ, z, F, hff, hmap, hvt, hvv⟩ := hv
    have hP' : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := hP.1
    obtain ⟨z', hz'⟩ := _root_.GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S S' φ d₀.pt
    obtain ⟨d, rfl⟩ := exists_reframe z z' (hz'.1.trans hmap.1.symm)
    have hb' := frBor_units_map_of_frMap φ d₀ d hb hmap hz'
    refine ⟨S', inferInstance, inferInstance, φ, d.pt,
      fun b => scaleSec Xo.univ.t.G (toΓ S' ((Units.map (φ : S →* S') (t none) : S'ˣ) : S')) (F b),
      hff, hz', fun b => isVtOver_scale _ _ _ (gen_eq d hb') (hvt b), ?_⟩
    rw [map_mul, map_wchar, hvv]
    unfold thExpr
    beta_reduce
    rw [sum_eq hC hn d hb' hP' l.M F]
    ring
  · obtain ⟨S', _, _, φ, z, zz, tp, F, hff, hmap, hz1, hz2, hz3, hz4, hvv⟩ := hv
    obtain ⟨z', hz'⟩ := _root_.GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S S' φ d₀.pt
    obtain ⟨d, rfl⟩ := exists_reframe z z' (hz'.1.trans hmap.1.symm)
    have hb' := frBor_units_map_of_frMap φ d₀ d hb hmap hz'
    refine ⟨S', inferInstance, inferInstance, φ, d.pt, zz, tp,
      fun q i b => scaleSec Xo.univ.t.G (toΓ S' ((Units.map (φ : S →* S') (t none) : S'ˣ) : S')) (F q i b),
      hff, hz', hz1, hz2, hz3, fun q i b => isUUOver_scale _ _ _ (gen_eq d hb') (hz4 q i b), ?_⟩
    rw [map_mul, map_wchar, hvv]
    simp only [sum_eq hC hn d hb' hP N]
    simp only [← Finset.mul_sum, mul_left_comm (algebraMap c.F S' (w _))]
    rw [← unit_mul_finsum (isUnit_wchar _ _) _]
    ring

end GlobalTheory
