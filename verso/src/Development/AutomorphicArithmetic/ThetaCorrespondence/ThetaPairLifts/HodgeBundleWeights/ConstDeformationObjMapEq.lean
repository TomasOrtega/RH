import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniqueness
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ConstDeformationActionTrivial
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CubicalStructureConstSectionPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniquenessStatement

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstDeform
/- English proof (translation)
Introduce `hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩`. Establish `hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x'` using `m.cart.1.w`. Set `g : o.t.G.left ⟶ A'.left` to `hπ'.1.lift m.cm.F o.t.G.hom hw`. Establish `hg : g ≫ π' = m.cm.F` using `hπ'.1.lift_fst _ _ _`. Establish `hgw : g ≫ A'.hom = o.t.G.hom` using `hπ'.1.lift_snd _ _ _`.

Establish `hgc : IsGrpPullback o.t.G A' (𝟙 _) g` using `hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])`. Establish `hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x'`. Rewrite using `[← hT.2]`. Both sides reduce to the same expression. Establish `hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)` using `(hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl`.

Use `haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance`. Establish `hgq` using `hgc.comp hq`. Establish `hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x`. Introduce `T x y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `hπ.1.hom_ext` to reduce the goal to its premises. Establish `e1` using `hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl`. Establish `e2` using `hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl`. Rewrite using `[← e1, ← e2, _root_.mul_comm]`. Rewrite using `[Over.w (x * y), Over.w (y * x)]`.

Establish `key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ), 0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left → σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left`. Introduce `σ τ n hn hσ hστ`. Set `u` to `pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ`. Establish `hu : u ^ n = 1` using `by rw [← map_pow, hσ, map_one]`. Establish `e` using `GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu`.

Establish `hul : u.left = σ.left ≫ g ≫ q` using `by show σ.left ≫ (g ≫ q) = _; rfl`. Rewrite `e` using `[hul]`. Set `w` to `spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g`. Establish `hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K`. Simplify using `only [w, Category.assoc, hgw, Category.id_comp]`.

Rewrite using `[Over.w σ]`. Both sides reduce to the same expression. Set `s₀` to `hi.1.lift w (𝟙 _) hw'`. Establish `hs₀ : s₀ ≫ i = w` using `hi.1.lift_fst _ _ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hs₀]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hiq, hiπ]`. Use `_ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by`. Rewrite using `[reassoc_of% hs₀]`.

Simplify using `only [w, Category.assoc, hg]`. Use `_ = constPt x' ≫ τ.left := by rw [hστ]; rfl`. Establish `hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) → ∀ (n : ℕ) a, f (n • a) = f a ^ n`. Introduce `f hf n a`. Proceed by induction on `n with`.

Consider the case `zero`. Establish `h0` using `hf 0 0`. Rewrite `h0` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`. Conclude with `mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)`.

Consider the case `succ n ih => rw [succ_nsmul, hf, ih, pow_succ]`. Establish `hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb`. Establish `h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`.

Conclude with `Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1`. Conclude with `⟨{ cm := cubeMapOf hF cart := hF base := rfl act := _root_.GlobalTheory.T.const_deformation_action_trivial hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF lin := _root_.GlobalTheory.T.cubical_structure_const_section_pullback hP hGD E H Dw l X …`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hM Submodule.mem_top))`. Use the proof step `(m.eta a)`.

Use `etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩`.
-/
theorem constDeformation_objMap_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := _root_.GlobalTheory.T.const_deformation_action_trivial hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := _root_.GlobalTheory.T.cubical_structure_const_section_pullback hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩
end GlobalTheory.ConstDeform
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.const_deformation_obj_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq <;> assumption)
end
