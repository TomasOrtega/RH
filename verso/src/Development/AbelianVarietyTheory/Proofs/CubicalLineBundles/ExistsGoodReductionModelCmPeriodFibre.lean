import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriodStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriodStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyExtendsOverDedekindDomainStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeFormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCmPeriodLatticeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.PeriodModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twist {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (b : Bool) : Ell H R (cond b ω (1 - ω)) where
  P := C.P
  dim := C.dim
  act := cond b C.act (Serre.comapAct C.act (EllConj.barK H))
  v := C.v
  basis := C.basis
  eig := by
    cases b
    · exact EllConj.isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
        (by
          show C.act.act (EllConj.barK H (wK H)) * C.act.act (wK H) = _
          rw [← C.act.add, EllConj.barK_wK_add, C.act.one]) C.eig
    · exact C.eig
  adj := by
    cases b
    · exact fun x y h => C.adj _ _ (congrArg H.bar h)
    · exact C.adj
  prim := by
    cases b
    · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
        (EllConj.lbIso_of_adj C.P.isLB
          (C.adj (EllConj.barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))
    · exact C.prim

/- English proof (translation)
Consider the cases of `b`. Conclude with `⟨by simp [h.1], h.2.1, h.2.2.1, fun a => h.2.2.2 _⟩`. Conclude with `h`.
-/
theorem ellMap_twist {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'} {C' : Ell H R' ω'} {C : Ell H R ω}
    {f : R →+* R'} {φ : C'.P.A.left ⟶ C.P.A.left} (h : EllMap C' C f φ) (b : Bool) :
    EllMap (twist C' b) (twist C b) f φ := by
  cases b
  · exact ⟨by simp [h.1], h.2.1, h.2.2.1, fun a => h.2.2.2 _⟩
  · exact h

/- English proof (translation)
Take `⟨U, hU, hg⟩` from `exists_pat_of_obj E H D l _ _ _ _ Xo.univ`. Take `⟨T, m, hT⟩` from `GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ f U`. Conclude with `⟨T, hU ▸ m, hT.trans hg⟩`.
-/
theorem exists_pat_univ {D : Datum H} {l : Level H} (Xo : Moduli D l) {S : Scheme.{0}} (f : S ⟶ Xo.X) :
    ∃ (T : PAT H S) (_ : SABMap T.t Xo.univ.t f), T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H D l _ _ _ _ Xo.univ
  obtain ⟨T, m, hT⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ f U
  exact ⟨T, hU ▸ m, hT.trans hg⟩

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h0 : ω.im ≠ 0` using `fun h0 => by`. Establish `e` using `congrArg Complex.re hρ`. Establish `hi : ρ.im = 0` using `by rw [← h]; simp [h0]`. Simplify using `only [pow_two, Complex.mul_re, hi, Complex.neg_re, Complex.natCast_re] at e`.

Use polynomial arithmetic with `[mul_self_nonneg ρ.re]`. Break down `lt_or_gt_of_ne h0 with h1 | h1` into its components or cases. Conclude with `⟨-1, by simpa using h1⟩`. Conclude with `⟨1, by simpa using h1⟩`.
-/
theorem exists_sign {ω ρ : ℂ} (h : 2 * ω - 1 = ρ) (hρ : ρ ^ 2 = -(H.d : ℂ)) :
    ∃ ε : ℤˣ, 0 < ((ε : ℤ) : ℝ) * ω.im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : ω.im ≠ 0 := fun h0 => by
    have e := congrArg Complex.re hρ
    have hi : ρ.im = 0 := by rw [← h]; simp [h0]
    simp only [pow_two, Complex.mul_re, hi, Complex.neg_re, Complex.natCast_re] at e
    nlinarith [mul_self_nonneg ρ.re]
  rcases lt_or_gt_of_ne h0 with h1 | h1
  · exact ⟨-1, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

/- English proof (translation)
Substitute `hN` using the available equality. Take `⟨ε, a, h⟩` from `exists_pure_vectors_periods_span E H D g ty Pe hP p q Z`. Use `⟨fun j => decide (ε j = 1), fun j => ⟨a j, ?_⟩, h⟩` and prove the remaining obligations. Use `(a j).2` as an intermediate fact. Break down `Int.units_eq_one_or (ε j) with e | e` into its components or cases.

Simplify `this` using `[e]`. Simplify `this` using `[e]`.
-/
theorem exists_pure_span {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    {hP : IsPeriod D ty Pe} {p q : ℕ} (Z : CMLat hP p q) {N : ℕ} (hN : N = Module.finrank ℚ E / 2 * (D.p + D.q)) :
    ∃ (b : Fin N → Bool) (a : ∀ j, PureType.lat hP (if b j then H.rt0 else -H.rt0)),
      ∀ z : Fin g → ℂ, ∃ c : Fin N → ℂ, z = ∑ j, c j • Pe (a j) := by
  subst hN
  obtain ⟨ε, a, h⟩ := exists_pure_vectors_periods_span E H D g ty Pe hP p q Z
  refine ⟨fun j => decide (ε j = 1), fun j => ⟨a j, ?_⟩, h⟩
  have := (a j).2
  rcases Int.units_eq_one_or (ε j) with e | e
  · simpa [e] using this
  · simpa [e] using this

/- English proof (translation)
Substitute `hs` using the available equality. Introduce `y`. Take `⟨z, hz⟩` from `honto (pushHom hφ (Over.mk t) y)`. Take `⟨c, rfl⟩` from `hv z`. Use `choose x hx using hψ`.

Use `⟨N, id, fun j => x j (c j), ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (pushHom hφ (Over.mk t))` using `fun a b h => Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))`. Apply `hinj` to reduce the goal to its premises. Set `F : Multiplicative V →* (Over.mk (t ≫ f) ⟶ G)` to `MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _`. Establish `h1 : e (∑ j, c j • v j) = (List.ofFn fun j => e (c j • v j)).prod`.

Use `map_list_prod F (List.ofFn fun j => Multiplicative.ofAdd (c j • v j))` as an intermediate fact. Rewrite `this` using `[List.map_ofFn, List.prod_ofFn, ← ofAdd_sum]`. Conclude with `this`. Rewrite using `[← hz, h1, map_list_prod, List.map_ofFn]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Conclude with `Over.OverMorphism.ext ((hx j (c j)).symm.trans (Category.assoc _ _ _).symm)`.
-/
theorem ontoAt_of_exp {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (t : Sp ℂ ⟶ S') {s : Sp ℂ ⟶ S}
    (hs : t ≫ f = s) {V : Type} [AddCommGroup V] [Module ℂ V] (e : V → (Over.mk s ⟶ G))
    (hadd : ∀ z w, e (z + w) = e z * e w) (honto : Function.Surjective e) {N : ℕ} (v : Fin N → V)
    (hv : ∀ z, ∃ c : Fin N → ℂ, z = ∑ j, c j • v j) {B : Over S'} (ψ : Fin N → (B ⟶ G'))
    (hψ : ∀ j (z : ℂ), ∃ x : Over.mk t ⟶ B, x.left ≫ (ψ j).left ≫ φ = (e (z • v j)).left) :
    OntoAt (B := fun _ => B) ψ t := by
  subst hs
  intro y
  obtain ⟨z, hz⟩ := honto (pushHom hφ (Over.mk t) y)
  obtain ⟨c, rfl⟩ := hv z
  choose x hx using hψ
  refine ⟨N, id, fun j => x j (c j), ?_⟩
  have hinj : Function.Injective (pushHom hφ (Over.mk t)) := fun a b h =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  apply hinj
  let F : Multiplicative V →* (Over.mk (t ≫ f) ⟶ G) := MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have h1 : e (∑ j, c j • v j) = (List.ofFn fun j => e (c j • v j)).prod := by
    have := map_list_prod F (List.ofFn fun j => Multiplicative.ofAdd (c j • v j))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this
  rw [← hz, h1, map_list_prod, List.map_ofFn]
  congr 2
  funext j
  exact Over.OverMorphism.ext ((hx j (c j)).symm.trans (Category.assoc _ _ _).symm)

/- English proof (translation)
Introduce `hC hPt hU hL hL₂ hX hK E _ _ _ H D l Xo g ty FU i Pe hP p q Z k hkf`. Establish `hB` using `hL.polBaseChange`. Establish `hm` using `H.d_mod`. Establish `: NeZero H.d` using `⟨by omega⟩`. Take `⟨χ, hχ⟩` from `exists_isKroneckerChar (d := H.d) (by omega) (by omega)`.

Take `⟨M, _, ω, C, -, hω, hpr, -⟩` from `GlobalTheory.T.exists_cmEllipticCurve_integers_with_period hC hU hL hX E H χ hχ H.rt0 H.sqrt_neg_disc_sq`. Take `⟨K₀, hK₀, y₀, _, hy₀, hy₀'⟩` from `GlobalTheory.T.exists_numberField_point_of_cmPeriodLattice hC hPt hU hL E H D l Xo g ty FU i Pe hP p q ⟨Z⟩`. Take `⟨k₀, _, e₁, e₂, e₃⟩ : ∃ k₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₀ ∧ K₀ ≤ k₀ ∧ M ≤ k₀ ∧ k ≤ k₀` from `⟨K₀ ⊔ M ⊔ k, inferInstance, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, le_sup_right⟩`. Take `⟨C₀, φ₀, c₀⟩` from `exists_ellMap hB E H _ ω C k₀ ((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M))`. Take `⟨C', φ, c'⟩` from `exists_ellMap hB E H _ _ C₀ ℂ (algebraMap k₀ ℂ)`.

Take `⟨T, mT, -⟩` from `exists_pat_univ Xo (spMap (IntermediateField.inclusion e₁).toRingHom ≫ y₀)`. Take `⟨T', n, -⟩` from `exists_pat_univ Xo (FU.u i Pe)`. Take `⟨mT', hmT'⟩` from `(Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ ℂ (RingHom.id _) (algebraMap k₀ ℂ)).2 _ _ _ _ _ _ mT n (by rw [← Category.assoc, spMap_comp_spMap]; exact hy₀')`. Take `⟨u₀, hu₀⟩` from `PureType.exists_isThetaUnif hU C'.P`. Take `⟨c, hc, hΛ⟩` from `hpr C'.P (φ ≫ φ₀) ((EllComp.ellMap_comp E H _ _ C _ _ C₀ _ _ c₀).1 _ _ C' _ _ c').2.1 u₀`.

Generalize the expression as in `hω' : (algebraMap k₀ ℂ) (((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M)) ω) = ω' at C' φ c' u₀ hu₀ hΛ`. Establish `hρ : ∀ b : Bool, 2 * cond b ω' (1 - ω') - 1 = if b then H.rt0 else -H.rt0` using `fun b => by`. Establish `: 2 * ω' - 1 = H.rt0` using `hω' ▸ hω`. Consider the cases of `b`. Simplify using `only [cond_false, Bool.false_eq_true, if_false]`.

Take the linear combination `-this`. Conclude with `this`. Apply the tactic sequence `choose ε hε using fun b => exists_sign (H := H) (hρ b) (by split_ifs <;> simp [H.sqrt_neg_disc_sq])`. Use `choose h hh _ using fun b => GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) (ε b)`. Establish `fam : ∀ b : Bool, ∃ ψ : PureType.lat hP (if b then H.rt0 else -H.rt0) → (C'.P.A ⟶ T'.t.G), IsFam (twist C' b) T' (fun x y => h b x y) _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ n.φ = (FU.ex i Pe (z • Pe a)).left` using `fun b => by`.

Rewrite using `[← hρ b]`. Conclude with `GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period hU hL E H D l Xo g ty FU i Pe hP _ (twist C' b) u₀ c T' n (ε b) _ hu₀ hc hΛ (hε b) (hh b)`. Use `choose ψ' hψ' hex using fam`. Use `choose k₁ hk₁ hle hdesc using fun b => GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k₀ _ (twist C₀ b) (FU.Di i) _ T _ _ (twist C' b) φ T' mT' (ψ' b) (ellMap_twist c' b) (hψ' b)`. Choose the witnesses or unpack the hypotheses as in `⟨K₁, _, e₄⟩ : ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ ∀ b, k₁ b ≤ K₁ := by`.

Use `hk₁ true` as an intermediate fact. Use `hk₁ false` as an intermediate fact. Conclude with `⟨k₁ true ⊔ k₁ false, inferInstance, fun b => by cases b; exacts [le_sup_right, le_sup_left]⟩`. Establish `: NumberField K₁` using `⟨⟩`. Establish `e₅ : k₀ ≤ K₁` using `(hle true).trans (e₄ true)`.

Take `⟨C₁, φ₁, c₁⟩` from `exists_ellMap hB E H _ ω C (𝓞 K₁) (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom)`. Take `⟨C₂, φ₁₂, c₁₂⟩` from `exists_ellMap hB E H _ _ C₁ K₁ (algebraMap (𝓞 K₁) K₁)`. Take `⟨φ₂, c₂, -⟩` from `(Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 M) k₀ K₁ _ (IntermediateField.inclusion e₅).toRingHom).1 _ _ _ C C₀ C₂ φ₀ _ c₀ ((EllComp.ellMap_comp E H _ _ C _ _ C₁ _ _ c₁).1 _ _ C₂ _ _ c₁₂)`. Take `⟨φ₃, c₃, hφ₃⟩` from `(Factor.ellMap_cancel_and_sabMap_cancel E H k₀ K₁ ℂ _ (algebraMap K₁ ℂ)).1 _ _ _ C₀ C₂ C' φ₂ φ c₂ c'`. Establish `hy : spMap (algebraMap K₁ ℂ) ≫ spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ = FU.u i Pe`.

Rewrite using `[← Category.assoc, spMap_comp_spMap]`. Conclude with `hy₀'`. Take `⟨T₂, m, hg⟩` from `exists_pat_univ Xo (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)`. Take `⟨m₂, hm₂⟩` from `(Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ K₁ (RingHom.id _) (IntermediateField.inclusion e₅).toRingHom).2 _ _ _ _ _ _ mT m (by rw [← Category.assoc, spMap_comp_spMap]; rfl)`. Take `⟨m₃, hm₃⟩` from `(Factor.ellMap_cancel_and_sabMap_cancel E H K₁ K₁ ℂ (RingHom.id _) (algebraMap K₁ ℂ)).2 _ _ _ _ _ _ m₂ mT' (by rw [spMap_comp_spMap]; rfl)`.

Establish `hn : m₃.φ ≫ m.φ = n.φ` using `by rw [← hm₂, ← Category.assoc, hm₃, hmT']`. Use `choose ψ₂ hψ₂ hsq using fun b => hdesc b K₁ e₅ (e₄ b) _ (twist C₂ b) φ₂ φ₃ T₂ m₂ m₃ (ellMap_twist c₂ b) (ellMap_twist c₃ b) hφ₃ hm₃`. Establish `hex₂ : ∀ b a (z : ℂ), ((u₀.ex fun _ => c * z).left ≫ φ₃ ≫ (ψ₂ b a).left) ≫ m.φ = (FU.ex i Pe (z • Pe a)).left` using `fun b a z => by`. Rewrite using `[← hex, ← hn, ← Category.assoc _ m₃.φ, Over.comp_left, Category.assoc _ _ m₃.φ]`. Conclude with `congrArg (fun q => (_ ≫ q) ≫ m.φ) (hsq b a).symm`.

Establish `hpt : ∀ z : Fin C'.P.g → ℂ, ((u₀.ex z).left ≫ φ₃) ≫ C₂.P.A.hom = spMap (algebraMap K₁ ℂ)` using `fun z => by`. Rewrite using `[Category.assoc, c₃.2.1.2.1.1.w, ← Category.assoc, Over.w]`. Conclude with `Category.id_comp _`. Take `⟨bb, a, hspan⟩` from `exists_pure_span Z (N := T₂.g) (by rw [hg, (FU.sig i).1, (FU.sig i).2])`. Take `⟨B, m', -⟩` from `GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms hU hL hL₂ hX hK E H (𝓞 K₁) K₁ (algebraMap K₁ ℂ) C₁.P C₂.P φ₁₂ T₂ (fun j => ψ₂ (bb j) (a j)) c₁₂.2.1 C₁.dim (fun j => ((hψ₂ (bb j)).1 (a j)).1) (ontoAt_of_exp m.cart _ hy (FU.ex i Pe) (FU.ex_add i Pe hP) (FU.ex_onto i …`.

Rewrite using `[← hex₂]`. Simplify using `only [Category.assoc]`. Conclude with `Category.assoc _ _ _⟩)`. Use `choose ψ hψ hsq' using fun b => GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hX E H (𝓞 K₁) K₁ _ (twist C₁ b) (FU.Di i) _ B _ _ (twist C₂ b) φ₁₂ T₂ m' (ψ₂ b) (ellMap_twist c₁₂ b) (hψ₂ b)`. Use `⟨K₁, inferInstance, hK₀.trans (e₁.trans e₅), _, twist C₁, ε, fun b x y => h b x y, B, _, T₂.t, m, m', ψ, _, twist C', fun _ => φ₃ ≫ φ₁₂, fun _ => u₀, fun _ => c, e₃.trans e₅, ?_, hy, fun b => ⟨hρ b, hε b, hh b, hψ b, ellMap_twist ((EllComp.ellMap_comp E H _ _ C₁ _ _ C₂ _ _ c₁₂).1 …` and prove the remaining obligations.

Rewrite using `[Category.assoc, hy₀, spMap_comp_spMap]`. Both sides reduce to the same expression. Rewrite using `[← hex₂ b a z]`. Use `congr 1`. Use `m'.cart.1.hom_ext ?_ ?_` and prove the remaining obligations.

Use `hx'.trans ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Conclude with `congrArg (fun q => _ ≫ φ₃ ≫ q) (hsq' b a).symm`. Rewrite using `[hx, ← hpt fun _ => c * z]`. Simplify using `only [Category.assoc]`.

Conclude with `congrArg (fun q => _ ≫ φ₃ ≫ q) (Over.w (ψ₂ b a)).symm`.
-/
theorem exists_model : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hC hPt hU hL hL₂ hX hK E _ _ _ H D l Xo g ty FU i Pe hP p q Z k hkf
  have hB := hL.polBaseChange
  have hm := H.d_mod
  have : NeZero H.d := ⟨by omega⟩
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar (d := H.d) (by omega) (by omega)
  obtain ⟨M, _, ω, C, -, hω, hpr, -⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period hC hU hL hX E H χ hχ H.rt0 H.sqrt_neg_disc_sq
  obtain ⟨K₀, hK₀, y₀, _, hy₀, hy₀'⟩ := GlobalTheory.T.exists_numberField_point_of_cmPeriodLattice hC hPt hU hL E H D l Xo g ty FU i Pe hP p q ⟨Z⟩

  obtain ⟨k₀, _, e₁, e₂, e₃⟩ : ∃ k₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₀ ∧ K₀ ≤ k₀ ∧ M ≤ k₀ ∧ k ≤ k₀ :=
    ⟨K₀ ⊔ M ⊔ k, inferInstance, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, le_sup_right⟩
  obtain ⟨C₀, φ₀, c₀⟩ := exists_ellMap hB E H _ ω C k₀
    ((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M))
  obtain ⟨C', φ, c'⟩ := exists_ellMap hB E H _ _ C₀ ℂ (algebraMap k₀ ℂ)
  obtain ⟨T, mT, -⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion e₁).toRingHom ≫ y₀)
  obtain ⟨T', n, -⟩ := exists_pat_univ Xo (FU.u i Pe)
  obtain ⟨mT', hmT'⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ ℂ (RingHom.id _) (algebraMap k₀ ℂ)).2
    _ _ _ _ _ _ mT n (by rw [← Category.assoc, spMap_comp_spMap]; exact hy₀')
  obtain ⟨u₀, hu₀⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P (φ ≫ φ₀) ((EllComp.ellMap_comp E H _ _ C _ _ C₀ _ _ c₀).1 _ _ C' _ _ c').2.1 u₀
  generalize hω' : (algebraMap k₀ ℂ) (((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M)) ω) = ω'
    at C' φ c' u₀ hu₀ hΛ
  have hρ : ∀ b : Bool, 2 * cond b ω' (1 - ω') - 1 = if b then H.rt0 else -H.rt0 := fun b => by
    have : 2 * ω' - 1 = H.rt0 := hω' ▸ hω
    cases b
    · simp only [cond_false, Bool.false_eq_true, if_false]
      linear_combination -this
    · exact this
  choose ε hε using fun b => exists_sign (H := H) (hρ b) (by split_ifs <;> simp [H.sqrt_neg_disc_sq])
  choose h hh _ using fun b => GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) (ε b)
  have fam : ∀ b : Bool, ∃ ψ : PureType.lat hP (if b then H.rt0 else -H.rt0) → (C'.P.A ⟶ T'.t.G),
      IsFam (twist C' b) T' (fun x y => h b x y) _ ψ ∧
      ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ n.φ = (FU.ex i Pe (z • Pe a)).left := fun b => by
    rw [← hρ b]
    exact GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period hU hL E H D l Xo g ty FU i Pe hP _ (twist C' b) u₀ c T' n (ε b) _ hu₀ hc hΛ (hε b) (hh b)
  choose ψ' hψ' hex using fam
  choose k₁ hk₁ hle hdesc using fun b => GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k₀ _ (twist C₀ b) (FU.Di i) _ T _ _ (twist C' b) φ T'
    mT' (ψ' b) (ellMap_twist c' b) (hψ' b)

  obtain ⟨K₁, _, e₄⟩ : ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ ∀ b, k₁ b ≤ K₁ := by
    have := hk₁ true
    have := hk₁ false
    exact ⟨k₁ true ⊔ k₁ false, inferInstance, fun b => by cases b; exacts [le_sup_right, le_sup_left]⟩
  have : NumberField K₁ := ⟨⟩
  have e₅ : k₀ ≤ K₁ := (hle true).trans (e₄ true)
  obtain ⟨C₁, φ₁, c₁⟩ := exists_ellMap hB E H _ ω C (𝓞 K₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom)
  obtain ⟨C₂, φ₁₂, c₁₂⟩ := exists_ellMap hB E H _ _ C₁ K₁ (algebraMap (𝓞 K₁) K₁)
  obtain ⟨φ₂, c₂, -⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 M) k₀ K₁ _
    (IntermediateField.inclusion e₅).toRingHom).1 _ _ _ C C₀ C₂ φ₀ _ c₀
    ((EllComp.ellMap_comp E H _ _ C _ _ C₁ _ _ c₁).1 _ _ C₂ _ _ c₁₂)
  obtain ⟨φ₃, c₃, hφ₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ K₁ ℂ _ (algebraMap K₁ ℂ)).1
    _ _ _ C₀ C₂ C' φ₂ φ c₂ c'
  have hy : spMap (algebraMap K₁ ℂ) ≫ spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ = FU.u i Pe := by
    rw [← Category.assoc, spMap_comp_spMap]; exact hy₀'
  obtain ⟨T₂, m, hg⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
  obtain ⟨m₂, hm₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ K₁ (RingHom.id _)
    (IntermediateField.inclusion e₅).toRingHom).2 _ _ _ _ _ _ mT m (by rw [← Category.assoc, spMap_comp_spMap]; rfl)
  obtain ⟨m₃, hm₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H K₁ K₁ ℂ (RingHom.id _)
    (algebraMap K₁ ℂ)).2 _ _ _ _ _ _ m₂ mT' (by rw [spMap_comp_spMap]; rfl)
  have hn : m₃.φ ≫ m.φ = n.φ := by rw [← hm₂, ← Category.assoc, hm₃, hmT']
  choose ψ₂ hψ₂ hsq using fun b => hdesc b K₁ e₅ (e₄ b) _ (twist C₂ b) φ₂ φ₃ T₂ m₂ m₃ (ellMap_twist c₂ b)
    (ellMap_twist c₃ b) hφ₃ hm₃
  have hex₂ : ∀ b a (z : ℂ), ((u₀.ex fun _ => c * z).left ≫ φ₃ ≫ (ψ₂ b a).left) ≫ m.φ =
      (FU.ex i Pe (z • Pe a)).left := fun b a z => by
    rw [← hex, ← hn, ← Category.assoc _ m₃.φ, Over.comp_left, Category.assoc _ _ m₃.φ]
    exact congrArg (fun q => (_ ≫ q) ≫ m.φ) (hsq b a).symm
  have hpt : ∀ z : Fin C'.P.g → ℂ, ((u₀.ex z).left ≫ φ₃) ≫ C₂.P.A.hom = spMap (algebraMap K₁ ℂ) := fun z => by
    rw [Category.assoc, c₃.2.1.2.1.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _

  obtain ⟨bb, a, hspan⟩ := exists_pure_span Z (N := T₂.g) (by rw [hg, (FU.sig i).1, (FU.sig i).2])
  obtain ⟨B, m', -⟩ := GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms hU hL hL₂ hX hK E H (𝓞 K₁) K₁ (algebraMap K₁ ℂ) C₁.P C₂.P φ₁₂ T₂
    (fun j => ψ₂ (bb j) (a j)) c₁₂.2.1 C₁.dim (fun j => ((hψ₂ (bb j)).1 (a j)).1)
    (ontoAt_of_exp m.cart _ hy (FU.ex i Pe) (FU.ex_add i Pe hP) (FU.ex_onto i Pe hP) _ hspan _ fun j z =>
      ⟨Over.homMk _ (hpt fun _ => c * z), by
        rw [← hex₂]
        simp only [Category.assoc]
        exact Category.assoc _ _ _⟩)
  choose ψ hψ hsq' using fun b => GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hX E H (𝓞 K₁) K₁ _ (twist C₁ b) (FU.Di i) _ B _ _ (twist C₂ b) φ₁₂
    T₂ m' (ψ₂ b) (ellMap_twist c₁₂ b) (hψ₂ b)
  refine ⟨K₁, inferInstance, hK₀.trans (e₁.trans e₅), _, twist C₁, ε, fun b x y => h b x y, B, _, T₂.t, m, m', ψ, _,
    twist C', fun _ => φ₃ ≫ φ₁₂, fun _ => u₀, fun _ => c, e₃.trans e₅, ?_, hy, fun b =>
      ⟨hρ b, hε b, hh b, hψ b, ellMap_twist ((EllComp.ellMap_comp E H _ _ C₁ _ _ C₂ _ _ c₁₂).1 _ _ C' _ _ c₃) b, hc, hΛ,
        fun a z x hx hx' => ?_⟩⟩
  · rw [Category.assoc, hy₀, spMap_comp_spMap]
    rfl
  · rw [← hex₂ b a z]
    congr 1
    refine m'.cart.1.hom_ext ?_ ?_
    · refine hx'.trans ?_
      simp only [Category.assoc]
      exact congrArg (fun q => _ ≫ φ₃ ≫ q) (hsq' b a).symm
    · rw [hx, ← hpt fun _ => c * z]
      simp only [Category.assoc]
      exact congrArg (fun q => _ ≫ φ₃ ≫ q) (Over.w (ψ₂ b a)).symm

end GlobalTheory.CM.PeriodModel
end
