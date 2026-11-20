import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatEpiLiftRaynaudExtensionFractionPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatShift

/- English proof (translation)
Introduce `ψ` and use `by have := hJ (r ≫ ψ) rwa [Scheme.Hom.comp_apply] at this`.
-/
theorem good_comp' {X Y Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Out.scal`. Conclude with `gs_pull r p z ⊤ trivial _`.
-/
theorem gs_scal_eq {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  exact gs_pull r p z ⊤ trivial _

/- English proof (translation)
Unfold `cst`. Rewrite using `[map_add, gs_add q z ⊤ trivial]`.
-/
theorem cst_add' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) :
    cst q z (a + b) = cst q z a + cst q z b := by
  unfold cst; rw [map_add, gs_add q z ⊤ trivial]

/- English proof (translation)
Use `cst_add' q z (a - b) b` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this, add_sub_cancel_right]`.
-/
theorem cst_sub' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) :
    cst q z (a - b) = cst q z a - cst q z b := by
  have := cst_add' q z (a - b) b
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/- English proof (translation)
Use `cst_add' q z 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`.
-/
theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  have := cst_add' q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

/- English proof (translation)
Establish `e` using `congrArg (p.stalkMap z).hom (H u hu hc (p z) _ (good_comp' p z hJ))`. Rewrite using `[GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul]`. Use `congr 2`. Use `GlobalTheory.HeatDefect.val_comp_stalk u (𝟙 _) p z hJ` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`.

Conclude with `this.symm`. Rewrite using `[← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) z ⊤ trivial, Category.comp_id]`. Conclude with `gs_scal_eq _ p z c`.
-/
theorem shiftEq_pt {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α}
    {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R} (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    {Z : Scheme.{0}} (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (p ≫ (DegPre.prB Q (FractionRing R)).left) z J =
      (val u p z J).val * sval σ (p ≫ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left) z J +
        cst (p ≫ (DegPre.BF Q (FractionRing R)).hom) z c * sval σ₂ (p ≫ (DegPre.prB Q (FractionRing R)).left) z J := by
  have e := congrArg (p.stalkMap z).hom (H u hu hc (p z) _ (good_comp' p z hJ))
  rw [GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ,
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul]
  congr 2
  · have := GlobalTheory.HeatDefect.val_comp_stalk u (𝟙 _) p z hJ
    rw [Category.comp_id] at this
    exact this.symm
  · rw [← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) z ⊤ trivial, Category.comp_id]
    exact gs_scal_eq _ p z c

/- English proof (translation)
Establish `hpow : ∀ i (n : ℕ), D (t i ^ n) = ((n : R) * d i) * t i ^ n`. Introduce `i n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, Derivation.leibniz, ih, hd, smul_eq_mul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ s : Finset (Fin m), D (∏ i ∈ s, t i ^ N i) = (∑ i ∈ s, (N i : R) * d i) * ∏ i ∈ s, t i ^ N i`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, Derivation.leibniz, ih, hpow, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `key _`.
-/
theorem der_prod {R : Type} [CommRing R] {m : ℕ} (D : Derivation ℤ R R) (t d : Fin m → R) (hd : ∀ i, D (t i) = d i * t i)
    (N : Fin m → ℕ) : D (∏ i, t i ^ N i) = (∑ i, (N i : R) * d i) * ∏ i, t i ^ N i := by
  have hpow : ∀ i (n : ℕ), D (t i ^ n) = ((n : R) * d i) * t i ^ n := by
    intro i n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hd, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have key : ∀ s : Finset (Fin m), D (∏ i ∈ s, t i ^ N i) = (∑ i ∈ s, (N i : R) * d i) * ∏ i ∈ s, t i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Derivation.leibniz, ih, hpow, smul_eq_mul, smul_eq_mul]
      ring
  exact key _

end GlobalTheory.HeatShift

open GlobalTheory.HeatShift in
/- English proof (translation)
Introduce `R _ _ _ _ _ _ Dd O _ _ _ oa Y m t gam hmon ht D hD mu`. Establish `hn : ∀ y, ∃ n : Fin m → ℕ, ∀ i, gam i y y = 2 * n i` using `fun y => by`. Take `⟨u, n, h, -⟩` from `hmon y`. Conclude with `⟨n, h⟩`. Use `choose n hn using hn`.

Use `choose ψ₀ hψ₀g hψ₀v using fun χ => GlobalTheory.T.exists_monomialPeriod_unitPart_generator R Dd.toPre m t gam hmon χ (n χ) (hn χ)`. Take `⟨xp, hxq, hxv⟩` from `GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates R Dd.toPre O oa Y m t gam Dd.tau_bimult ht n hn ψ₀ hψ₀g hψ₀v mu`. Establish `hqm : IsMonHom Y.q` using `Y.q_linear.isMonHom`. Establish `hx : (xp⁻¹ ≫ Y.q) * Dd.toPre.c mu = 1`. Rewrite using `[← hxq, ← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]`.

Take `⟨e, heg, hew, hev⟩` from `GlobalTheory.T.exists_raynaudGauge_generator_weight_neg R Dd.toPre O oa Y mu xp⁻¹ hx (ψ₀ mu) (hψ₀g mu)`. Establish `hd : ∀ i, ∃ d : R, D (t i) = d * t i` using `fun i => by`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 (hD i)`. Conclude with `⟨c, by rw [hc, mul_comm]⟩`. Use `choose d hd using hd`.

Establish `n0 : ∀ i, n 0 i = 0` using `fun i => by`. Use `hn 0 i` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `fadd : ∀ (a b : Dd.toPre.X) i, ((n (mu + (a + b)) i : ℤ) - n mu i - n (a + b) i) = ((n (mu + a) i : ℤ) - n mu i - n a i) + ((n (mu + b) i : ℤ) - n mu i - n b i)`.

Introduce `a b i`. Establish `h1` using `hn (mu + (a + b)) i`. Establish `h2` using `hn mu i`. Establish `h3` using `hn (a + b) i`. Establish `h4` using `hn (mu + a) i`.

Establish `h5` using `hn a i`. Establish `h6` using `hn (mu + b) i`. Establish `h7` using `hn b i`. Simplify using `only [map_add, LinearMap.add_apply] at h1 h3 h4 h6`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `w : Dd.toPre.X →+ R` to `{ toFun := fun a => ∑ i, ((((n (mu + a) i : ℤ) - n mu i - n a i : ℤ)) : R) * d i map_zero' := by simp [n0] map_add' := fun a b => by`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[fadd a b i]`. Use `push_cast`.

Use `ring }`. Use `⟨xp⁻¹, e, -mu, w, ∑ i, (n mu i : R) * d i, 0, heg, hew, ?_⟩` and prove the remaining obligations. Introduce `k α hk`. Establish `ht0 : ∀ N : Fin m → ℕ, (∏ i, t i ^ N i) ≠ 0` using `fun N => Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ht i)`. Establish `hjFK : IsIso (jFK (R` using `R) (FractionRing R)) := by`.

Establish `: IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R)))`. Rewrite using `[Algebra.algebraMap_self]`. Conclude with `inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))`. Use `infer_instance`. Establish `htr : ∀ (T : Over (Sp R)) (pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R)) (yp : T ⟶ Y.H), pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q → pp ≫ DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R) = (yp * (toUnit T ≫ xp)) ≫ Y.q`.

Introduce `T pp yp h`. Rewrite using `[DegPre.trF, lift_snd, show ∀ f g : DegPre.BF Dd.toPre (FractionRing R) ⟶ Dd.toPre.P.A, padd Dd.toPre.P.A f g = f * g from fun _ _ => rfl, MonObj.comp_mul, MonObj.mul_comp, h, ← Category.assoc, comp_toUnit, Category.assoc, hxq]`. Establish `hsq : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), (y * (toUnit T ≫ xp⁻¹)) * (toUnit T ≫ xp) = y`. Introduce `T y`. Rewrite using `[_root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel, MonObj.comp_one, _root_.mul_one]`.

Establish `hTx : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), y ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)) = y * (toUnit T ≫ xp⁻¹)`. Introduce `T y`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]`. Use `set A₀ : R := ∏ i, t i ^ n (mu + α) i with hA₀`. Use `set B₀ : R := ∏ i, t i ^ (n mu i + n α i) with hB₀`.

Use `set P₀ : R := ∏ i, t i ^ n mu i with hP₀`. Use `set b : R := ∏ i, t i ^ (k * n mu i + n (mu + α) i) with hb`. Establish `hb' : b = P₀ ^ k * A₀`. Rewrite using `[hb, hP₀, hA₀, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[pow_add, mul_comm k, pow_mul]`. Use `⟨B₀, b, ht0 _, ?_⟩` and prove the remaining obligations. Introduce `σ σ₁ τ τ₁ ρ hS hT hT₁ hρ`. Establish `key` using `fun u hu hc => GlobalTheory.T.raynaudShift_unitIdentity_fractionField R Dd.toPre O oa Y Dd.tau_bimult k mu α xp A₀ B₀ P₀ (ψ₀ mu) e hxq (fun Z g z J hJ => hxv Z g α z J hJ) (fun Z g z J hJ => hψ₀v mu Z g z J hJ) hev u hu hc`. Take `⟨⟨u, hu, hc⟩, -⟩` from `gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α`.

Establish `C1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom B₀) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J`. Use `GlobalTheory.T.raynaud_section_identity_of_generic_fibre R Dd.toPre O oa Y k ρ τ B₀ b fun Z g r hr z J hJ => ?_` and prove the remaining obligations. Set `T : Over (Sp R)` to `Over.mk (g ≫ jK R)`. Set `y : T ⟶ Y.H` to `Over.homMk r hr`. Set `yp : T ⟶ Y.H` to `y * (toUnit T ≫ xp⁻¹)`.

Set `pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R)` to `lift (Over.homMk (g ≫ inv (jFK (R := R) (FractionRing R))) (by show (g ≫ inv (jFK (R := R) (FractionRing R))) ≫ jFK (R := R) (FractionRing R) ≫ jK R = g ≫ jK R`. Rewrite using `[Category.assoc, IsIso.inv_hom_id_assoc])) (yp ≫ Y.q)`. Establish `hpp1 : (pp ≫ fst _ _).left ≫ jFK (R` using `R) (FractionRing R) = g := by`. Simplify using `[pp]`. Establish `hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q` using `lift_snd _ _`.

Establish `hK` using `key u hu hc Z g pp yp hpp1 hpp2 z J hJ`. Rewrite `hK` using `[hsq T y]`. Establish `hsh` using `shiftEq_pt hS u hu hc pp.left z J hJ`. Rewrite `hsh` using `[cst_zero', zero_mul, add_zero, ← Over.comp_left, ← Over.comp_left, hpp2, htr T pp yp hpp2, hsq T y]`. Establish `e1` using `hρ Z r z J hJ`.

Establish `e1' : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left` using `by show y.left ≫ _ = _`. Rewrite using `[← Over.comp_left]`. Conclude with `congrArg (·.left) (hTx T y)`. Rewrite `e1` using `[e1']`. Establish `e2` using `hT₁ T yp z J hJ`.

Establish `e3 : sval τ r z J = _` using `hT T y z J hJ`. Rewrite using `[gs_scal_eq, gs_scal_eq, hr]`. Rewrite using `[e1, e2, e3, hsh, hb']`. Establish `fin : ∀ {S : Type} [CommRing S] (cA cB U s S' E X : S), cA * U * S' * E = cB * X → cA * (U * s * S' * E) = cB * (s * X)` using `fun cA cB U s S' E X h => by linear_combination s * h`. Conclude with `fin _ _ _ _ _ _ _ hK`.

Use `⟨C1, ?_⟩` and prove the remaining obligations. Introduce `σ'' σ₁' τ'' τ₁' ρ' hT'' hT₁' hρ' hL u' hu' hc' z J hJ`. Take `⟨Z, p, w0, y0, rfl, hepi, hinj, hyq⟩` from `GlobalTheory.T.exists_flat_epi_lift_raynaud_extension_fraction_point R Dd.toPre O oa Y z`. Establish `hJ₁ : ∃ J₁ : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι, Good Dd.toPre.P.L w0 J₁ ∧ ∀ ψ, J₁ (p ≫ ψ) = J ψ` using `by classical`. Use `⟨fun φ => if h : ∃ ψ, p ≫ ψ = φ then J h.choose else (exists_chart Dd.toPre.P.isLB (φ w0)).choose, fun φ => ?_, fun ψ => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : ∃ ψ, p ≫ ψ = φ`. Simplify using `only [dif_pos h]`. Establish `e` using `h.choose_spec`. Establish `: (p ≫ h.choose) w0 ∈ Dd.toPre.P.L.U (J h.choose)`. Rewrite using `[Scheme.Hom.comp_apply]`.

Conclude with `hJ _`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Simplify using `only [dif_neg h]`. Conclude with `(exists_chart Dd.toPre.P.isLB (φ w0)).choose_spec`. Establish `h : ∃ ψ', p ≫ ψ' = p ≫ ψ` using `⟨ψ, rfl⟩`.

Simplify using `only [dif_pos h]`. Conclude with `congrArg J ((cancel_epi p).1 h.choose_spec)`. Take `⟨J₁, gJ₁, eJ₁⟩` from `hJ₁`. Establish `eJ : J = fun ψ => J₁ (p ≫ ψ)` using `funext fun ψ => (eJ₁ ψ).symm`. Substitute `eJ` using the available equality.

Apply `hinj` to reduce the goal to its premises. Establish `hv` using `GlobalTheory.HeatDefect.val_comp_stalk u' (𝟙 _) p w0 gJ₁`. Rewrite `hv` using `[Category.comp_id]`. Rewrite using `[map_add, map_mul, map_mul, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← hv, ← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) w0 ⊤ trivial, Category.comp_id, g …`. Use `clear hv eJ₁ hJ hinj`.

Use `set g : Z ⟶ (TK R).left := p ≫ (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) with hg`. Establish `hpB : p ≫ (DegPre.BF Dd.toPre (FractionRing R)).hom = g ≫ jK R`. Rewrite using `[← Over.w (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A), hg]`. Simplify using `only [Category.assoc]`. Both sides reduce to the same expression.

Set `T : Over (Sp R)` to `Over.mk (g ≫ jK R)`. Set `pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R)` to `Over.homMk p hpB`. Set `yp : T ⟶ Y.H` to `Over.homMk y0 (by show y0 ≫ Y.H.hom = g ≫ jK R`. Rewrite using `[← Over.w Y.q, ← Category.assoc, hyq, Category.assoc, Over.w (DegPre.prB Dd.toPre (FractionRing R)), hpB])`. Establish `hpp1 : (pp ≫ fst _ _).left ≫ jFK (R` using `R) (FractionRing R) = g := by`.

Rewrite using `[hg]`. Simplify using `[pp]`. Establish `hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q` using `Over.OverMorphism.ext hyq.symm`. Set `y : T ⟶ Y.H` to `yp * (toUnit T ≫ xp)`. Set `r : Z ⟶ Y.H.left` to `y.left`.

Establish `hyy : y * (toUnit T ≫ xp⁻¹) = yp` using `by show yp * (toUnit T ≫ xp) * (toUnit T ≫ xp⁻¹) = yp`. Rewrite using `[_root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]`. Establish `rT : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left` using `by show y.left ≫ _ = _`. Rewrite using `[← Over.comp_left, hTx T y, hyy]`. Establish `hrH : r ≫ Y.H.hom = g ≫ jK R` using `Over.w y`.

Establish `q1 : p ≫ (DegPre.prB Dd.toPre (FractionRing R)).left = (yp ≫ Y.q).left` using `congrArg (·.left) hpp2`. Establish `q2 : p ≫ (DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R)).left = (y ≫ Y.q).left` using `congrArg (·.left) (htr T pp yp hpp2)`. Rewrite using `[q1, q2, hpB]`. Establish `f1` using `hρ' Z r w0 J₁ gJ₁`. Rewrite `f1` using `[rT]`.

Establish `f2` using `hρ Z r w0 J₁ gJ₁`. Rewrite `f2` using `[rT]`. Establish `f3` using `hT₁' T yp w0 J₁ gJ₁`. Establish `f4` using `hT₁ T yp w0 J₁ gJ₁`. Establish `f5` using `hT'' T y w0 J₁ gJ₁`.

Establish `f6` using `hT T y w0 J₁ gJ₁`. Establish `f7` using `C1 Z r w0 J₁ gJ₁`. Establish `f8` using `hL Z r w0 J₁ gJ₁`. Establish `f9` using `key u' hu' hc' Z g pp yp hpp1 hpp2 w0 J₁ gJ₁`. Simplify using `only [gs_scal_eq, hrH] at f7 f8`.

Use `set δa : R := ∑ i, ((n mu i + n α i : ℕ) : R) * d i with hδa`. Use `set δb : R := ∑ i, ((k * n mu i + n (mu + α) i : ℕ) : R) * d i with hδb`. Establish `hDa : 2 * (k : R) * D B₀ = (2 * k * δa) * B₀`. Rewrite using `[hB₀, der_prod D t d hd (fun i => n mu i + n α i)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hDb : 2 * (k : R) * D b = (2 * k * δb) * b`. Rewrite using `[hb, der_prod D t d hd (fun i => k * n mu i + n (mu + α) i)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `f8` using `[hDa, hDb, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δa) B₀, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δb) b]`. Establish `hw : (w α : R) = ∑ i, ((((n (mu + α) i : ℤ) - n mu i - n α i : ℤ)) : R) * d i` using `rfl`.

Establish `hc1 : 2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0 = 2 * k * δb - 2 * k * δa`. Rewrite using `[hw, hδa, hδb]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, mul_zero, add_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e10 : cst (g ≫ jK R) w0 (2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0) = cst (g ≫ jK R) w0 (2 * k * δb) - cst (g ≫ jK R) w0 (2 * k * δa)`. Rewrite using `[hc1, cst_sub']`. Establish `hU : IsUnit (cst (g ≫ jK R) w0 B₀ * (val ((Y.Φ T yp).s (α + k • mu)) (𝟙 Z) w0 J₁).val * (val e r w0 J₁ ^ k).val)` using `((GlobalTheory.ExpInt.isUnit_cst g w0 (ht0 _)).mul (Units.isUnit _)).mul (Units.isUnit _)`. Rewrite `f7`, `f8` using `[hb']`.

Establish `fin2 : ∀ {S : Type} [CommRing S] (cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ : S), IsUnit (cA * S' * E) → ρ' = τ₁' * E → ρ = τ₁ * E → τ₁' = s1' * S' → τ₁ = s1 * S' → τ'' = s'' * X → cA * ρ = cB * τ → cA * ρ' + (dA * cA) * ρ = cB * τ'' + (dB * cB) * τ → cA * U * S' * E = …`. Introduce `S _ cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ hu e1 e3 e2 e4 e5 e7 e8 e9 e10`. Establish `k0 : (cA * S' * E) * (s1' - (U * s'' + C * s1)) = 0`. Take the linear combination `e8 - dB * e7 - cA * ρ * e10 - cA * e1 - cA * E * e2 - s'' * e9 + cB * e5 + C * cA * e3 + C * cA * E * e4`. Conclude with `sub_eq_zero.1 (hu.mul_right_eq_zero.1 k0)`.

Conclude with `fin2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU f1 f2 f3 f4 f5 f7 f8 f9 e10`.
-/
theorem GlobalTheory.HeatShift.shift_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ mu : Dd.toPre.X, ∃ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Dd.toPre.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Dd.toPre.X) (w : Dd.toPre.X →+ R) (π π' : R), e.IsGen ∧ (∀ (j : Fin 2 → Dd.toPre.P.L.ι) (V : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Dd.toPre.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (k : ℕ) (α : Dd.toPre.X), 1 ≤ k → ∃ a b : R, a ≠ 0 ∧ ∀ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (τ τ₁ ρ : SecM Y.q.left Dd.toPre.P.L k), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → IsTerm Y k α σ τ → IsTerm Y k (α + k • mu) σ₁ τ₁ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ r z J = sval τ₁ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) ∧ ∀ (σ'' : Dd.toPre.SecB k α) (σ₁' : Dd.toPre.SecB k (α + k • mu)) (τ'' τ₁' ρ' : SecM Y.q.left Dd.toPre.P.L k), IsTerm Y k α σ'' τ'' → IsTerm Y k (α + k • mu) σ₁' τ₁' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ' r z J = sval τ₁' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ'' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D b)) * sval τ r z J) → ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y m t gam hmon ht D hD mu
  have hn : ∀ y, ∃ n : Fin m → ℕ, ∀ i, gam i y y = 2 * n i := fun y => by
    obtain ⟨u, n, h, -⟩ := hmon y
    exact ⟨n, h⟩
  choose n hn using hn
  choose ψ₀ hψ₀g hψ₀v using fun χ => GlobalTheory.T.exists_monomialPeriod_unitPart_generator R Dd.toPre m t gam hmon χ (n χ) (hn χ)
  obtain ⟨xp, hxq, hxv⟩ := GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates R Dd.toPre O oa Y m t gam Dd.tau_bimult ht n hn ψ₀ hψ₀g hψ₀v mu
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hx : (xp⁻¹ ≫ Y.q) * Dd.toPre.c mu = 1 := by
    rw [← hxq, ← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  obtain ⟨e, heg, hew, hev⟩ := GlobalTheory.T.exists_raynaudGauge_generator_weight_neg R Dd.toPre O oa Y mu xp⁻¹ hx (ψ₀ mu) (hψ₀g mu)
  have hd : ∀ i, ∃ d : R, D (t i) = d * t i := fun i => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hD i)
    exact ⟨c, by rw [hc, mul_comm]⟩
  choose d hd using hd
  have n0 : ∀ i, n 0 i = 0 := fun i => by
    have := hn 0 i
    simp at this
    omega
  have fadd : ∀ (a b : Dd.toPre.X) i, ((n (mu + (a + b)) i : ℤ) - n mu i - n (a + b) i) =
      ((n (mu + a) i : ℤ) - n mu i - n a i) + ((n (mu + b) i : ℤ) - n mu i - n b i) := by
    intro a b i
    have h1 := hn (mu + (a + b)) i
    have h2 := hn mu i
    have h3 := hn (a + b) i
    have h4 := hn (mu + a) i
    have h5 := hn a i
    have h6 := hn (mu + b) i
    have h7 := hn b i
    simp only [map_add, LinearMap.add_apply] at h1 h3 h4 h6
    linarith
  let w : Dd.toPre.X →+ R :=
    { toFun := fun a => ∑ i, ((((n (mu + a) i : ℤ) - n mu i - n a i : ℤ)) : R) * d i
      map_zero' := by simp [n0]
      map_add' := fun a b => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fadd a b i]
        push_cast
        ring }
  refine ⟨xp⁻¹, e, -mu, w, ∑ i, (n mu i : R) * d i, 0, heg, hew, ?_⟩
  intro k α hk

  have ht0 : ∀ N : Fin m → ℕ, (∏ i, t i ^ N i) ≠ 0 := fun N =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ht i)
  have hjFK : IsIso (jFK (R := R) (FractionRing R)) := by
    have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) := by
      rw [Algebra.algebraMap_self]
      exact inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))
    infer_instance

  have htr : ∀ (T : Over (Sp R)) (pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R)) (yp : T ⟶ Y.H),
      pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q →
      pp ≫ DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R) = (yp * (toUnit T ≫ xp)) ≫ Y.q := by
    intro T pp yp h
    rw [DegPre.trF, lift_snd, show ∀ f g : DegPre.BF Dd.toPre (FractionRing R) ⟶ Dd.toPre.P.A, padd Dd.toPre.P.A f g = f * g from
      fun _ _ => rfl, MonObj.comp_mul, MonObj.mul_comp, h, ← Category.assoc, comp_toUnit, Category.assoc, hxq]
  have hsq : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), (y * (toUnit T ≫ xp⁻¹)) * (toUnit T ≫ xp) = y := by
    intro T y
    rw [_root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
  have hTx : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), y ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)) = y * (toUnit T ≫ xp⁻¹) := by
    intro T y
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  set A₀ : R := ∏ i, t i ^ n (mu + α) i with hA₀
  set B₀ : R := ∏ i, t i ^ (n mu i + n α i) with hB₀
  set P₀ : R := ∏ i, t i ^ n mu i with hP₀
  set b : R := ∏ i, t i ^ (k * n mu i + n (mu + α) i) with hb
  have hb' : b = P₀ ^ k * A₀ := by
    rw [hb, hP₀, hA₀, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_add, mul_comm k, pow_mul]
  refine ⟨B₀, b, ht0 _, ?_⟩
  intro σ σ₁ τ τ₁ ρ hS hT hT₁ hρ

  have key := fun u hu hc => GlobalTheory.T.raynaudShift_unitIdentity_fractionField R Dd.toPre O oa Y Dd.tau_bimult k mu α xp A₀ B₀ P₀ (ψ₀ mu) e hxq
    (fun Z g z J hJ => hxv Z g α z J hJ) (fun Z g z J hJ => hψ₀v mu Z g z J hJ) hev u hu hc
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  have C1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι),
      Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom B₀) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
    refine GlobalTheory.T.raynaud_section_identity_of_generic_fibre R Dd.toPre O oa Y k ρ τ B₀ b fun Z g r hr z J hJ => ?_
    let T : Over (Sp R) := Over.mk (g ≫ jK R)
    let y : T ⟶ Y.H := Over.homMk r hr
    let yp : T ⟶ Y.H := y * (toUnit T ≫ xp⁻¹)
    let pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R) :=
      lift (Over.homMk (g ≫ inv (jFK (R := R) (FractionRing R))) (by
        show (g ≫ inv (jFK (R := R) (FractionRing R))) ≫ jFK (R := R) (FractionRing R) ≫ jK R = g ≫ jK R
        rw [Category.assoc, IsIso.inv_hom_id_assoc])) (yp ≫ Y.q)
    have hpp1 : (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g := by
      simp [pp]
    have hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q := lift_snd _ _
    have hK := key u hu hc Z g pp yp hpp1 hpp2 z J hJ
    rw [hsq T y] at hK
    have hsh := shiftEq_pt hS u hu hc pp.left z J hJ
    rw [cst_zero', zero_mul, add_zero, ← Over.comp_left, ← Over.comp_left, hpp2, htr T pp yp hpp2, hsq T y] at hsh
    have e1 := hρ Z r z J hJ
    have e1' : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left := by
      show y.left ≫ _ = _
      rw [← Over.comp_left]; exact congrArg (·.left) (hTx T y)
    rw [e1'] at e1
    have e2 := hT₁ T yp z J hJ
    have e3 : sval τ r z J = _ := hT T y z J hJ
    rw [gs_scal_eq, gs_scal_eq, hr]
    rw [e1, e2, e3, hsh, hb']
    have fin : ∀ {S : Type} [CommRing S] (cA cB U s S' E X : S), cA * U * S' * E = cB * X →
        cA * (U * s * S' * E) = cB * (s * X) := fun cA cB U s S' E X h => by linear_combination s * h
    exact fin _ _ _ _ _ _ _ hK

  refine ⟨C1, ?_⟩
  intro σ'' σ₁' τ'' τ₁' ρ' hT'' hT₁' hρ' hL u' hu' hc' z J hJ
  obtain ⟨Z, p, w0, y0, rfl, hepi, hinj, hyq⟩ := GlobalTheory.T.exists_flat_epi_lift_raynaud_extension_fraction_point R Dd.toPre O oa Y z
  have hJ₁ : ∃ J₁ : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι, Good Dd.toPre.P.L w0 J₁ ∧ ∀ ψ, J₁ (p ≫ ψ) = J ψ := by
    classical
    refine ⟨fun φ => if h : ∃ ψ, p ≫ ψ = φ then J h.choose else (exists_chart Dd.toPre.P.isLB (φ w0)).choose,
      fun φ => ?_, fun ψ => ?_⟩
    · by_cases h : ∃ ψ, p ≫ ψ = φ
      · simp only [dif_pos h]
        have e := h.choose_spec
        have : (p ≫ h.choose) w0 ∈ Dd.toPre.P.L.U (J h.choose) := by
          rw [Scheme.Hom.comp_apply]; exact hJ _
        rwa [e] at this
      · simp only [dif_neg h]
        exact (exists_chart Dd.toPre.P.isLB (φ w0)).choose_spec
    · have h : ∃ ψ', p ≫ ψ' = p ≫ ψ := ⟨ψ, rfl⟩
      simp only [dif_pos h]
      exact congrArg J ((cancel_epi p).1 h.choose_spec)
  obtain ⟨J₁, gJ₁, eJ₁⟩ := hJ₁
  have eJ : J = fun ψ => J₁ (p ≫ ψ) := funext fun ψ => (eJ₁ ψ).symm
  subst eJ
  apply hinj
  have hv := GlobalTheory.HeatDefect.val_comp_stalk u' (𝟙 _) p w0 gJ₁
  rw [Category.comp_id] at hv
  rw [map_add, map_mul, map_mul, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁,
    ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← hv, ← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) w0 ⊤ trivial,
    Category.comp_id, gs_scal_eq]
  clear hv eJ₁ hJ hinj
  set g : Z ⟶ (TK R).left := p ≫ (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
    with hg
  have hpB : p ≫ (DegPre.BF Dd.toPre (FractionRing R)).hom = g ≫ jK R := by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A), hg]
    simp only [Category.assoc]
    rfl
  let T : Over (Sp R) := Over.mk (g ≫ jK R)
  let pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R) := Over.homMk p hpB
  let yp : T ⟶ Y.H := Over.homMk y0 (by
    show y0 ≫ Y.H.hom = g ≫ jK R
    rw [← Over.w Y.q, ← Category.assoc, hyq, Category.assoc, Over.w (DegPre.prB Dd.toPre (FractionRing R)), hpB])
  have hpp1 : (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g := by
    rw [hg]; simp [pp]
  have hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q := Over.OverMorphism.ext hyq.symm
  let y : T ⟶ Y.H := yp * (toUnit T ≫ xp)
  let r : Z ⟶ Y.H.left := y.left
  have hyy : y * (toUnit T ≫ xp⁻¹) = yp := by
    show yp * (toUnit T ≫ xp) * (toUnit T ≫ xp⁻¹) = yp
    rw [_root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]
  have rT : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left := by
    show y.left ≫ _ = _
    rw [← Over.comp_left, hTx T y, hyy]
  have hrH : r ≫ Y.H.hom = g ≫ jK R := Over.w y
  have q1 : p ≫ (DegPre.prB Dd.toPre (FractionRing R)).left = (yp ≫ Y.q).left := congrArg (·.left) hpp2
  have q2 : p ≫ (DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R)).left = (y ≫ Y.q).left :=
    congrArg (·.left) (htr T pp yp hpp2)
  rw [q1, q2, hpB]
  have f1 := hρ' Z r w0 J₁ gJ₁
  rw [rT] at f1
  have f2 := hρ Z r w0 J₁ gJ₁
  rw [rT] at f2
  have f3 := hT₁' T yp w0 J₁ gJ₁
  have f4 := hT₁ T yp w0 J₁ gJ₁
  have f5 := hT'' T y w0 J₁ gJ₁
  have f6 := hT T y w0 J₁ gJ₁
  have f7 := C1 Z r w0 J₁ gJ₁
  have f8 := hL Z r w0 J₁ gJ₁
  have f9 := key u' hu' hc' Z g pp yp hpp1 hpp2 w0 J₁ gJ₁
  simp only [gs_scal_eq, hrH] at f7 f8
  set δa : R := ∑ i, ((n mu i + n α i : ℕ) : R) * d i with hδa
  set δb : R := ∑ i, ((k * n mu i + n (mu + α) i : ℕ) : R) * d i with hδb
  have hDa : 2 * (k : R) * D B₀ = (2 * k * δa) * B₀ := by
    rw [hB₀, der_prod D t d hd (fun i => n mu i + n α i)]; ring
  have hDb : 2 * (k : R) * D b = (2 * k * δb) * b := by
    rw [hb, der_prod D t d hd (fun i => k * n mu i + n (mu + α) i)]; ring
  rw [hDa, hDb, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δa) B₀, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δb) b] at f8
  have hw : (w α : R) = ∑ i, ((((n (mu + α) i : ℤ) - n mu i - n α i : ℤ)) : R) * d i := rfl
  have hc1 : 2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0 =
      2 * k * δb - 2 * k * δa := by
    rw [hw, hδa, hδb]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have e10 : cst (g ≫ jK R) w0 (2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0) =
      cst (g ≫ jK R) w0 (2 * k * δb) - cst (g ≫ jK R) w0 (2 * k * δa) := by
    rw [hc1, cst_sub']
  have hU : IsUnit (cst (g ≫ jK R) w0 B₀ * (val ((Y.Φ T yp).s (α + k • mu)) (𝟙 Z) w0 J₁).val * (val e r w0 J₁ ^ k).val) :=
    ((GlobalTheory.ExpInt.isUnit_cst g w0 (ht0 _)).mul (Units.isUnit _)).mul (Units.isUnit _)
  rw [hb'] at f7 f8
  have fin2 : ∀ {S : Type} [CommRing S] (cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ : S),
      IsUnit (cA * S' * E) → ρ' = τ₁' * E → ρ = τ₁ * E → τ₁' = s1' * S' → τ₁ = s1 * S' → τ'' = s'' * X →
      cA * ρ = cB * τ → cA * ρ' + (dA * cA) * ρ = cB * τ'' + (dB * cB) * τ → cA * U * S' * E = cB * X →
      C = dB - dA → s1' = U * s'' + C * s1 := by
    intro S _ cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ hu e1 e3 e2 e4 e5 e7 e8 e9 e10
    have k0 : (cA * S' * E) * (s1' - (U * s'' + C * s1)) = 0 := by
      linear_combination e8 - dB * e7 - cA * ρ * e10 - cA * e1 - cA * E * e2 - s'' * e9 + cB * e5 + C * cA * e3 +
        C * cA * E * e4
    exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 k0)
  exact fin2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU f1 f2 f3 f4 f5 f7 f8 f9 e10
