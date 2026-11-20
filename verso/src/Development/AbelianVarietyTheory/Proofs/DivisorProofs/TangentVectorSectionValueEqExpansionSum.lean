import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombinationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

section Alg
variable {K : Type} [Field K]

/- English proof (translation)
Use `show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).fst = _`. Simplify using the standard rewrite rules.
-/
theorem dualMap_fst {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).fst = f z.fst := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).fst = _
  simp

/- English proof (translation)
Use `show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).snd = _`. Simplify using the standard rewrite rules.
-/
theorem dualMap_snd {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).snd = f z.snd := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).snd = _
  simp

/- English proof (translation)
Rewrite using `[TrivSqZeroExt.snd_mul]`. Simplify using `only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`.
-/
theorem dn_snd_mul (u x : DualNumber K) : (u * x).snd = u.fst * x.snd + u.snd * x.fst := by
  rw [TrivSqZeroExt.snd_mul]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg TrivSqZeroExt.fst (Units.mul_inv u)`. Rewrite `h1` using `[TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one]`. Conclude with `zero_ne_one h1`.
-/
theorem unit_fst_ne (u : (DualNumber K)ˣ) : (u : DualNumber K).fst ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at h1
  exact zero_ne_one h1

/- English proof (translation)
Establish `h1` using `congrArg TrivSqZeroExt.fst (Units.mul_inv u)`. Rewrite `h1` using `[TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one]`. Conclude with `eq_inv_of_mul_eq_one_right h1`.
-/
theorem unit_inv_fst (u : (DualNumber K)ˣ) : ((u⁻¹ : (DualNumber K)ˣ) : DualNumber K).fst = ((u : DualNumber K).fst)⁻¹ := by
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

/- English proof (translation)
Establish `hu` using `unit_fst_ne U₁`. Establish `e1` using `dn_snd_mul (U₁ : DualNumber K) P`. Establish `e2` using `dn_snd_mul (U₁ : DualNumber K) (TrivSqZeroExt.inl r)`. Use `ext`. Simplify using `only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, dn_snd_mul]`. Simplify using `only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, e2, add_zero, zero_add, mul_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualNumber_unit_mul_decomposition (U₁ : (DualNumber K)ˣ) (r : K) (hr : r ≠ 0) (P : DualNumber K) :
    (U₁ : DualNumber K) * P = TrivSqZeroExt.inl (((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst) *
      (TrivSqZeroExt.inl (P.fst / r) + TrivSqZeroExt.inr (P.snd / r +
        ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).snd / ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst * (P.fst / r))) := by
  have hu := unit_fst_ne U₁
  have e1 := dn_snd_mul (U₁ : DualNumber K) P
  have e2 := dn_snd_mul (U₁ : DualNumber K) (TrivSqZeroExt.inl r)
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    field_simp
  · rw [e1, dn_snd_mul]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, e2, add_zero, zero_add, mul_zero]
    field_simp
    ring

/- English proof (translation)
Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_inl, unit_inv_fst]`.
-/
theorem fst_U (Θ T ω : (DualNumber K)ˣ) (k : ℕ) (r : K) :
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber K)ˣ) : DualNumber K) * TrivSqZeroExt.inl r).fst =
      (Θ : DualNumber K).fst * ((T : DualNumber K).fst)⁻¹ * (((ω : DualNumber K).fst)⁻¹) ^ k * r := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.fst_inl, unit_inv_fst]

/- English proof (translation)
Substitute `h1 h2 h3` using the available equality. Rewrite using `[mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fst_eq_of (θ τ ω g m r p : K) (k : ℕ) (hτ : τ ≠ 0) (hω : ω ≠ 0) (h1 : θ * g ^ k = p) (h2 : τ * m ^ k = r)
    (h3 : ω * g = m) : θ * τ⁻¹ * ω⁻¹ ^ k * r = p := by
  subst h1 h2 h3
  rw [mul_pow, inv_pow]
  field_simp

variable {Ix : Type}

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [TrivSqZeroExt.fst_mul]`. Conclude with `h.1.mul_left _`. Simplify using `only [dn_snd_mul]`. Conclude with `(h.2.mul_left _).add (h.1.mul_left _)`.
-/
theorem ds_mul_left {f : Ix → DualNumber K} {s : DualNumber K} [TopologicalSpace K] [IsTopologicalRing K] (u : DualNumber K)
    (h : HasSum (fun a => (f a).fst) s.fst ∧ HasSum (fun a => (f a).snd) s.snd) :
    HasSum (fun a => (u * f a).fst) (u * s).fst ∧ HasSum (fun a => (u * f a).snd) (u * s).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_mul]
    exact h.1.mul_left _
  · simp only [dn_snd_mul]
    exact (h.2.mul_left _).add (h.1.mul_left _)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [TrivSqZeroExt.fst_sum]`. Conclude with `hasSum_sum fun i _ => (h i).1`. Simplify using `only [TrivSqZeroExt.snd_sum]`. Conclude with `hasSum_sum fun i _ => (h i).2`.
-/
theorem ds_sum {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] (f : Fin n → Ix → DualNumber K) (s : Fin n → DualNumber K)
    (h : ∀ i, HasSum (fun a => (f i a).fst) (s i).fst ∧ HasSum (fun a => (f i a).snd) (s i).snd) :
    HasSum (fun a => (∑ i, f i a).fst) (∑ i, s i).fst ∧ HasSum (fun a => (∑ i, f i a).snd) (∑ i, s i).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_sum]
    exact hasSum_sum fun i _ => (h i).1
  · simp only [TrivSqZeroExt.snd_sum]
    exact hasSum_sum fun i _ => (h i).2

/- English proof (translation)
Introduce `p _`. Establish `hle : (p : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B` using `(PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)`. Use `first`. Consider the case `exact (hle.map x.continuous).mem_open W.isOpen h`. Consider the case `exact (hle.map x.base.hom.continuous).mem_open W.isOpen h`.
-/
private theorem isChart_choose_and_symm_apply {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (W : X.Opens)
    (h : x (IsLocalRing.closedPoint B) ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro p _
  have hle : (p : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  first
  | exact (hle.map x.continuous).mem_open W.isOpen h
  | exact (hle.map x.base.hom.continuous).mem_open W.isOpen h

end Alg

/- English proof (translation)
Introduce `V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hν w₀ ρ hρ y gm₀ gm yA hy hrel hpull hvec k i₀ hi₀`. Use `haveI : IsLocalRing (DualNumber V) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V`. Take `⟨J0, hJ0⟩` from `GlobalTheory.UU.exists_good_pt U.LG.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))`. Take `⟨J1, hJ1⟩` from `GlobalTheory.UU.exists_good_pt D.toPre.P.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))`. Establish `hjG : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U (J0 y.left)` using `isChart_choose_and_symm_apply _ _ (hJ0 y.left)`.

Establish `hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J1 ψ)` using `fun ψ => isChart_choose_and_symm_apply _ _ (hJ1 ψ)`. Establish `hgt : GtTan gm₀` using `GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin V hV D A G hG U y gm₀ hy hrel`. Take `⟨W, hW1, hW2⟩` from `GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum V hV D A G hG U y gm₀ hy hrel k (J0 y.left) J1 hjG hJ`. Take `⟨T, hD, hT1, hT2⟩` from `GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange V D.toPre C N ν gm₀ gm hgt hpull k J1 hJ`. Take `⟨Θ, hΘ1, hΘ2⟩` from `GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination V (IsLocalRing.maximalIdeal V) D A G U.toUnifPre C w₀ ρ hρ y yA hy hvec k i₀ (J0 y.left) hi₀ hjG`.

Take `⟨ω, hω⟩ : ∃ ω : (DualNumber C)ˣ, (ω : DualNumber C) = dualMap (toF V C) (W : DualNumber V)` from `⟨Units.map (dualMap (toF V C)).toMonoidHom W, rfl⟩`. Establish `hωfst : (ω : DualNumber C).fst = toF V C (W : DualNumber V).fst` using `by rw [hω, dualMap_fst]`. Establish `h3 : (ω : DualNumber C).fst * toF V C (rigVal U.LG (J0 y.left)) = toF V C (rigValD D.toPre (J1 gm₀.b.left))`. Rewrite using `[hωfst, ← map_mul, hW1]`. Establish `hinj : Function.Injective (toF V C)` using `by show Function.Injective ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))`.

Rewrite using `[RingHom.coe_comp]`. Conclude with `(algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))`. Establish `hm : toF V C (rigValD D.toPre (J1 gm₀.b.left)) ≠ 0`. Introduce `h0`. Apply `hD` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[h0, map_zero]`. Establish `hτ` using `unit_fst_ne T`. Establish `hωne` using `unit_fst_ne ω`. Establish `hr : ν.rg ^ k ≠ 0`.

Rewrite using `[← hT1]`. Conclude with `mul_ne_zero hτ (pow_ne_zero _ hm)`. Establish `hfst` using `(fst_U Θ T ω k (ν.rg ^ k)).trans (fst_eq_of _ _ _ _ _ _ _ k hτ hωne hΘ1 hT1 h3)`. Use `⟨(((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).snd / (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).fst, ?_⟩` and prove the remaining obligations. Introduce `t s hts`.

Take `⟨σ', hcar, n, cc, σ, fa, hexp, hlin, hslin⟩` from `hts`. Establish `hA : ∀ i, HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).fst) (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).fst ∧ HasSum (fun α => (dualMap (toF V C) ( …`. Introduce `i`. Take `⟨h1, h2⟩` from `GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum V (IsLocalRing.maximalIdeal V) C hC _ _ (hW2 (σ i) (fa i) (hexp i))`. Simplify using `only [dualMap_fst, dualMap_snd]`.

Conclude with `⟨(Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).fst) ν.eX.toEquiv).2 h1, (Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).snd) ν.eX.toEquiv).2 h2⟩`. Establish `hB` using `ds_mul_left (T : DualNumber C) (ds_sum (fun i α => TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))) _ (fun i => ds_mul_left (TrivSqZeroExt.inl (cc i)) (hA i)))`. Establish `hjc` using `hT2 s n cc fa hslin`. Simplify using `only [← hjc] at hB`. Take `⟨hf, hs⟩` from `hB`.

Establish `hS : ((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * ((T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) = (Θ : Dual …`. Simplify using `only [map_mul, map_pow, ← hω]`. Establish `e1 : ∀ i, TrivSqZeroExt.inl (cc i) * ((ω : DualNumber C) ^ k * dualMap (toF V C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) = (ω : DualNumber C) ^ k * (TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left (LB …` using `fun i => by ring`. Simplify using `only [e1, ← Finset.mul_sum]`. Establish `hb : ((T⁻¹ : (DualNumber C)ˣ) : DualNumber C) * (T : DualNumber C) = 1` using `Units.inv_mul T`.

Establish `hw : ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k = 1`. Rewrite using `[← mul_pow, Units.inv_mul, one_pow]`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]`. Take the linear combination `((Θ : DualNumber C) * (∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) * ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k) * hb + ((Θ : DualNumber …`. Use `⟨(hf.div_const _).summable, (hs.div_const _).summable, ?_⟩` and prove the remaining obligations.

Rewrite using `[(hf.div_const _).tsum_eq, (hs.div_const _).tsum_eq, hΘ2 t σ' hcar n cc σ hlin, ← hS, dualNumber_unit_mul_decomposition _ _ hr, hfst]`.
-/
theorem value_at_tangent : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hν w₀ ρ hρ y gm₀ gm yA hy hrel hpull hvec k i₀ hi₀
  haveI : IsLocalRing (DualNumber V) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  obtain ⟨J0, hJ0⟩ := GlobalTheory.UU.exists_good_pt U.LG.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  obtain ⟨J1, hJ1⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  have hjG : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U (J0 y.left) := isChart_choose_and_symm_apply _ _ (hJ0 y.left)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J1 ψ) := fun ψ => isChart_choose_and_symm_apply _ _ (hJ1 ψ)
  have hgt : GtTan gm₀ := GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin V hV D A G hG U y gm₀ hy hrel
  obtain ⟨W, hW1, hW2⟩ := GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum V hV D A G hG U y gm₀ hy hrel k (J0 y.left) J1 hjG hJ
  obtain ⟨T, hD, hT1, hT2⟩ := GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange V D.toPre C N ν gm₀ gm hgt hpull k J1 hJ
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination V (IsLocalRing.maximalIdeal V) D A G U.toUnifPre C w₀ ρ hρ y yA hy hvec k i₀
    (J0 y.left) hi₀ hjG
  obtain ⟨ω, hω⟩ : ∃ ω : (DualNumber C)ˣ, (ω : DualNumber C) = dualMap (toF V C) (W : DualNumber V) :=
    ⟨Units.map (dualMap (toF V C)).toMonoidHom W, rfl⟩
  have hωfst : (ω : DualNumber C).fst = toF V C (W : DualNumber V).fst := by rw [hω, dualMap_fst]
  have h3 : (ω : DualNumber C).fst * toF V C (rigVal U.LG (J0 y.left)) =
      toF V C (rigValD D.toPre (J1 gm₀.b.left)) := by
    rw [hωfst, ← map_mul, hW1]
  have hinj : Function.Injective (toF V C) := by
    show Function.Injective ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    rw [RingHom.coe_comp]
    exact (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hm : toF V C (rigValD D.toPre (J1 gm₀.b.left)) ≠ 0 := by
    intro h0
    apply hD
    apply hinj
    rw [h0, map_zero]
  have hτ := unit_fst_ne T
  have hωne := unit_fst_ne ω
  have hr : ν.rg ^ k ≠ 0 := by
    rw [← hT1]
    exact mul_ne_zero hτ (pow_ne_zero _ hm)
  have hfst := (fst_U Θ T ω k (ν.rg ^ k)).trans (fst_eq_of _ _ _ _ _ _ _ k hτ hωne hΘ1 hT1 h3)
  refine ⟨(((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).snd /
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).fst, ?_⟩
  intro t s hts
  obtain ⟨σ', hcar, n, cc, σ, fa, hexp, hlin, hslin⟩ := hts
  have hA : ∀ i, HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).fst)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).fst ∧
      HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).snd)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).snd := by
    intro i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum V (IsLocalRing.maximalIdeal V) C hC _ _ (hW2 (σ i) (fa i) (hexp i))
    simp only [dualMap_fst, dualMap_snd]
    exact ⟨(Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).fst) ν.eX.toEquiv).2 h1,
      (Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).snd) ν.eX.toEquiv).2 h2⟩
  have hB := ds_mul_left (T : DualNumber C)
    (ds_sum (fun i α => TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α))))
      _ (fun i => ds_mul_left (TrivSqZeroExt.inl (cc i)) (hA i)))
  have hjc := hT2 s n cc fa hslin
  simp only [← hjc] at hB
  obtain ⟨hf, hs⟩ := hB
  have hS : ((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * ((T : DualNumber C) *
      ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
      (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left)) := by
    simp only [map_mul, map_pow, ← hω]
    have e1 : ∀ i, TrivSqZeroExt.inl (cc i) * ((ω : DualNumber C) ^ k * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
        (ω : DualNumber C) ^ k * (TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) :=
      fun i => by ring
    simp only [e1, ← Finset.mul_sum]
    have hb : ((T⁻¹ : (DualNumber C)ˣ) : DualNumber C) * (T : DualNumber C) = 1 := Units.inv_mul T
    have hw : ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination ((Θ : DualNumber C) * (∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) *
        ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k) * hb +
      ((Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) * hw
  refine ⟨(hf.div_const _).summable, (hs.div_const _).summable, ?_⟩
  rw [(hf.div_const _).tsum_eq, (hs.div_const _).tsum_eq, hΘ2 t σ' hcar n cc σ hlin, ← hS, dualNumber_unit_mul_decomposition _ _ hr, hfst]

end GlobalTheory.MBLow.TanExp

end
