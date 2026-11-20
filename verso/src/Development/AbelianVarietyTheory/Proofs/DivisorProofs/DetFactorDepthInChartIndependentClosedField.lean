import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthField

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth

section Monomials

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
The claim follows from `WithBot.coe_le_coe.2 h`.
-/
theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := WithBot.coe_le_coe.2 h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, v.map_zero]`. Conclude with `le_top`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Establish `h1` using `h a (Finset.mem_insert_self _ _)`. Establish `h2` using `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`. Use `le_trans ?_ (toE_mono (v.map_add _ _))` and prove the remaining obligations. Apply the tactic sequence `rcases min_choice (v (g a)) (v (∑ i ∈ S, g i)) with e | e <;> rw [e] <;> assumption`.
-/
theorem le_toE_sum {ι : Type} (S : Finset ι) (g : ι → C) {r : EReal} (h : ∀ i ∈ S, r ≤ toE (v (g i))) :
    r ≤ toE (v (∑ i ∈ S, g i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, v.map_zero]; exact le_top
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine le_trans ?_ (toE_mono (v.map_add _ _))
    rcases min_choice (v (g a)) (v (∑ i ∈ S, g i)) with e | e <;> rw [e] <;> assumption

/- English proof (translation)
Use `⟨P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset, ?_⟩` and prove the remaining obligations. Simplify using `only [derivAt0, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[coeff_subst hE, finsum_eq_sum_of_support_subset (s := P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset) _ fun β hβ => by`.

Simplify using `only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]`. Conclude with `⟨α, hα, (Set.Finite.mem_toFinset _).2 hβ⟩, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[subst_monomial hE, map_one, one_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_subst {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E) (P : MvPolynomial τ C)
    (f : MvPowerSeries σ C) : ∃ S : Finset (σ →₀ ℕ),
      derivAt0 P (subst E f) = ∑ β ∈ S, coeff β f * derivAt0 P (subst E (monomial β (1 : C))) := by
  classical
  refine ⟨P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset, ?_⟩
  simp only [derivAt0, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_subst hE, finsum_eq_sum_of_support_subset (s := P.support.biUnion
    fun α => (coeff_subst_finite hE f α).toFinset) _ fun β hβ => by
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨α, hα, (Set.Finite.mem_toFinset _).2 hβ⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [subst_monomial hE, map_one, one_mul, smul_eq_mul]
  ring

variable {κ : Type} {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]

/- English proof (translation)
Introduce `e`. Simplify using `[map_sum]`.
-/
theorem hasSubst_lin (u : ∀ b, ι b → Fin (d b) → C) (b : κ) :
    ∀ e : Fin (d b), constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := by
  intro e
  simp [map_sum]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1) ((isExp_expOf (G x.1)).1 x.2)`.
-/
theorem hasSubst_expAlong [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C) :
    HasSubst (expAlong G u) :=
  hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
      ((isExp_expOf (G x.1)).1 x.2)

/- English proof (translation)
Use `le_antisymm (le_iInf fun β => iInf_le_of_le ⟨monomial β 1, fun α => ?_⟩ le_rfl) (le_iInf fun f => ?_)` and prove the remaining obligations. Apply the tactic sequence `rw [IsIntV, coeff_monomial] split_ifs <;> simp`. Take `⟨S, hS⟩` from `derivAt0_subst (hasSubst_expAlong G u) P f.1`. Rewrite using `[hS]`. Use `le_toE_sum S _ fun β _ => iInf_le_of_le β (toE_mono ?_)` and prove the remaining obligations.

Rewrite using `[v.map_mul]`. Conclude with `le_add_of_nonneg_left (f.2 β)`.
-/
theorem depth_eq_iInf_monomial [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C)
    (P : MvPolynomial (Σ b, ι b) C) :
    depth G u P = ⨅ β : (Σ b, Fin (d b)) →₀ ℕ,
      toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  classical
  refine le_antisymm (le_iInf fun β => iInf_le_of_le ⟨monomial β 1, fun α => ?_⟩ le_rfl) (le_iInf fun f => ?_)
  · rw [IsIntV, coeff_monomial]
    split_ifs <;> simp
  · obtain ⟨S, hS⟩ := derivAt0_subst (hasSubst_expAlong G u) P f.1
    rw [hS]
    refine le_toE_sum S _ fun β _ => iInf_le_of_le β (toE_mono ?_)
    rw [v.map_mul]
    exact le_add_of_nonneg_left (f.2 β)

end Monomials

section Map

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {v : AddValuation C (WithTop ℝ)}
  {w : AddValuation K (WithTop ℝ)}

/- English proof (translation)
Simplify using `only [derivAt0, MvPolynomial.support_map_of_injective _ φ.injective, map_sum, map_mul, MvPolynomial.coeff_map, coeff_map, mfact, Finsupp.prod, map_prod, map_natCast]`.
-/
theorem derivAt0_map {σ : Type} (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.map φ P) (MvPowerSeries.map φ g) = φ (derivAt0 P g) := by
  simp only [derivAt0, MvPolynomial.support_map_of_injective _ φ.injective, map_sum, map_mul,
    MvPolynomial.coeff_map, coeff_map, mfact, Finsupp.prod, map_prod, map_natCast]

/- English proof (translation)
Establish `he` using `isExp_expOf G`. Establish `: IsExp G' fun a => MvPowerSeries.map φ (expOf G a)`. Use `⟨fun a => by simp [he.1 a], fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[h, ← map_subst (hasSubst_of_constantCoeff_zero he.1), he.2, map_X]`. Rewrite using `[← isExp_unique G' this]`.
-/
theorem expOf_map {d : ℕ} (G : LogFGL w d) (G' : LogFGL v d)
    (h : ∀ a, G'.lg a = MvPowerSeries.map φ (G.lg a)) (a : Fin d) :
    expOf G' a = MvPowerSeries.map φ (expOf G a) := by
  have he := isExp_expOf G
  have : IsExp G' fun a => MvPowerSeries.map φ (expOf G a) := by
    refine ⟨fun a => by simp [he.1 a], fun a => ?_⟩
    rw [h, ← map_subst (hasSubst_of_constantCoeff_zero he.1), he.2, map_X]
  rw [← isExp_unique G' this]

/- English proof (translation)
Establish `hE : expAlong G' (fun b a e => φ (u b a e)) = fun x => MvPowerSeries.map φ (expAlong G u x)`. Use function extensionality and compare the values at `x`. Simplify using `only [expAlong]`. Rewrite using `[map_subst (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)), expOf_map φ _ _ (h x.1)]`. Use `congr 1`.

Use function extensionality and compare the values at `e`. Simplify using `[map_sum, smul_eq_C_mul]`. Rewrite using `[depth_eq_iInf_monomial, depth_eq_iInf_monomial, hE]`. Use `iInf_congr fun β => ?_` and prove the remaining obligations. Rewrite using `[← hv, ← derivAt0_map, map_subst (hasSubst_expAlong G u), map_monomial, φ.map_one]`.
-/
theorem depth_map {κ : Type} [Finite κ] {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]
    (hv : ∀ x, v (φ x) = w x) (G : ∀ b, LogFGL w (d b)) (G' : ∀ b, LogFGL v (d b))
    (h : ∀ b a, (G' b).lg a = MvPowerSeries.map φ ((G b).lg a)) (u : ∀ b, ι b → Fin (d b) → K)
    (P : MvPolynomial (Σ b, ι b) K) :
    depth G' (fun b a e => φ (u b a e)) (MvPolynomial.map φ P) = depth G u P := by
  have hE : expAlong G' (fun b a e => φ (u b a e)) = fun x => MvPowerSeries.map φ (expAlong G u x) := by
    funext x
    simp only [expAlong]
    rw [map_subst (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)), expOf_map φ _ _ (h x.1)]
    congr 1
    funext e
    simp [map_sum, smul_eq_C_mul]
  rw [depth_eq_iInf_monomial, depth_eq_iInf_monomial, hE]
  refine iInf_congr fun β => ?_
  rw [← hv, ← derivAt0_map, map_subst (hasSubst_expAlong G u), map_monomial, φ.map_one]

/- English proof (translation)
Rewrite using `[detPow, detPow, map_pow, RingHom.map_det]`. Use `congr 2`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem detPow_map (i c : ℕ) : MvPolynomial.map φ (detPow K i c) = detPow C i c := by
  rw [detPow, detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

/- English proof (translation)
Use extensionality with `α`. Simplify using `[coeff_pderiv]`.
-/
theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv K i f) = pderiv C i (MvPowerSeries.map φ f) := by
  ext α
  simp [coeff_pderiv]

/- English proof (translation)
Establish `hJ : JM (GlobalTheory.FBMap.mapLaw φ G) = (JM G).map (MvPowerSeries.map φ)` using `by ext1 i b`. Simplify using `only [JM, Jac, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[GlobalTheory.FBMap.map_ev2 φ (GlobalTheory.FBMap.nc_pt _) GlobalTheory.FBMap.nc_zero, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_zero, map_pderiv]`. Both sides reduce to the same expression. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations.

Rewrite using `[hJ, ← Matrix.map_mul, om_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem om_map {d : ℕ} (G : FGLaw K d) :
    Om (GlobalTheory.FBMap.mapLaw φ G) = (Om G).map (MvPowerSeries.map φ) := by
  have hJ : JM (GlobalTheory.FBMap.mapLaw φ G) = (JM G).map (MvPowerSeries.map φ) := by
    ext1 i b
    simp only [JM, Jac, Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.FBMap.map_ev2 φ (GlobalTheory.FBMap.nc_pt _) GlobalTheory.FBMap.nc_zero, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_zero,
      map_pderiv]
    rfl
  refine Matrix.inv_eq_left_inv ?_
  rw [hJ, ← Matrix.map_mul, om_mul, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, eq_C_of_pderiv_zero (g := logOf (GlobalTheory.FBMap.mapLaw φ G) a - MvPowerSeries.map φ (logOf G a))]`. Simplify using `[logOf, constantCoeff_prim]`. Introduce and unpack `⟨j, b⟩`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Rewrite using `[map_sub, ← map_pderiv, pderiv_logOf, pderiv_logOf, om_map, Matrix.map_apply, sub_self]`.
-/
theorem logOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (a : Fin d) :
    logOf (GlobalTheory.FBMap.mapLaw φ G) a = MvPowerSeries.map φ (logOf G a) := by
  rw [← sub_eq_zero, eq_C_of_pderiv_zero (g := logOf (GlobalTheory.FBMap.mapLaw φ G) a - MvPowerSeries.map φ (logOf G a))]
  · simp [logOf, constantCoeff_prim]
  · rintro ⟨j, b⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, ← map_pderiv, pderiv_logOf, pderiv_logOf, om_map, Matrix.map_apply, sub_self]

/- English proof (translation)
Use `show subst (oneVar C d) (logOf (GlobalTheory.FBMap.mapLaw φ G) a) = MvPowerSeries.map φ (subst (oneVar K d) (logOf G a))`. Rewrite using `[logOf_map, map_subst hs_oneVar]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `[oneVar]`.
-/
theorem lg_logFGLOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (hG) (hG') (a : Fin d) :
    (logFGLOf v (GlobalTheory.FBMap.mapLaw φ G) hG').lg a = MvPowerSeries.map φ ((logFGLOf w G hG).lg a) := by
  show subst (oneVar C d) (logOf (GlobalTheory.FBMap.mapLaw φ G) a) = MvPowerSeries.map φ (subst (oneVar K d) (logOf G a))
  rw [logOf_map, map_subst hs_oneVar]
  congr 1
  funext q
  simp [oneVar]

end Map

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Introduce `p _ T io y Ch X X' f k`. Use `letI := io.toAlgebra`. Use `haveI : CharZero T.Fr := X.ιF.charZero`.

Set `w : AddValuation T.Fr (WithTop ℝ)` to `(vX_vp X).comap X.ιF`. Establish `hw : ∀ (Y : ValExt T p) x, vX_vp Y (Y.ιF x) = w x`. Introduce `Y x`. Use `show _ = vX_vp X (X.ιF x)`. Distinguish the cases in `hx : x = 0`.

Rewrite using `[hx, Y.ιF.map_zero, X.ιF.map_zero, AddValuation.map_zero, AddValuation.map_zero]`. Rewrite using `[vX_vp_ιF Y hx, vX_vp_ιF X hx]`. Establish `hG : ∀ a, MvIsInt w (subst (twoVars T.Fr _) (Ch.ch.B.G.F a))`. Introduce `a α`. Establish `h` using `(fgl Ch X).F_int a α`.

Establish `e : (fgl Ch X).F a = MvPowerSeries.map X.ιF (subst (twoVars T.Fr _) (Ch.ch.B.G.F a))`. Rewrite using `[map_subst hs_twoVars]`. Use `show subst (twoVars X.C _) (MvPowerSeries.map X.ιF (Ch.ch.B.G.F a)) = _`. Use `congr 1`. Use function extensionality and compare the values at `q`.

Simplify using `[twoVars]`. Rewrite `h` using `[e, coeff_map]`. Conclude with `h`. Establish `key : ∀ Y : ValExt T p, nuFacC Ch Y f k = detDepth (logFGLOf w Ch.ch.B.G hG) (fun (a : Fin (rk f)) e => algebraMap T.V T.Fr (Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)) k`. Introduce `Y`.

Rewrite using `[nuFacC, detDepth, detDepth, ← detPow_map Y.ιF]`. Conclude with `depth_map Y.ιF (hw Y) _ _ (fun _ a => lg_logFGLOf_map Y.ιF _ hG _ a) _ _`. Rewrite using `[key, key]`.
-/
theorem nuFacC_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X X' f k
  letI := io.toAlgebra
  haveI : CharZero T.Fr := X.ιF.charZero
  let w : AddValuation T.Fr (WithTop ℝ) := (vX_vp X).comap X.ιF
  have hw : ∀ (Y : ValExt T p) x, vX_vp Y (Y.ιF x) = w x := by
    intro Y x
    show _ = vX_vp X (X.ιF x)
    by_cases hx : x = 0
    · rw [hx, Y.ιF.map_zero, X.ιF.map_zero, AddValuation.map_zero, AddValuation.map_zero]
    · rw [vX_vp_ιF Y hx, vX_vp_ιF X hx]
  have hG : ∀ a, MvIsInt w (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
    intro a α
    have h := (fgl Ch X).F_int a α
    have e : (fgl Ch X).F a = MvPowerSeries.map X.ιF (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
      rw [map_subst hs_twoVars]
      show subst (twoVars X.C _) (MvPowerSeries.map X.ιF (Ch.ch.B.G.F a)) = _
      congr 1
      funext q
      simp [twoVars]
    rw [e, coeff_map] at h
    exact h
  have key : ∀ Y : ValExt T p, nuFacC Ch Y f k = detDepth (logFGLOf w Ch.ch.B.G hG)
      (fun (a : Fin (rk f)) e => algebraMap T.V T.Fr (Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)) k := by
    intro Y
    rw [nuFacC, detDepth, detDepth, ← detPow_map Y.ιF]
    exact depth_map Y.ιF (hw Y) _ _ (fun _ a => lg_logFGLOf_map Y.ιF _ hG _ a) _ _
  rw [key, key]

end GlobalTheory.DepthField
