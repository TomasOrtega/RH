import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBertiniPolyDiscrepancySncBoundaryStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocalStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeneralMember

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Conclude with `⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩`.
-/
theorem regAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `h`. Conclude with `⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩`.
-/
theorem unitAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : UnitAt (q y) f) : UnitAt y (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]`. Conclude with `bot_le`. Consider the case `succ r ih => rw [succ_nsmul]`. Conclude with `(CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)`.
-/
theorem supp_nsmul_le (D : CartierDiv X) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

/- English proof (translation)
Use `CartierDiv.mem_sections.2 fun y => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `A.exists_isEqn (q y)`. Establish `h1` using `hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))`. Use `⟨fnPull q g, isEqn_pullCart q hg, ?_⟩` and prove the remaining obligations. Use `regAt_functionFieldMap q y h1` as an intermediate fact.

Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis.
-/
theorem functionFieldMap_mem_sections (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X}
    {f : X.functionField} (h : f ∈ A.sections) : functionFieldMap q f ∈ (pullCart q A).sections := by
  refine CartierDiv.mem_sections.2 fun y => ?_
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  have h1 := hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := regAt_functionFieldMap q y h1
  rwa [map_mul] at this

/- English proof (translation)
Take `⟨g, hg⟩` from `A.exists_isEqn (q y)`. Use `⟨fnPull q g, isEqn_pullCart q hg, ?_⟩` and prove the remaining obligations. Use `unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)` as an intermediate fact. Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis.
-/
theorem generatesAt_pullCart (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X} {y : Y}
    {f : X.functionField} (h : A.GeneratesAt (q y) f) :
    (pullCart q A).GeneratesAt y (functionFieldMap q f) := by
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)
  rwa [map_mul] at this

variable [IsLocallyNoetherian X]

/- English proof (translation)
Use `⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, hgV⟩` from `hg.exists_nhds`. Take `⟨g₁, hg₁⟩` from `G.exists_isEqn z`. Take `⟨d, hd⟩` from `D₀.exists_isEqn z`. Establish `h3` using `((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)`.

Rewrite `h3` using `[← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow]`. Establish `h4` using `hG.eqn z g₁ hg₁ z specializes_rfl E hE`. Establish `hd'` using `hd.mult_eq`. Rewrite `hd'` using `[← hE.ord_eq]`. Establish `h1 : (m' : ℚ) ≠ 0` using `by exact_mod_cast hm'.ne'`.

Establish `h2 : (e : ℚ) ≠ 0` using `by exact_mod_cast he.ne'`. Rewrite using `[Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]`. Use `push_cast`. Rewrite using `[← h4]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isLogMult_add {p : X ⟶ Sp ℂ} {n : ℕ} {Δ : X → ℚ} {η : RatForms p n} {m m' b e : ℕ}
    {G D₀ : CartierDiv X} {a : ℚ} (hG : IsLogMult p n Δ η m G) (hm' : 0 < m') (he : 0 < e)
    (hab : a = b / e) :
    IsLogMult p n (Δ + a • qWeil D₀ m') η (m * (e * m')) ((e * m') • G + m • (b • D₀)) := by
  refine ⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨g₁, hg₁⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow] at h3
  have h4 := hG.eqn z g₁ hg₁ z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h2 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory.GeneralMember

open GlobalTheory.GeneralMember in

/- English proof (translation)
Introduce `hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs`. Take `⟨η, hη⟩` from `hG.exists_isLogMult hm`. Take `⟨m', D₀, hm', -, rfl⟩` from `hD`. Take `⟨Y, hY, π, hπ, K, B, hres, hB⟩` from `GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top`. Use `haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj`.

Use `haveI := hres.smooth`. Use `haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1`. Use `haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1`. Use `haveI : IsProper π := IsProper.of_comp π p`. Take `⟨Q, hQ0, hQ⟩` from `GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)`.

Use `⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩` and prove the remaining obligations. Use `set b : ℕ := a.num.toNat with hb`. Use `set e : ℕ := a.den with he`. Establish `hepos : 0 < e` using `a.den_pos`. Establish `hab : a = b / e`.

Establish `h0 : (0 : ℤ) ≤ a.num` using `Rat.num_nonneg.2 ha`. Establish `h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h0]`. Rewrite using `[hb, he, h1]`. Conclude with `(Rat.num_div_den a).symm`.

Use `set m'' := m * (e * m') with hm''`. Use `set G' := (e * m') • G + m • (b • D₀) with hG'`. Establish `hm''pos : 0 < m''` using `Nat.mul_pos hm (Nat.mul_pos hepos hm')`. Establish `hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G'` using `isLogMult_add hη hm' hepos hab`. Establish `hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀`.

Establish `hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D` using `fun r D => map_nsmul (pullCartHom π) r D`. Rewrite using `[hG', pullCart_add, hn1, hn1, hn1, hm'']`. Use `module`. Establish `hsupp : (pullCart π G' - m'' • K).supp ≤ B`. Rewrite using `[hΘ]`.

Use `(CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp) ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))` and prove the remaining obligations. Establish `hres' : IsLogRes p n η m'' G' π K B` using `{ hres with supp := hsupp }`. Take `⟨g'', hg''⟩` from `G'.exists_isEqn y`. Establish `hL` using `hmult.eqn y g'' hg''`. Take `⟨ya, hya⟩` from `A.exists_isEqn y`.

Establish `hH : (CartierDiv.principal t + A).IsEqn y (t * ya)` using `(CartierDiv.isEqn_principal t y).add hya`. Establish `hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ)`. Introduce `z hz E hE`. Take `⟨V, hV, hHV⟩` from `hH.exists_nhds`. Rewrite using `[qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]`.

Take `⟨m₂, g₂, hm₂, hL₂, hdisc⟩` from `isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m') (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz`. Rewrite using `[hL₂.kltAt_iff hn hη.ne_zero hm₂]`. Introduce `E hE`. Rewrite using `[hdisc]`. Take `⟨E', hE'⟩` from `GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E`.

Take `⟨y', rfl, hy'⟩` from `GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE`. Establish `hη' : EtaleKlt.ratPull p π n η ≠ 0` using `fun h => hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))`. Establish `hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m''` using `fun w hw => ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w (hw.map π.continuous)`. Establish `hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'')`. Rewrite using `[sub_add_cancel]`.

Conclude with `isEqn_pullCart π hg''`. Establish `ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) = ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i)`. Express the relevant statement in the definitionally equal form `functionFieldMap π (t : X.functionField) = _`. Rewrite using `[ht, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]`. Establish `hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya))`. Rewrite using `[map_mul]`. Conclude with `(CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)`. Establish `key` using `hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η) K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos hsupp hc hΘm hΘe hH' E' hy'`.

Establish `e1` using `GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero`. Establish `e2` using `GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''`. Establish `e3` using `GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)`. Simplify using `only [discrep, e1, e2, e3] at key`. Simplify `key` using `[discrep]`.
-/
theorem GlobalTheory.PairStep.kltAt_add_general_member : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  intro hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  obtain ⟨m', D₀, hm', -, rfl⟩ := hD
  obtain ⟨Y, hY, π, hπ, K, B, hres, hB⟩ :=
    GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top
  haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj
  haveI := hres.smooth
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper π := IsProper.of_comp π p
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι
    (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)
  refine ⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩

  set b : ℕ := a.num.toNat with hb
  set e : ℕ := a.den with he
  have hepos : 0 < e := a.den_pos
  have hab : a = b / e := by
    have h0 : (0 : ℤ) ≤ a.num := Rat.num_nonneg.2 ha
    have h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hb, he, h1]
    exact (Rat.num_div_den a).symm
  set m'' := m * (e * m') with hm''
  set G' := (e * m') • G + m • (b • D₀) with hG'
  have hm''pos : 0 < m'' := Nat.mul_pos hm (Nat.mul_pos hepos hm')
  have hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G' := isLogMult_add hη hm' hepos hab

  have hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀ := by
    have hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D :=
      fun r D => map_nsmul (pullCartHom π) r D
    rw [hG', pullCart_add, hn1, hn1, hn1, hm'']
    module
  have hsupp : (pullCart π G' - m'' • K).supp ≤ B := by
    rw [hΘ]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp)
      ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))
  have hres' : IsLogRes p n η m'' G' π K B := { hres with supp := hsupp }

  obtain ⟨g'', hg''⟩ := G'.exists_isEqn y
  have hL := hmult.eqn y g'' hg''
  obtain ⟨ya, hya⟩ := A.exists_isEqn y
  have hH : (CartierDiv.principal t + A).IsEqn y (t * ya) := (CartierDiv.isEqn_principal t y).add hya
  have hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    obtain ⟨V, hV, hHV⟩ := hH.exists_nhds
    rw [qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, hL₂, hdisc⟩ := isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m')
    (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz
  rw [hL₂.kltAt_iff hn hη.ne_zero hm₂]
  intro E hE
  rw [hdisc]

  obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E
  obtain ⟨y', rfl, hy'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE
  have hη' : EtaleKlt.ratPull p π n η ≠ 0 := fun h =>
    hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))
  have hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m'' := fun w hw =>
    ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w
      (hw.map π.continuous)
  have hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'') := by
    rw [sub_add_cancel]; exact isEqn_pullCart π hg''
  have ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) =
      ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i) := by
    change functionFieldMap π (t : X.functionField) = _
    rw [ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]
  have hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya)) := by
    rw [map_mul]; exact (CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)
  have key := hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η)
    K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos
    hsupp hc hΘm hΘe hH' E' hy'
  have e1 := GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero
  have e2 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''
  have e3 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)
  simp only [discrep, e1, e2, e3] at key
  simpa [discrep] using key
