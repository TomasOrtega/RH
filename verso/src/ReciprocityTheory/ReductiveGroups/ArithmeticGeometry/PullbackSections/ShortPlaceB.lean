import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AdaptAt {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ k : ℕ, ((k : 𝓞 K) ∉ la.asIdeal) ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧
    Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La

def ShortFreeNSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (Λ : GenLat D.host.E n) (N N' : ℕ) (x0 : Fin n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F)
    (f : T.toTop.R j),
    Λ.Unimod → Λ.TrivAt (badN D) → P ∈ harmL T.Q.c Λ a → Λ.LevOK N (T.dδ j n).l₂.M → Λ.LevOK N' (T.dδ j n).l₂.M →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N' x0 P f

def ShortRepSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j w.n).pd} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      ∃ (u : T.Q.c.F) (g' : T.toTop.R j), u ≠ 0 ∧ vLa la u = 0 ∧ g = u • g' ∧
        ∃ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La)
          (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
          g' ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ j w.n).l₂.M ∧
          Λ.LevOK N (T.dδ j w.n).l₂.M ∧ AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 ∧ P ∈ harmL T.Q.c Λ (wtA w) ∧
          AdaptAt Λ la ∧ ((N : 𝓞 T.Q.c.F) ∉ la.asIdeal) ∧ IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g'

def PdOffRamD (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ),
    Nat.Coprime (T.dδ j n).pd (2 * D.host.q * D.host.d)

def ShortValChartSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ (w : WeightFamilies.Wt D j)
    (g : T.toTop.R j)
    (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M →
    Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((N : 𝓞 T.Q.c.F) ∉ la.asIdeal) → AdaptAt Λ la →
      ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), OverLa la T'.V (iT.comp io) e' ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)),
        (letI := io.toAlgebra
         letI := (iT.comp io).toAlgebra
         ∃ φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1) ∧
      ∃ (io₂ : (T.dδ j w.n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j w.n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂), yI₂.IsAlg ∧
        (letI := (iT.comp io).toAlgebra
         letI := io₂.toAlgebra
         FrOver (T.dδ j w.n) yI₂.1 yI'.1) ∧
      ∃ (C : IntegralChartA3 (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂ yI₂) (ι : Type) (_ : Fintype ι) (cf : ι → T'.Fr)
        (P' : MvPolynomial (LtN (T.Q.Dw j) w.n) T'.Fr) (gm : ι → Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)) (k : ℕ),
        P' ∈ FFV (Dw := T.Q.Dw j) T' (wtA w) w.n ∧ (∀ i b, IsIntPS T' (gm i b)) ∧ (∀ i, 0 ≤ nval T'.V e' (cf i)) ∧
        letI := io₂.toAlgebra
        nval T'.V e' (∑ i, cf i * ∑ mo ∈ P'.support, P'.coeff mo *
          ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 k (gm i b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)) ≤
          nval Tc.V e (evI yI g)

def ChartValueIntegralAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw j) l') (c' : Coeff l') (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr)
      (io' : c'.F →+* Tc.Fr), (∀ (a : c'.F) (b : T.Q.c.F), (a : ℂ) = b → io' a = io b) →
    ∀ (yI : IntFr Xo' c' Tc io') (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ (C : IntegralChartA3 Xo' c' Tc io' yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io'.toAlgebra
        0 ≤ nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
          ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

def ChartValueRamifiedAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw j) l') (c' : Coeff l') (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr)
      (io' : c'.F →+* Tc.Fr), (∀ (a : c'.F) (b : T.Q.c.F), (a : ℂ) = b → io' a = io b) →
    ∀ (yI : IntFr Xo' c' Tc io') (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 Xo' c' Tc io' yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io'.toAlgebra
        (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
          nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
            ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

/- English proof (translation)
Introduce `D T h j hj inst hs Tc io`. Conclude with `hG D T h j hj hs _ _ _ Tc io io (fun a b hab => congrArg io (Subtype.ext hab))`.
-/
theorem chartValueIntegral_of_anyLevel (hG : ChartValueIntegralAnyLevel) : ChartValueIntegralGood := by
  intro D T h j hj inst hs Tc io
  exact hG D T h j hj hs _ _ _ Tc io io (fun a b hab => congrArg io (Subtype.ext hab))

/- English proof (translation)
Introduce `D T h j hj inst hs Tc io`. Conclude with `hG D T h j hj hs _ _ _ Tc io io (fun a b hab => congrArg io (Subtype.ext hab))`.
-/
theorem chartValueRamified_of_anyLevel (hG : ChartValueRamifiedAnyLevel) : ChartValueBoundRamified := by
  intro D T h j hj inst hs Tc io
  exact hG D T h j hj hs _ _ _ Tc io io (fun a b hab => congrArg io (Subtype.ext hab))

section Ultra

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

/- English proof (translation)
Unfold `nval at h ⊢`. Use `split_ifs with hs`. Conclude with `le_top`. Establish `hne : s.Nonempty`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[Finset.not_nonempty_iff_eq_empty]`. Conclude with `hs (by rw [hn, Finset.sum_empty])`. Take `⟨i, hi, hmax⟩` from `Finset.exists_max_image s (fun i => valV V (f i)) hne`. Establish `hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i)` using `Valuation.map_sum_le _ hmax`. Establish `hfi : f i ≠ 0`.

Introduce `h0`. Rewrite `hle` using `[h0, Valuation.map_zero]`. Conclude with `hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))`. Establish `h1` using `h i hi`. Rewrite `h1` using `[if_neg hfi]`.

Use `h1.trans ?_` and prove the remaining obligations. Establish `hlog` using `(WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle`. Use `EReal.coe_le_coe_iff.2 ?_` and prove the remaining obligations. Establish `hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ)`. Conclude with `neg_le_neg hlog` after adjusting the coercions.

Conclude with `div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)`.
-/
theorem le_nval_sum (e : ℕ) {ι : Type} (s : Finset ι) (f : ι → K') (r : EReal) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  unfold nval at h ⊢
  split_ifs with hs
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      exact hs (by rw [hn, Finset.sum_empty])
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun i => valV V (f i)) hne
    have hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i) := Valuation.map_sum_le _ hmax
    have hfi : f i ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hle
      exact hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))
    have h1 := h i hi
    rw [if_neg hfi] at h1
    refine h1.trans ?_
    have hlog := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle
    refine EReal.coe_le_coe_iff.2 ?_
    have hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ) := by
      exact_mod_cast neg_le_neg hlog
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)

/- English proof (translation)
Use `le_nval_sum e Finset.univ _ r (fun i _ => ?_)` and prove the remaining obligations. Establish `hc'` using `hc i`. Establish `hS'` using `hS i`. Unfold `nval at hc' hS' ⊢`. Distinguish the cases in `h0 : cf i * S i = 0`.

Rewrite using `[if_pos h0]`. Conclude with `le_top`. Rewrite using `[if_neg h0]`. Establish `hcf : cf i ≠ 0` using `left_ne_zero_of_mul h0`. Establish `hSi : S i ≠ 0` using `right_ne_zero_of_mul h0`.

Rewrite `hc'` using `[if_neg hcf]`. Rewrite `hS'` using `[if_neg hSi]`. Use `hS'.trans (EReal.coe_le_coe_iff.2 ?_)` and prove the remaining obligations. Establish `hc''` using `EReal.coe_nonneg.1 hc'`. Establish `h2 : ((vV V (cf i) : ℤ) : ℝ) / (e : ℝ) + ((vV V (S i) : ℤ) : ℝ) / (e : ℝ) = ((vV V (cf i * S i) : ℤ) : ℝ) / (e : ℝ)`.

Unfold `vV`. Rewrite using `[map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hcf) ((Valuation.ne_zero_iff _).2 hSi)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_nval_comb (e : ℕ) {ι : Type} [Fintype ι] (cf S : ι → K') (r : EReal) (hc : ∀ i, 0 ≤ nval V e (cf i))
    (hS : ∀ i, r ≤ nval V e (S i)) : r ≤ nval V e (∑ i, cf i * S i) := by
  classical
  refine le_nval_sum e Finset.univ _ r (fun i _ => ?_)
  have hc' := hc i
  have hS' := hS i
  unfold nval at hc' hS' ⊢
  by_cases h0 : cf i * S i = 0
  · rw [if_pos h0]; exact le_top
  rw [if_neg h0]
  have hcf : cf i ≠ 0 := left_ne_zero_of_mul h0
  have hSi : S i ≠ 0 := right_ne_zero_of_mul h0
  rw [if_neg hcf] at hc'
  rw [if_neg hSi] at hS'
  refine hS'.trans (EReal.coe_le_coe_iff.2 ?_)
  have hc'' := EReal.coe_nonneg.1 hc'
  have h2 : ((vV V (cf i) : ℤ) : ℝ) / (e : ℝ) + ((vV V (S i) : ℤ) : ℝ) / (e : ℝ) =
      ((vV V (cf i * S i) : ℤ) : ℝ) / (e : ℝ) := by
    unfold vV
    rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hcf) ((Valuation.ne_zero_iff _).2 hSi)]
    push_cast
    ring
  rw [← h2]
  linarith

end Ultra

/- English proof (translation)
Use `letI : StarRing (𝓞 D.host.E) := { star := T.Q.H.bar star_involutive := fun a => by`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[T.Q.H.bar_eq, T.Q.H.bar_eq]`. Use `first`. Consider the case `simp`.

Consider the case `exact IsCMField.complexConj_apply_apply _ _`. Use `star_mul := fun a b => by rw [map_mul, mul_comm]`. Use `star_add := fun a b => map_add _ a b }`. Establish `hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a` using `fun a => rfl`. Take `⟨T', iT, e', ho', yI', -, io₂, hio₂, yI₂, hy₂, -, C, ι, hι, cf, P', gm, k, hP', hgm, hcf, hle⟩` from `hV D T hF j hj hs w g Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hN hA`.

Use `le_trans ?_ hle` and prove the remaining obligations. Conclude with `le_nval_comb e' cf _ 0 hcf (fun i => hCI D T.toTop hF.p j hj hs _ _ _ T' (iT.comp io) io₂ hio₂ yI₂ e' la ho' hy₂ hbad C k (wtA w) w.n P' hP' (gm i) (hgm i))`.
-/
theorem shortValInt_of (hV : ShortValChartSt) (hCI : ChartValueIntegralAnyLevel) (D : D7) (T : Full D) (hF : LawsFull T)
    (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F)
    (hsec : g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) (hU : Λ.Unimod) (hTb : Λ.TrivAt (badN D))
    (hTl : Λ.TrivAt (T.dδ j w.n).l₂.M) (hLev : Λ.LevOK N (T.dδ j w.n).l₂.M)
    (hAdm : AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0) (hP : P ∈ harmL T.Q.c Λ (wtA w))
    (hR : IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (ho : OverLa la Tc.V io e) (hy : yI.IsAlg)
    (hbad : ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal))
    (hN : (N : 𝓞 T.Q.c.F) ∉ la.asIdeal) (hA : AdaptAt Λ la) : 0 ≤ nval Tc.V e (evI yI g) := by
  letI : StarRing (𝓞 D.host.E) :=
    { star := T.Q.H.bar
      star_involutive := fun a => by
        apply NumberField.RingOfIntegers.ext
        rw [T.Q.H.bar_eq, T.Q.H.bar_eq]
        first
        | simp
        | exact IsCMField.complexConj_apply_apply _ _
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add _ a b }
  have hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun a => rfl
  obtain ⟨T', iT, e', ho', yI', -, io₂, hio₂, yI₂, hy₂, -, C, ι, hι, cf, P', gm, k, hP', hgm, hcf, hle⟩ :=
    hV D T hF j hj hs w g Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hN hA
  refine le_trans ?_ hle
  exact le_nval_comb e' cf _ 0 hcf (fun i => hCI D T.toTop hF.p j hj hs _ _ _ T' (iT.comp io) io₂ hio₂
    yI₂ e' la ho' hy₂ hbad C k (wtA w) w.n P' hP' (gm i) (hgm i))

/- English proof (translation)
Establish `hv : (0 : ℤ) ≤ vLa la ((p : ℕ) : T.Q.c.F)` using `by clear hV hCR hsec hU hTb hTl hLev hAdm hP hR ho hy hp hpl hN hA`. Unfold `vLa`. Establish `hle : la.valuation T.Q.c.F ((p : ℕ) : T.Q.c.F) ≤ 1`. Simplify using `using la.valuation_le_one (K := T.Q.c.F) ((p : ℕ) : 𝓞 T.Q.c.F)`. Distinguish the cases in `h0 : la.valuation T.Q.c.F ((p : ℕ) : T.Q.c.F) = 0`.

Rewrite using `[h0, WithZero.log_zero]`. Simplify using the standard rewrite rules. Establish `h1` using `(WithZero.log_le_log h0 one_ne_zero).2 hle`. Rewrite `h1` using `[WithZero.log_one]`. Use linear arithmetic over natural numbers and integers.

Use `letI : StarRing (𝓞 D.host.E) := { star := T.Q.H.bar star_involutive := fun a => by`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[T.Q.H.bar_eq, T.Q.H.bar_eq]`. Use `first`. Consider the case `simp`.

Consider the case `exact IsCMField.complexConj_apply_apply _ _`. Use `star_mul := fun a b => by rw [map_mul, mul_comm]`. Use `star_add := fun a b => map_add _ a b }`. Establish `hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a` using `fun a => rfl`. Take `⟨T', iT, e', ho', yI', -, io₂, hio₂, yI₂, hy₂, -, C, ι, hι, cf, P', gm, k, hP', hgm, hcf, hle⟩` from `hV D T hF j hj hs w g Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hN hA`.

Use `le_trans ?_ hle` and prove the remaining obligations. Use `le_trans (EReal.coe_le_coe_iff.2 ?_) (le_nval_comb e' cf _ _ hcf (fun i => hCR D T.toTop hF.p j hj hs _ _ _ T' (iT.comp io) io₂ hio₂ yI₂ e' la ho' hy₂ p hp hpl C k (wtA w) w.n P' hP' (gm i) (hgm i)))` and prove the remaining obligations. Establish `h1` using `DF_wtA_le T.toTop j w`. Establish `h2` using `differentExponent_nonneg D p`. Establish `h3 : (0 : ℝ) ≤ ((vLa la ((p : ℕ) : T.Q.c.F) : ℤ) : ℝ)` using `by exact_mod_cast hv`.

Establish `h4 : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (WeightAlgebra.DF w : ℝ)` using `by exact_mod_cast h1`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 (mul_nonneg h3 h2)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem shortValRam_of (hV : ShortValChartSt) (hCR : ChartValueRamifiedAnyLevel) (D : D7) (T : Full D) (hF : LawsFull T)
    (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F)
    (hsec : g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) (hU : Λ.Unimod) (hTb : Λ.TrivAt (badN D))
    (hTl : Λ.TrivAt (T.dδ j w.n).l₂.M) (hLev : Λ.LevOK N (T.dδ j w.n).l₂.M)
    (hAdm : AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0) (hP : P ∈ harmL T.Q.c Λ (wtA w))
    (hR : IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (ho : OverLa la Tc.V io e) (hy : yI.IsAlg) (p : ℕ)
    (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal)
    (hN : (N : 𝓞 T.Q.c.F) ∉ la.asIdeal) (hA : AdaptAt Λ la) :
    (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) / 2)) : ℝ) : EReal) ≤
      nval Tc.V e (evI yI g) := by
  have hv : (0 : ℤ) ≤ vLa la ((p : ℕ) : T.Q.c.F) := by
    clear hV hCR hsec hU hTb hTl hLev hAdm hP hR ho hy hp hpl hN hA
    unfold vLa
    have hle : la.valuation T.Q.c.F ((p : ℕ) : T.Q.c.F) ≤ 1 := by
      simpa using la.valuation_le_one (K := T.Q.c.F) ((p : ℕ) : 𝓞 T.Q.c.F)
    by_cases h0 : la.valuation T.Q.c.F ((p : ℕ) : T.Q.c.F) = 0
    · rw [h0, WithZero.log_zero]; simp
    · have h1 := (WithZero.log_le_log h0 one_ne_zero).2 hle
      rw [WithZero.log_one] at h1
      omega
  letI : StarRing (𝓞 D.host.E) :=
    { star := T.Q.H.bar
      star_involutive := fun a => by
        apply NumberField.RingOfIntegers.ext
        rw [T.Q.H.bar_eq, T.Q.H.bar_eq]
        first
        | simp
        | exact IsCMField.complexConj_apply_apply _ _
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add _ a b }
  have hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun a => rfl
  obtain ⟨T', iT, e', ho', yI', -, io₂, hio₂, yI₂, hy₂, -, C, ι, hι, cf, P', gm, k, hP', hgm, hcf, hle⟩ :=
    hV D T hF j hj hs w g Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hN hA
  refine le_trans ?_ hle
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (le_nval_comb e' cf _ _ hcf (fun i => hCR D T.toTop hF.p j hj hs _ _ _
    T' (iT.comp io) io₂ hio₂ yI₂ e' la ho' hy₂ p hp hpl C k (wtA w) w.n P' hP' (gm i) (hgm i)))
  have h1 := DF_wtA_le T.toTop j w
  have h2 := differentExponent_nonneg D p
  have h3 : (0 : ℝ) ≤ ((vLa la ((p : ℕ) : T.Q.c.F) : ℤ) : ℝ) := by exact_mod_cast hv
  have h4 : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := by exact_mod_cast h1
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg h3 h2)
  linarith

/- English proof (translation)
Take `⟨k, hk, hk1, hk2⟩` from `hTb`. Establish `hp2qd : p ∣ 2 * D.host.q * D.host.d`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hp`. Break down `hp with rfl | rfl | rfl` into its components or cases. Conclude with `dvd_mul_of_dvd_left (dvd_mul_right _ _) _`.

Conclude with `dvd_mul_of_dvd_left (dvd_mul_left _ _) _`. Conclude with `dvd_mul_left _ _`. Establish `hpb : p ∣ badN D`. Unfold `badN`. Conclude with `dvd_mul_of_dvd_left (hp2qd.trans (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right D.host.two_dvd_QS _) _)) _`.

Establish `h2b : 2 ∣ badN D`. Unfold `badN`. Conclude with `dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left D.host.two_dvd_QS _) _) _`. Establish `hkl : (k : 𝓞 T.Q.c.F) ∉ la.asIdeal` using `fun h => Pf.not_both_mem la (Nat.Coprime.coprime_dvd_right hpb hk) h hpl`. Establish `hM2 : (T.dδ j n).l₂.M = T.Q.l.M * (T.dδ j n).pd` using `(hF.sh.dLev j hj n).2.1`.

Establish `hMl : ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal` using `M_not_mem_of_ram D T.toTop hF.p la p hp hpl`. Establish `hpdl : (((T.dδ j n).pd : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal` using `fun h => Pf.not_both_mem la (Nat.Coprime.coprime_dvd_right hp2qd (hOff T hF j hj n)) h hpl`. Use `⟨(T.dδ j n).l₂.M * k, ⟨?_, dvd_mul_right _ _, ?_⟩, ?_, ⟨k, hkl, hk1, hk2⟩⟩` and prove the remaining obligations. Conclude with `(hLev.1.of_dvd_nat hLev.2.1).mul (Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right h2b hk))`. Use `show _ ≤ Λ.La ⊓ stdLat D.host.E n`.

Use `le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right` and prove the remaining obligations. Use `Ideal.span_singleton_le_span_singleton.2 ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_mul]`. Conclude with `dvd_mul_left _ _`. Introduce `h`.

Rewrite `h` using `[hM2, Nat.cast_mul, Nat.cast_mul]`. Break down `la.isPrime.mem_or_mem h with h | h` into its components or cases. Break down `la.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hMl h`. Conclude with `hpdl h`.

Conclude with `hkl h`.
-/
theorem levOK_adapt {D : D7} (hOff : PdOffRamD D) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ}
    (Λ : GenLat D.host.E n) (N : ℕ) (hTb : Λ.TrivAt (badN D)) (hLev : Λ.LevOK N (T.dδ j n).l₂.M)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ))
    (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal) :
    ∃ N' : ℕ, Λ.LevOK N' (T.dδ j n).l₂.M ∧ ((N' : 𝓞 T.Q.c.F) ∉ la.asIdeal) ∧ AdaptAt Λ la := by
  obtain ⟨k, hk, hk1, hk2⟩ := hTb
  have hp2qd : p ∣ 2 * D.host.q * D.host.d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · exact dvd_mul_left _ _
  have hpb : p ∣ badN D := by
    unfold badN
    exact dvd_mul_of_dvd_left (hp2qd.trans (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right D.host.two_dvd_QS _) _)) _
  have h2b : 2 ∣ badN D := by
    unfold badN
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left D.host.two_dvd_QS _) _) _
  have hkl : (k : 𝓞 T.Q.c.F) ∉ la.asIdeal := fun h =>
    Pf.not_both_mem la (Nat.Coprime.coprime_dvd_right hpb hk) h hpl
  have hM2 : (T.dδ j n).l₂.M = T.Q.l.M * (T.dδ j n).pd := (hF.sh.dLev j hj n).2.1
  have hMl : ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := M_not_mem_of_ram D T.toTop hF.p la p hp hpl
  have hpdl : (((T.dδ j n).pd : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := fun h =>
    Pf.not_both_mem la (Nat.Coprime.coprime_dvd_right hp2qd (hOff T hF j hj n)) h hpl
  refine ⟨(T.dδ j n).l₂.M * k, ⟨?_, dvd_mul_right _ _, ?_⟩, ?_, ⟨k, hkl, hk1, hk2⟩⟩
  · exact (hLev.1.of_dvd_nat hLev.2.1).mul (Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right h2b hk))
  · show _ ≤ Λ.La ⊓ stdLat D.host.E n
    refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
    refine Ideal.span_singleton_le_span_singleton.2 ?_
    rw [Nat.cast_mul]
    exact dvd_mul_left _ _
  · intro h
    rw [hM2, Nat.cast_mul, Nat.cast_mul] at h
    rcases la.isPrime.mem_or_mem h with h | h
    · rcases la.isPrime.mem_or_mem h with h | h
      · exact hMl h
      · exact hpdl h
    · exact hkl h

/- English proof (translation)
Take `⟨hsec, Λ, N, x0, P, hU, hTb, hTl, hLev, hAdm, hP, hR⟩` from `hg`. Take `⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩` from `y.2`. Establish `hv : vAtV y g = nval Tc.V e (evI yI g)` using `by show y.1.1 g = _`. Rewrite using `[hq]`. Both sides reduce to the same expression.

Rewrite using `[hv]`. Take `⟨N', hLev', hN', hA⟩` from `levOK_adapt hOff T hF j hj Λ N hTb hLev la p hp hpl`. Conclude with `shortValRam_of hV hCR D T hF j hj w g Λ N' x0 P hsec hU hTb hTl hLev' hAdm hP (hN D T hF j hj w.n (wtA w) Λ N N' x0 P g hU hTb hP hLev hLev' hR) Tc io yI e la ho hy p hp hpl hN' hA`.
-/
theorem shortPlaceRam_of (hN : ShortFreeNSt) (hV : ShortValChartSt) (hCR : ChartValueRamifiedAnyLevel)
    (D : D7) (hOff : PdOffRamD D) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j)
    (hg : g ∈ T.toTop.sh j w) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ)
    (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal) :
    (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g := by
  obtain ⟨hsec, Λ, N, x0, P, hU, hTb, hTl, hLev, hAdm, hP, hR⟩ := hg
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv : vAtV y g = nval Tc.V e (evI yI g) := by
    show y.1.1 g = _
    rw [hq]
    rfl
  rw [hv]
  obtain ⟨N', hLev', hN', hA⟩ := levOK_adapt hOff T hF j hj Λ N hTb hLev la p hp hpl
  exact shortValRam_of hV hCR D T hF j hj w g Λ N' x0 P hsec hU hTb hTl hLev' hAdm hP
    (hN D T hF j hj w.n (wtA w) Λ N N' x0 P g hU hTb hP hLev hLev' hR) Tc io yI e la ho hy p hp hpl hN' hA

def ShortSeriesRamifiedPlaceTwoAt (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceBqdAt (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ),
      p ∈ ({D.host.q, D.host.d} : Finset ℕ) → ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `exact ⟨fun h D => h D, fun h D => h D⟩`. Consider the case `exact ⟨fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla, fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla⟩`.
-/
theorem shortSeriesRamifiedPlaceTwo_iff_forall : ShortSeriesRamifiedPlaceTwo ↔ ∀ D, ShortSeriesRamifiedPlaceTwoAt D := by
  first
    | exact Iff.rfl
    | exact ⟨fun h D => h D, fun h D => h D⟩
    | exact ⟨fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla,
        fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla⟩

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `exact ⟨fun h D => h D, fun h D => h D⟩`. Consider the case `exact ⟨fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla, fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla⟩`.
-/
theorem shortPlaceBqdSt_iff : ShortPlaceBqdSt ↔ ∀ D, ShortPlaceBqdAt D := by
  first
    | exact Iff.rfl
    | exact ⟨fun h D => h D, fun h D => h D⟩
    | exact ⟨fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla,
        fun h D T hF j hj w g hg la y hla => h D T hF j hj w g hg la y hla⟩

/- English proof (translation)
Introduce `T hF j hj w g hg la y hla`. Establish `h` using `shortPlaceRam_of hN hV hCR D hOff T hF j hj w g hg la y 2 (by simp) hla`. Unfold `vdP at h`. Rewrite `h` using `[if_pos rfl]`. Conclude with `h`.
-/
theorem shortSeriesRamifiedPlaceTwo_of_charts (hN : ShortFreeNSt) (hV : ShortValChartSt) (hCR : ChartValueRamifiedAnyLevel) {D : D7}
    (hOff : PdOffRamD D) : ShortSeriesRamifiedPlaceTwoAt D := by
  intro T hF j hj w g hg la y hla
  have h := shortPlaceRam_of hN hV hCR D hOff T hF j hj w g hg la y 2 (by simp) hla
  unfold vdP at h
  rw [if_pos rfl] at h
  exact h

/- English proof (translation)
Introduce `T hF j hj w g hg la y p hp hpl`. Establish `hp' : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢`. The claim follows by propositional logic. Establish `h` using `shortPlaceRam_of hN hV hCR D hOff T hF j hj w g hg la y p hp' hpl`.

Unfold `vdP at h`. Establish `hp2 : p ≠ 2`. Introduce `h2`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hp`. Establish `hQ : 2 ∣ D.host.QS` using `(dvd_pow_self 2 (by omega)).trans D.host.tower_dvd`.

Establish `h2dvd : 2 ∣ D.host.q * D.host.d`. Break down `hp with h | h` into its components or cases. Rewrite using `[← h, h2]`. Conclude with `dvd_mul_right 2 _`. Rewrite using `[← h, h2]`.

Conclude with `dvd_mul_left 2 _`. Establish `hc` using `Nat.Coprime.coprime_dvd_left hQ D.host.QS_coprime`. Use `Nat.Coprime.eq_one_of_dvd hc h2dvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[if_neg hp2]`.

Conclude with `h`.
-/
theorem shortPlaceBqd_at (hN : ShortFreeNSt) (hV : ShortValChartSt) (hCR : ChartValueRamifiedAnyLevel) {D : D7}
    (hOff : PdOffRamD D) : ShortPlaceBqdAt D := by
  intro T hF j hj w g hg la y p hp hpl
  have hp' : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    tauto
  have h := shortPlaceRam_of hN hV hCR D hOff T hF j hj w g hg la y p hp' hpl
  unfold vdP at h
  have hp2 : p ≠ 2 := by
    intro h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have hQ : 2 ∣ D.host.QS := (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd
    have h2dvd : 2 ∣ D.host.q * D.host.d := by
      rcases hp with h | h
      · rw [← h, h2]; exact dvd_mul_right 2 _
      · rw [← h, h2]; exact dvd_mul_left 2 _
    have hc := Nat.Coprime.coprime_dvd_left hQ D.host.QS_coprime
    have := Nat.Coprime.eq_one_of_dvd hc h2dvd
    omega
  rw [if_neg hp2] at h
  exact h

/- English proof (translation)
Introduce `D T hF j hj w g hg la y hbad`. Take `⟨u, g', hu, hvu, rfl, Λ, N, x0, P, hsec, hU, hTb, hTl, hLev, hAdm, hP, hA, hN, hR⟩` from `hRep D T hF j hj w g hg la hbad`. Take `⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩` from `y.2`. Establish `hv : vAtV y (u • g') = nval Tc.V e (evI yI (u • g'))` using `by show y.1.1 (u • g') = _`. Rewrite using `[hq]`.

Both sides reduce to the same expression. Rewrite using `[hv, evI_smul, nval_smul ho hu, hvu]`. Simplify using `only [Int.cast_zero, EReal.coe_zero, zero_add]`. Establish `hbad3 : ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)`. Introduce `p hp`.

Apply `hbad p` to reduce the goal to its premises. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢`. The claim follows by propositional logic. Conclude with `shortValInt_of hV hCI D T hF j hj w g' Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hbad3 hN hA`.
-/
theorem shortPlaceA_of (hRep : ShortRepSt) (hV : ShortValChartSt) (hCI : ChartValueIntegralAnyLevel) : ShortPlaceASt := by
  intro D T hF j hj w g hg la y hbad
  obtain ⟨u, g', hu, hvu, rfl, Λ, N, x0, P, hsec, hU, hTb, hTl, hLev, hAdm, hP, hA, hN, hR⟩ :=
    hRep D T hF j hj w g hg la hbad
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv : vAtV y (u • g') = nval Tc.V e (evI yI (u • g')) := by
    show y.1.1 (u • g') = _
    rw [hq]
    rfl
  rw [hv, evI_smul, nval_smul ho hu, hvu]
  simp only [Int.cast_zero, EReal.coe_zero, zero_add]
  have hbad3 : ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ),
      ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal) := by
    intro p hp
    apply hbad p
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    tauto
  exact shortValInt_of hV hCI D T hF j hj w g' Λ N x0 P hsec hU hTb hTl hLev hAdm hP hR Tc io yI e la ho hy hbad3 hN hA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
