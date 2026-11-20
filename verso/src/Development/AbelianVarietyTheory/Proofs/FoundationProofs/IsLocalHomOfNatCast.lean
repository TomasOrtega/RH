import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SameCharacterCommonExtension

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TwistedSelmerCompare

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ K a ρ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).1 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ L a _ h)), fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ L a _ ((GlobalTh …`.
-/
theorem isSSRep_map_iff {Γ K L : Type} [Group Γ] [Field K] [Field L] [CharZero K] [CharZero L] (f : K →+* L)
    {a : ℕ} (ρ : Γ →* GL (Fin a) K) : IsSSRep (mapRep f ρ) ↔ IsSSRep ρ :=
  ⟨fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ K a ρ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).1 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ L a _ h)),
    fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ L a _ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).2 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ K a ρ h))⟩

section Param

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

/- English proof (translation)
Establish `hd` using `A.locG_dim χ w`. Establish `hp' : A.unr (A.locG (A.tw p.π χ) w)` using `by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ`. Establish `he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c)`. Rewrite using `[A.locG_tw]`. Conclude with `A.frobEig_char _ _ c hp hχ hd hc`.

Unfold `spehLoc`. Simplify using `only`. Generalize the expression as in `(List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l`. Proceed by induction on `l with`. Consider the case `nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩`.

Consider the case `cons k l ih`. Take `⟨i1, i2, i3⟩` from `ih`. Simplify using `only [List.foldr_cons]`. Use `⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3, A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]`.

Use `congr 2`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem speh_twist (p : Part A.CG) (χ : A.CG 1) (w : PlE H) (c : ℂ) (hp : A.unr (A.locG p.π w))
    (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (spehLoc N A p w) ∧ A.unr (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) ∧
      A.frobEig (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) = (A.frobEig (spehLoc N A p w)).map (· * c) := by
  have hd := A.locG_dim χ w
  have hp' : A.unr (A.locG (A.tw p.π χ) w) := by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ
  have he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c) := by
    rw [A.locG_tw]; exact A.frobEig_char _ _ c hp hχ hd hc
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3,
      A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    funext x
    simp only [Function.comp_apply]
    ring

/- English proof (translation)
Proceed by induction on `S with`. Consider the case `nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩`. Consider the case `cons p S ih`. Take `⟨i1, i2, i3⟩` from `ih fun q hq => hS q (List.mem_cons_of_mem _ hq)`. Take `⟨j1, j2, j3⟩` from `speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc`.

Express the relevant statement in the definitionally equal form `A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧ A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧ A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) = (A.frobEig (A.lpSum (spehLoc N A p w) (is …`. Use `⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add]`.
-/
theorem iso_twist (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) (c : ℂ)
    (hS : ∀ p ∈ S, A.unr (A.locG p.π w)) (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (isoLoc N A S w) ∧ A.unr (isoLoc N A (twistIso N A S χ) w) ∧
      A.frobEig (isoLoc N A (twistIso N A S χ) w) = (A.frobEig (isoLoc N A S w)).map (· * c) := by
  induction S with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩
  | cons p S ih =>
    obtain ⟨i1, i2, i3⟩ := ih fun q hq => hS q (List.mem_cons_of_mem _ hq)
    obtain ⟨j1, j2, j3⟩ := speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc
    change A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧
      A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧
      A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) =
        (A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A S w))).map (· * c)
    refine ⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add]

/- English proof (translation)
Establish `h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w)` using `(Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π`. Use `filter_upwards [h] with w hw`. Establish `hχ` using `(A.etaTinv_def w).1`. Establish `hd` using `A.locG_dim A.etaTinv w`. Take `⟨c, hc⟩` from `Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)`.

Take `⟨i1, i2, i3⟩` from `iso_twist N A S _ w c hw hχ hc`. Unfold `galPol`. Rewrite using `[A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]`.
-/
theorem galPol_twist (S : List (Part A.CG)) (t : ℝ) : ∀ᶠ w in Filter.cofinite,
    galPol A (A.lpTw (A.lpChar (isoLoc N A S w) (A.locG A.etaTinv w)) t) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A S A.etaTinv) w) t) := by
  have h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w) :=
    (Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π
  filter_upwards [h] with w hw
  have hχ := (A.etaTinv_def w).1
  have hd := A.locG_dim A.etaTinv w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)
  obtain ⟨i1, i2, i3⟩ := iso_twist N A S _ w c hw hχ hc
  unfold galPol
  rw [A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]

/- English proof (translation)
Establish `h1 : (placesOver H.E (N.l a)).Finite`. Establish `h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0`. Simplify using `using (N.lPrime a).out.ne_zero`. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Simplify `hv` using `[Ideal.dvd_span_singleton, placesOver]`.

Use `filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem, (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3`. Conclude with `⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩`.
-/
theorem splitOut_ae (a : N.Loc) : ∀ᶠ w in Filter.cofinite, (SplitOut N a w ↔ IsSplitPl H w) := by
  have h1 : (placesOver H.E (N.l a)).Finite := by
    have h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (N.lPrime a).out.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    simpa [Ideal.dvd_span_singleton, placesOver] using hv
  filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem,
    (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3
  exact ⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩

end Param

variable (D : D7)

/- English proof (translation)
Use `and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))` and prove the remaining obligations. Establish `: CharZero (FractionRing (D.nd.O a))` using `((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance`. Establish `: CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a)))` using `((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance`. Rewrite using `[← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]`. Establish `: mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) = mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s))`.

Use extensionality with `g i j`. Conclude with `(fracMap_alg _ (twO_inj D.ntw a) _).symm`. Rewrite using `[this]`. Use `Filter.eventually_congr ?_ filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2` and prove the remaining obligations. Rewrite using `[h2]`.

Use `forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ => forall_congr' fun _ => ?_` and prove the remaining obligations. Rewrite using `[← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]`. Both sides reduce to the same expression.
-/
theorem triple_iff (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG))
    (h : HasParamW D.nd D.naut a σ Sg) (s : TwistedTriples.Trip D a) : TwistedTriples.IsTripleOf D a σ s ↔ IsTriple D a s Sg := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    rw [← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]
    have : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    rw [this]
  · refine Filter.eventually_congr ?_
    filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2
    rw [h2]
    refine forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]
    rfl

def RowsHaveParam : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), TwistedTriples.IsGoodRow D a σ → ∃ Sg, HasParamW D.nd D.naut a σ Sg

/- English proof (translation)
Introduce `a σ Sg hg hp` and use `(h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs`.
-/
theorem allTriples_of_tripAll (h : TwistedTriples.TripAll D) : AllTriples D := fun a σ Sg hg hp =>
  (h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs

def LatticeIso : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a → ∀ s, Attached D a π s →
    ∀ ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoPt D a π (ρ π) →
      ∃ P : GL (Fin D.R.r) (D.nd.O a), ∀ g,
        WpO D.nd a ρ π g * (P : Matrix _ _ _) =
          (P : Matrix _ _ _) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g

def ClosedAt (𝒞 : FamClass) (P : D7 → Prop) : Prop :=
  Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (Fm.D x i)

/- English proof (translation)
Take `⟨e, he, h⟩` from `h`. Use `⟨e, he, fun eps h1 h2 => (h eps h1 h2).imp fun K hK Fm CH c1 c2 => ?_⟩` and prove the remaining obligations. Conclude with `(hK Fm CH c1 c2).imp fun x0 hx x h i => hPQ _ (hx x h i)`.
-/
theorem ClosedAt.mono {𝒞 : FamClass} {P Q : D7 → Prop} (h : ClosedAt 𝒞 P) (hPQ : ∀ D, P D → Q D) :
    ClosedAt 𝒞 Q := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, fun eps h1 h2 => (h eps h1 h2).imp fun K hK Fm CH c1 c2 => ?_⟩
  exact (hK Fm CH c1 c2).imp fun x0 hx x h i => hPQ _ (hx x h i)

/- English proof (translation)
Take `⟨e, he, h⟩` from `Closed.and hP hQ`. Use `⟨e, he, fun eps h1 h2 => (h eps h1 h2).imp fun K hK Fm CH c1 c2 => ?_⟩` and prove the remaining obligations. Take `⟨⟨x1, a1⟩, x2, a2⟩` from `hK Fm CH c1 c2`. Conclude with `⟨max x1 x2, fun x hx i => ⟨a1 x (le_of_max_le_left hx) i, a2 x (le_of_max_le_right hx) i⟩⟩`.
-/
theorem ClosedAt.and {𝒞 : FamClass} {P Q : D7 → Prop} (hP : ClosedAt 𝒞 P) (hQ : ClosedAt 𝒞 Q) :
    ClosedAt 𝒞 fun D => P D ∧ Q D := by
  obtain ⟨e, he, h⟩ := Closed.and hP hQ
  refine ⟨e, he, fun eps h1 h2 => (h eps h1 h2).imp fun K hK Fm CH c1 c2 => ?_⟩
  obtain ⟨⟨x1, a1⟩, x2, a2⟩ := hK Fm CH c1 c2
  exact ⟨max x1 x2, fun x hx i => ⟨a1 x (le_of_max_le_left hx) i, a2 x (le_of_max_le_right hx) i⟩⟩

end GlobalTheory.TwistedSelmerCompare

end
