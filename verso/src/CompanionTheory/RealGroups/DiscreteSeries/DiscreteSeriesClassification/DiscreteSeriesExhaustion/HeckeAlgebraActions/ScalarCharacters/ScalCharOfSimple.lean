import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)

variable {n : ℕ}

/- English proof (translation)
Establish `hker : ∀ a b, ∀ x ∈ LinearMap.ker N, X.E a b x ∈ LinearMap.ker N`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← Module.End.mul_apply, ← (hc a b).eq, Module.End.mul_apply, hx, map_zero]`. Break down `hS.2 (LinearMap.ker N) hker with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hinj : Function.Injective N` using `LinearMap.ker_eq_bot.1 h`. Establish `hinjk : Function.Injective ⇑(N ^ k)`. Rewrite using `[Module.End.coe_pow]`. Conclude with `hinj.iterate k`.

Take `⟨x, y, hxy⟩` from `hS.1.exists_pair_ne`. Apply `hxy` to reduce the goal to its premises. Apply `hinjk` to reduce the goal to its premises. Simplify using `[hk]`. Conclude with `LinearMap.ker_eq_top.1 h`.
-/
private theorem eq_zero_of_pow_eq_zero_of_commute_of_isSimple {X : GMod n} (hS : IsSimple X) (N : Module.End ℂ X.V)
    (hc : ∀ a b, Commute (X.E a b) N) (k : ℕ) (hk : N ^ k = 0) : N = 0 := by
  have hker : ∀ a b, ∀ x ∈ LinearMap.ker N, X.E a b x ∈ LinearMap.ker N := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, ← (hc a b).eq, Module.End.mul_apply, hx, map_zero]
  rcases hS.2 (LinearMap.ker N) hker with h | h
  · exfalso
    have hinj : Function.Injective N := LinearMap.ker_eq_bot.1 h
    have hinjk : Function.Injective ⇑(N ^ k) := by
      rw [Module.End.coe_pow]
      exact hinj.iterate k
    obtain ⟨x, y, hxy⟩ := hS.1.exists_pair_ne
    apply hxy
    apply hinjk
    simp [hk]
  · exact LinearMap.ker_eq_top.1 h

/- English proof (translation)
Unfold `CompanionTheory.RgExh.ScalChar`. Take `⟨k, hk⟩` from `hH`. Introduce `Y`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_pow_eq_zero_of_commute_of_isSimple hS _ (fun a b => ?_) k (hk Y)` and prove the remaining obligations.

Establish `hc : Commute (X.E a b) (Formalism.REAL.qdet X.E (Y + ((n : ℂ) - 1) / 2))`. Rewrite using `[hQ n X.V X.E (Y + ((n : ℂ) - 1) / 2)]`. Conclude with `ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliC_central X.E X.gl _ a b`. Conclude with `hc.sub_right ((Commute.one_right _).smul_right _)`.
-/
theorem scalChar_of_simple (hQ : QdetEq) {X : GMod n} {χ : Fin n → ℂ} (hS : IsSimple X) (hH : HasChar X χ) :
    ScalChar X χ := by
  unfold CompanionTheory.RgExh.ScalChar
  obtain ⟨k, hk⟩ := hH
  intro Y
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_eq_zero_of_commute_of_isSimple hS _ (fun a b => ?_) k (hk Y)
  have hc : Commute (X.E a b) (Formalism.REAL.qdet X.E (Y + ((n : ℂ) - 1) / 2)) := by
    rw [hQ n X.V X.E (Y + ((n : ℂ) - 1) / 2)]
    exact ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliC_central X.E X.gl _ a b
  exact hc.sub_right ((Commute.one_right _).smul_right _)

/- English proof (translation)
Establish `h` using `hV n X χ s hH hN hf`. Use `show Nontrivial ↥(stepSub X (χ s))`. Conclude with `(Submodule.nontrivial_iff_ne_bot).2 h`.
-/
theorem nontrivial_step (hV : NonVan) {X : GMod n} {χ : Fin n → ℂ} {s : Fin n} (hH : HasChar X χ)
    (hN : Nontrivial X.V) (hf : ∀ r, χ r ≠ χ s + 1) : Nontrivial (step X (χ s)).V := by
  have h := hV n X χ s hH hN hf
  show Nontrivial ↥(stepSub X (χ s))
  exact (Submodule.nontrivial_iff_ne_bot).2 h

/- English proof (translation)
Introduce `ss`. Proceed by induction on `ss with`. Consider the case `nil`. Introduce `X χ _ _ _ hS`. Express the relevant statement in the definitionally equal form `ScalChar X χ at hS`.

Use `⟨hS, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `True`. Discharge the goal by the elementary cases of `trivial`. Consider the case `cons s ss ih`. Introduce `X χ hG hH hN hS`.

Express the relevant statement in the definitionally equal form `(∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG`. Express the relevant statement in the definitionally equal form `ScalChar (path (step X (χ s)) (χ + Pi.single s 1) ss) (pathEnd (χ + Pi.single s 1) ss) at hS`. Take `⟨hf, hG'⟩` from `hG`. Establish `hH'` using `hC n X χ s hH`. Establish `hN'` using `nontrivial_step hV hH hN hf`.

Take `⟨hS1, hSP⟩` from `ih (step X (χ s)) (χ + Pi.single s 1) hG' hH' hN' hS`. Take `⟨hSX, hom⟩` from `hB n X χ s hH hf hS1`. Use `⟨hSX, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss`. Use `⟨?_, hSP⟩` and prove the remaining obligations.

Introduce `r hrs heq`. Take `⟨f, hf1, hf2⟩` from `hNS n X χ s hSX hN hf ⟨r, hrs, heq⟩`. Conclude with `hf2 (hom f hf1)`.
-/
theorem backPath (hC : StepChar) (hV : NonVan) (hNS : NonScal) (hB : Back) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → HasChar X χ → Nontrivial X.V →
      ScalChar (path X χ ss) (pathEnd χ ss) → ScalChar X χ ∧ SimplePath χ ss := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ _ hS
    change ScalChar X χ at hS
    refine ⟨hS, ?_⟩
    change True
    trivial
  | cons s ss ih =>
    intro X χ hG hH hN hS
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change ScalChar (path (step X (χ s)) (χ + Pi.single s 1) ss) (pathEnd (χ + Pi.single s 1) ss) at hS
    obtain ⟨hf, hG'⟩ := hG
    have hH' := hC n X χ s hH
    have hN' := nontrivial_step hV hH hN hf
    obtain ⟨hS1, hSP⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hH' hN' hS
    obtain ⟨hSX, hom⟩ := hB n X χ s hH hf hS1
    refine ⟨hSX, ?_⟩
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss
    refine ⟨?_, hSP⟩
    intro r hrs heq
    obtain ⟨f, hf1, hf2⟩ := hNS n X χ s hSX hN hf ⟨r, hrs, heq⟩
    exact hf2 (hom f hf1)

/- English proof (translation)
Introduce `ss`. Proceed by induction on `ss with`. Consider the case `nil`. Introduce `X χ _ _ hS _`. Use `⟨?_, fun X' _ _ hI => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `IsSimple X`. Conclude with `hS`. Express the relevant statement in the definitionally equal form `Iso X X' at hI`. Conclude with `hI`. Consider the case `cons s ss ih`.

Introduce `X χ hG hSP hS hH`. Express the relevant statement in the definitionally equal form `(∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG`. Express the relevant statement in the definitionally equal form `(∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss at hSP`. Take `⟨hf, hG'⟩` from `hG`. Take `⟨hd, hSP'⟩` from `hSP`.

Establish `hSc` using `scalChar_of_simple hQ hS hH`. Establish `hS1 : IsSimple (step X (χ s))` using `hF n X χ s hS hSc hf hd (hOS n X χ s hSc hd)`. Establish `hH1` using `hC n X χ s hH`. Take `⟨hP, hRefl⟩` from `ih (step X (χ s)) (χ + Pi.single s 1) hG' hSP' hS1 hH1`. Use `⟨?_, fun X' hS' hH' hI => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `IsSimple (path (step X (χ s)) (χ + Pi.single s 1) ss)`. Conclude with `hP`. Express the relevant statement in the definitionally equal form `Iso (path (step X (χ s)) (χ + Pi.single s 1) ss) (path (step X' (χ s)) (χ + Pi.single s 1) ss) at hI`. Establish `hSc'` using `scalChar_of_simple hQ hS' hH'`. Establish `hS1' : IsSimple (step X' (χ s))` using `hF n X' χ s hS' hSc' hf hd (hOS n X' χ s hSc' hd)`.

Establish `hI1` using `hRefl (step X' (χ s)) hS1' (hC n X' χ s hH') hI`. Conclude with `hR n X X' χ s hSc hSc' hf hd hI1`.
-/
theorem fwdPath (hQ : QdetEq) (hC : StepChar) (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → SimplePath χ ss → IsSimple X →
      HasChar X χ → IsSimple (path X χ ss) ∧
        ∀ X' : GMod n, IsSimple X' → HasChar X' χ → Iso (path X χ ss) (path X' χ ss) → Iso X X' := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ hS _
    refine ⟨?_, fun X' _ _ hI => ?_⟩
    · change IsSimple X
      exact hS
    · change Iso X X' at hI
      exact hI
  | cons s ss ih =>
    intro X χ hG hSP hS hH
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss at hSP
    obtain ⟨hf, hG'⟩ := hG
    obtain ⟨hd, hSP'⟩ := hSP
    have hSc := scalChar_of_simple hQ hS hH
    have hS1 : IsSimple (step X (χ s)) := hF n X χ s hS hSc hf hd (hOS n X χ s hSc hd)
    have hH1 := hC n X χ s hH
    obtain ⟨hP, hRefl⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hSP' hS1 hH1
    refine ⟨?_, fun X' hS' hH' hI => ?_⟩
    · change IsSimple (path (step X (χ s)) (χ + Pi.single s 1) ss)
      exact hP
    · change Iso (path (step X (χ s)) (χ + Pi.single s 1) ss) (path (step X' (χ s)) (χ + Pi.single s 1) ss) at hI
      have hSc' := scalChar_of_simple hQ hS' hH'
      have hS1' : IsSimple (step X' (χ s)) := hF n X' χ s hS' hSc' hf hd (hOS n X' χ s hSc' hd)
      have hI1 := hRefl (step X' (χ s)) hS1' (hC n X' χ s hH') hI
      exact hR n X X' χ s hSc hSc' hf hd hI1

/- English proof (translation)
Unfold `CompanionTheory.RgExh.Hecke`. Introduce `m X χ ss hG hS hH hSc`. Establish `hb` using `backPath hC hV hNS hB ss X χ hG hH hS.1 hSc`. Establish `hf` using `fwdPath hQ hC hOS hF hR ss X χ hG hb.2 hS hH`. Conclude with `⟨hb.2, hf.1, hf.2⟩`.
-/
theorem hecke_of' (hQ : QdetEq) (hC : StepChar) (_hCH : CayleyHam) (hV : NonVan) (hNS : NonScal) (hB : Back)
    (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) : Hecke := by
  unfold CompanionTheory.RgExh.Hecke
  intro m X χ ss hG hS hH hSc
  have hb := backPath hC hV hNS hB ss X χ hG hH hS.1 hSc
  have hf := fwdPath hQ hC hOS hF hR ss X χ hG hb.2 hS hH
  exact ⟨hb.2, hf.1, hf.2⟩

end CompanionTheory.RgExh.Hk
