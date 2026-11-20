import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypePlacesCover

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E

/- English proof (translation)
Introduce `x y hxy`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Establish `: cO y = x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, hxy]`.

Use `show IsCMField.complexConj D.host.E (D.host.conj (x : D.host.E)) = _`. Establish `h : D.host.conj (x : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E)` using `D.host.φ₀.injective (by`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`. Rewrite using `[h]`. Conclude with `IsCMField.complexConj_apply_apply D.host.E _`.

Rewrite using `[this]`.
-/
theorem isConjPl_conjPlE (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : cO y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
    show IsCMField.complexConj D.host.E (D.host.conj (x : D.host.E)) = _
    have h : D.host.conj (x : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) :=
      D.host.φ₀.injective (by
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
    rw [h]; exact IsCMField.complexConj_apply_apply D.host.E _
  rw [this]

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]`.
-/
theorem conjPlE_conjPlE (P : PlE D.host) : GlobalTheory.SplitConjPlace.conjPlE (GlobalTheory.SplitConjPlace.conjPlE P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_algebraMap]`.
-/
theorem comap_conjPlE (P : PlE D.host) :
    (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_algebraMap]

/- English proof (translation)
Establish `h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord` using `D.host.finrank_cmField`. Establish `h5 : D.R.f = 2 * D.R.ord` using `rfl`. Rewrite using `[h1, h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

/- English proof (translation)
Set `T : Set (PlE D.host)` to `{u | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal}`. Establish `hg : ∀ v, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal` using `fun v => D.naut.plGw_over k v`. Set `f : D.nd.PlG k ⊕ D.nd.PlG k → T` to `Sum.elim (fun v => ⟨D.naut.plGw k v, hg v⟩) fun v => ⟨GlobalTheory.SplitConjPlace.conjPlE (D.naut.plGw k v), by show _ ∈ (GlobalTheory.SplitConjPlace.conjPlE _).asIdeal`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]`. Conclude with `hg v⟩`.

Establish `hne : ∀ a b, D.naut.plGw k a ≠ GlobalTheory.SplitConjPlace.conjPlE (D.naut.plGw k b)` using `fun a b e => D.naut.plGw_nconj k b a (e ▸ isConjPl_conjPlE _)`. Establish `hinj : Function.Injective f`. Apply the tactic sequence `rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e`. Conclude with `congrArg Sum.inl (D.naut.plGw_inj k e')`. Conclude with `absurd e' (hne a b)`.

Conclude with `absurd e'.symm (hne b a)`. Use `congrArg GlobalTheory.SplitConjPlace.conjPlE e'` as an intermediate fact. Simplify using `only [f, Sum.elim_inr, conjPlE_conjPlE] at this`. Conclude with `congrArg Sum.inr (D.naut.plGw_inj k this)`. Establish `hT : T.ncard = 2 * D.R.f`.

Rewrite using `[← finrank_E D]`. Conclude with `D.nd.g_split k`. Establish `hc : Nat.card T = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k)`. Rewrite using `[Nat.card_coe_set_eq, hT, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]`. Use `haveI : Finite T := by`.

Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[Nat.card_coe_set_eq, hT]`. Establish `: 0 < D.R.f` using `by show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩`.

Break down `x with v | v` into its components or cases. Conclude with `⟨v, Or.inl (congrArg Subtype.val hx).symm⟩`. Conclude with `⟨v, Or.inr (congrArg Subtype.val hx).symm⟩`.
-/
theorem cover (k : Fin 2) (w : PlE D.host) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = GlobalTheory.SplitConjPlace.conjPlE (D.naut.plGw k v) := by
  let T : Set (PlE D.host) := {u | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal}
  have hg : ∀ v, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := fun v => D.naut.plGw_over k v
  let f : D.nd.PlG k ⊕ D.nd.PlG k → T :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, hg v⟩) fun v => ⟨GlobalTheory.SplitConjPlace.conjPlE (D.naut.plGw k v), by
      show _ ∈ (GlobalTheory.SplitConjPlace.conjPlE _).asIdeal
      rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]; exact hg v⟩
  have hne : ∀ a b, D.naut.plGw k a ≠ GlobalTheory.SplitConjPlace.conjPlE (D.naut.plGw k b) := fun a b e =>
    D.naut.plGw_nconj k b a (e ▸ isConjPl_conjPlE _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · exact congrArg Sum.inl (D.naut.plGw_inj k e')
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg GlobalTheory.SplitConjPlace.conjPlE e'
      simp only [f, Sum.elim_inr, conjPlE_conjPlE] at this
      exact congrArg Sum.inr (D.naut.plGw_inj k this)
  have hT : T.ncard = 2 * D.R.f := by
    rw [← finrank_E D]; exact D.nd.g_split k
  have hc : Nat.card T = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, hT, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite T := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, hT]
    have : 0 < D.R.f := by show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos
    omega
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · exact ⟨v, Or.inr (congrArg Subtype.val hx).symm⟩

open GlobalTheory.LevCmp in

/- English proof (translation)
Use `⟨fun k v => ⟨D.naut.plGw_over k v, GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `u ⟨w, hwu, k, hwk⟩`. Take `⟨v, hv⟩` from `cover k w hwk`. Take `⟨s, hs⟩` from `GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩`. Use `⟨k, v, s, HeightOneSpectrum.ext ?_, hs⟩` and prove the remaining obligations.

Establish `hu : u.asIdeal = (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))`. Rewrite using `[← hwu]`. Break down `hv with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Conclude with `comap_conjPlE _`.

Rewrite using `[hu, ← s.w_under, hs]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[← Fintype.card_pos_iff, D.nd.card_PlG 0]`. Use `show 0 < 2 * D.R.ord`. Conclude with `Nat.mul_pos two_pos D.R.ord_pos`.
-/
theorem gPlaces (D : D7) : GPlaces D := by
  refine ⟨fun k v => ⟨D.naut.plGw_over k v, GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩⟩, ?_, ?_⟩
  · rintro u ⟨w, hwu, k, hwk⟩
    obtain ⟨v, hv⟩ := cover k w hwk
    obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
    refine ⟨k, v, s, HeightOneSpectrum.ext ?_, hs⟩
    have hu : u.asIdeal = (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [← hwu]
      rcases hv with rfl | rfl
      · rfl
      · exact comap_conjPlE _
    rw [hu, ← s.w_under, hs]
  · refine ⟨0, ?_⟩
    rw [← Fintype.card_pos_iff, D.nd.card_PlG 0]
    show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos

end GlobalTheory.TypePlacesCover

open GlobalTheory.TypePlacesCover in

/- English proof (translation)
Introduce `_` and use `StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ => gPlaces (Dof x)`.
-/
theorem GlobalTheory.TypePlacesCover.gPlaces_all : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => LA hL x → GPlaces (Dof x) :=
  fun _ => StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ => gPlaces (Dof x)

end
