import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeCptTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem labelEmb_inl_rt (c : Coeff l) (τ : CMType H) : ((labelEmb c (.inl τ) H.rt : c.F) : ℂ) = H.rt0 := τ.2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem imaginary_root_conj (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · exact h
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem labelEmb_inr_rt (c : Coeff l) (τ : CMType H) : ((labelEmb c (.inr τ) H.rt : c.F) : ℂ) = -H.rt0 := by
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = _
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, τ.2, imaginary_root_conj]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem rootIdx_bijective (D : Datum H) : Function.Bijective (HodgeCpt.rootIdx D) := by
  constructor
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    unfold HodgeCpt.rootIdx at h
    have hi := i.2
    have hi' := i'.2
    by_cases a : (i : ℕ) < D.p <;> by_cases b : (i' : ℕ) < D.p <;> simp only [a, b, dif_pos, dif_neg, not_false_eq_true] at h
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl := Sum.inl.inj h1
      have := congrArg Fin.val (eq_of_heq h2)
      exact Prod.ext rfl (Fin.ext this)
    · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
    · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl := Sum.inr.inj h1
      have := congrArg Fin.val (eq_of_heq h2)
      simp only at this
      exact Prod.ext rfl (Fin.ext (by show (i : ℕ) = i'; omega))
  · rintro ⟨τ | τ, k⟩
    · have hk : (k : ℕ) < D.p := k.2
      refine ⟨(τ, ⟨k, by omega⟩), ?_⟩
      unfold HodgeCpt.rootIdx
      rw [dif_pos hk]
    · have hk : (k : ℕ) < D.q := k.2
      refine ⟨(τ, ⟨D.p + D.q - 1 - k, by omega⟩), ?_⟩
      unfold HodgeCpt.rootIdx
      rw [dif_neg (by show ¬ (D.p + D.q - 1 - k < D.p); omega)]
      congr 1
      exact Fin.ext (by show D.p + D.q - 1 - (D.p + D.q - 1 - k) = k; omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem rootIdx_first_omega (D : Datum H) (τ : CMType H) (hq : 0 < D.q) :
    HodgeCpt.rootIdx D (τ, ⟨D.p, by omega⟩) = ⟨.inr τ, ⟨D.q - 1, by show _ < D.q; omega⟩⟩ ∧
      HodgeCpt.rootSgn D (τ, ⟨D.p, by omega⟩) = -1 := by
  constructor
  · unfold HodgeCpt.rootIdx
    rw [dif_neg (by simp)]
    congr 1
    exact Fin.ext (by show D.p + D.q - 1 - D.p = D.q - 1; omega)
  · simp [HodgeCpt.rootSgn]

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem V_isVB (s) : (𝔐.V s).IsVB (labelRk D s) (𝔐.Vgen s) := 𝔐.vb s

include 𝔐 in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem charZero : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).mp inferInstance

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem finrank_Vgen (s) : Module.finrank Ω (𝔐.Vgen s) = labelRk D s := by
  obtain ⟨U, hU, b, hb, hfr⟩ := V_isVB 𝔐 s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  rw [← hb, finrank_span_eq_card (hfr _ trivial hU).1, Fintype.card_fin]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem V_eq_dR (s) (q : Cpt 𝔐.ξ) (h : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) : 𝔐.V s q = 𝔐.dR s q := by
  unfold HodgeCpt.V Lat.patch
  rw [if_neg (by rintro ⟨p, hp, hq⟩; exact h p hp hq)]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem flagStep_top {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} (b : Fin r → F) :
    flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem span_span_regAt {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (q : Cpt ξ) {F : Type} [AddCommGroup F]
    [Module Ω F] (s : Set F) :
    Submodule.span Ω (Submodule.span (regAt ξ q) s : Set F) = Submodule.span Ω s :=
  Submodule.span_span_of_tower _ _ _

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem flag_span (Fl : 𝔐.Flag) (s) : Submodule.span Ω (Set.range (Fl.b s)) = 𝔐.Vgen s := by
  obtain ⟨U, hU, b, hb, hfr⟩ := V_isVB 𝔐 s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  obtain ⟨U', hU', b', hb', hfr'⟩ := Fl.sub s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  have h1 := (hfr _ trivial hU).2
  have h2 := (hfr' _ trivial hU').2
  have h3 := congrArg (fun N : Submodule (regAt 𝔐.ξ ⟨genPt 𝔐.ξ, specializes_rfl⟩) 𝔐.Li =>
    Submodule.span Ω (N : Set 𝔐.Li)) (h2.symm.trans h1)
  have h4 := (span_span_regAt _ _).symm.trans (h3.trans (span_span_regAt _ _))
  rw [← flagStep_top, ← hb', flagStep_top, ← hb, h4]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem flag_deg_pos (Fl : 𝔐.Flag) : 0 < Fl.deg := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := Fl.generic
  exact h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem rootLat_gen {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (r) (q : Cpt 𝔐.ξ) (t : Ω)
    (ht : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt q t) :
    (Fl.rootLat r).IsGenAt q (t ^ HodgeCpt.rootSgn D r) := by
  refine ⟨zpow_ne_zero _ ht.1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    have h := hs ()
    have e : Submodule.span (regAt 𝔐.ξ q) {s ()} = Submodule.span (regAt 𝔐.ξ q) {t} := h.2.symm.trans ht.2
    have a1 : s () ∈ Submodule.span (regAt 𝔐.ξ q) {t} := e ▸ Submodule.mem_span_singleton_self _
    have a2 : t ∈ Submodule.span (regAt 𝔐.ξ q) {s ()} := e ▸ Submodule.mem_span_singleton_self _
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp a1
    obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.mp a2
    simp only [Finset.univ_unique, Finset.prod_singleton, SetLike.mem_coe]
    refine Submodule.mem_span_singleton.mpr ?_
    unfold HodgeCpt.rootSgn
    split_ifs
    · exact ⟨u, by simpa using hu⟩
    · refine ⟨v, ?_⟩
      have hv' : (v : Ω) * s () = t := hv
      have h0 := h.1
      have h1 := ht.1
      show (v : Ω) * t ^ (-1 : ℤ) = s () ^ (-1 : ℤ)
      rw [zpow_neg_one, zpow_neg_one, ← hv']
      have : (v : Ω) ≠ 0 := by rintro hv0; rw [hv0, zero_mul] at hv'; exact h1 hv'.symm
      field_simp
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨fun _ => t, fun _ => ht, by simp⟩

end GlobalTheory.CompanionTheory.Ar.HodgeCptTest
