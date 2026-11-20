import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalarStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SphericalOperatorsExist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CAllFin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

/- English proof (translation)
Simplify using `[opOf]`.
-/
theorem opOf_zero (t : UA E a →₀ ℂ) : opOf (RU E a) t (0 : UA E a → ℂ) = 0 := by simp [opOf]

/- English proof (translation)
Take `⟨t, ht, hact⟩` from `GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw Kw hc ho f z act`. Set `e : Submodule ℂ (UA E a → ℂ) → ℂ` to `fun U => if h : IsAutRepU U then z (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U h w hw).1.choose else 0`. Establish `he : ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) t φ = e U • φ` using `fun U hU φ hφ hx => by`. Simplify using `only [e, dif_pos hU]`. Conclude with `hact U hU _ (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1.choose_spec φ hφ hx`.

Use `⟨t, e, ht, he, ?_⟩` and prove the remaining obligations. Introduce and unpack `U hU ⟨φ, hφ, h0, hx⟩ σ hσ`. Conclude with `smul_left_injective ℂ h0 ((he U hU φ hφ hx).symm.trans (hact U hU σ hσ φ hφ hx))`.
-/
theorem exists_op {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (Kw : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (ho : IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E)))) (hc : IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))))
    (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ)
    (act : ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) :
    ∃ (t : UA E a →₀ ℂ) (e : Submodule ℂ (UA E a → ℂ) → ℂ), (∀ g ∈ t.support, g ∈ locU a w ∧ t g = f (cLoc w g)) ∧
      (∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) t φ = e U • φ) ∧
      ∀ U, IsAutRepU U → (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → e U = z σ := by
  classical
  obtain ⟨t, ht, hact⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw Kw hc ho f z act
  let e : Submodule ℂ (UA E a → ℂ) → ℂ := fun U =>
    if h : IsAutRepU U then z (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U h w hw).1.choose else 0
  have he : ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) →
      opOf (RU E a) t φ = e U • φ := fun U hU φ hφ hx => by
    simp only [e, dif_pos hU]
    exact hact U hU _ (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1.choose_spec φ hφ hx
  refine ⟨t, e, ht, he, ?_⟩
  rintro U hU ⟨φ, hφ, h0, hx⟩ σ hσ
  exact smul_left_injective ℂ h0 ((he U hU φ hφ hx).symm.trans (hact U hU σ hσ φ hφ hx))

/- English proof (translation)
Take `⟨φ, hφ, h0, hx⟩` from `h`. Establish `e : (locU a w ⊓ Kw.comap (cLoc w)).map (cLoc w) = Kw`. Use `le_antisymm ?_ fun g hg => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx.2`.

Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL E a w hw`. Establish `h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g` using `by rw [← he, e.apply_symm_apply]`. Conclude with `⟨(e.symm g).1, ⟨(e.symm g).2, show cLoc w _ ∈ Kw from h1.symm ▸ hg⟩, h1⟩`. Rewrite using `[← e]`. Conclude with `GlobalTheory.Cong.AdaptLev.fixed_ne_bot_of_fix hU hw σ hσ inf_le_left hφ h0 fun x hx' => hx x hx'.1 hx'.2`.
-/
theorem fixed_ne_bot {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {Kw : Subgroup (GL (Fin a) (w.adicCompletion E))}
    (h : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hσ : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) : GlobalTheory.PRep.fixed σ.ρ Kw ≠ ⊥ := by
  obtain ⟨φ, hφ, h0, hx⟩ := h
  have e : (locU a w ⊓ Kw.comap (cLoc w)).map (cLoc w) = Kw := by
    refine le_antisymm ?_ fun g hg => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
      have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
      exact ⟨(e.symm g).1, ⟨(e.symm g).2, show cLoc w _ ∈ Kw from h1.symm ▸ hg⟩, h1⟩
  rw [← e]
  exact GlobalTheory.Cong.AdaptLev.fixed_ne_bot_of_fix hU hw σ hσ inf_le_left hφ h0 fun x hx' => hx x hx'.1 hx'.2

/- English proof (translation)
Take `⟨σ, hσ⟩` from `(GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1`. Take `⟨B, hB⟩` from `(UpperTheory.Cb.spherical_operators_exist E w a).1 σ (fixed_ne_bot hU hw h σ hσ)`. Conclude with `⟨B, σ, hσ, hB⟩`.
-/
theorem exists_satU {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (h : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → RU E a x φ = φ) : ∃ B, SatU U w B := by
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1
  obtain ⟨B, hB⟩ := (UpperTheory.Cb.spherical_operators_exist E w a).1 σ (fixed_ne_bot hU hw h σ hσ)
  exact ⟨B, σ, hσ, hB⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `UpperTheory.Cb.spherical_operators_exist E w a`. Take `⟨f, -, hf⟩` from `h2 n`. Take `⟨ho, hc⟩` from `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a`. Set `z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ` to `fun σ => if h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (· ^ n)).sum else 0`. Establish `hz : ∀ σ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → z σ = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum` using `fun σ B hB => by`.

Establish `h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B` using `⟨B, hB⟩`. Simplify using `only [z, dif_pos h]`. Rewrite using `[GlobalTheory.LFun.HasSatGL.unique h.choose_spec hB]`. Take `⟨t, ht, hact⟩` from `GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw _ hc ho f z fun σ v hv => by`. Distinguish the cases in `h0 : v = 0`.

Simplify using `[h0, opOf]`. Take `⟨B, hB⟩` from `h1 σ ((Submodule.ne_bot_iff _).2 ⟨v, hv, h0⟩)`. Rewrite using `[hz σ B hB]`. Conclude with `hf σ B hB v hv`. Use `⟨t, fun g hg => (ht g hg).1, fun U hU φ hφ hx => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : φ = 0`. Rewrite using `[h0, opOf_zero, smul_zero]`. Establish `h` using `exists_satU hU hw ⟨φ, hφ, h0, hx⟩`. Take `⟨σ, hσ, hB⟩` from `h.choose_spec`. Rewrite using `[PowSatU, dif_pos h, ← hz σ _ hB]`.

Conclude with `hact U hU σ hσ φ hφ hx`.
-/
theorem exists_powOp {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (n : ℤ) :
    ∃ t : UA E a →₀ ℂ, (∀ g ∈ t.support, g ∈ locU a w) ∧ ∀ U, IsAutRepU U → ∀ φ ∈ U,
      (∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → RU E a x φ = φ) → opOf (RU E a) t φ = PowSatU U w n • φ := by
  classical
  obtain ⟨h1, h2⟩ := UpperTheory.Cb.spherical_operators_exist E w a
  obtain ⟨f, -, hf⟩ := h2 n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  let z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ := fun σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (· ^ n)).sum else 0
  have hz : ∀ σ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → z σ = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum := fun σ B hB => by
    have h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B := ⟨B, hB⟩
    simp only [z, dif_pos h]
    rw [GlobalTheory.LFun.HasSatGL.unique h.choose_spec hB]
  obtain ⟨t, ht, hact⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw _ hc ho f z fun σ v hv => by
    by_cases h0 : v = 0
    · simp [h0, opOf]
    · obtain ⟨B, hB⟩ := h1 σ ((Submodule.ne_bot_iff _).2 ⟨v, hv, h0⟩)
      rw [hz σ B hB]
      exact hf σ B hB v hv
  refine ⟨t, fun g hg => (ht g hg).1, fun U hU φ hφ hx => ?_⟩
  by_cases h0 : φ = 0
  · rw [h0, opOf_zero, smul_zero]
  · have h := exists_satU hU hw ⟨φ, hφ, h0, hx⟩
    obtain ⟨σ, hσ, hB⟩ := h.choose_spec
    rw [PowSatU, dif_pos h, ← hz σ _ hB]
    exact hact U hU σ hσ φ hφ hx

open UpperTheory.Gal.Gen in

/- English proof (translation)
Establish `hX` using `satEx_holds`. Take `⟨p, hp, hpe, -⟩` from `symEx_holds a Φ`. Take `⟨C, hC⟩` from `globOp_holds E a K w hw hK`. Take `⟨f, hloc, -, -, hact⟩` from `hC p hp`. Take `⟨η, hη⟩ : ∃ η : Submodule ℂ (UA E a → ℂ) → ℂ, ∀ U (h : ∃ z, SatAt U w z), η U = evalAt h.choose p` from `⟨fun U => if h : ∃ z, SatAt U w z then evalAt h.choose p else 0, fun U h => dif_pos h⟩`.

Use `⟨f, η, hloc, fun U hU => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `φ hφ hfix`. Distinguish the cases in `h0 : φ = 0`. Substitute `h0` using the available equality. Simplify using `[opOf]`.

Establish `hz` using `hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩`. Rewrite using `[hη U hz]`. Conclude with `hact U hU _ hz.choose_spec φ hφ hfix`. Introduce and unpack `⟨φ, hφ, h0, hfix⟩`. Establish `hz` using `hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩`.

Establish `key : ∀ z, SatAt U w z → evalAt z p = η U`. Introduce `z hzz`. Establish `h1` using `hact U hU z hzz φ hφ hfix`. Establish `h2` using `hact U hU _ hz.choose_spec φ hφ hfix`. Rewrite using `[hη U hz]`.

Conclude with `smul_left_injective ℂ h0 (h1.symm.trans h2)`. Prove the components needed by the constructor for the conclusion. Introduce `hne z hzz`. Rewrite `hne` using `[← key z hzz, hpe z]`. Simplify using `using Finset.prod_ne_zero_iff.1 hne 1 (Finset.mem_univ _)`.

Introduce `hgen`. Take `⟨z, hzz⟩` from `hz`. Rewrite using `[← key z hzz, hpe z]`. Use `Finset.prod_ne_zero_iff.2 fun σ _ => ?_` and prove the remaining obligations. Establish `hs : SatAt U w (z ∘ σ)`.

Take `⟨τ, h1, h2⟩` from `hzz`. Use `⟨τ, h1, ?_⟩` and prove the remaining obligations. Establish `hm : Finset.univ.val.map (z ∘ σ) = Finset.univ.val.map z`. Rewrite using `[← Multiset.map_map, Multiset.map_univ_val_equiv]`. Rewrite using `[hm]`.

Conclude with `h2`. Conclude with `hgen _ hs`.
-/
theorem exists_testOp (K : Subgroup (UA E a)) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (hK : HypAt K w)
    (Φ : MvPolynomial (Fin a) ℂ) : ∃ (f : UA E a →₀ ℂ) (η : Submodule ℂ (UA E a → ℂ) → ℂ),
      (∀ g ∈ f.support, g ∈ locU a w) ∧ ∀ U, IsAutRepU U →
        (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) f φ = η U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (η U ≠ 0 ↔ UpperTheory.Gal.Gen.GenAt w Φ U)) := by
  have hX := satEx_holds
  obtain ⟨p, hp, hpe, -⟩ := symEx_holds a Φ
  obtain ⟨C, hC⟩ := globOp_holds E a K w hw hK
  obtain ⟨f, hloc, -, -, hact⟩ := hC p hp
  classical
  obtain ⟨η, hη⟩ : ∃ η : Submodule ℂ (UA E a → ℂ) → ℂ,
      ∀ U (h : ∃ z, SatAt U w z), η U = evalAt h.choose p :=
    ⟨fun U => if h : ∃ z, SatAt U w z then evalAt h.choose p else 0, fun U h => dif_pos h⟩
  refine ⟨f, η, hloc, fun U hU => ⟨?_, ?_⟩⟩
  · intro φ hφ hfix
    by_cases h0 : φ = 0
    · subst h0
      simp [opOf]
    · have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
      rw [hη U hz]
      exact hact U hU _ hz.choose_spec φ hφ hfix
  · rintro ⟨φ, hφ, h0, hfix⟩
    have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
    have key : ∀ z, SatAt U w z → evalAt z p = η U := by
      intro z hzz
      have h1 := hact U hU z hzz φ hφ hfix
      have h2 := hact U hU _ hz.choose_spec φ hφ hfix
      rw [hη U hz]
      exact smul_left_injective ℂ h0 (h1.symm.trans h2)
    constructor
    · intro hne z hzz
      rw [← key z hzz, hpe z] at hne
      simpa using Finset.prod_ne_zero_iff.1 hne 1 (Finset.mem_univ _)
    · intro hgen
      obtain ⟨z, hzz⟩ := hz
      rw [← key z hzz, hpe z]
      refine Finset.prod_ne_zero_iff.2 fun σ _ => ?_
      have hs : SatAt U w (z ∘ σ) := by
        obtain ⟨τ, h1, h2⟩ := hzz
        refine ⟨τ, h1, ?_⟩
        have hm : Finset.univ.val.map (z ∘ σ) = Finset.univ.val.map z := by
          rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
        rw [hm]
        exact h2
      exact hgen _ hs

open UpperTheory.Gal.Gen in

/- English proof (translation)
Establish `hl : Nat.Prime l` using `Fact.out`. Take `⟨d, hd⟩` from `denomBdd_holds E l hl a (f.support : Set (UA E a)) f.support.finite_toSet.isCompact`. Establish `hl1 : (1 : ℝ) < (l : ℝ)` using `by exact_mod_cast hl.one_lt`. Establish `hq0 : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.mpr (by linarith)`. Establish `hq1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`.

Use `set S : ℝ := ∑ g ∈ f.support, ‖ι.symm (f g)‖ with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Set `r : UA E a → ℕ` to `fun g => a * d * ∑ᶠ (u : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ cLoc u g ≠ 1), wtSizeOver ι lam u`. Use `set B : ℝ := ((l : ℝ)⁻¹) ^ (a * d * wtSize lam + ∑ g ∈ f.support, r g) with hB`. Establish `hB0 : 0 < B` using `pow_pos hq0 _`.

Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (div_pos hB0 (by linarith : (0 : ℝ) < S + 1)) hq1`. Establish `hk' : ((l : ℝ)⁻¹) ^ k * (S + 1) ≤ B` using `((lt_div_iff₀ (by linarith : (0 : ℝ) < S + 1)).mp hk).le`. Establish `hnorm : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k`. Establish `h1 : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹`. Use `PadicAlgCl.norm_extends l (l : ℚ_[l])` as an intermediate fact.

Simplify `this` using `[map_natCast, Padic.norm_p]`. Rewrite using `[map_pow, map_natCast, norm_pow, h1]`. Establish `key : ∀ g ∈ f.support, ‖ι.symm ((((l : ℂ) ^ k) • f) g)‖ ≤ B` using `fun g hgf => by`. Rewrite using `[Finsupp.smul_apply, smul_eq_mul, map_mul, norm_mul, hnorm]`. Establish `hle : ‖ι.symm (f g)‖ ≤ S + 1`.

Use `Finset.single_le_sum (f := fun g => ‖ι.symm (f g)‖) (fun _ _ => norm_nonneg _) hgf` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mul_le_mul_of_nonneg_left hle (pow_pos hq0 k).le).trans hk'`. Use `⟨(l : ℂ) ^ k, pow_ne_zero _ (by exact_mod_cast hl.ne_zero), fun g hg => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hgf : g ∈ f.support` using `Finsupp.support_smul hg`.

Conclude with `⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_add_right _ _))⟩`. Establish `hgf : g ∈ f.support` using `Finsupp.support_smul hg`. Conclude with `⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le ((Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hgf).trans (Nat.le_add_left _ _)))⟩`.
-/
theorem exists_scale {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ)
    (hf : ∀ g ∈ f.support, g ∈ finU E a) : ∃ c : ℂ, c ≠ 0 ∧ IntW ι lam (c • f) ∧ Loc.IntL ι lam (c • f) := by
  have hl : Nat.Prime l := Fact.out
  obtain ⟨d, hd⟩ := denomBdd_holds E l hl a (f.support : Set (UA E a)) f.support.finite_toSet.isCompact
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
  have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  set S : ℝ := ∑ g ∈ f.support, ‖ι.symm (f g)‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let r : UA E a → ℕ := fun g => a * d *
    ∑ᶠ (u : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ cLoc u g ≠ 1), wtSizeOver ι lam u
  set B : ℝ := ((l : ℝ)⁻¹) ^ (a * d * wtSize lam + ∑ g ∈ f.support, r g) with hB
  have hB0 : 0 < B := pow_pos hq0 _
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hB0 (by linarith : (0 : ℝ) < S + 1)) hq1
  have hk' : ((l : ℝ)⁻¹) ^ k * (S + 1) ≤ B := ((lt_div_iff₀ (by linarith : (0 : ℝ) < S + 1)).mp hk).le
  have hnorm : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
    have h1 : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have := PadicAlgCl.norm_extends l (l : ℚ_[l])
      simpa [map_natCast, Padic.norm_p] using this
    rw [map_pow, map_natCast, norm_pow, h1]
  have key : ∀ g ∈ f.support, ‖ι.symm ((((l : ℂ) ^ k) • f) g)‖ ≤ B := fun g hgf => by
    rw [Finsupp.smul_apply, smul_eq_mul, map_mul, norm_mul, hnorm]
    have hle : ‖ι.symm (f g)‖ ≤ S + 1 := by
      have := Finset.single_le_sum (f := fun g => ‖ι.symm (f g)‖) (fun _ _ => norm_nonneg _) hgf
      linarith
    exact (mul_le_mul_of_nonneg_left hle (pow_pos hq0 k).le).trans hk'
  refine ⟨(l : ℂ) ^ k, pow_ne_zero _ (by exact_mod_cast hl.ne_zero), fun g hg => ?_, fun g hg => ?_⟩
  · have hgf : g ∈ f.support := Finsupp.support_smul hg
    exact ⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_add_right _ _))⟩
  · have hgf : g ∈ f.support := Finsupp.support_smul hg
    exact ⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le
      ((Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hgf).trans (Nat.le_add_left _ _)))⟩

end UpperTheory.Gal.Int.Cong

end
