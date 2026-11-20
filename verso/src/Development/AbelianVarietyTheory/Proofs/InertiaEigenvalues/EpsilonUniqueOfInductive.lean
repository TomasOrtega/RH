import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrincipleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilBrauer

/- English proof (translation)
Introduce `hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind`. Use `set f : WD h → ℂˣ := fun x => ε x / ε' x with hf`. Establish `fmul : ∀ x y, f (x.lpSum y) = f x * f y`. Introduce `x y`. Simplify using `only [hf, hε, hε']`.

Conclude with `mul_div_mul_comm _ _ _ _`. Establish `fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y`. Introduce `x y hxy`. Take `⟨h1, h2⟩` from `hcp x y hxy`. Simplify using `only [hf, h1, h2]`.

Establish `key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1`. Introduce `n a μ hμ hfin`. Set `u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ` to `a.ρ.toHomUnits`. Set `G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ` to `u.range`. Establish `hGfin : Finite G`.

Establish `hr : (Set.range u).Finite`. Use `Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn` and prove the remaining obligations. Use `hfin.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨σ, rfl⟩, rfl⟩`. Conclude with `⟨σ, rfl⟩`.

Establish `: ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u` using `MonoidHom.coe_range u`. Conclude with `Set.finite_coe_iff.mpr (this ▸ hr)`. Use `letI : Fintype G := Fintype.ofFinite G`. Set `π : Weil h →* G` to `u.rangeRestrict`. Establish `hπs : Function.Surjective π` using `MonoidHom.rangeRestrict_surjective u`.

Set `ρG : Representation ℂ G (Fin n → ℂ)` to `(Units.coeHom _).comp G.subtype`. Establish `hρG : ∀ σ, ρG (π σ) = a.ρ σ` using `fun σ => rfl`. Establish `hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1`. Introduce `σ`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Rewrite using `[← hρG, h1, map_one]`. Introduce `h1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `h1`. Establish `hopen : IsOpen {σ : Ine (F` using `E) A | π (ineIncl h σ) = 1} := by`. Establish `: {σ : Ine (F` using `E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} := Set.ext fun σ => hπ1 _`. Rewrite using `[this]`. Conclude with `a.smooth`.

Take `⟨r, H, χ, c, hbr⟩` from `hB G (Fin n → ℂ) ρG`. Establish `hi1` using `fun i => GlobalTheory.T.induced_representation_character G (H i) (χ i)`. Establish `hi2` using `fun i => GlobalTheory.T.induced_representation_character G (H i) 1`. Use `choose Rχ vχ hRχ using hi1`. Use `choose R1 v1 hR1 using hi2`.

Establish `hp1` using `fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ`. Establish `hp2` using `fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ`. Use `choose bχ hbχ using hp1`. Use `choose b1 hb1 using hp2`. Establish `span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ)) (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ), (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ → Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤`.

Introduce `i R b v hb hs`. Rewrite using `[eq_top_iff, ← hs, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Take `⟨σ, rfl⟩` from `hπs g`. Use `show R (π σ) v ∈ _`.

Establish `e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v`. Rewrite using `[hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)`. Establish `hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i))`.

Introduce `i`. Set `H'` to `(H i).comap π`. Establish `hidx : (H i).index = H'.index` using `(Subgroup.index_comap_of_surjective _ hπs).symm`. Use `haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩`. Establish `hop : IsOpen {σ : Ine (F` using `E) A | ineIncl h σ ∈ H'} := by`.

Establish `hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h)`. Introduce `σ hσ`. Rewrite `hσ` using `[MonoidHom.mem_ker, MonoidHom.comp_apply]`. Use `show π (ineIncl h σ) ∈ H i`. Rewrite using `[hσ]`.

Conclude with `one_mem _`. Conclude with `Subgroup.isOpen_mono hle hopen`. Set `χ₁ : H' →* ℂˣ` to `μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))`. Set `χ₂ : H' →* ℂˣ` to `μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))`. Establish `e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i`.

Introduce `σ`. Rewrite using `[hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]`. Both sides reduce to the same expression. Establish `e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i`. Introduce `σ`.

Rewrite using `[hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]`. Both sides reduce to the same expression. Establish `hh` using `hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2 (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)`. Simplify using `only [hf]`. Conclude with `div_eq_div_iff_mul_eq_mul.mpr hh`.

Establish `hμ1 : f (WD.mk (WDRep.ofChars h (ι` using `Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by`. Use `hchar μ hμ` as an intermediate fact. Simplify using `only [hf]`. Conclude with `div_eq_one.mpr this`. Set `F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ)` to `Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩) (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩)) (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))`.

Set `cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ` to `Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))`. Establish `htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0`. Introduce `σ`. Establish `hb` using `hbr (π σ)`. Rewrite `hb` using `[Module.finrank_fin_fun]`.

Establish `t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ) ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) = (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ))` using `by show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _`. Rewrite using `[WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]`. Establish `t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ) ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ)` using `by show LinearMap.trace ℂ (Fin 1 → ℂ) ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _`. Rewrite using `[WDRep.ofChars_ρ]`. Establish `e : (diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ))`.

Use extensionality with `v i`. Simplify using the standard rewrite rules. Rewrite using `[e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one, mul_one]`. Establish `tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ) ((F (Sum.inr (Sum.inl i))).2.ρ σ) = (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)`. Introduce `i`.

Use `show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _`. Rewrite using `[hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]`. Establish `t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ) ((F (Sum.inr (Sum.inr i))).2.ρ σ) = (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)`. Introduce `i`. Use `show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _`.

Rewrite using `[hb1, map_smul, smul_eq_mul, (hR1 i).2.2]`. Simplify using the standard rewrite rules. Simplify using `only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']`. Simplify using `only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast, one_mul]`. Establish `hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) + ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) = -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) - indFun (H i) (fun _ => 1) (π σ))`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`. Take the linear combination `(μ σ : ℂ) * hb`.

Establish `hv` using `GlobalTheory.T.multiplicative_virtual_character E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr`. Establish `hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1` using `hμ1`. Establish `hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2)` using `hpair`. Simplify using `only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv`. Simplify using `only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one, mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv`.

Conclude with `hv`. Introduce `x`. Establish `hx` using `GlobalTheory.T.weil_deligne_induction_principle E Ω A w h (fun x => f x = 1) (fun x y hx hy => by rw [fmul, hx, hy, one_mul]) (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x`. Simplify using `only [hf] at hx`. Conclude with `div_eq_one.mp hx`.
-/
theorem eq_of_induced : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  intro hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind
  classical
  set f : WD h → ℂˣ := fun x => ε x / ε' x with hf
  have fmul : ∀ x y, f (x.lpSum y) = f x * f y := by
    intro x y
    simp only [hf, hε, hε']
    exact mul_div_mul_comm _ _ _ _
  have fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hcp x y hxy
    simp only [hf, h1, h2]
  have key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1 := by
    intro n a μ hμ hfin
    let u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ := a.ρ.toHomUnits
    let G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ := u.range
    have hGfin : Finite G := by
      have hr : (Set.range u).Finite := by
        refine Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
        refine hfin.subset ?_
        rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      have : ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u := MonoidHom.coe_range u
      exact Set.finite_coe_iff.mpr (this ▸ hr)
    letI : Fintype G := Fintype.ofFinite G
    let π : Weil h →* G := u.rangeRestrict
    have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective u
    let ρG : Representation ℂ G (Fin n → ℂ) := (Units.coeHom _).comp G.subtype
    have hρG : ∀ σ, ρG (π σ) = a.ρ σ := fun σ => rfl
    have hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1 := by
      intro σ
      constructor
      · intro h1
        rw [← hρG, h1, map_one]
      · intro h1
        apply Subtype.ext
        apply Units.ext
        exact h1
    have hopen : IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} := by
      have : {σ : Ine (F := E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} :=
        Set.ext fun σ => hπ1 _
      rw [this]
      exact a.smooth
    obtain ⟨r, H, χ, c, hbr⟩ := hB G (Fin n → ℂ) ρG
    have hi1 := fun i => GlobalTheory.T.induced_representation_character G (H i) (χ i)
    have hi2 := fun i => GlobalTheory.T.induced_representation_character G (H i) 1
    choose Rχ vχ hRχ using hi1
    choose R1 v1 hR1 using hi2
    have hp1 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ
    have hp2 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ
    choose bχ hbχ using hp1
    choose b1 hb1 using hp2
    have span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ))
        (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ),
        (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ →
        Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤ := by
      intro i R b v hb hs
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨σ, rfl⟩ := hπs g
      show R (π σ) v ∈ _
      have e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v := by
        rw [hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    have hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i)) := by
      intro i
      let H' := (H i).comap π
      have hidx : (H i).index = H'.index := (Subgroup.index_comap_of_surjective _ hπs).symm
      haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩
      have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H'} := by
        have hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h) := by
          intro σ hσ
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
          show π (ineIncl h σ) ∈ H i
          rw [hσ]
          exact one_mem _
        exact Subgroup.isOpen_mono hle hopen
      let χ₁ : H' →* ℂˣ := μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))
      let χ₂ : H' →* ℂˣ := μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))
      have e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i := by
        intro σ
        rw [hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i := by
        intro σ
        rw [hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have hh := hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2
        (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)
      simp only [hf]
      exact div_eq_div_iff_mul_eq_mul.mpr hh
    have hμ1 : f (WD.mk (WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by
      have := hchar μ hμ
      simp only [hf]
      exact div_eq_one.mpr this
    let F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ) :=
      Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩)
          (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩))
        (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))
    let cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ :=
      Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))
    have htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0 := by
      intro σ
      have hb := hbr (π σ)
      rw [Module.finrank_fin_fun] at hb
      have t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) =
          (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ)) := by
        show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _
        rw [WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]
      have t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ) := by
        show LinearMap.trace ℂ (Fin 1 → ℂ)
          ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _
        rw [WDRep.ofChars_ρ]
        have e : (diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
          ext v i
          simp
        rw [e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one,
          mul_one]
      have tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ)
          ((F (Sum.inr (Sum.inl i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _
        rw [hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]
      have t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ)
          ((F (Sum.inr (Sum.inr i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _
        rw [hb1, map_smul, smul_eq_mul, (hR1 i).2.2]
        simp
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']
      simp only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast,
        one_mul]
      have hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) +
          ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) =
          -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) -
            indFun (H i) (fun _ => 1) (π σ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs]
      linear_combination (μ σ : ℂ) * hb
    have hv := GlobalTheory.T.multiplicative_virtual_character E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr
    have hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1 := hμ1
    have hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2) :=
      hpair
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv
    simp only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one,
      mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv
    exact hv
  intro x
  have hx := GlobalTheory.T.weil_deligne_induction_principle E Ω A w h (fun x => f x = 1)
    (fun x y hx hy => by rw [fmul, hx, hy, one_mul])
    (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x
  simp only [hf] at hx
  exact div_eq_one.mp hx

end GlobalTheory.WeilBrauer
