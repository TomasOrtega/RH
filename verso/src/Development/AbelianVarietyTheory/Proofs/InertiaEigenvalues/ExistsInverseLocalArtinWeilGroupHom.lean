import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvLocalArtin

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h art ha`. Establish `hinj` using `GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w`. Use `set f : (w.adicCompletion E)ˣ →* GlobalTheory.HeckeGal.Gab E Ω := art.comp (Neutral.B1.localIdele E w) with hf`. Establish `hfi : Function.Injective f` using `hinj`. Set `o : (w.adicCompletion E)ˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]`.

Establish `ho : ∀ x, ord (w.adicCompletion E) x = Multiplicative.toAdd (o x)` using `fun _ => rfl`. Establish `unit_iff : ∀ x, Formalism.L2.Host.IsUnitAt w x ↔ ord (w.adicCompletion E) x = 0`. Introduce `x`. Unfold `Formalism.L2.Host.IsUnitAt`. Rewrite using `[GlobalTheory.CompletionNorm.valued_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj]`.

Use linear arithmetic over natural numbers and integers. Establish `unif_ord : ∀ x, Formalism.L2.Host.IsUnifAt w x → ord (w.adicCompletion E) x = 1`. Introduce `x hx`. Unfold `Formalism.L2.Host.IsUnifAt at hx`. Rewrite `hx` using `[GlobalTheory.CompletionNorm.valued_eq_exp, WithZero.exp_inj]`.

Use linear arithmetic over natural numbers and integers. Take `⟨π, hπ, hπf⟩` from `(ha.frob w A h (GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)⁻¹)).2 ⟨_, isFrob_frob, rfl⟩`. Establish `hπo : ord (w.adicCompletion E) π = 1` using `unif_ord π hπ`. Establish `hπf' : f π⁻¹ = GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)`. Rewrite using `[map_inv]`.

Use `show (art (Neutral.B1.localIdele E w π))⁻¹ = _`. Rewrite using `[hπf, map_inv, inv_inv]`. Establish `ordpow : ∀ n : ℤ, ord (w.adicCompletion E) (π⁻¹ ^ n) = -n`. Introduce `n`. Rewrite using `[ho, map_zpow, map_inv, toAdd_zpow, toAdd_inv, ← ho, hπo]`.

Simplify using the standard rewrite rules. Establish `hex : ∀ σ : Weil h, ∃ x, ord (w.adicCompletion E) x = -deg σ ∧ f x = GlobalTheory.HeckeGal.toAb E Ω σ`. Introduce `σ`. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul deg_frob σ`. Take `⟨u, hu, huf⟩` from `(ha.ine w A h (GlobalTheory.HeckeGal.toAb E Ω τ)).2 ⟨τ, τ.2, rfl⟩`.

Use `⟨π⁻¹ ^ deg σ * u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SmGL.ord_mul, ordpow, (unit_iff u).1 hu, add_zero]`. Rewrite using `[map_mul, map_zpow, hπf'] show _ * art (Neutral.B1.localIdele E w u) = _`. Rewrite using `[huf, ← map_zpow, ← map_mul]`. Use `congr 1`.

Use `conv_rhs => rw [hτ]`. Simplify using `[Subgroup.coe_mul, Subgroup.coe_zpow]`. Use `choose g hgo hgf using hex`. Set `a : Weil h →* (w.adicCompletion E)ˣ` to `{ toFun := g map_one' := hfi (by rw [hgf, map_one, Subgroup.coe_one, map_one]) map_mul' := fun σ τ => hfi (by rw [hgf, map_mul, hgf, hgf, Subgroup.coe_mul, map_mul]) }`. Use `⟨a, ?_, hgo, fun σ => hgf σ⟩` and prove the remaining obligations.

Introduce `x`. Use `set n := ord (w.adicCompletion E) x`. Establish `hu : Formalism.L2.Host.IsUnitAt w (x * π⁻¹ ^ n)`. Rewrite using `[unit_iff, SmGL.ord_mul, ordpow]`. Simplify using `[n]`.

Take `⟨τ, hτ, hτf⟩` from `(ha.ine w A h (f (x * π⁻¹ ^ n))).1 ⟨_, hu, rfl⟩`. Use `⟨ineIncl h ⟨τ, hτ⟩ * frob h ^ (-n), hfi ?_⟩` and prove the remaining obligations. Use `show f (g _) = f x`. Rewrite using `[hgf, Subgroup.coe_mul, Subgroup.coe_zpow, coe_ineIncl, map_mul, map_zpow, hτf, ← hπf', ← map_zpow, ← map_mul]`. Use `congr 1`.

Rewrite using `[mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]`.
-/
theorem exists_invLocalArtin : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h art ha
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w
  set f : (w.adicCompletion E)ˣ →* GlobalTheory.HeckeGal.Gab E Ω := art.comp (Neutral.B1.localIdele E w) with hf
  have hfi : Function.Injective f := hinj
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  have ho : ∀ x, ord (w.adicCompletion E) x = Multiplicative.toAdd (o x) := fun _ => rfl
  have unit_iff : ∀ x, Formalism.L2.Host.IsUnitAt w x ↔ ord (w.adicCompletion E) x = 0 := by
    intro x
    unfold Formalism.L2.Host.IsUnitAt
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj]
    omega
  have unif_ord : ∀ x, Formalism.L2.Host.IsUnifAt w x → ord (w.adicCompletion E) x = 1 := by
    intro x hx
    unfold Formalism.L2.Host.IsUnifAt at hx
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, WithZero.exp_inj] at hx
    omega

  obtain ⟨π, hπ, hπf⟩ := (ha.frob w A h (GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)⁻¹)).2 ⟨_, isFrob_frob, rfl⟩
  have hπo : ord (w.adicCompletion E) π = 1 := unif_ord π hπ
  have hπf' : f π⁻¹ = GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω) := by
    rw [map_inv]; show (art (Neutral.B1.localIdele E w π))⁻¹ = _; rw [hπf, map_inv, inv_inv]
  have ordpow : ∀ n : ℤ, ord (w.adicCompletion E) (π⁻¹ ^ n) = -n := by
    intro n
    rw [ho, map_zpow, map_inv, toAdd_zpow, toAdd_inv, ← ho, hπo]; simp
  have hex : ∀ σ : Weil h, ∃ x, ord (w.adicCompletion E) x = -deg σ ∧ f x = GlobalTheory.HeckeGal.toAb E Ω σ := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    obtain ⟨u, hu, huf⟩ := (ha.ine w A h (GlobalTheory.HeckeGal.toAb E Ω τ)).2 ⟨τ, τ.2, rfl⟩
    refine ⟨π⁻¹ ^ deg σ * u, ?_, ?_⟩
    · rw [SmGL.ord_mul, ordpow, (unit_iff u).1 hu, add_zero]
    · rw [map_mul, map_zpow, hπf']
      show _ * art (Neutral.B1.localIdele E w u) = _
      rw [huf, ← map_zpow, ← map_mul]
      congr 1
      conv_rhs => rw [hτ]
      simp [Subgroup.coe_mul, Subgroup.coe_zpow]
  choose g hgo hgf using hex
  let a : Weil h →* (w.adicCompletion E)ˣ :=
    { toFun := g
      map_one' := hfi (by rw [hgf, map_one, Subgroup.coe_one, map_one])
      map_mul' := fun σ τ => hfi (by rw [hgf, map_mul, hgf, hgf, Subgroup.coe_mul, map_mul]) }
  refine ⟨a, ?_, hgo, fun σ => hgf σ⟩
  intro x
  set n := ord (w.adicCompletion E) x
  have hu : Formalism.L2.Host.IsUnitAt w (x * π⁻¹ ^ n) := by
    rw [unit_iff, SmGL.ord_mul, ordpow]; simp [n]
  obtain ⟨τ, hτ, hτf⟩ := (ha.ine w A h (f (x * π⁻¹ ^ n))).1 ⟨_, hu, rfl⟩
  refine ⟨ineIncl h ⟨τ, hτ⟩ * frob h ^ (-n), hfi ?_⟩
  show f (g _) = f x
  rw [hgf, Subgroup.coe_mul, Subgroup.coe_zpow, coe_ineIncl, map_mul, map_zpow, hτf, ← hπf', ← map_zpow, ← map_mul]
  congr 1
  rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]

end GlobalTheory.InvLocalArtin
