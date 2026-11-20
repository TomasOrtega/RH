import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead ValuativeRel

namespace GlobalTheory.SatakeExists

/- English proof (translation)
Establish `hc` using `LocGL.isCompl_fixed_twKer hρ hH`. Set `T : Subrepresentation ρ` to `⟨twKer ρ H 1, fun g _ hv => twKer_le_comap ρ H g (hn g) hv⟩`. Set `σ` to `onFixed ρ H (MonoidHom.id G) hn`. Set `p : ρ.IntertwiningMap σ` to `⟨Submodule.projectionOnto _ _ hc, fun g => LinearMap.ext fun v => by`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))`.

Establish `e1` using `Submodule.projectionOnto_apply_left hc ⟨a, ha⟩`. Establish `e2` using `Submodule.projectionOnto_apply_right hc ⟨b, hb⟩`. Establish `e3` using `Submodule.projectionOnto_apply_left hc (σ g ⟨a, ha⟩)`. Establish `e4` using `Submodule.projectionOnto_apply_right hc ⟨ρ g b, T.apply_mem_toSubmodule g hb⟩`. Simplify using `only [LinearMap.comp_apply, map_add]`.

Rewrite using `[e1, e2, e4, map_zero]`. Conclude with `congrArg (· + 0) e3⟩`. Establish `hp : ∀ x : fixed ρ H, p x.1 = x` using `fun x => Submodule.projectionOnto_apply_left hc x`. Take `⟨ψ, m, hm0, hm⟩` from `GlobalTheory.exists_character_eigenvector_of_commute ℂ G _ σ.dual fun a b => by`. Rewrite using `[← map_mul, hcomm, map_mul]`.

Establish `hm' : ∀ g x, m (σ g x) = ((ψ g)⁻¹ : ℂˣ) * m x` using `fun g x => by`. Use `LinearMap.congr_fun (hm g⁻¹) x` as an intermediate fact. Simplify `this` using `[Representation.dual_apply, Module.Dual.transpose_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x, m x ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hm0 (LinearMap.ext fun x => by simpa using h x)`. Use `⟨ψ⁻¹, m ∘ₗ p.toLinearMap, fun h => hx₀ ?_, fun g v => ?_, fun h hh => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun h x₀.1` as an intermediate fact. Simplify `this` using `[hp]`.

Use `show m (p (ρ g v)) = _`. Rewrite using `[p.isIntertwining, hm']`. Both sides reduce to the same expression. Establish `h1 : σ h x₀ = x₀`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ρ h x₀.1 = x₀.1`. Simplify using `using x₀.2 ⟨h, hh⟩`. Establish `h2` using `hm' h x₀`. Rewrite `h2` using `[h1]`. Establish `h3 : (((ψ h)⁻¹ : ℂˣ) : ℂ) = 1`.

Use `mul_right_cancel₀ hx₀ (show (1 : ℂ) * m x₀ = (((ψ h)⁻¹ : ℂˣ) : ℂ) * m x₀ by rw [one_mul]; exact h2)` as an intermediate fact. Conclude with `this.symm`. Conclude with `Units.ext (by simpa using h3)`.
-/
theorem exists_eigenform {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hcomm : ∀ a b : G, a * b = b * a)
    (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    [FiniteDimensional ℂ (fixed ρ H)] [Nontrivial (fixed ρ H)] :
    ∃ (χ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (χ g : ℂ) * l v) ∧
      ∀ h ∈ H, χ h = 1 := by
  have hc := LocGL.isCompl_fixed_twKer hρ hH
  let T : Subrepresentation ρ := ⟨twKer ρ H 1, fun g _ hv => twKer_le_comap ρ H g (hn g) hv⟩
  let σ := onFixed ρ H (MonoidHom.id G) hn
  let p : ρ.IntertwiningMap σ :=
    ⟨Submodule.projectionOnto _ _ hc, fun g => LinearMap.ext fun v => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have e1 := Submodule.projectionOnto_apply_left hc ⟨a, ha⟩
      have e2 := Submodule.projectionOnto_apply_right hc ⟨b, hb⟩
      have e3 := Submodule.projectionOnto_apply_left hc (σ g ⟨a, ha⟩)
      have e4 := Submodule.projectionOnto_apply_right hc ⟨ρ g b, T.apply_mem_toSubmodule g hb⟩
      simp only [LinearMap.comp_apply, map_add]
      rw [e1, e2, e4, map_zero]
      exact congrArg (· + 0) e3⟩
  have hp : ∀ x : fixed ρ H, p x.1 = x := fun x => Submodule.projectionOnto_apply_left hc x
  obtain ⟨ψ, m, hm0, hm⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ G _ σ.dual fun a b => by
    rw [← map_mul, hcomm, map_mul]
  have hm' : ∀ g x, m (σ g x) = ((ψ g)⁻¹ : ℂˣ) * m x := fun g x => by
    have := LinearMap.congr_fun (hm g⁻¹) x
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x, m x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (LinearMap.ext fun x => by simpa using h x)
  refine ⟨ψ⁻¹, m ∘ₗ p.toLinearMap, fun h => hx₀ ?_, fun g v => ?_, fun h hh => ?_⟩
  · have := LinearMap.congr_fun h x₀.1
    simpa [hp] using this
  · show m (p (ρ g v)) = _
    rw [p.isIntertwining, hm']
    rfl
  · have h1 : σ h x₀ = x₀ := by
      apply Subtype.ext
      show ρ h x₀.1 = x₀.1
      simpa using x₀.2 ⟨h, hh⟩
    have h2 := hm' h x₀
    rw [h1] at h2
    have h3 : (((ψ h)⁻¹ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hx₀ (show (1 : ℂ) * m x₀ = (((ψ h)⁻¹ : ℂˣ) : ℂ) * m x₀ by rw [one_mul]; exact h2)
      exact this.symm
    exact Units.ext (by simpa using h3)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by`. Take `⟨c, hc⟩` from `valuation_surjective (uniformizer k)`. Use `⟨Units.mk0 c fun h => ?_, hc⟩` and prove the remaining obligations. Rewrite `hc` using `[h, map_zero]`. Conclude with `IwahoriInj.unif_pos.ne hc`.

Set `c : Fin n → kˣ →* ℂˣ` to `fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)`. Establish `hc : ∀ i, IsUnram (c i)` using `fun i x hx => hμ _ fun j => by`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using hx`.

Simplify using `[Pi.mulSingle_eq_of_ne h]`. Use `⟨fun i => c i ϖ, MonoidHom.ext fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[torusChar_apply]`. Simplify using `only [← eq_unrChar (hc _) hϖ]`. Use `conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]`.

Both sides reduce to the same expression.
-/
theorem exists_eq_torusChar {n : ℕ} (μ : (Fin n → kˣ) →* ℂˣ) (hμ : ∀ t ∈ torusO k (Fin n), μ t = 1) :
    ∃ α : Fin n → ℂˣ, torusChar (fun i => unrChar k (α i)) = μ := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 c fun h => ?_, hc⟩
    rw [h, map_zero] at hc
    exact IwahoriInj.unif_pos.ne hc
  let c : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)
  have hc : ∀ i, IsUnram (c i) := fun i x hx => hμ _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hx
    · simp [Pi.mulSingle_eq_of_ne h]
  refine ⟨fun i => c i ϖ, MonoidHom.ext fun t => ?_⟩
  rw [torusChar_apply]
  simp only [← eq_unrChar (hc _) hϖ]
  conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
  rfl

/- English proof (translation)
Set `ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ` to `(ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom`. Set `φ : (jac (points (Fin n)) π).IntertwiningMap ρ` to `⟨l, fun g => LinearMap.ext fun x => by`. Take `⟨t, rfl⟩` from `(leviTorus k (Fin n)).surjective g`. Establish `e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x` using `by show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _`. Rewrite using `[MulEquiv.symm_apply_apply, ofChar_apply]`.

Conclude with `(hl t x).trans e.symm⟩`. Take `⟨f, hf⟩` from `(Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ`. Establish `hne : ∃ v, f v ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `hl0 (LinearMap.ext fun x => ?_)` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1` using `by rw [← hf]; rfl`. Establish `h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v)` using `rfl`. Rewrite using `[h2, h1, h v]`.

Both sides reduce to the same expression. Use `IsSubquotient.of_injective f ((injective_iff_map_eq_zero f.toLinearMap).2 ?_)` and prove the remaining obligations. Set `K : Subrepresentation π` to `⟨LinearMap.ker f.toLinearMap, fun g v hv => by show f (π g v) = 0`. Rewrite using `[f.isIntertwining]`. Establish `: f v = 0` using `hv`.

Rewrite using `[this, map_zero]⟩`. Use `haveI := hirr`. Break down `eq_bot_or_eq_top K with h | h` into its components or cases. Introduce `v hv`. Establish `: v ∈ K.toSubmodule` using `hv`.

Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Take `⟨v, hv⟩` from `hne`. Conclude with `absurd (show v ∈ K.toSubmodule by rw [h]; trivial) hv`.
-/
theorem isSubquotient_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) (hirr : π.IsIrreducible)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    IsSubquotient π (indB (ofChar μ)) := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  have hne : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    refine hl0 (LinearMap.ext fun x => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
    have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
    rw [h2, h1, h v]
    rfl
  refine IsSubquotient.of_injective f ((injective_iff_map_eq_zero f.toLinearMap).2 ?_)
  let K : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    have : f v = 0 := hv
    rw [this, map_zero]⟩
  haveI := hirr
  rcases eq_bot_or_eq_top K with h | h
  · intro v hv
    have : v ∈ K.toSubmodule := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · obtain ⟨v, hv⟩ := hne
    exact absurd (show v ∈ K.toSubmodule by rw [h]; trivial) hv

/- English proof (translation)
Use `haveI := hadm.2 _ (SmGL.IwahoriOnto.isOpen_iwahori k (Fin n)) (SmGL.IwahoriOnto.isCompact_iwahori k (Fin n))`. Establish `hb` using `GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm`. Use `haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) := Module.Finite.of_surjective _ hb.2`. Use `haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 hI`. Use `haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial`.

Conclude with `exists_eigenform (isSmooth_jacBU hadm.1) (SmGL.UnramFixed.isCompact_torusO k (Fin n)) mul_comm fun _ => by rw [Subgroup.normalizer_eq_top]; trivial`.
-/
theorem exists_eigenform_jacBU {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ (χ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 ∧
      (∀ g v, l (jacBU π g v) = (χ g : ℂ) * l v) ∧ ∀ h ∈ torusO k (Fin n), χ h = 1 := by
  haveI := hadm.2 _ (SmGL.IwahoriOnto.isOpen_iwahori k (Fin n))
    (SmGL.IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 hI
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  exact exists_eigenform (isSmooth_jacBU hadm.1) (SmGL.UnramFixed.isCompact_torusO k (Fin n)) mul_comm
    fun _ => by rw [Subgroup.normalizer_eq_top]; trivial

/- English proof (translation)
Take `⟨χ, l, hl0, hl, hχ⟩` from `exists_eigenform_jacBU hadm hI`. Set `δ : (Fin n → kˣ) →* ℂˣ` to `(deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom`. Take `⟨α, hα⟩` from `exists_eq_torusChar (χ * δ⁻¹) fun t ht => by`. Establish `: δ t = 1` using `SmGL.UnramFixed.deltaHalf_torusO k ht`. Simplify using `[hχ t ht, this]`.

Use `⟨α, ?_⟩` and prove the remaining obligations. Establish `key` using `isSubquotient_of_eigenform hadm.1 hirr (χ * δ⁻¹) l hl0 fun t x => by`. Rewrite using `[SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[← hα]`.

Conclude with `key`.
-/
theorem exists_isSubquotient_prinSeries {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π) (hirr : π.IsIrreducible)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ α : Fin n → ℂˣ, IsSubquotient π (prinSeries fun i => unrChar k (α i)) := by
  obtain ⟨χ, l, hl0, hl, hχ⟩ := exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  refine ⟨α, ?_⟩
  have key := isSubquotient_of_eigenform hadm.1 hirr (χ * δ⁻¹) l hl0 fun t x => by
    rw [SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  rw [← hα] at key
  exact key

/- English proof (translation)
Introduce `hBZ k _ _ _ _ n π hs`. Establish `hadm : IsAdmissible π.π` using `(hBZ k).1 (Fin n) π.V π.π π.smooth π.irr`. Establish `hI : fixed π.π (iwahori k (Fin n)) ≠ ⊥`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hs`. Use `(Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩` and prove the remaining obligations.

Conclude with `hv ⟨h.1, iwahori_le_KO k _ h.2⟩`. Take `⟨α, hα⟩` from `exists_isSubquotient_prinSeries hadm π.irr hI`. Conclude with `⟨α, π.irr, hs, hα⟩`.
-/
theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  intro hBZ k _ _ _ _ n π hs
  have hadm : IsAdmissible π.π := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hI : fixed π.π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := exists_isSubquotient_prinSeries hadm π.irr hI
  exact ⟨α, π.irr, hs, hα⟩

end GlobalTheory.SatakeExists
