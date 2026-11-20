import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

open private iso_comm iso_act from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
open private satLocFree from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree

section

open Formalism.L2.Host Matrix

/- English proof (translation)
Use `⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩` and prove the remaining obligations. Take `⟨f, h0, hf⟩` from `hσ`. Express the relevant statement in the definitionally equal form `⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤`. Establish `hi` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Establish `hop : ∀ (o : Op E a) (x : π.V), x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) → π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1`.

Introduce `o x hx`. Consider the cases of `o with`. Consider the case `fin k`. Establish `h1` using `iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w) (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by`. Simplify using `only [CuspSub.locRep, MonoidHom.comp_apply]`.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)`. Establish `e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k) (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x`. Rewrite using `[CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Both sides reduce to the same expression. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.

Consider the case `cpt k`. Use `iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 = (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X`.

Use `iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1`. Break down `π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, hop o x hx, rfl⟩) with h1 | h1`.

Establish `h2` using `hi (h1.trans (Submodule.map_bot _).symm)`. Conclude with `absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0`. Conclude with `hi (h1.trans (Submodule.map_subtype_top _).symm)`.
-/
private theorem isotypic {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    UpperTheory.V.Af.LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end

/- English proof (translation)
Substitute `e` using the available equality. Substitute `he` using the available equality. Take `⟨f, h0, hm, hf⟩` from `h`. Use `(satLocFree E _ w σ).2 _ π.finPart (isotypic π w σ ⟨f.codRestrict _ hm, fun e => h0 ?_, fun g v => Subtype.ext (hf g v)⟩) B` and prove the remaining obligations. Conclude with `LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)`.
-/
private theorem sat_part {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} (e : N = n)
    (V : Submodule ℂ (Sm E N)) (π : CuspSub E n) (he : e ▸ V = π.V) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B := by
  subst e
  subst he
  obtain ⟨f, h0, hm, hf⟩ := h
  refine (satLocFree E _ w σ).2 _ π.finPart (isotypic π w σ
    ⟨f.codRestrict _ hm, fun e => h0 ?_, fun g v => Subtype.ext (hf g v)⟩) B
  exact LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)

/- English proof (translation)
Introduce `E _ _ _ n _ π D hD w B`. Take `⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩` from `D`. Take `⟨hc, hV⟩` from `hD`. Take `rfl : c = 1` from `hc`. Take `⟨e, he⟩` from `hV 0`.

Establish `key` using `sat_part e (V 0) π he w (σ 0 w) (loc 0 w) B`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Establish `h1` using `key.1 hs`. Use `⟨fun _ => B, fun i => ?_, by simp⟩` and prove the remaining obligations.

Take `rfl : i = 0` from `Subsingleton.elim _ _`. Conclude with `⟨h1.1, h1⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Establish `h1` using `(hb 0).2`. Simplify using `using (sat_part e (V 0) π he w (σ 0 w) (loc 0 w) (b 0)).2 h1`.
-/
theorem UpperTheory.V.Z.Tf.GOne.oneSat :
    OneSat := by
  intro E _ _ _ n _ π D hD w B
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := D
  obtain ⟨hc, hV⟩ := hD
  obtain rfl : c = 1 := hc
  obtain ⟨e, he⟩ := hV 0
  have key := sat_part e (V 0) π he w (σ 0 w) (loc 0 w) B
  constructor
  · intro hs
    have h1 := key.1 hs
    refine ⟨fun _ => B, fun i => ?_, by simp⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨h1.1, h1⟩
  · rintro ⟨b, hb, rfl⟩
    have h1 := (hb 0).2
    simpa using (sat_part e (V 0) π he w (σ 0 w) (loc 0 w) (b 0)).2 h1
