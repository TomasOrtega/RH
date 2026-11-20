import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Rewrite `h`, the goal using `[Filter.eventually_cofinite]`. Use `(h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hne : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`.

Establish `e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v` using `HeightOneSpectrum.ext hl.over.symm`. Conclude with `⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩`.
-/
private theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

/- English proof (translation)
Take `⟨T, hT, -⟩` from `h`. Use `hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `T.surjective x`. Apply `T.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply, TR.CuspSub.chiDet_locGL]`.

Both sides reduce to the same expression.
-/
private theorem sat_of_isoTwist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n}
    {η : HChar F} (h : IsoTwist π η) {v : HeightOneSpectrum (𝓞 F)} (hη : η.UnrAt v) {B : Multiset ℂˣ}
    (hB : π.HasSat v B) : B = B.map (· * η.val v) := by
  obtain ⟨T, hT, -⟩ := h
  refine hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)
  obtain ⟨x, rfl⟩ := T.surjective x
  apply T.injective
  rw [LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply,
    TR.CuspSub.chiDet_locGL]
  rfl

/- English proof (translation)
Simplify using `[algSat, Multiset.bind_singleton, Multiset.map_map]`.
-/
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

/- English proof (translation)
Introduce `hIso hTw hEx hFr hSch hIrr F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n r π hc hatt hirr η hη hT`. Take `⟨δ, hδc, hδ1, hδs, hδu⟩` from `hEx F E Ω l h2`. Use `haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic`. Conclude with `Algebra.IsAlgebraic.trans F E Ω⟩`. Use `hδ1 (hSch _ _ _ n r (res F Ω E) δ hirr ?_ ?_)` and prove the remaining obligations.

Use extensionality with `s`. Use `(hδs.1 _).2 ⟨s, rfl⟩` as an intermediate fact. Simplify using `using this`. Use `hIso F Ω l ι n r _ hc (hIrr.2 _ _ n r δ hc hδc) hatt.1 ((hIrr.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_ filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw` and prove the remaining obligations. Take `⟨w, rfl, hw⟩` from `hw`.

Take `⟨B, hB, hE⟩` from `hv`. Take `⟨h1, h3⟩` from `hw (w.under (𝓞 F)) rfl`. Use `⟨_, hE, ?_⟩` and prove the remaining obligations. Establish `h4` using `hTw F Ω l ι n r δ _ _ _ hE (hFr F E Ω l ι δ hδs w hu)`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Use `conv_lhs => rw [sat_of_isoTwist hT h1 hB]`. Establish `h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1`. Use `(congrArg Units.val h3).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [algSat_eq, Multiset.map_map]`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← h5]`. Simplify using `only [Function.comp_apply, Units.val_mul, mul_assoc]`.
-/
theorem UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible :
    UpperTheory.V.Af.IsoOfFrob → UpperTheory.V.Af.Bc.FrobTw → UpperTheory.V.Af.Bc.SignEx → UpperTheory.V.Af.Bc.SignFrob → UpperTheory.V.Af.Bc.SchurTw → UpperTheory.V.Af.Bc.IrrBasic → UpperTheory.V.Af.Bc.NoTwist := by
  intro hIso hTw hEx hFr hSch hIrr F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n r π hc hatt hirr η hη hT
  obtain ⟨δ, hδc, hδ1, hδs, hδu⟩ := hEx F E Ω l h2
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F E Ω⟩
  refine hδ1 (hSch _ _ _ n r (res F Ω E) δ hirr ?_ ?_)
  · ext s
    have := (hδs.1 _).2 ⟨s, rfl⟩
    simpa using this
  · refine hIso F Ω l ι n r _ hc (hIrr.2 _ _ n r δ hc hδc) hatt.1 ((hIrr.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw
    obtain ⟨w, rfl, hw⟩ := hw
    obtain ⟨B, hB, hE⟩ := hv
    obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
    refine ⟨_, hE, ?_⟩
    have h4 := hTw F Ω l ι n r δ _ _ _ hE (hFr F E Ω l ι δ hδs w hu)
    convert h4 using 1
    conv_lhs => rw [sat_of_isoTwist hT h1 hB]
    have h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1 := by
      refine (congrArg Units.val h3).trans ?_
      change ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _
      split_ifs <;> simp
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [← h5]
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
