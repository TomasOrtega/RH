import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FinCompR

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd.Wc

/- English proof (translation)
Take `⟨-, hirr⟩` from `(isIrreducible_iff σ).1 hσ`. Establish `key : ∀ (f : X →ₗ[ℂ] V), (∀ g v, f (σ g v) = τ g (f v)) → ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, τ g v ∈ U) → ¬ LinearMap.range f ≤ U → ∀ x, f x ∈ U → x = 0`. Introduce `f hf U hU hn x hx`. Break down `hirr (U.comap f) (fun g v hv => by` into its components or cases. Rewrite using `[Submodule.mem_comap, hf]`.

Conclude with `hU g _ hv) with e | e`. Establish `: x ∈ U.comap f` using `hx`. Rewrite `this` using `[e, Submodule.mem_bot]`. Then use the resulting hypothesis. Conclude with `absurd (LinearMap.range_le_iff_comap.2 e) hn`. Take `⟨M, ⟨hst, hxM⟩, hmax⟩` from `zorn_le₀ {U : Submodule ℂ V | (∀ g, ∀ v ∈ U, τ g v ∈ U) ∧ x ∉ U} (fun c hc hch => by`.

Break down `c.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨⊥, ⟨fun g v hv => by simp_all, by simpa using hx⟩, by simp⟩`. Use `⟨sSup c, ⟨fun g v hv => ?_, fun hv' => ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Take `⟨U, hU, hvU⟩` from `(Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv`. Conclude with `le_sSup hU ((hc hU).1 g v hvU)`.

Take `⟨U, hU, hvU⟩` from `(Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv'`. Conclude with `(hc hU).2 hvU)`. Establish `hsup : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) → ∀ g, ∀ v ∈ M ⊔ LinearMap.range f, τ g v ∈ M ⊔ LinearMap.range f` using `fun f hf g v hv => by`. Take `⟨a, ha, _, ⟨y, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add, ← hf]`.

Conclude with `Submodule.add_mem_sup (hst g a ha) ⟨_, rfl⟩`. Establish `hmem : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) → ¬ LinearMap.range f ≤ M → x ∈ M ⊔ LinearMap.range f` using `fun f hf hn => by`. Assume the negation of the conclusion as `hc`. Conclude with `hn (le_sup_right.trans (hmax ⟨hsup f hf, hc⟩ le_sup_left))`. Choose the witnesses or unpack the hypotheses as in `⟨⟨f, hf⟩, hn⟩ : ∃ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, ¬ LinearMap.range f.1 ≤ M := by`.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Establish `: (⊤ : Submodule ℂ V) ≤ M` using `h ▸ iSup_le hn`. Conclude with `hxM (this trivial)`. Establish `htop : (⊤ : Submodule ℂ V) ≤ M ⊔ LinearMap.range f`.

Rewrite using `[← h]`. Use `iSup_le fun f' => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Take `⟨a, ha, _, ⟨y, rfl⟩, e⟩` from `Submodule.mem_sup.1 (hmem f'.1 f'.2 fun hl => hc (hl.trans le_sup_left))`. Establish `h2 : f'.1 y ∈ M ⊔ LinearMap.range f`.

Rewrite using `[eq_sub_of_add_eq' e]`. Conclude with `Submodule.sub_mem _ (hmem f hf hn) (Submodule.mem_sup_left ha)`. Establish `h3` using `key f'.1 f'.2 _ (hsup f hf) hc y h2`. Substitute `h3` using the available equality. Conclude with `hxM (by rw [← e]; simpa using ha)`.

Establish `hbij : Function.Bijective (M.mkQ ∘ₗ f)`. Use `⟨(injective_iff_map_eq_zero _).2 fun y hy => key f hf M hst hn y ((Submodule.Quotient.mk_eq_zero M).1 hy), fun q => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `M.mkQ_surjective q`. Take `⟨a, ha, _, ⟨y, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add]`. Both sides reduce to the same expression. Set `e` to `LinearEquiv.ofBijective _ hbij`. Establish `hp : ∀ a ∈ M, ∀ y, e.symm (M.mkQ (a + f y)) = y` using `fun a ha y => by`. Rewrite using `[map_add, show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add, LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Use `⟨e.symm.toLinearMap ∘ₗ M.mkQ, fun h0 => hxM ?_, fun g v => ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.mk_eq_zero M).1 ((map_eq_zero_iff e.symm e.symm.injective).1 h0)`. Take `⟨a, ha, _, ⟨y, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))`. Express the relevant statement in the definitionally equal form `e.symm (M.mkQ _) = σ g (e.symm (M.mkQ _))`.

Rewrite using `[hp a ha, map_add (τ g), ← hf, hp _ (hst g a ha)]`.
-/
private theorem sep_of_sum {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] X, p x ≠ 0 ∧ ∀ g y, p (τ g y) = σ g (p y) := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff σ).1 hσ
  have key : ∀ (f : X →ₗ[ℂ] V), (∀ g v, f (σ g v) = τ g (f v)) → ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, τ g v ∈ U) →
      ¬ LinearMap.range f ≤ U → ∀ x, f x ∈ U → x = 0 := by
    intro f hf U hU hn x hx
    rcases hirr (U.comap f) (fun g v hv => by
      rw [Submodule.mem_comap, hf]; exact hU g _ hv) with e | e
    · have : x ∈ U.comap f := hx
      rwa [e, Submodule.mem_bot] at this
    · exact absurd (LinearMap.range_le_iff_comap.2 e) hn
  obtain ⟨M, ⟨hst, hxM⟩, hmax⟩ := zorn_le₀ {U : Submodule ℂ V | (∀ g, ∀ v ∈ U, τ g v ∈ U) ∧ x ∉ U}
    (fun c hc hch => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, ⟨fun g v hv => by simp_all, by simpa using hx⟩, by simp⟩
      refine ⟨sSup c, ⟨fun g v hv => ?_, fun hv' => ?_⟩, fun z hz => le_sSup hz⟩
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv
        exact le_sSup hU ((hc hU).1 g v hvU)
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv'
        exact (hc hU).2 hvU)
  have hsup : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) →
      ∀ g, ∀ v ∈ M ⊔ LinearMap.range f, τ g v ∈ M ⊔ LinearMap.range f := fun f hf g v hv => by
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, ← hf]
    exact Submodule.add_mem_sup (hst g a ha) ⟨_, rfl⟩
  have hmem : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) → ¬ LinearMap.range f ≤ M →
      x ∈ M ⊔ LinearMap.range f := fun f hf hn => by
    by_contra hc
    exact hn (le_sup_right.trans (hmax ⟨hsup f hf, hc⟩ le_sup_left))
  obtain ⟨⟨f, hf⟩, hn⟩ : ∃ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, ¬ LinearMap.range f.1 ≤ M := by
    by_contra hn
    push Not at hn
    have : (⊤ : Submodule ℂ V) ≤ M := h ▸ iSup_le hn
    exact hxM (this trivial)
  have htop : (⊤ : Submodule ℂ V) ≤ M ⊔ LinearMap.range f := by
    rw [← h]
    refine iSup_le fun f' => ?_
    by_contra hc
    obtain ⟨a, ha, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (hmem f'.1 f'.2 fun hl => hc (hl.trans le_sup_left))
    have h2 : f'.1 y ∈ M ⊔ LinearMap.range f := by
      rw [eq_sub_of_add_eq' e]
      exact Submodule.sub_mem _ (hmem f hf hn) (Submodule.mem_sup_left ha)
    have h3 := key f'.1 f'.2 _ (hsup f hf) hc y h2
    subst h3
    exact hxM (by rw [← e]; simpa using ha)
  have hbij : Function.Bijective (M.mkQ ∘ₗ f) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => key f hf M hst hn y ((Submodule.Quotient.mk_eq_zero M).1 hy), fun q => ?_⟩
    obtain ⟨v, rfl⟩ := M.mkQ_surjective q
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    refine ⟨y, ?_⟩
    rw [map_add, show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add]
    rfl
  let e := LinearEquiv.ofBijective _ hbij
  have hp : ∀ a ∈ M, ∀ y, e.symm (M.mkQ (a + f y)) = y := fun a ha y => by
    rw [map_add, show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add, LinearEquiv.symm_apply_eq]
    rfl
  refine ⟨e.symm.toLinearMap ∘ₗ M.mkQ, fun h0 => hxM ?_, fun g v => ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero M).1 ((map_eq_zero_iff e.symm e.symm.injective).1 h0)
  · obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    change e.symm (M.mkQ _) = σ g (e.symm (M.mkQ _))
    rw [hp a ha, map_add (τ g), ← hf, hp _ (hst g a ha)]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 = (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1`. Rewrite using `[← map_mul, ← map_mul, TR.infGL_comm]`.
-/
private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

/- English proof (translation)
Use `set W := ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 with hW`. Establish `h1 : ∀ g, ∀ x ∈ W, π.finPart g x ∈ W` using `fun g x hx => by`. Use `Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.finPart g) _) fun f => ?_) hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩`.

Establish `h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → ∀ x ∈ W, T x ∈ W` using `fun T hT x hx => by`. Use `Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by`. Rewrite using `[LinearMap.comp_apply, f.2]`.

Conclude with `hT g _⟩ ⟨v, rfl⟩`. Establish `hi` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Establish `hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W` using `fun o x hx => by`. Consider the cases of `o with`. Consider the case `fin k => exact h1 k x hx`.

Consider the case `cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx`. Consider the case `lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X g) y.1)) x hx`. Break down `π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, hop o x hx, rfl⟩) with e | e`.

Establish `e' : W = ⊥` using `hi (e.trans (Submodule.map_bot _).symm)`. Take `⟨f, h0, hf⟩` from `h`. Conclude with `absurd (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e') ⟨f, hf⟩)) h0`. Conclude with `hi (e.trans (Submodule.map_subtype_top _).symm)`.
-/
private theorem sum_top (π : TR.CuspSub F n) (σ : SmIrr (GL (Fin n) (Af F))) (h : π.IsFinComp σ) :
    ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 = ⊤ := by
  set W := ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 with hW
  have h1 : ∀ g, ∀ x ∈ W, π.finPart g x ∈ W := fun g x hx => by
    refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.finPart g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  have h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → ∀ x ∈ W, T x ∈ W := fun T hT x hx => by
    refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k => exact h1 k x hx
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X g) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with e | e
  · have e' : W = ⊥ := hi (e.trans (Submodule.map_bot _).symm)
    obtain ⟨f, h0, hf⟩ := h
    exact absurd (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e') ⟨f, hf⟩)) h0
  · exact hi (e.trans (Submodule.map_subtype_top _).symm)

end UpperTheory.V.Sd.Wc

/- English proof (translation)
Introduce `P F _ _ _ π hreg`. Take `⟨τ, h1⟩` from `UpperTheory.V.Br.finCompR P.admR F 2 π`. Conclude with `⟨τ, h1, sep_of_sum τ.ρ τ.irred π.finPart (sum_top π τ h1)⟩`.
-/
theorem UpperTheory.V.Sd.Wc.finProj :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.Wc.FinProj := by
  intro P F _ _ _ π hreg
  obtain ⟨τ, h1⟩ := UpperTheory.V.Br.finCompR P.admR F 2 π
  exact ⟨τ, h1, sep_of_sum τ.ρ τ.irred π.finPart (sum_top π τ h1)⟩
