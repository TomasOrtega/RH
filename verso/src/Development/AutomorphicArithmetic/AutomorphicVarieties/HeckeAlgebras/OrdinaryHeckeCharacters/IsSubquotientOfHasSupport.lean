import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreTer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨q, hq⟩` from `hd`. Establish `h0` using `congrArg (Polynomial.aeval f) hq`. Rewrite `h0` using `[map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`. Establish `hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple` using `Module.End.isSemisimple_sub_algebraMap_iff.2 hf`. Use `sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)` as an intermediate fact.

Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.
-/
private theorem eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum s t h`.
-/
private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t :=
  _root_.UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum s t h

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨m, b, rfl, hirr⟩` from `hz`. Establish `hc : ∀ g k, b.ρ g * b.ρ k = b.ρ k * b.ρ g` using `fun g k => by`. Establish `h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1`. Establish `h2` using `hd ((k * g)⁻¹ * (g * k))`. Establish `h3 : ∀ j, η j ((k * g)⁻¹ * (g * k)) = 1` using `fun j => by`.

Rewrite using `[map_mul, map_inv, map_mul, map_mul, mul_comm (η j g), inv_mul_cancel]`. Simplify using `only [h3, Units.val_one, Finset.prod_const, WD.charPol_mk] at h2`. Conclude with `eq_one_of_charpoly_dvd _ (b.semisimple _) h2`. Rewrite using `[← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]`. Establish `hsub : ∀ S : Submodule ℂ (Fin m → ℂ), (∀ g v, v ∈ S → b.ρ g v ∈ S) → S = ⊥ ∨ S = ⊤` using `fun S hS => by`.

Break down `hirr.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h` into its components or cases. Conclude with `Or.inl (congrArg Subrepresentation.toSubmodule h)`. Conclude with `Or.inr (congrArg Subrepresentation.toSubmodule h)`. Use `haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hirr`. Establish `hsc : ∀ g, ∃ c : ℂ, ∀ v, b.ρ g v = c • v` using `fun g => by`.

Take `⟨c, hcv⟩` from `Module.End.exists_eigenvalue (b.ρ g)`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Break down `hsub (Module.End.eigenspace (b.ρ g) c) (fun k u hu => by` into its components or cases. Rewrite `hu`, the goal using `[Module.End.mem_eigenspace_iff]`. Use `LinearMap.congr_fun (hc g k) u` as an intermediate fact.

Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hu, map_smul]) with h | h`. Conclude with `absurd h (Module.End.hasEigenvalue_iff.mp hcv)`. Conclude with `Module.End.mem_eigenspace_iff.mp (h ▸ Submodule.mem_top)`. Establish `hm : m = 1`.

Take `⟨v, hv⟩` from `exists_ne (0 : Fin m → ℂ)`. Break down `hsub (Submodule.span ℂ {v}) (fun g u hu => by` into its components or cases. Take `⟨c, h⟩` from `hsc g`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hu) with h | h`.

Conclude with `absurd (Submodule.span_singleton_eq_bot.mp h) hv`. Use `finrank_span_singleton (K := ℂ) hv` as an intermediate fact. Rewrite `this` using `[h, finrank_top]`. Simplify using `using this`. Substitute `hm` using the available equality.

Establish `hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v` using `fun f v => by`. Establish `hv : v = v 0 • (1 : Fin 1 → ℂ)`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Use `conv_lhs => rw [hv, map_smul]`. Simplify using `[mul_comm]`. Set `c : Weil h →* ℂ` to `{ toFun := fun σ => b.ρ σ 1 0 map_one' := by simp map_mul' := fun σ τ => by`.

Rewrite using `[map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]`. Simplify using `}`. Establish `hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1` using `fun σ hσ => by`. Use `ext`. Use `show b.ρ σ 1 0 = 1`.

Simplify using `[hσ]`. Establish `hN : b.N = 0`. Take `⟨n, hn⟩` from `b.nilpotent`. Establish `e : b.N = b.N 1 0 • (1 : Module.End ℂ (Fin 1 → ℂ))` using `LinearMap.ext fun v => by`. Rewrite using `[hsc b.N v]`.

Both sides reduce to the same expression. Rewrite `hn` using `[e, _root_.smul_pow, one_pow]`. Use `congrFun (LinearMap.congr_fun hn 1) 0` as an intermediate fact. Establish `h2 : b.N 1 0 ^ n = 0` using `by simpa using this`. Rewrite using `[e, pow_eq_zero_iff'.mp h2 |>.1, zero_smul]`.

Use `⟨c.toHomUnits, b.smooth.of_le hker, ?_⟩` and prove the remaining obligations. Use `WD.sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[WDRep.ofChars_ρ, diagEnd_apply, LinearEquiv.refl_apply, LinearEquiv.refl_apply, hsc (b.ρ σ) v]`. Both sides reduce to the same expression.

Simplify using `[hN]`.
-/
private theorem exists_char {z : WD h} (hz : IsIrrWD z) {n : ℕ} (η : Fin n → Weil h →* ℂˣ)
    (hd : ∀ g, z.charPol g ∣ ∏ j, (X - C (η j g : ℂ))) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), z = WD.lpOfChar h ξ hξ := by
  obtain ⟨m, b, rfl, hirr⟩ := hz
  have hc : ∀ g k, b.ρ g * b.ρ k = b.ρ k * b.ρ g := fun g k => by
    have h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1 := by
      have h2 := hd ((k * g)⁻¹ * (g * k))
      have h3 : ∀ j, η j ((k * g)⁻¹ * (g * k)) = 1 := fun j => by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (η j g), inv_mul_cancel]
      simp only [h3, Units.val_one, Finset.prod_const, WD.charPol_mk] at h2
      exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]
  have hsub : ∀ S : Submodule ℂ (Fin m → ℂ), (∀ g v, v ∈ S → b.ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := fun S hS => by
    rcases hirr.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hirr
  have hsc : ∀ g, ∃ c : ℂ, ∀ v, b.ρ g v = c • v := fun g => by
    obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue (b.ρ g)
    refine ⟨c, fun v => ?_⟩
    rcases hsub (Module.End.eigenspace (b.ρ g) c) (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      have := LinearMap.congr_fun (hc g k) u
      simp only [Module.End.mul_apply] at this
      rw [this, hu, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.mp hcv)
    · exact Module.End.mem_eigenspace_iff.mp (h ▸ Submodule.mem_top)
  have hm : m = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
    rcases hsub (Submodule.span ℂ {v}) (fun g u hu => by
      obtain ⟨c, h⟩ := hsc g
      rw [h]; exact Submodule.smul_mem _ _ hu) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h, finrank_top] at this
      simpa using this
  subst hm
  have hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v := fun f v => by
    have hv : v = v 0 • (1 : Fin 1 → ℂ) := by
      funext i; rw [Subsingleton.elim i 0]; simp
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  let c : Weil h →* ℂ :=
    { toFun := fun σ => b.ρ σ 1 0
      map_one' := by simp
      map_mul' := fun σ τ => by
        rw [map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]; simp }
  have hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1 := fun σ hσ => by
    ext
    show b.ρ σ 1 0 = 1
    simp [hσ]
  have hN : b.N = 0 := by
    obtain ⟨n, hn⟩ := b.nilpotent
    have e : b.N = b.N 1 0 • (1 : Module.End ℂ (Fin 1 → ℂ)) := LinearMap.ext fun v => by
      rw [hsc b.N v]; rfl
    rw [e, _root_.smul_pow, one_pow] at hn
    have := congrFun (LinearMap.congr_fun hn 1) 0
    have h2 : b.N 1 0 ^ n = 0 := by simpa using this
    rw [e, pow_eq_zero_iff'.mp h2 |>.1, zero_smul]
  refine ⟨c.toHomUnits, b.smooth.of_le hker, ?_⟩
  refine WD.sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, LinearEquiv.refl_apply, LinearEquiv.refl_apply, hsc (b.ρ σ) v]
    rfl
  · simp [hN]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (w.adicCompletion E) → WD h}

/- English proof (translation)
Rewrite using `[H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]`. Simplify using the standard rewrite rules.
-/
private theorem charPol_ofChar (H : Laws a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

/- English proof (translation)
Use `⟨fun hs g => ?_, fun hp => ?_⟩` and prove the remaining obligations. Rewrite using `[H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]`. Conclude with `congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => charPol_ofChar H _ _ g)`. Take `⟨s, hs⟩` from `SupportRing.exists_hasSupport hZ x`. Establish `hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y` using `fun y hy => by`.

Take `⟨ξ, hξ, e⟩` from `exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by`. Use `Dvd.dvd.trans ?_ (hp g).dvd` and prove the remaining obligations. Rewrite using `[H.supp _ s hs g]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)`. Take `⟨χ, hχ, rfl⟩` from `ha.factor ξ hξ`.

Conclude with `⟨χ, hχ, (H.bij.1 (e.trans (H.one χ hχ).symm)).symm⟩`. Set `S` to `{χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}`. Set `F : S → IrrGL (w.adicCompletion E)` to `fun χ => IrrGL.ofChar χ.1 χ.2`. Take `⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s` from `haveI : CanLift (IrrGL (w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩ (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by`. Take `⟨χ, hχ, e⟩` from `hch y hy`.

Conclude with `⟨⟨χ, hχ⟩, e⟩`. Set `c : S → (w.adicCompletion E)ˣ →* ℂ` to `fun χ => (Units.coeHom ℂ).comp χ.1`. Establish `hc : Function.Injective c` using `fun χ ψ e => Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))`. Set `t' : Multiset S` to `Finset.univ.val.map fun i => ⟨ω i, hω i⟩`. Establish `htt : t = t'`.

Use `Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)` and prove the remaining obligations. Take `⟨g, rfl⟩` from `ha.surj y`. Establish `h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod = (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod`. Establish `h2` using `(H.supp x _ hs g).symm.trans (hp g)`. Simplify using `only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢`.

Rewrite `h2` using `[Finset.prod_eq_multiset_prod]`. Use `Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2` and prove the remaining obligations. Conclude with `(charPol_ofChar H χ.1 χ.2 g).symm`. Establish `h3` using `congrArg Polynomial.roots h1`. Rewrite `h3` using `[roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C]`.

Rewrite using `[h3]`. Rewrite `hs` using `[htt, Multiset.map_map]`. Conclude with `hs`.
-/
private theorem hasSupport_iff (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : Laws a ha ε rc)
    (x : IrrGL (w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) ↔
      ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ)) := by
  refine ⟨fun hs g => ?_, fun hp => ?_⟩
  · rw [H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => charPol_ofChar H _ _ g)
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    exact ⟨χ, hχ, (H.bij.1 (e.trans (H.one χ hχ).symm)).symm⟩
  let S := {χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (w.adicCompletion E) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := hch y hy
      exact ⟨⟨χ, hχ⟩, e⟩
  let c : S → (w.adicCompletion E)ˣ →* ℂ := fun χ => (Units.coeHom ℂ).comp χ.1
  have hc : Function.Injective c := fun χ ψ e =>
    Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))
  let t' : Multiset S := Finset.univ.val.map fun i => ⟨ω i, hω i⟩
  have htt : t = t' := by
    refine Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)
    obtain ⟨g, rfl⟩ := ha.surj y
    have h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod =
        (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod := by
      have h2 := (H.supp x _ hs g).symm.trans (hp g)
      simp only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢
      rw [Finset.prod_eq_multiset_prod] at h2
      refine Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2
      exact (charPol_ofChar H χ.1 χ.2 g).symm
    have h3 := congrArg Polynomial.roots h1
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
    rw [h3]
  rw [htt, Multiset.map_map] at hs
  exact hs

end

/- English proof (translation)
Establish `hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n` using `by simp [IrrGL.ofChar]`. Use `IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)` and prove the remaining obligations. Take `⟨Z, Ψ, -, hΨ, -⟩` from `hZ k`. Establish `h1` using `SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr`. Take `⟨hp, ep⟩` from `SupportRing.prodIrr_cls hΨ _ hd`.

Use `SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_` and prove the remaining obligations. Establish `h2` using `h1 (IrrGL.of τ.ρ τ.smooth τ.irr)`. Rewrite `h2` using `[SupportRing.pc_map, ← ep]`. Establish `e1 : ∀ (A : GrothGL k) (y : IrrGL k), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1`. Introduce `A y`.

Rewrite using `[SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]`. Rewrite `h2` using `[e1]`. Introduce `h3`. Rewrite `h2` using `[h3]`. Conclude with `absurd h2 (by norm_num)`.
-/
private theorem isSubquotient_of_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (μ : Fin n → kˣ →* ℂˣ)
    (hμ : ∀ i, IsSmoothChar (μ i)) (hs : HasSupport τ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (μ i) (hμ i))) :
    IsSubquotient τ.ρ (prinSeries μ) := by
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL k), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ n w A h a ha rc hrc σ ω hω`. Take `⟨a', ha', ε, -, H⟩` from `hrc`. Choose the witnesses or unpack the hypotheses as in `rfl : a' = a := by`. Take `⟨art, hart⟩` from `P.aut.art L Ω`. Establish `hinj` using `GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w`.

Conclude with `MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)`. Use `haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _`. Establish `hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2))` using `fun i => (hω i).mul (isSmoothChar_absPow _)`. Establish `e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0` using `by push_cast; ring`. Establish `e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i)` using `fun i => IrrGL.tw_ofChar _ _ _ _`.

Rewrite using `[← hasSupport_iff P.loc.zel H (algNorm σ) ω hω]`. Set `τ : IrrRep (GL (Fin n) (w.adicCompletion L))` to `⟨_, σ.ρ, σ.smooth, σ.irred⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Establish `h1` using `(hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)`.

Establish `h2` using `SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)`. Simplify using `only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2`. Conclude with `h2`. Introduce `hs`. Establish `h2` using `SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)`.

Establish `e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred`. Rewrite using `[algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]`. Establish `key : ∀ (x y : IrrGL (w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s`. Introduce and unpack `_ _ _ rfl h`. Conclude with `h`.

Establish `h3` using `(key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm`. Simplify using `only [Multiset.map_map, Function.comp_def, e1] at h3`. Conclude with `isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3`.
-/
theorem UpperTheory.V.Hi.psRec :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, IsRec h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (IsSubquotient σ.ρ (PS ω) ↔ ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ))) := by
  intro P L Ω _ _ _ _ _ n w A h a ha rc hrc σ ω hω
  obtain ⟨a', ha', ε, -, H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  rw [← hasSupport_iff P.loc.zel H (algNorm σ) ω hω]
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  constructor
  · intro hs
    have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
    have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
    simp only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2
    exact h2
  · intro hs
    have h2 := SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)
    have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
    have key : ∀ (x y : IrrGL (w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
      rintro _ _ _ rfl h; exact h
    have h3 := (key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    simp only [Multiset.map_map, Function.comp_def, e1] at h3
    exact isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3
