import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.TypeVLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.J.D.TypeVAux
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
Establish `key : ∀ (u : Multiset (Γ →* ℂ)) (g : Γ), Finsupp.linearCombination ℂ (fun f : Γ →* ℂ => (f : Γ → ℂ)) (u.map fun f => Finsupp.single f (1 : ℂ)).sum g = (u.map fun f => f g).sum` using `fun u g => by`. Proceed by induction on `u using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a u ih => simp [ih]`. Establish `cnt : ∀ (u : Multiset (Γ →* ℂ)) (f : Γ →* ℂ), (u.map fun f => Finsupp.single f (1 : ℂ)).sum f = (u.count f : ℂ)` using `fun u f => by`.

Proceed by induction on `u using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a u ih`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons, Finsupp.single_apply]`. Distinguish the cases in `e : a = f`.

Simplify using `[e, add_comm]`. Simplify using `[e, Ne.symm e]`. Establish `h1` using `linearIndependent_monoidHom Γ ℂ (funext fun g => (key s g).trans ((h g).trans (key t g).symm))`. Use extensionality with `f`. Establish `h2` using `(cnt s f).symm.trans ((congrArg (fun u => u f) h1).trans (cnt t f))`.

Conclude with `h2` after adjusting the coercions.
-/
private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t := by
  classical
  have key : ∀ (u : Multiset (Γ →* ℂ)) (g : Γ),
      Finsupp.linearCombination ℂ (fun f : Γ →* ℂ => (f : Γ → ℂ))
        (u.map fun f => Finsupp.single f (1 : ℂ)).sum g = (u.map fun f => f g).sum := fun u g => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih => simp [ih]
  have cnt : ∀ (u : Multiset (Γ →* ℂ)) (f : Γ →* ℂ),
      (u.map fun f => Finsupp.single f (1 : ℂ)).sum f = (u.count f : ℂ) := fun u f => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons, Finsupp.single_apply]
      by_cases e : a = f
      · simp [e, add_comm]
      · simp [e, Ne.symm e]
  have h1 := linearIndependent_monoidHom Γ ℂ (funext fun g => (key s g).trans ((h g).trans (key t g).symm))
  ext f
  have h2 := (cnt s f).symm.trans ((congrArg (fun u => u f) h1).trans (cnt t f))
  exact_mod_cast h2
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Set `x : Fin n → IrrGL k` to `fun i => IrrGL.ofChar (ω i) (hω i)`. Establish `hx : ∀ i, (x i).IsCusp` using `fun i => IrrGL.isCusp_ofChar _ _`. Establish `hd : ∑ i, (x i).1 = n` using `by simp [x, IrrGL.ofChar]`. Establish `hnu : ∀ i j, x j ≠ (x i).nu 1` using `fun i j e => by`. Simplify using `only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e`.

Conclude with `h i j e`. Establish `hP : (prodIrr x hd).IsIrreducible` using `GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i)) (fun i => (single_spec (hx i)).2.1)`. Set `e₀` to `Equiv.sigmaUnique (Fin n) fun _ => Fin 1`. Take `⟨p⟩` from `(Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (x i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ω i))`. Establish `hM : (multiProd e₀ fun i => detRep (Fin 1) (ω i)).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans (multiProdEquiv (stdBlocks (fun i => (x i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (ω i) (hω i)))).symm hP`.

Use `haveI := nontrivial_of_irreducible hM`. Use `haveI := nontrivial_of_isSubquotient (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω)`. Take `⟨E⟩` from `equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv E hM`.
-/
private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  let x : Fin n → IrrGL k := fun i => IrrGL.ofChar (ω i) (hω i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by simp [x, IrrGL.ofChar]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i))
      (fun i => (single_spec (hx i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (x i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ω i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ω i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (x i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ω i) (hω i)))).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI := nontrivial_of_isSubquotient (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω)
  obtain ⟨E⟩ := equiv_of_isSubquotient (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hM
end Loc
section WD
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
private theorem charPol_ofChar (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
/- English proof (translation)
Take `⟨s, hs⟩` from `SupportRing.exists_hasSupport hZ x`. Establish `hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y` using `fun y hy => by`. Take `⟨ξ, hξ, e⟩` from `exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by`. Use `Dvd.dvd.trans ?_ (hp g).dvd` and prove the remaining obligations. Rewrite using `[H.supp _ s hs g]`.

Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)`. Take `⟨χ, hχ, rfl⟩` from `ha.factor ξ hξ`. Establish `e'` using `e.trans (H.one χ hχ).symm`. Establish `hy1 : y.1 = 1`. Rewrite using `[← H.dim y, e', H.dim]`.

Simplify using `[IrrGL.ofChar]`. Establish `hg : UpperTheory.Zero.LLC.Good y` using `⟨{y}, hasSupport_self (hs.isCusp hy), fun u hu => Or.inl (by rwa [Multiset.mem_singleton.1 hu])⟩`. Conclude with `⟨χ, hχ, H.inj _ _ hg e'.symm⟩`. Set `S` to `{χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}`. Set `F : S → IrrGL (w.adicCompletion E)` to `fun χ => IrrGL.ofChar χ.1 χ.2`.

Take `⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s` from `haveI : CanLift (IrrGL (w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩ (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by`. Take `⟨χ, hχ, e⟩` from `hch y hy`. Conclude with `⟨⟨χ, hχ⟩, e⟩`. Set `c : S → (w.adicCompletion E)ˣ →* ℂ` to `fun χ => (Units.coeHom ℂ).comp χ.1`. Establish `hc : Function.Injective c` using `fun χ ψ e => Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))`.

Set `t' : Multiset S` to `Finset.univ.val.map fun i => ⟨ω i, hω i⟩`. Establish `htt : t = t'`. Use `Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)` and prove the remaining obligations. Take `⟨g, rfl⟩` from `ha.surj y`. Establish `h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod = (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod`.

Establish `h2` using `(H.supp x _ hs g).symm.trans (hp g)`. Simplify using `only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢`. Rewrite `h2` using `[Finset.prod_eq_multiset_prod]`. Use `Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2` and prove the remaining obligations. Conclude with `(charPol_ofChar H χ.1 χ.2 g).symm`.

Establish `h3` using `congrArg Polynomial.roots h1`. Rewrite `h3` using `[roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C]`. Rewrite using `[h3]`. Rewrite `hs` using `[htt, Multiset.map_map]`. Conclude with `hs`.
-/
private theorem hasSupport_of_charPol (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    (x : IrrGL (w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) (hp : ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ))) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) := by
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    have e' := e.trans (H.one χ hχ).symm
    have hy1 : y.1 = 1 := by
      rw [← H.dim y, e', H.dim]
      simp [IrrGL.ofChar]
    have hg : UpperTheory.Zero.LLC.Good y :=
      ⟨{y}, hasSupport_self (hs.isCusp hy), fun u hu => Or.inl (by rwa [Multiset.mem_singleton.1 hu])⟩
    exact ⟨χ, hχ, H.inj _ _ hg e'.symm⟩
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
/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _`. Take `⟨b, hb, hN⟩` from `hm`. Take `⟨ψ, hc, h1, hgen⟩` from `hg`. Take `⟨c, Δ, x, hd, hun, hL, ⟨φ⟩⟩` from `Lc.gen _ n _ σ.ρ σ.smooth σ.irred ⟨ψ, hc, h1, (GlobalTheory.Whittaker.isGeneric_iff_isGenericFor ψ σ.ρ).1 hgen⟩`. Establish `hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2))` using `fun i => (hω i).mul (isSmoothChar_absPow _)`.

Establish `e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0` using `by push_cast; ring`. Establish `e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i)` using `fun i => IrrGL.tw_ofChar _ _ _ _`. Establish `e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred`. Rewrite using `[algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]`. Establish `hs0 : HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (Finset.univ.val.map fun i => IrrGL.ofChar _ (hμ i))`.

Establish `h2` using `SupportRing.hasSupport_nu (hasSupport_of_charPol Lc.zel H (algNorm σ) ω hω hp) (((n : ℂ) - 1) / 2)`. Establish `key : ∀ (x y : IrrGL (w.adicCompletion E)) s, x = y → HasSupport x.rep s → HasSupport y.rep s`. Introduce and unpack `_ _ _ rfl h`. Conclude with `h`. Establish `h3` using `key _ _ _ e2 h2`.

Simplify `h3` using `only [Multiset.map_map, Function.comp_def, e1]`. Establish `hm0 : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).mono0`. Establish `h2` using `(WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN`. Rewrite `h2` using `[hb, algNorm, H.nu_eq, WD.monomial_twist_iff]`. Then use the resulting hypothesis. Establish `hIsL : IsL ((List.ofFn Δ : List _) : Multiset _) σ.ρ` using `⟨c, x, hd, ⟨Δ, ⟨Fin.univ_val_map _, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩, (isCosocle_self σ.irred).of_equiv (.refl _) φ⟩`.

Establish `hIsL'` using `hIsL.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)`. Rewrite `hm0` using `[H.langlands _ _ hIsL']`. Establish `hlen : ∀ i, (Δ i).len = 1` using `fun i => by`. Establish `hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2))`. Rewrite using `[← H.nu_eq]`.

Conclude with `(H.cusp _).1 ((Δ i).isCusp_first.nu _)`. Establish `hmi : (((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)).lpChar (WD.lpSp h (Δ i).len)).mono0` using `GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm0 _ (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)`. Establish `hpos` using `(Δ i).len_pos`. Assume the negation of the conclusion as `hne`. Conclude with `GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi`.

Establish `hms` using `hasSupport_msupp_of_isL Lc.zel _ _ _ hIsL'`. Establish `heq` using `SupportUnique.hasSupport_unique Lc.geo Lc.bz Lc.zel _ _ _ _ hs0 hms`. Establish `hmem : ∀ i, ∃ p, IrrGL.ofChar _ (hμ i) = (Δ p).first` using `fun i => by`. Establish `hi : IrrGL.ofChar _ (hμ i) ∈ msupp ((List.ofFn Δ : List _) : Multiset _)` using `heq ▸ Multiset.mem_map_of_mem (fun i => IrrGL.ofChar _ (hμ i)) (Finset.mem_univ_val i)`. Take `⟨D, hD, hy⟩` from `Multiset.mem_bind.1 hi`.

Take `⟨p, rfl⟩` from `List.mem_ofFn.1 (by simpa using hD)`. Take `⟨j, hj, e⟩` from `Segment.mem_carrier.1 (Segment.mem_ms.1 hy)`. Take `rfl : j = 0` from `by rw [hlen p] at hj; omega`. Conclude with `⟨p, by rw [← e]; simp⟩`. Establish `eΔ : ∀ p, Δ p = Segment.single (Δ p).first (Δ p).isCusp_first` using `fun p => Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, hlen p])`.

Establish `hne : ∀ i j, ω j * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2) ≠ (ω i * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2)) * absPow (w.adicCompletion E) 1` using `fun i j e => by`. Take `⟨p, ep⟩` from `hmem i`. Take `⟨q, eq⟩` from `hmem j`. Establish `hnu : (Δ q).first = (Δ p).first.nu 1`. Rewrite using `[← ep, ← eq]`.

Simplify using `only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`. Conclude with `e`. Establish `hself : (Δ p).first ≠ (Δ p).first.nu 1` using `fun e3 => by`. Use `GlobalTheory.UnlinkedMono.lpTw_one_ne (rc (Δ p).first) (by rw [H.dim]; exact (Δ p).isCusp_first.1) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hpq : p ≠ q` using `fun e3 => hself (by rw [← hnu, e3])`. Use `hun p q hpq ?_` and prove the remaining obligations. Rewrite using `[eΔ p, eΔ q]`. Conclude with `GlobalTheory.UnlinkedFirst.single_linked_single_nu _ _ hself hnu`. Establish `hs1` using `hs0.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm`.

Take `⟨hi, hq⟩` from `(UpperTheory.Gal.LocD.ofSupport_holds _ n σ.V σ.ρ _ hμ).1 hs1`. Take `⟨E'⟩` from `hq.nonempty_equiv hi (prinSeries_irreducible _ hμ hne)`. Conclude with `⟨E'.symm⟩`.
-/
theorem nonempty_equiv_principal_series_of_char_poly_of_generic (Lc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) (hp : ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ)))
    (hm : ∃ b : WDRep h (Fin n → ℂ), WD.mk b = rc (algNorm σ) ∧ b.N = 0)
    (hg : ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ σ.ρ) :
    Nonempty (σ.ρ.Equiv (PS ω)) := by
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨b, hb, hN⟩ := hm
  obtain ⟨ψ, hc, h1, hgen⟩ := hg
  obtain ⟨c, Δ, x, hd, hun, hL, ⟨φ⟩⟩ := Lc.gen _ n _ σ.ρ σ.smooth σ.irred
    ⟨ψ, hc, h1, (GlobalTheory.Whittaker.isGeneric_iff_isGenericFor ψ σ.ρ).1 hgen⟩
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
  have hs0 : HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep
      (Finset.univ.val.map fun i => IrrGL.ofChar _ (hμ i)) := by
    have h2 := SupportRing.hasSupport_nu (hasSupport_of_charPol Lc.zel H (algNorm σ) ω hω hp) (((n : ℂ) - 1) / 2)
    have key : ∀ (x y : IrrGL (w.adicCompletion E)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
      rintro _ _ _ rfl h; exact h
    have h3 := key _ _ _ e2 h2
    simpa only [Multiset.map_map, Function.comp_def, e1] using h3
  have hm0 : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).mono0 := by
    have h2 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN
    rwa [hb, algNorm, H.nu_eq, WD.monomial_twist_iff] at h2
  have hIsL : IsL ((List.ofFn Δ : List _) : Multiset _) σ.ρ :=
    ⟨c, x, hd, ⟨Δ, ⟨Fin.univ_val_map _, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self σ.irred).of_equiv (.refl _) φ⟩
  have hIsL' := hIsL.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  rw [H.langlands _ _ hIsL'] at hm0
  have hlen : ∀ i, (Δ i).len = 1 := fun i => by
    have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
      rw [← H.nu_eq]; exact (H.cusp _).1 ((Δ i).isCusp_first.nu _)
    have hmi : (((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)).lpChar (WD.lpSp h (Δ i).len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm0 _ (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    have hpos := (Δ i).len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  have hms := hasSupport_msupp_of_isL Lc.zel _ _ _ hIsL'
  have heq := SupportUnique.hasSupport_unique Lc.geo Lc.bz Lc.zel _ _ _ _ hs0 hms
  have hmem : ∀ i, ∃ p, IrrGL.ofChar _ (hμ i) = (Δ p).first := fun i => by
    have hi : IrrGL.ofChar _ (hμ i) ∈ msupp ((List.ofFn Δ : List _) : Multiset _) :=
      heq ▸ Multiset.mem_map_of_mem (fun i => IrrGL.ofChar _ (hμ i)) (Finset.mem_univ_val i)
    obtain ⟨D, hD, hy⟩ := Multiset.mem_bind.1 hi
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 (by simpa using hD)
    obtain ⟨j, hj, e⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
    obtain rfl : j = 0 := by rw [hlen p] at hj; omega
    exact ⟨p, by rw [← e]; simp⟩
  have eΔ : ∀ p, Δ p = Segment.single (Δ p).first (Δ p).isCusp_first := fun p =>
    Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, hlen p])
  have hne : ∀ i j, ω j * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2) ≠
      (ω i * absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2)) * absPow (w.adicCompletion E) 1 := fun i j e => by
    obtain ⟨p, ep⟩ := hmem i
    obtain ⟨q, eq⟩ := hmem j
    have hnu : (Δ q).first = (Δ p).first.nu 1 := by
      rw [← ep, ← eq]
      simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
      exact e
    have hself : (Δ p).first ≠ (Δ p).first.nu 1 := fun e3 => by
      refine GlobalTheory.UnlinkedMono.lpTw_one_ne (rc (Δ p).first) (by rw [H.dim]; exact (Δ p).isCusp_first.1) ?_
      calc (rc (Δ p).first).lpTw 1 = rc ((Δ p).first.nu ((1 : ℝ) : ℂ)) := (H.nu_eq _ 1).symm
        _ = rc (Δ p).first := by rw [Complex.ofReal_one, ← e3]
    have hpq : p ≠ q := fun e3 => hself (by rw [← hnu, e3])
    refine hun p q hpq ?_
    rw [eΔ p, eΔ q]
    exact GlobalTheory.UnlinkedFirst.single_linked_single_nu _ _ hself hnu
  have hs1 := hs0.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds _ n σ.V σ.ρ _ hμ).1 hs1
  obtain ⟨E'⟩ := hq.nonempty_equiv hi (prinSeries_irreducible _ hμ hne)
  exact ⟨E'.symm⟩
end WD
end UpperTheory.V.Z.J.D.TypeVAux
end
end
