import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsLinSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SpLocIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.FreeSummand
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilMapMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ChiApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpParts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Pa.Lev.OpP

/- English proof (translation)
Use `letI : Module Λ W := Module.compHom W (algebraMap Λ R)`. Use `haveI : IsScalarTower Λ R W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Take `⟨N, _, _, _, _, i, pr, hpi, hC, hX, hr, hc⟩` from `nilPart (Λ := Λ) (fun p => act1 (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p))) fun _ _ => (Commute.all _ _).map act1`. Establish `hinj : Function.Injective i` using `Function.LeftInverse.injective hpi`. Establish `evT : ∀ p, ev (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p)) = MvPowerSeries.X p` using `fun p => by`.

Rewrite using `[map_sub, evC, evX, add_sub_cancel_left]`. Establish `evy : ∀ p, s (MvPowerSeries.X p) = ev (MvPolynomial.X (.inr p))` using `fun p => by simp [hs, evX]`. Establish `hi : ∀ t x, i (ev t • x) = act1 t (i x)` using `fun t => by`. Proceed by induction on `t using MvPolynomial.induction_on with`. Consider the case `C c => intro x`.

Rewrite using `[evC, hC]`. Conclude with `(LinearMap.congr_fun (act1.commutes c) _).symm`. Consider the case `add b c hb hc => intro x`. Rewrite using `[map_add, add_smul, map_add, hb, hc, map_add, LinearMap.add_apply]`. Consider the case `mul_X b p hb`.

Introduce `x`. Rewrite using `[map_mul, mul_smul, hb, evX, add_smul, map_add, hC, hX, map_mul, Module.End.mul_apply]`. Simplify using the standard rewrite rules. Establish `hcomm : ∀ t t' m, act1 t (act1 t' m) = act1 t' (act1 t m)` using `fun t t' m => LinearMap.congr_fun ((Commute.all t t').map act1).eq m`. Establish `hpr : ∀ t m, pr (act1 t m) = ev t • pr m` using `fun t m => hinj ((hc ((act1 t).restrictScalars Λ) (fun _ _ => hcomm _ _ _) m).trans (hi _ _).symm)`.

Establish `hρc : ∀ g m, i (pr (ρ g m)) = ρ g (i (pr m))` using `fun g => LinearMap.congr_fun (del_gen hl ((Submonoid.centralizer {(i ∘ₗ pr : Module.End Λ M)}).comap ρ) (fun p => by`. Introduce and unpack `_ rfl`. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Use `show i (pr (ρ _ m)) = ρ _ (i (pr m))`. Rewrite using `[hρ p.1 p.2, hρ p.1 p.2, hpr, hi]) g _ rfl)`.

Take `⟨rk, e, he⟩` from `freePart ρ hl hlm hP i pr hpi hρc s fun p x => by`. Rewrite using `[hρ p.1 p.2, ← hi, map_add, map_add, map_one, map_one, evy]`. Take `⟨j, κ, hj, hκ, hκj, hjr⟩` from `quotPart act1 actw tr hsurj hker (fun p => hu p.1 p.2) ut ev i pr hpi hi hpr hr (fun p => s (MvPowerSeries.X p)) evy`. Take `⟨_, hnS, η, φ, ψ, ηC, ηX, hφ, hψ, hψφ, hφn, hφψ⟩` from `spPart (Λ := Λ) P hm hd β hβ ut ub hub actw f two`. Establish `hη : ∀ t, θ (ev (MvPolynomial.rename Sum.inl t)) = η t` using `fun t => by`.

Proceed by induction on `t using MvPolynomial.induction_on with`. Consider the case `C c => rw [MvPolynomial.rename_C, evC, θC, ηC]`. Consider the case `add b c hb hc => simp only [map_add, hb, hc]`. Consider the case `mul_X b p hb`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, hb, MvPolynomial.rename_X, evX, map_add, θC, θl, ηX p.1 p.2, Sp.u, map_add, Sum.elim_inl, ← hub p.1 p.2]`.

Both sides reduce to the same expression. Use `haveI : Module.Finite Λ N := Module.Finite.of_surjective pr fun x => ⟨_, hpi x⟩`. Set `I : Submodule (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) N` to `Ideal.span (Set.range fun p => s (MvPowerSeries.X p)) • ⊤`. Establish `hy : ∀ p (x : N ⧸ I), (MvPowerSeries.X (.inr p) : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) • x = 0` using `fun p x => by`. Take `⟨x, rfl⟩` from `I.mkQ_surjective x`.

Rewrite using `[← map_smul, ← hs]`. Conclude with `(Submodule.Quotient.mk_eq_zero I).2 (Submodule.smul_mem_smul (Ideal.subset_span ⟨p, rfl⟩) trivial)`. Establish `hnX : ∀ p (k : ℕ) (x : N ⧸ I), ∃ d : ℕ, (RingHom.id (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R)) (MvPowerSeries.X p) ^ d • x ∈ (maximalIdeal Λ ^ k • ⊤ : Submodule Λ (N ⧸ I))` using `fun p k x => by`. Take `⟨x, rfl⟩` from `I.mkQ_surjective x`. Take `⟨d, hd⟩` from `mem_topNil_iff_exists.1 (hr.le ⟨x, rfl⟩) p k`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `h1` using `nilMap _ (I.mkQ.restrictScalars Λ ∘ₗ pr).toAddMonoidHom (map_smul (I.mkQ.restrictScalars Λ ∘ₗ pr)) hd`. Establish `h2 : ((act1 (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p))).restrictScalars Λ ^ d) (i x) = act1 ((MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p)) ^ d) (i x)`. Rewrite using `[map_pow, Module.End.pow_apply, Module.End.pow_apply]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `I.mkQ (pr _) ∈ _ at h1`. Rewrite `h1` using `[h2, hpr, hpi, map_pow, evT, map_smul]`. Then use the resulting hypothesis. Establish `hnS' : ∀ p (k : ℕ) (z : Sp P ub ⊗[B] M₀), ∃ d : ℕ, θ (MvPowerSeries.X p) ^ d • z ∈ (maximalIdeal Λ ^ k • ⊤ : Submodule Λ (Sp P ub ⊗[B] M₀))`. Introduce and unpack `(p | p) k z`. Rewrite using `[θl]`.

Conclude with `hnS p k z`. Conclude with `⟨1, by rw [θr, pow_one, zero_smul]; exact zero_mem _⟩`. Establish `hθL : ∀ c, θ (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ _ c` using `fun c => by`. Rewrite using `[θC, hβ, ← IsScalarTower.algebraMap_apply]`. Establish `hidL : ∀ c, (RingHom.id (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R)) (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ _ c` using `fun c => MvPowerSeries.algebraMap_apply.symm`.

Establish `eC : ∀ c, MvPowerSeries.C c = ev (MvPolynomial.rename Sum.inl (MvPolynomial.C c : PU R q n))` using `fun c => by`. Rewrite using `[MvPolynomial.rename_C, evC]`. Establish `eX : ∀ p, MvPowerSeries.X (.inl p) = ev (MvPolynomial.rename Sum.inl (MvPolynomial.X p - MvPolynomial.C (ut p) : PU R q n))` using `fun p => by`. Rewrite using `[map_sub, MvPolynomial.rename_C, MvPolynomial.rename_X]`. Conclude with `(evT (.inl p)).symm`.

Establish `k1 : ∀ t z, κ (φ (θ (ev (MvPolynomial.rename Sum.inl t)) • z)) = ev (MvPolynomial.rename Sum.inl t) • κ (φ z)` using `fun t z => by rw [hη, hφ, hκ]`. Establish `k2 : ∀ t x, ψ (j (ev (MvPolynomial.rename Sum.inl t) • x)) = θ (ev (MvPolynomial.rename Sum.inl t)) • ψ (j x)` using `fun t z => by rw [hη, hj, hψ]`. Use `⟨N, inferInstance, inferInstance, rk, e, he, fun t ht m => hinj (by rw [hi, ht, map_zero]; rfl), κ.comp φ, ψ.comp j, psLin' θ (RingHom.id _) hθL hidL hnS' hnX _ (fun c z => ?_) ?_, psLin' (RingHom.id _) θ hidL hθL hnX hnS' _ (fun c z => ?_) ?_, fun x => ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[eC]`. Conclude with `k1 _ z`.

Introduce and unpack `(p | p) z`. Rewrite using `[eX]`. Conclude with `k1 _ z`. Rewrite using `[θr, zero_smul, map_zero]`. Conclude with `(hy p _).symm`.

Rewrite using `[eC]`. Conclude with `k2 _ z`. Introduce and unpack `(p | p) z`. Rewrite using `[eX]`. Conclude with `k2 _ z`.

Rewrite using `[θr, zero_smul, RingHom.id_apply, hy, map_zero]`. Use `show κ (φ (ψ (j x))) = _`. Rewrite using `[hφψ _ ((hjr _).2 ⟨x, rfl⟩), hκ, hκj]`. Use `show ψ (j (κ (φ z))) = _`. Take `⟨x, hx⟩` from `(hjr _).1 (hφn z)`.

Rewrite using `[hη, ← hψφ, ← hx, hκj]`.
-/
private theorem opCore {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {B M₀ : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Algebra Λ B]
    [IsLocalHom (algebraMap Λ B)] [AddCommGroup M₀] [Module B M₀] [Module Λ M₀] [IsScalarTower Λ B M₀]
    [Module.Finite Λ M₀] {l q n : ℕ} (hl : l.Prime) (hlm : (l : Λ) ∈ maximalIdeal Λ)
    (P : Fin q → Polynomial B) (hm : ∀ j, (P j).Monic) (hd : ∀ j, (P j).natDegree = n)
    {R M W : Type} [CommRing R] [Algebra Λ R] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Finite Λ M] [AddCommGroup W] [Module R W]
    (β : R →+* B) (hβ : ∀ c, β (algebraMap Λ R c) = algebraMap Λ B c) (ut : Fin q × Fin n → R) (ub : Fin q → Fin n → B)
    (hub : ∀ j i, ub j i = β (ut (j, i)))
    (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (f : PU R q n)
    (two : TwoMaps (M := M₀) β P actw f) {a : Fin q → ℕ} (ρ : Representation Λ (Del l n a) M)
    (hρ : ∀ j i m, ρ (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1)) m = act1 (1 + yV R j i) m)
    (hP : Module.Projective (MonoidAlgebra Λ (Del l n a)) ρ.asModule)
    (tr : M →ₗ[R] W) (hsurj : Function.Surjective tr)
    (hker : LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)))
    (hu : ∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m))
    (s : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R)
    (hs : ∀ p, s (MvPowerSeries.X p) = MvPowerSeries.X (.inr p))
    (θ : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R →+* Sp P ub)
    (θC : ∀ x, θ (MvPowerSeries.C x) = algebraMap B _ (β x))
    (θl : ∀ p, θ (MvPowerSeries.X (.inl p)) = Sp.mk P ub (MvPowerSeries.X p)) (θr : ∀ p, θ (MvPowerSeries.X (.inr p)) = 0)
    (ev : PUY R q n →+* MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R)
    (evC : ∀ x, ev (MvPolynomial.C x) = MvPowerSeries.C x)
    (evX : ∀ p, ev (MvPolynomial.X p) = MvPowerSeries.C (Sum.elim ut 0 p) + MvPowerSeries.X p) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) N) (rk : ℕ)
      (e : N ≃+ (Fin rk → MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a)), (∀ z m, e (s z • m) = z • e m) ∧
      (∀ t, act1 t = 0 → ∀ m : N, ev t • m = 0) ∧
      ∃ (φ : Sp P ub ⊗[B] M₀ →+ N ⧸ (Ideal.span (Set.range fun p => s (MvPowerSeries.X p)) • ⊤ : Submodule (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) N))
        (ψ : (N ⧸ (Ideal.span (Set.range fun p => s (MvPowerSeries.X p)) • ⊤ : Submodule (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) N)) →+ Sp P ub ⊗[B] M₀),
        (∀ t z, φ (θ t • z) = t • φ z) ∧ (∀ (t : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) z, ψ (t • z) = θ t • ψ z) ∧
        (∀ z, φ (ψ z) = ev (MvPolynomial.rename Sum.inl f) • z) ∧
        ∀ z, ψ (φ z) = θ (ev (MvPolynomial.rename Sum.inl f)) • z := by
  letI : Module Λ W := Module.compHom W (algebraMap Λ R)
  haveI : IsScalarTower Λ R W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨N, _, _, _, _, i, pr, hpi, hC, hX, hr, hc⟩ := nilPart (Λ := Λ)
    (fun p => act1 (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p))) fun _ _ => (Commute.all _ _).map act1
  have hinj : Function.Injective i := Function.LeftInverse.injective hpi
  have evT : ∀ p, ev (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p)) = MvPowerSeries.X p := fun p => by
    rw [map_sub, evC, evX, add_sub_cancel_left]
  have evy : ∀ p, s (MvPowerSeries.X p) = ev (MvPolynomial.X (.inr p)) := fun p => by simp [hs, evX]
  have hi : ∀ t x, i (ev t • x) = act1 t (i x) := fun t => by
    induction t using MvPolynomial.induction_on with
    | C c => intro x; rw [evC, hC]; exact (LinearMap.congr_fun (act1.commutes c) _).symm
    | add b c hb hc => intro x; rw [map_add, add_smul, map_add, hb, hc, map_add, LinearMap.add_apply]
    | mul_X b p hb =>
      intro x
      rw [map_mul, mul_smul, hb, evX, add_smul, map_add, hC, hX, map_mul, Module.End.mul_apply]
      simp
  have hcomm : ∀ t t' m, act1 t (act1 t' m) = act1 t' (act1 t m) := fun t t' m =>
    LinearMap.congr_fun ((Commute.all t t').map act1).eq m
  have hpr : ∀ t m, pr (act1 t m) = ev t • pr m := fun t m =>
    hinj ((hc ((act1 t).restrictScalars Λ) (fun _ _ => hcomm _ _ _) m).trans (hi _ _).symm)
  have hρc : ∀ g m, i (pr (ρ g m)) = ρ g (i (pr m)) := fun g =>
    LinearMap.congr_fun (del_gen hl ((Submonoid.centralizer {(i ∘ₗ pr : Module.End Λ M)}).comap ρ) (fun p => by
      rintro _ rfl
      refine LinearMap.ext fun m => ?_
      show i (pr (ρ _ m)) = ρ _ (i (pr m))
      rw [hρ p.1 p.2, hρ p.1 p.2, hpr, hi]) g _ rfl)
  obtain ⟨rk, e, he⟩ := freePart ρ hl hlm hP i pr hpi hρc s fun p x => by
    rw [hρ p.1 p.2, ← hi, map_add, map_add, map_one, map_one, evy]
  obtain ⟨j, κ, hj, hκ, hκj, hjr⟩ := quotPart act1 actw tr hsurj hker (fun p => hu p.1 p.2) ut ev i pr hpi hi hpr hr
    (fun p => s (MvPowerSeries.X p)) evy
  obtain ⟨_, hnS, η, φ, ψ, ηC, ηX, hφ, hψ, hψφ, hφn, hφψ⟩ := spPart (Λ := Λ) P hm hd β hβ ut ub hub actw f two
  have hη : ∀ t, θ (ev (MvPolynomial.rename Sum.inl t)) = η t := fun t => by
    induction t using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.rename_C, evC, θC, ηC]
    | add b c hb hc => simp only [map_add, hb, hc]
    | mul_X b p hb =>
      rw [map_mul, map_mul, map_mul, map_mul, hb, MvPolynomial.rename_X, evX, map_add, θC, θl, ηX p.1 p.2, Sp.u, map_add,
        Sum.elim_inl, ← hub p.1 p.2]
      rfl
  haveI : Module.Finite Λ N := Module.Finite.of_surjective pr fun x => ⟨_, hpi x⟩
  let I : Submodule (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) N := Ideal.span (Set.range fun p => s (MvPowerSeries.X p)) • ⊤
  have hy : ∀ p (x : N ⧸ I), (MvPowerSeries.X (.inr p) : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R) • x = 0 :=
    fun p x => by
      obtain ⟨x, rfl⟩ := I.mkQ_surjective x
      rw [← map_smul, ← hs]
      exact (Submodule.Quotient.mk_eq_zero I).2 (Submodule.smul_mem_smul (Ideal.subset_span ⟨p, rfl⟩) trivial)
  have hnX : ∀ p (k : ℕ) (x : N ⧸ I), ∃ d : ℕ,
      (RingHom.id (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R)) (MvPowerSeries.X p) ^ d • x ∈
      (maximalIdeal Λ ^ k • ⊤ : Submodule Λ (N ⧸ I)) := fun p k x => by
    obtain ⟨x, rfl⟩ := I.mkQ_surjective x
    obtain ⟨d, hd⟩ := mem_topNil_iff_exists.1 (hr.le ⟨x, rfl⟩) p k
    refine ⟨d, ?_⟩
    have h1 := nilMap _ (I.mkQ.restrictScalars Λ ∘ₗ pr).toAddMonoidHom (map_smul (I.mkQ.restrictScalars Λ ∘ₗ pr)) hd
    have h2 : ((act1 (MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p))).restrictScalars Λ ^ d) (i x) =
        act1 ((MvPolynomial.X p - MvPolynomial.C (Sum.elim ut 0 p)) ^ d) (i x) := by
      rw [map_pow, Module.End.pow_apply, Module.End.pow_apply]; rfl
    change I.mkQ (pr _) ∈ _ at h1
    rwa [h2, hpr, hpi, map_pow, evT, map_smul] at h1
  have hnS' : ∀ p (k : ℕ) (z : Sp P ub ⊗[B] M₀), ∃ d : ℕ, θ (MvPowerSeries.X p) ^ d • z ∈
      (maximalIdeal Λ ^ k • ⊤ : Submodule Λ (Sp P ub ⊗[B] M₀)) := by
    rintro (p | p) k z
    · rw [θl]; exact hnS p k z
    · exact ⟨1, by rw [θr, pow_one, zero_smul]; exact zero_mem _⟩
  have hθL : ∀ c, θ (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ _ c := fun c => by
    rw [θC, hβ, ← IsScalarTower.algebraMap_apply]
  have hidL : ∀ c, (RingHom.id (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R))
      (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ _ c := fun c => MvPowerSeries.algebraMap_apply.symm
  have eC : ∀ c, MvPowerSeries.C c = ev (MvPolynomial.rename Sum.inl (MvPolynomial.C c : PU R q n)) := fun c => by
    rw [MvPolynomial.rename_C, evC]
  have eX : ∀ p, MvPowerSeries.X (.inl p) =
      ev (MvPolynomial.rename Sum.inl (MvPolynomial.X p - MvPolynomial.C (ut p) : PU R q n)) := fun p => by
    rw [map_sub, MvPolynomial.rename_C, MvPolynomial.rename_X]
    exact (evT (.inl p)).symm
  have k1 : ∀ t z, κ (φ (θ (ev (MvPolynomial.rename Sum.inl t)) • z)) = ev (MvPolynomial.rename Sum.inl t) • κ (φ z) :=
    fun t z => by rw [hη, hφ, hκ]
  have k2 : ∀ t x, ψ (j (ev (MvPolynomial.rename Sum.inl t) • x)) = θ (ev (MvPolynomial.rename Sum.inl t)) • ψ (j x) :=
    fun t z => by rw [hη, hj, hψ]
  refine ⟨N, inferInstance, inferInstance, rk, e, he, fun t ht m => hinj (by rw [hi, ht, map_zero]; rfl),
    κ.comp φ, ψ.comp j, psLin' θ (RingHom.id _) hθL hidL hnS' hnX _ (fun c z => ?_) ?_,
    psLin' (RingHom.id _) θ hidL hθL hnX hnS' _ (fun c z => ?_) ?_, fun x => ?_, fun z => ?_⟩
  · rw [eC]; exact k1 _ z
  · rintro (p | p) z
    · rw [eX]; exact k1 _ z
    · rw [θr, zero_smul, map_zero]; exact (hy p _).symm
  · rw [eC]; exact k2 _ z
  · rintro (p | p) z
    · rw [eX]; exact k2 _ z
    · rw [θr, zero_smul, RingHom.id_apply, hy, map_zero]
  · show κ (φ (ψ (j x))) = _
    rw [hφψ _ ((hjr _).2 ⟨x, rfl⟩), hκ, hκj]
  · show ψ (j (κ (φ z))) = _
    obtain ⟨x, hx⟩ := (hjr _).1 (hφn z)
    rw [hη, ← hψφ, ← hx, hκj]

/- English proof (translation)
Simplify using `only [fEl, map_prod, map_mul, map_sub, map_natCast]`.
-/
private theorem fEl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {q n : ℕ} (Nq : Fin q → ℕ)
    (u : Fin q → Fin n → R) : f (fEl Nq u) = fEl Nq fun j i => f (u j i) := by
  simp only [fEl, map_prod, map_mul, map_sub, map_natCast]

/- English proof (translation)
Rewrite using `[map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]`.
-/
private theorem mapRingHom_single_mul_charpoly_of_roots {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) {n : ℕ} (g ph : G) (u : Fin n → R) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q1El ph u) =
      MonoidAlgebra.single g 1 * q1El ph fun i => f (u i) := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]
  congr 3
  funext i
  simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
Rewrite using `[map_mul, q2El, q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, map_one, map_one]`. Use `congr 4`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, apply_ite (MonoidAlgebra.mapRingHom G f), map_sub, MonoidAlgebra.mapRingHom_single, map_one]`.
-/
private theorem mapRingHom_single_mul_partial_charpoly {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) {n : ℕ} (g ph ta : G) (u : Fin n → R)
    (i : Fin n) (y : R) : MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q2El ph ta u i y) =
      MonoidAlgebra.single g 1 * q2El ph ta (fun i => f (u i)) i (f y) := by
  rw [map_mul, q2El, q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub, MonoidAlgebra.mapRingHom_single,
    MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, map_one, map_one]
  congr 4
  funext k
  simp only [Function.comp_apply, apply_ite (MonoidAlgebra.mapRingHom G f), map_sub, MonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[MvPowerSeries.coeff_killCompl, MvPowerSeries.coeff_C]`. Use `split_ifs with h`. Rewrite using `[h, Finsupp.embDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_rename]`. Use `MvPowerSeries.coeff_rename_eq_zero _ _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨y, hy⟩`. Use `h (Finsupp.ext fun a => ?_)` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun hy (Function.Embedding.inl a)`. Rewrite `h1` using `[Finsupp.embDomain_apply_self, Finsupp.mapDomain_notin_range _ _ (by simp)]`. Conclude with `h1.symm`.
-/
private theorem kill_ren {R σ τ : Type} [CommRing R] [Finite τ] (z : MvPowerSeries τ R) :
    MvPowerSeries.killCompl (Function.Embedding.inl : σ ↪ σ ⊕ τ) (MvPowerSeries.rename Sum.inr z) =
      MvPowerSeries.C (MvPowerSeries.constantCoeff z) := by
  classical
  ext x
  rw [MvPowerSeries.coeff_killCompl, MvPowerSeries.coeff_C]
  split_ifs with h
  · rw [h, Finsupp.embDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_rename]
  · refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨y, hy⟩
    refine h (Finsupp.ext fun a => ?_)
    have h1 := DFunLike.congr_fun hy (Function.Embedding.inl a)
    rw [Finsupp.embDomain_apply_self, Finsupp.mapDomain_notin_range _ _ (by simp)] at h1
    exact h1.symm

/- English proof (translation)
Introduce `l hl L G0 O _ _ _ hO _ n r B _ _ _ u J D b G h q N A Nq ph ta ex ut rel`. Use `haveI := hO.complete`. Use `haveI := hO.finite`. Use `haveI := hO.char`. Use `haveI : IsCO O (abelian₂ O Empty D) := co_mvps O O _`.

Use `haveI : IsAdicComplete (maximalIdeal (abelian₂ O Empty D)) (abelian₂ O Empty D) := IsCO.complete (O := O)`. Use `haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)`. Use `haveI : IsCO O (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R) := co_mvps O A.R _`. Use `haveI := A.fin1`. Use `haveI := b.fin`.

Establish `hloc : ∀ x ∈ maximalIdeal (abelian₂ O Empty D), b.lam x ∈ maximalIdeal B` using `fun x hx => by`. Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]` and apply the resulting hypothesis. Establish `hβ : A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R) = b.lam`. Use `(co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) fun s => hloc _ ?_).unique ⟨fun c => AlgHom.commutes _ c, ?_⟩ ⟨fun c => b.lam.commutes c, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`.

Simplify using the standard rewrite rules. Introduce and unpack `(s | k)`. Conclude with `s.elim`. Use `show A.β (algebraMap _ A.R _) = _`. Rewrite using `[A.segmentWeightExponent, b.segmentWeightExponent, map_sub, map_mul, map_one, AlgHom.commutes, ← A.β_pair.2]`.

Both sides reduce to the same expression. Use `letI : Algebra (abelian₂ O Empty D) B := b.lam.toRingHom.toAlgebra`. Use `haveI : IsScalarTower (abelian₂ O Empty D) B b.M := IsScalarTower.of_algebraMap_smul fun c m => (b.smul_lam c m).symm`. Use `haveI : IsLocalHom (algebraMap (abelian₂ O Empty D) B) := ⟨fun x hx => by`. Assume the negation of the conclusion as `hn`.

Conclude with `hloc x hn hx⟩`. Establish `hlm : (l : abelian₂ O Empty D) ∈ maximalIdeal (abelian₂ O Empty D)`. Rewrite using `[← res_eq_zero_iff O, map_natCast, CharP.cast_eq_zero]`. Set `s : Sinf O Empty D q n →ₐ[abelian₂ O Empty D] MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R` to `((MvPowerSeries.rename Sum.inr).restrictScalars _).comp (MvPowerSeries.mapAlgHom (Algebra.ofId (abelian₂ O Empty D) A.R))`. Establish `hs : ∀ z, s z = MvPowerSeries.rename Sum.inr (MvPowerSeries.map (algebraMap (abelian₂ O Empty D) A.R) z)` using `fun _ => rfl`.

Establish `hsX : ∀ p, s (MvPowerSeries.X p) = MvPowerSeries.X (.inr p)` using `fun p => by`. Rewrite using `[hs, MvPowerSeries.map_X, MvPowerSeries.rename_X]`. Set `θ : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R →ₐ[O] SpAt u (fun j => h.p₀ (ph j)) ut` to `((Sp.mk _ _).restrictScalars O).comp ((MvPowerSeries.mapAlgHom A.β).comp ((MvPowerSeries.killCompl Function.Embedding.inl).restrictScalars O))`. Establish `hθ : ∀ z, θ z = Sp.mk _ _ (MvPowerSeries.map A.β.toRingHom (MvPowerSeries.killCompl Function.Embedding.inl z))` using `fun _ => rfl`. Establish `θC : ∀ x, θ (MvPowerSeries.C x) = algebraMap B _ (A.β x)` using `fun x => by`.

Rewrite using `[hθ, MvPowerSeries.killCompl_C, MvPowerSeries.map_C]`. Both sides reduce to the same expression. Establish `θl : ∀ p, θ (MvPowerSeries.X (.inl p)) = Sp.mk _ _ (MvPowerSeries.X p)` using `fun p => by`. Rewrite using `[hθ]`. Conclude with `congrArg _ ((congrArg _ (MvPowerSeries.killCompl_X p)).trans (MvPowerSeries.map_X _ _))`.

Establish `θr : ∀ p, θ (MvPowerSeries.X (.inr p)) = 0` using `fun p => by`. Rewrite using `[hθ, MvPowerSeries.killCompl_X_eq_zero (by simp), map_zero, map_zero]`. Set `c : Fin q × Fin n → A.R` to `fun p => algebraMap O A.R (ut p.1 p.2)`. Set `ev : PUY A.R q n →+* MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R` to `MvPolynomial.eval₂Hom MvPowerSeries.C fun p => MvPowerSeries.C (Sum.elim c 0 p) + MvPowerSeries.X p`. Establish `evC : ∀ x, ev (MvPolynomial.C x) = MvPowerSeries.C x` using `fun x => MvPolynomial.eval₂Hom_C _ _ x`.

Establish `evX : ∀ p, ev (MvPolynomial.X p) = MvPowerSeries.C (Sum.elim c 0 p) + MvPowerSeries.X p` using `fun p => MvPolynomial.eval₂Hom_X' _ _ p`. Take `⟨M, _, _, rk, e, he, hk, φ, ψ, h1, h2, h3, h4⟩` from `opCore (Λ := abelian₂ O Empty D) hl.out hlm _ (fun j => (Det.chiApi u.D _).2.2.1) (fun j => le_antisymm (Det.chiApi u.D _).2.2.2.1 (Polynomial.le_natDegree_of_ne_zero (by`. Establish `h0` using `(Det.chiApi u.D (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1`. Rewrite `h0` using `[GDet.lam, pow_zero, one_mul, Nat.sub_zero]`. Rewrite using `[h0]`.

Conclude with `one_ne_zero)))`. Use the proof step `A.β.toRingHom (AlgHom.congr_fun hβ) c (fun j i => algebraMap O B (ut j i)) (fun j i => (A.β.commutes _).symm)`. Use the proof step `A.act1 A.actw _ rel.two A.ρ A.ρ_gen A.proj A.tr A.tr_surj A.tr_ker A.tr_u s hsX θ.toRingHom θC θl θr ev evC evX`. Set `ι : A.R →ₐ[O] MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R` to `IsScalarTower.toAlgHom O _ _`. Establish `hι : ∀ x, ι x = MvPowerSeries.C x` using `fun _ => rfl`.

Take `⟨p, hp1, hp2⟩` from `CA.pair_map A.rN A.p ι`. Establish `hf : ev (MvPolynomial.rename Sum.inl (fEl Nq fun j i => (MvPolynomial.X (j, i) : PU A.R q n))) = fEl Nq fun j i => ev (uV A.R j i)`. Use `(fEl_map (ev.comp (MvPolynomial.rename Sum.inl).toRingHom) Nq _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `htr : ∀ y, ev ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr y) = p.D.tr (MonoidAlgebra.mapRingHom _ ev y)` using `fun y => by`.

Establish `hc : ev.comp MvPolynomial.C = (ι : A.R →+* _)` using `RingHom.ext evC`. Rewrite using `[← hp1, ← hc, ← (CA.d_gmap A.p.D).2.1]`. Conclude with `(((CA.d_gmap _).2.2.1 ev y).2 1).symm`. Rewrite `h3`, `h4` using `[hf]`. Use `⟨{ rN := A.rN, compat := A.compat, R := MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R, p := p s := s.restrictScalars O, s_w := fun k => ?_, U := fun j i => ev (uV A.R j i), U_res := fun j i => ?_ M := M, a := A.a, le_a := A.le_a, rk := rk, e := e, e_smul := he }, ⟨{ θ := …` and prove the remaining obligations.

Use `show s _ = _`. Rewrite using `[hs, MvPowerSeries.map_C, MvPowerSeries.rename_C, A.segmentWeightExponent, ← hι, map_sub, map_mul, map_one, AlgHom.commutes, ← hp2]`. Both sides reduce to the same expression. Rewrite using `[evX, ← ι.commutes, hι, Sum.elim_inl, add_sub_cancel_left, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules.

Use `show p.D.map _ = _`. Rewrite using `[← hp1, ← A.β_pair.1, (CA.d_gmap _).2.1, (CA.d_gmap _).2.1]`. Conclude with `congrArg _ (RingHom.ext θC)`. Use `show pushCh _ (p.ψ v i) = pushCh _ (u.ψ v i)`. Rewrite using `[← hp2, ← A.β_pair.2 v i]`.

Conclude with `MonoidHom.ext fun g => Units.ext (θC _)`. Use `show θ (s z) = _`. Rewrite using `[hθ, hs, kill_ren, MvPowerSeries.map_C, MvPowerSeries.constantCoeff_map, ← hβ]`. Both sides reduce to the same expression. Use `show θ (ev _) = _`.

Rewrite using `[evX, map_add, θC, θl, Sum.elim_inl, A.β.commutes, Sp.u, map_add]`. Both sides reduce to the same expression. Use `hk _ (rel.rel1 j g) m` as an intermediate fact. Rewrite `this` using `[map_pow, map_mul, fEl_map, htr, mapRingHom_single_mul_charpoly_of_roots]`. Then use the resulting hypothesis. Use `hk _ (rel.rel2 j i g) m` as an intermediate fact.

Rewrite `this` using `[map_pow, map_mul, fEl_map, htr, mapRingHom_single_mul_partial_charpoly, evX (.inr _), Sum.elim_inr, Pi.zero_apply, map_zero, zero_add, ← hsX]`. Conclude with `this`.
-/
theorem UpperTheory.V.Pa.Lev.opToTW :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G : Glob l L) (h : G.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (ut : Fin q → Fin n → O), OpRel A Nq ph ta ex → ∃ A' : TWRing b h ut N, Nonempty (TWMaps Nq ph ta A' ex) := by
  intro l hl L G0 O _ _ _ hO _ n r B _ _ _ u J D b G h q N A Nq ph ta ex ut rel
  haveI := hO.complete
  haveI := hO.finite
  haveI := hO.char
  haveI : IsCO O (abelian₂ O Empty D) := co_mvps O O _
  haveI : IsAdicComplete (maximalIdeal (abelian₂ O Empty D)) (abelian₂ O Empty D) := IsCO.complete (O := O)
  haveI : IsAdicComplete (maximalIdeal B) B := IsCO.complete (O := O)
  haveI : IsCO O (MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R) := co_mvps O A.R _
  haveI := A.fin1
  haveI := b.fin
  have hloc : ∀ x ∈ maximalIdeal (abelian₂ O Empty D), b.lam x ∈ maximalIdeal B := fun x hx => by
    rwa [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  have hβ : A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R) = b.lam := by
    refine (co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) fun s => hloc _ ?_).unique
      ⟨fun c => AlgHom.commutes _ c, ?_⟩ ⟨fun c => b.lam.commutes c, fun _ => rfl⟩
    · rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    · rintro (s | k)
      · exact s.elim
      · show A.β (algebraMap _ A.R _) = _
        rw [A.segmentWeightExponent, b.segmentWeightExponent, map_sub, map_mul, map_one, AlgHom.commutes, ← A.β_pair.2]
        rfl
  letI : Algebra (abelian₂ O Empty D) B := b.lam.toRingHom.toAlgebra
  haveI : IsScalarTower (abelian₂ O Empty D) B b.M := IsScalarTower.of_algebraMap_smul fun c m => (b.smul_lam c m).symm
  haveI : IsLocalHom (algebraMap (abelian₂ O Empty D) B) := ⟨fun x hx => by
    by_contra hn
    exact hloc x hn hx⟩
  have hlm : (l : abelian₂ O Empty D) ∈ maximalIdeal (abelian₂ O Empty D) := by
    rw [← res_eq_zero_iff O, map_natCast, CharP.cast_eq_zero]
  let s : Sinf O Empty D q n →ₐ[abelian₂ O Empty D] MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R :=
    ((MvPowerSeries.rename Sum.inr).restrictScalars _).comp (MvPowerSeries.mapAlgHom (Algebra.ofId (abelian₂ O Empty D) A.R))
  have hs : ∀ z, s z = MvPowerSeries.rename Sum.inr (MvPowerSeries.map (algebraMap (abelian₂ O Empty D) A.R) z) := fun _ => rfl
  have hsX : ∀ p, s (MvPowerSeries.X p) = MvPowerSeries.X (.inr p) := fun p => by
    rw [hs, MvPowerSeries.map_X, MvPowerSeries.rename_X]
  let θ : MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R →ₐ[O] SpAt u (fun j => h.p₀ (ph j)) ut :=
    ((Sp.mk _ _).restrictScalars O).comp ((MvPowerSeries.mapAlgHom A.β).comp
      ((MvPowerSeries.killCompl Function.Embedding.inl).restrictScalars O))
  have hθ : ∀ z, θ z = Sp.mk _ _ (MvPowerSeries.map A.β.toRingHom (MvPowerSeries.killCompl Function.Embedding.inl z)) :=
    fun _ => rfl
  have θC : ∀ x, θ (MvPowerSeries.C x) = algebraMap B _ (A.β x) := fun x => by
    rw [hθ, MvPowerSeries.killCompl_C, MvPowerSeries.map_C]
    rfl
  have θl : ∀ p, θ (MvPowerSeries.X (.inl p)) = Sp.mk _ _ (MvPowerSeries.X p) := fun p => by
    rw [hθ]
    exact congrArg _ ((congrArg _ (MvPowerSeries.killCompl_X p)).trans (MvPowerSeries.map_X _ _))
  have θr : ∀ p, θ (MvPowerSeries.X (.inr p)) = 0 := fun p => by
    rw [hθ, MvPowerSeries.killCompl_X_eq_zero (by simp), map_zero, map_zero]
  let c : Fin q × Fin n → A.R := fun p => algebraMap O A.R (ut p.1 p.2)
  let ev : PUY A.R q n →+* MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R :=
    MvPolynomial.eval₂Hom MvPowerSeries.C fun p => MvPowerSeries.C (Sum.elim c 0 p) + MvPowerSeries.X p
  have evC : ∀ x, ev (MvPolynomial.C x) = MvPowerSeries.C x := fun x => MvPolynomial.eval₂Hom_C _ _ x
  have evX : ∀ p, ev (MvPolynomial.X p) = MvPowerSeries.C (Sum.elim c 0 p) + MvPowerSeries.X p :=
    fun p => MvPolynomial.eval₂Hom_X' _ _ p
  obtain ⟨M, _, _, rk, e, he, hk, φ, ψ, h1, h2, h3, h4⟩ := opCore (Λ := abelian₂ O Empty D) hl.out hlm _
    (fun j => (Det.chiApi u.D _).2.2.1)
    (fun j => le_antisymm (Det.chiApi u.D _).2.2.2.1 (Polynomial.le_natDegree_of_ne_zero (by
      have h0 := (Det.chiApi u.D (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1
      rw [GDet.lam, pow_zero, one_mul, Nat.sub_zero] at h0
      rw [h0]
      exact one_ne_zero)))
    A.β.toRingHom (AlgHom.congr_fun hβ) c (fun j i => algebraMap O B (ut j i)) (fun j i => (A.β.commutes _).symm)
    A.act1 A.actw _ rel.two A.ρ A.ρ_gen A.proj A.tr A.tr_surj A.tr_ker A.tr_u s hsX θ.toRingHom θC θl θr ev evC evX
  let ι : A.R →ₐ[O] MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R := IsScalarTower.toAlgHom O _ _
  have hι : ∀ x, ι x = MvPowerSeries.C x := fun _ => rfl
  obtain ⟨p, hp1, hp2⟩ := CA.pair_map A.rN A.p ι
  have hf : ev (MvPolynomial.rename Sum.inl (fEl Nq fun j i => (MvPolynomial.X (j, i) : PU A.R q n))) =
      fEl Nq fun j i => ev (uV A.R j i) := by
    refine (fEl_map (ev.comp (MvPolynomial.rename Sum.inl).toRingHom) Nq _).trans ?_
    simp
  have htr : ∀ y, ev ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr y) =
      p.D.tr (MonoidAlgebra.mapRingHom _ ev y) := fun y => by
    have hc : ev.comp MvPolynomial.C = (ι : A.R →+* _) := RingHom.ext evC
    rw [← hp1, ← hc, ← (CA.d_gmap A.p.D).2.1]
    exact (((CA.d_gmap _).2.2.1 ev y).2 1).symm
  rw [hf] at h3 h4
  refine ⟨{ rN := A.rN, compat := A.compat, R := MvPowerSeries ((Fin q × Fin n) ⊕ (Fin q × Fin n)) A.R, p := p
            s := s.restrictScalars O, s_w := fun k => ?_, U := fun j i => ev (uV A.R j i), U_res := fun j i => ?_
            M := M, a := A.a, le_a := A.le_a, rk := rk, e := e, e_smul := he },
    ⟨{ θ := θ, θ_pair := ⟨?_, fun v i => ?_⟩, theta_coefficientMap_eq := fun z => ?_, θ_U := fun j i => ?_, φ := φ, ψ := ψ, φ_smul := h1
       ψ_smul := h2, φψ := h3, ψφ := h4, rel1 := fun j g m => ?_, rel2 := fun j i g m => ?_ }⟩⟩
  · show s _ = _
    rw [hs, MvPowerSeries.map_C, MvPowerSeries.rename_C, A.segmentWeightExponent, ← hι, map_sub, map_mul, map_one, AlgHom.commutes, ← hp2]
    rfl
  · rw [evX, ← ι.commutes, hι, Sum.elim_inl, add_sub_cancel_left, mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  · show p.D.map _ = _
    rw [← hp1, ← A.β_pair.1, (CA.d_gmap _).2.1, (CA.d_gmap _).2.1]
    exact congrArg _ (RingHom.ext θC)
  · show pushCh _ (p.ψ v i) = pushCh _ (u.ψ v i)
    rw [← hp2, ← A.β_pair.2 v i]
    exact MonoidHom.ext fun g => Units.ext (θC _)
  · show θ (s z) = _
    rw [hθ, hs, kill_ren, MvPowerSeries.map_C, MvPowerSeries.constantCoeff_map, ← hβ]
    rfl
  · show θ (ev _) = _
    rw [evX, map_add, θC, θl, Sum.elim_inl, A.β.commutes, Sp.u, map_add]
    rfl
  · have := hk _ (rel.rel1 j g) m
    rwa [map_pow, map_mul, fEl_map, htr, mapRingHom_single_mul_charpoly_of_roots] at this
  · have := hk _ (rel.rel2 j i g) m
    rw [map_pow, map_mul, fEl_map, htr, mapRingHom_single_mul_partial_charpoly, evX (.inr _), Sum.elim_inr, Pi.zero_apply, map_zero, zero_add, ← hsX] at this
    exact this
