import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.BcBackOffTOfSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

/- English proof (translation)
Introduce `E _ _ _ n π hπ w hw P P' h h'`. Set `Ψ : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`. Take `⟨e, he⟩` from `GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw`. Take `⟨r, -, -, hr2⟩` from `GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w`. Establish `hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g` using `fun g => by rw [← he, e.apply_symm_apply]`.

Set `s : GL (Fin n) (w.adicCompletion E) →* UA E n` to `(locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom`. Establish `mk : ∀ Q : LocIrr w n, IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) Q.ρ → ∃ F : Q.ρ.IntertwiningMap (Ψ.rep.comp s), F ≠ 0` using `fun Q ⟨_, f, hf0, hfm, hf⟩ => ⟨⟨f.codRestrict Ψ.V hfm, fun g => LinearMap.ext fun v => Subtype.ext (by`. Use `hf (e.symm g) v` as an intermediate fact. Rewrite `this` using `[show ((cLoc w).comp (locU n w).subtype) (e.symm g) = g from hcl g]`. Conclude with `this)⟩, fun h0 => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))⟩`.

Take `⟨F, hF⟩` from `mk P h`. Take `⟨F', hF'⟩` from `mk P' h'`. Use `(GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (GL (Fin n) (w.adicCompletion E)) Ψ.V P.V P'.V Ψ.rep s P.ρ P'.ρ Ψ.isIrreducible_rep P.irred P'.irred (fun g => ⟨e (r g), fun y => ?_⟩) F hF).2 F' hF'` and prove the remaining obligations. Establish `: s (e (r g)) = (r g : UA E n)` using `congrArg Subtype.val (e.symm_apply_apply (r g))`. Rewrite using `[this]`.

Conclude with `hr2 g (e.symm y)`.
-/
theorem compUnique : CompUnique := by
  intro E _ _ _ n π hπ w hw P P' h h'
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by rw [← he, e.apply_symm_apply]
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n := (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ Q : LocIrr w n, IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) Q.ρ →
      ∃ F : Q.ρ.IntertwiningMap (Ψ.rep.comp s), F ≠ 0 := fun Q ⟨_, f, hf0, hfm, hf⟩ =>
    ⟨⟨f.codRestrict Ψ.V hfm, fun g => LinearMap.ext fun v => Subtype.ext (by
      have := hf (e.symm g) v
      rw [show ((cLoc w).comp (locU n w).subtype) (e.symm g) = g from hcl g] at this
      exact this)⟩, fun h0 => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))⟩
  obtain ⟨F, hF⟩ := mk P h
  obtain ⟨F', hF'⟩ := mk P' h'
  refine (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (GL (Fin n) (w.adicCompletion E)) Ψ.V P.V P'.V Ψ.rep s P.ρ P'.ρ Ψ.isIrreducible_rep P.irred
    P'.irred (fun g => ⟨e (r g), fun y => ?_⟩) F hF).2 F' hF'
  have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
  rw [this]
  exact hr2 g (e.symm y)

/- English proof (translation)
Substitute `hm` using the available equality. Take `⟨τ, rfl⟩ : ∃ τ, σ = fun _ => τ` from `⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩`. Take `⟨e₁⟩` from `nonempty_equiv_multiProd_one τ.smooth (stdBlocks (fun _ : Fin 1 => m) h) fun a i => Fin.ext (by`. Rewrite using `[stdBlocks_val, Subsingleton.elim a 0]`. Use the proof step `simp)`.

Take `⟨hd, hτ, p, hp, -⟩` from `hs`. Establish `key : ∀ y : Fin 1 → IrrGL (w.adicCompletion E), y = (fun _ => IrrGL.of ρ.ρ ρ.smooth ρ.irred) → ∀ hd : ∑ i, (y i).1 = m, Nonempty ((IrrGL.of ρ.ρ ρ.smooth ρ.irred).rep.Equiv (prodIrr y hd))`. Introduce and unpack `_ rfl hd`. Conclude with `nonempty_equiv_prodIrr_one _ hd`. Take `⟨e⟩` from `key _ (funext fun _ => by simp [spehFactor]) hd`.

Set `q : ρ.ρ.IntertwiningMap τ.ρ` to `p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toIntertwiningMap)`. Establish `hq : Function.Surjective q` using `hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toLinearEquiv.surjective)`. Establish `hinj : Function.Injective q` using `GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible ρ.irred q fun h0 => by`. Establish `: Nontrivial τ.V` using `((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1`. Take `⟨y, hy⟩` from `exists_ne (0 : τ.V)`.

Take `⟨v, rfl⟩` from `hq y`. Conclude with `hy (LinearMap.congr_fun h0 v)`. Conclude with `⟨e₁.symm.trans (q.ofBijective ⟨hinj, hq⟩).symm⟩`.
-/
private theorem speh_single_factor_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (n m : ℕ)
    (hm : m = n) (h : ∑ _i : Fin 1, m = n) (ρ : LocIrr w n) (σ : Fin 1 → LocIrr w m)
    (hs : IsSpeh (IrrGL.of ρ.ρ ρ.smooth ρ.irred) 1 (σ 0).ρ) :
    Nonempty ((locProd (N := fun _ : Fin 1 => m) h w σ).Equiv ρ.ρ) := by
  subst hm
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = fun _ => τ := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨e₁⟩ := nonempty_equiv_multiProd_one τ.smooth (stdBlocks (fun _ : Fin 1 => m) h) fun a i => Fin.ext (by
    rw [stdBlocks_val, Subsingleton.elim a 0]; simp)
  obtain ⟨hd, hτ, p, hp, -⟩ := hs
  have key : ∀ y : Fin 1 → IrrGL (w.adicCompletion E), y = (fun _ => IrrGL.of ρ.ρ ρ.smooth ρ.irred) →
      ∀ hd : ∑ i, (y i).1 = m, Nonempty ((IrrGL.of ρ.ρ ρ.smooth ρ.irred).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.ρ.IntertwiningMap τ.ρ :=
    p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).toLinearEquiv.surjective)
  have hinj : Function.Injective q := GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible ρ.irred q fun h0 => by
    have : Nontrivial τ.V := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
    obtain ⟨y, hy⟩ := exists_ne (0 : τ.V)
    obtain ⟨v, rfl⟩ := hq y
    exact hy (LinearMap.congr_fun h0 v)
  exact ⟨e₁.symm.trans (q.ofBijective ⟨hinj, hq⟩).symm⟩

/- English proof (translation)
Introduce `_ _ _ _ w n h ρ σ hs` and use `speh_single_factor_equiv w n (1 * n) (one_mul n) h ρ σ hs`.
-/
theorem oneFactor : OneFactor := fun _ _ _ _ w n h ρ σ hs => speh_single_factor_equiv w n (1 * n) (one_mul n) h ρ σ hs

end PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

end
