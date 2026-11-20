import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.DiscreteGroups.GlobalIrreducibility.DzTwChar
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SerSys GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.TypeExistence

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

/- English proof (translation)
Use `set π := σ.ρ.comp (GeneralLinearGroup.map i.toRingHom) with hπ`. Establish `hπc : IsCuspidal π`. Use `isCuspidal_comp_generalLinearGroupMap i.symm (by rwa [RingEquiv.symm_symm]) σ.ρ hc` as an intermediate fact. Rewrite `this` using `[RingEquiv.symm_symm]`. Then use the resulting hypothesis. Establish `hsc` using `GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[g] n σ.V π hπc`.

Establish `hfin` using `GlobalTheory.DepthZeroCusp.isCuspidal_repK hsc`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hf`. Establish `hvK : v ∈ GlobalTheory.GLp.fixK1 π`. Rewrite using `[GlobalTheory.GLp.Model.mem_principalCongruenceFixedVectors_iff]`. Introduce `k hk`.

Conclude with `(GlobalTheory.LGrp.mem_fixed.1 hv) _ (DiscreteGroups.sglob.DzIso.map_mem_KOne i hi k hk)`. Take `⟨τ, φ, hsimp, hinj, hφ, -⟩` from `TameGen.exists_simple (GlobalTheory.GLp.Supp.repK π) 1 (fun a => by rw [one_mul, mul_one]) ⟨v, hvK⟩ (fun h => hv0 (congrArg Subtype.val h)) (by simp)`. Use `⟨τ, TameGen.isCusp_character hn τ hsimp ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb hne u hu`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `hfin b hb hne (φ u) (fun x hx => by rw [← hφ, hu x hx])`. Use `haveI := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hsimp haveI : Nontrivial τ.V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Gn g n)) (Representation.asModule τ.ρ)`. Take `⟨u, hu⟩` from `exists_ne (0 : τ.V)`. Use `⟨(GlobalTheory.GLp.fixK1 π).subtype ∘ₗ φ, fun h0 => hu (hinj ?_), fun k x => ?_⟩` and prove the remaining obligations.

Establish `h1` using `LinearMap.congr_fun h0 u`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply] at h1`. Rewrite using `[map_zero]`. Conclude with `Subtype.ext h1`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`.

Rewrite using `[hφ, GlobalTheory.GLp.Supp.repK_red]`.
-/
private theorem exists_cusp {n : ℕ} (hn : 0 < n) (σ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hc : IsCuspidal σ.ρ) (hf : fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥) :
    ∃ τ : FDRep ℂ (Gn g n), IsCusp τ.character ∧
      TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ := by
  classical
  set π := σ.ρ.comp (GeneralLinearGroup.map i.toRingHom) with hπ
  have hπc : IsCuspidal π := by
    have := isCuspidal_comp_generalLinearGroupMap i.symm (by rwa [RingEquiv.symm_symm]) σ.ρ hc
    rwa [RingEquiv.symm_symm] at this
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[g] n σ.V π hπc
  have hfin := GlobalTheory.DepthZeroCusp.isCuspidal_repK hsc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
  have hvK : v ∈ GlobalTheory.GLp.fixK1 π := by
    rw [GlobalTheory.GLp.Model.mem_principalCongruenceFixedVectors_iff]
    intro k hk
    exact (GlobalTheory.LGrp.mem_fixed.1 hv) _ (DiscreteGroups.sglob.DzIso.map_mem_KOne i hi k hk)
  obtain ⟨τ, φ, hsimp, hinj, hφ, -⟩ := TameGen.exists_simple (GlobalTheory.GLp.Supp.repK π) 1
    (fun a => by rw [one_mul, mul_one]) ⟨v, hvK⟩ (fun h => hv0 (congrArg Subtype.val h)) (by simp)
  refine ⟨τ, TameGen.isCusp_character hn τ hsimp ?_, ?_⟩
  · intro b hb hne u hu
    apply hinj
    rw [map_zero]
    exact hfin b hb hne (φ u) (fun x hx => by rw [← hφ, hu x hx])
  · haveI := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hsimp
    haveI : Nontrivial τ.V :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Gn g n)) (Representation.asModule τ.ρ)
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    refine ⟨(GlobalTheory.GLp.fixK1 π).subtype ∘ₗ φ, fun h0 => hu (hinj ?_), fun k x => ?_⟩
    · have h1 := LinearMap.congr_fun h0 u
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply] at h1
      rw [map_zero]
      exact Subtype.ext h1
    · simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hφ, GlobalTheory.GLp.Supp.repK_red]

private def resE : 𝓀[w.adicCompletion E] ≃+* ZMod g :=
  RingEquiv.ofBijective (DiscreteGroups.sglob.DzTw.resMap i hi) ⟨RingHom.injective _, fun a => by
    obtain ⟨y, rfl⟩ := DiscreteGroups.sglob.DzIso.redO_surjective i hi a
    exact ⟨IsLocalRing.residue _ y, rfl⟩⟩

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `show resE i hi ((redK (w.adicCompletion E) (Fin n) x : Matrix (Fin n) (Fin n) 𝓀[w.adicCompletion E]) a b) = PadicInt.toZMod (κ.val a b)`. Rewrite using `[redK_apply]`. Use `show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi _) = _`. Use `congr 1`.

Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[DiscreteGroups.sglob.DzIso.coe_toInt]`. Use `show i.symm (((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b) = _`. Rewrite using `[← hκ]`. Conclude with `i.symm_apply_apply _`.
-/
private theorem resE_redK {n : ℕ} (x : KO (w.adicCompletion E) (Fin n)) (κ : GL (Fin n) ℤ_[g])
    (hκ : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = x) :
    GeneralLinearGroup.map (resE i hi).toRingHom (redK (w.adicCompletion E) (Fin n) x) = GlobalTheory.GLp.red g n κ := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  show resE i hi ((redK (w.adicCompletion E) (Fin n) x : Matrix (Fin n) (Fin n) 𝓀[w.adicCompletion E]) a b) =
    PadicInt.toZMod (κ.val a b)
  rw [redK_apply]
  show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi _) = _
  congr 1
  apply PadicInt.ext
  rw [DiscreteGroups.sglob.DzIso.coe_toInt]
  show i.symm (((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b) = _
  rw [← hκ]
  exact i.symm_apply_apply _

/- English proof (translation)
Establish `hF` using `PositivityTheory.Rg.DzCount.finite_cuspidal_of_isCuspidal τ (PositivityTheory.GreenCharacters.isCuspidal_of_isCusp τ hτ)`. Introduce `s d e hne v hv`. Use `hF s d e (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hne)) v ?_` and prove the remaining obligations. Introduce `u hu`. Set `u' : GL (Fin n) 𝓀[w.adicCompletion E]` to `GeneralLinearGroup.map (resE i hi).symm.toRingHom u`.

Establish `hu' : u' ∈ unipRad 𝓀[w.adicCompletion E] e`. Rewrite `hu`, the goal using `[GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]`. Introduce `a b hab`. Establish `h1` using `hu a b hab`. Simplify using `only [u', GeneralLinearGroup.map_apply, h1]`.

Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hmap : GeneralLinearGroup.map (resE i hi).toRingHom u' = u`. Use extensionality with `a b`. Simplify using `[u']`.

Establish `h2` using `hv u' hu'`. Rewrite `h2` using `[MonoidHom.comp_apply, hmap]`. Conclude with `h2`.
-/
private theorem finCusp_comp {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) :
    PositivityTheory.Rg.DzCount.FinCusp (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) := by
  have hF := PositivityTheory.Rg.DzCount.finite_cuspidal_of_isCuspidal τ (PositivityTheory.GreenCharacters.isCuspidal_of_isCusp τ hτ)
  intro s d e hne v hv
  refine hF s d e (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hne)) v ?_
  intro u hu
  let u' : GL (Fin n) 𝓀[w.adicCompletion E] := GeneralLinearGroup.map (resE i hi).symm.toRingHom u
  have hu' : u' ∈ unipRad 𝓀[w.adicCompletion E] e := by
    rw [GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries] at hu ⊢
    intro a b hab
    have h1 := hu a b hab
    simp only [u', GeneralLinearGroup.map_apply, h1]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hmap : GeneralLinearGroup.map (resE i hi).toRingHom u' = u := by
    ext a b
    simp [u']
  have h2 := hv u' hu'
  rw [MonoidHom.comp_apply, hmap] at h2
  exact h2

/- English proof (translation)
Establish `hker : LinearMap.ker φ = ⊥`. Set `S : Subrepresentation τ.ρ` to `⟨LinearMap.ker φ, fun x v hv => by`. Take `⟨k, rfl⟩` from `GlobalTheory.GLp.Model.red_surjective n x`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hφ, hv, map_zero]⟩`.

Use `haveI := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ (DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1)`. Break down `eq_bot_or_eq_top S with h | h` into its components or cases. Conclude with `congrArg Subrepresentation.toSubmodule h`. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises.

Use extensionality with `u`. Establish `hu : u ∈ S.toSubmodule`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Establish `hu' : u ∈ LinearMap.ker φ` using `hu`.

Rewrite `hu'` using `[LinearMap.mem_ker]`. Rewrite using `[hu', LinearMap.zero_apply]`. Establish `inj : Function.Injective φ` using `LinearMap.ker_eq_bot.1 hker`. Use `haveI : Nontrivial τ := by`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Conclude with `h0 (LinearMap.ext fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])`. Use `⟨inj, PositivityTheory.Rg.DzCount.B.st6 (w.adicCompletion E) _ n (τ.ρ.comp (GeneralLinearGroup.map (resE i hi).toRingHom)) (finCusp_comp i hi τ hτ) σ ω hω φ ⟨inj, ?_⟩⟩` and prove the remaining obligations. Introduce `x v`. Take `⟨κ, hκ⟩` from `DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2`.

Rewrite using `[MonoidHom.comp_apply, resE_redK i hi x κ hκ, hφ, hκ]`.
-/
private theorem fixed_eq_range {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u)) :
    Function.Injective φ ∧ fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) = LinearMap.range φ := by
  have hker : LinearMap.ker φ = ⊥ := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker φ, fun x v hv => by
      obtain ⟨k, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n x
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hφ, hv, map_zero]⟩
    haveI := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ (DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1)
    rcases eq_bot_or_eq_top S with h | h
    · exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply h0
      ext u
      have hu : u ∈ S.toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      have hu' : u ∈ LinearMap.ker φ := hu
      rw [LinearMap.mem_ker] at hu'
      rw [hu', LinearMap.zero_apply]
  have inj : Function.Injective φ := LinearMap.ker_eq_bot.1 hker
  haveI : Nontrivial τ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h0 (LinearMap.ext fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])
  refine ⟨inj, PositivityTheory.Rg.DzCount.B.st6 (w.adicCompletion E) _ n
    (τ.ρ.comp (GeneralLinearGroup.map (resE i hi).toRingHom)) (finCusp_comp i hi τ hτ) σ ω hω φ ⟨inj, ?_⟩⟩
  intro x v
  obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
  rw [MonoidHom.comp_apply, resE_redK i hi x κ hκ, hφ, hκ]

omit hi in
/- English proof (translation)
Set `L : τ ≃ₗ[ℂ] τ'` to `(LinearEquiv.ofInjective φ h1).trans ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective φ' h2).symm)`. Establish `hL : ∀ u, φ' (L u) = φ u` using `fun u => by`. Use `(LinearEquiv.ofInjective φ' h2).apply_symm_apply (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective φ h1 u))` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Use function extensionality and compare the values at `x`.

Take `⟨k, rfl⟩` from `GlobalTheory.GLp.Model.red_surjective n x`. Establish `hi' : ∀ u, L (τ.ρ (GlobalTheory.GLp.red g n k) u) = τ'.ρ (GlobalTheory.GLp.red g n k) (L u)` using `fun u => h2 (by rw [hL, hA, hA', hL])`. Establish `hc : τ'.ρ (GlobalTheory.GLp.red g n k) = L.conj (τ.ρ (GlobalTheory.GLp.red g n k))` using `LinearMap.ext fun v => by`. Rewrite using `[LinearEquiv.conj_apply_apply, hi', L.apply_symm_apply]`. Use `show LinearMap.trace ℂ τ' (τ'.ρ (GlobalTheory.GLp.red g n k)) = LinearMap.trace ℂ τ (τ.ρ (GlobalTheory.GLp.red g n k))`.

Rewrite using `[hc, LinearMap.trace_conj']`.
-/
private theorem char_eq {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ τ' : FDRep ℂ (Gn g n))
    (φ : τ →ₗ[ℂ] V) (φ' : τ' →ₗ[ℂ] V) (h1 : Function.Injective φ) (h2 : Function.Injective φ')
    (hr : LinearMap.range φ = LinearMap.range φ') (A : GL (Fin n) ℤ_[g] → V →ₗ[ℂ] V)
    (hA : ∀ k u, φ (τ.ρ (GlobalTheory.GLp.red g n k) u) = A k (φ u))
    (hA' : ∀ k u, φ' (τ'.ρ (GlobalTheory.GLp.red g n k) u) = A k (φ' u)) : τ'.character = τ.character := by
  let L : τ ≃ₗ[ℂ] τ' := (LinearEquiv.ofInjective φ h1).trans
    ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective φ' h2).symm)
  have hL : ∀ u, φ' (L u) = φ u := fun u => by
    have := (LinearEquiv.ofInjective φ' h2).apply_symm_apply (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective φ h1 u))
    exact congrArg Subtype.val this
  funext x
  obtain ⟨k, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n x
  have hi' : ∀ u, L (τ.ρ (GlobalTheory.GLp.red g n k) u) = τ'.ρ (GlobalTheory.GLp.red g n k) (L u) := fun u =>
    h2 (by rw [hL, hA, hA', hL])
  have hc : τ'.ρ (GlobalTheory.GLp.red g n k) = L.conj (τ.ρ (GlobalTheory.GLp.red g n k)) := LinearMap.ext fun v => by
    rw [LinearEquiv.conj_apply_apply, hi', L.apply_symm_apply]
  show LinearMap.trace ℂ τ' (τ'.ρ (GlobalTheory.GLp.red g n k)) = LinearMap.trace ℂ τ (τ.ρ (GlobalTheory.GLp.red g n k))
  rw [hc, LinearMap.trace_conj']

end UpperTheory.Zero.LLC.TypeExistence

/- English proof (translation)
Take `⟨φ, h0, hφ⟩` from `h`. Use `⟨e.toLinearMap ∘ₗ φ, fun h1 => h0 ?_, fun k u => ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Establish `hu` using `LinearMap.congr_fun h1 u`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at hu`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `(LinearEquiv.map_eq_zero_iff e).1 hu`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hφ, he]`.
-/
private theorem inflates_lemma {g : ℕ} [Fact g.Prime] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (π' : Representation ℂ (GL (Fin n) ℚ_[g]) V') (e : V ≃ₗ[ℂ] V') (he : ∀ x v, e (π x v) = π' x (e v))
    (τ : FDRep ℂ (Gn g n)) (h : TameGen.Inflates π τ) : TameGen.Inflates π' τ := by
  obtain ⟨φ, h0, hφ⟩ := h
  refine ⟨e.toLinearMap ∘ₗ φ, fun h1 => h0 ?_, fun k u => ?_⟩
  · ext u
    have hu := LinearMap.congr_fun h1 u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at hu
    rw [LinearMap.zero_apply]
    exact (LinearEquiv.map_eq_zero_iff e).1 hu
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hφ, he]

open UpperTheory.Zero.LLC.TypeExistence in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w hA g _ i hi n hn σ`. Set `R` to `σ.cl.rep`. Take `⟨e0⟩` from `IrrRep.nonempty_equiv_rep σ`. Set `e0l : R.V ≃ₗ[ℂ] σ.V` to `e0.toLinearEquiv`. Establish `he0 : ∀ y v, e0l (R.ρ y v) = σ.ρ y (e0l v)` using `fun y v => LinearMap.congr_fun (e0.isIntertwining' y) v`.

Establish `he0s : ∀ y v, e0l.symm (σ.ρ y v) = R.ρ y (e0l.symm v)` using `fun y v => e0l.injective (by rw [he0, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])`. Use `⟨fun hcusp hdz => ?_, fun σ' τ τ' hcl hτ hτ' hinf hinf' => ?_⟩` and prove the remaining obligations. Take `⟨τ, hτ, hinf⟩` from `exists_cusp i hi hn R hcusp.2 hdz`. Conclude with `⟨τ, hτ, inflates_lemma _ _ e0l (fun x v => he0 _ v) τ hinf⟩`. Establish `hcl' : σ'.cl = σ.cl` using `eq_of_heq (Sigma.mk.inj hcl).2`.

Take `⟨e1⟩` from `IrrRep.cl_eq_iff.1 hcl'`. Set `e1l : σ'.V ≃ₗ[ℂ] σ.V` to `e1.toLinearEquiv`. Establish `he1 : ∀ y v, e1l (σ'.ρ y v) = σ.ρ y (e1l v)` using `fun y v => LinearMap.congr_fun (e1.isIntertwining' y) v`. Establish `hR` using `inflates_lemma _ (R.ρ.comp (GeneralLinearGroup.map i.toRingHom)) e0l.symm (fun x v => he0s _ v) τ hinf`. Establish `hR'` using `inflates_lemma _ (R.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (e1l.trans e0l.symm) (fun x v => by`.

Simplify using `only [MonoidHom.comp_apply, LinearEquiv.trans_apply]`. Rewrite using `[he1, he0s]) τ' hinf'`. Take `⟨φ, h0, hφ⟩` from `hR`. Take `⟨φ', h0', hφ'⟩` from `hR'`. Take `⟨ω, hω⟩` from `(GlobalTheory.T.centralCharacter_subquotient_productIrreducibles (w.adicCompletion E)).1 (GlobalTheory.LocLanglands.cls σ)`.

Establish `F` using `fixed_eq_range i hi τ hτ R ω hω φ h0 hφ`. Establish `F'` using `fixed_eq_range i hi τ' hτ' R ω hω φ' h0' hφ'`. Conclude with `char_eq τ τ' φ φ' F.1 F'.1 (F.2.symm.trans F'.2) (fun k => R.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) hφ hφ'`.
-/
theorem UpperTheory.Zero.LLC.typeEx :
    UpperTheory.Zero.LLC.TypeEx := by
  intro E Ω _ _ _ _ _ A w hA g _ i hi n hn σ
  let R := σ.cl.rep
  obtain ⟨e0⟩ := IrrRep.nonempty_equiv_rep σ
  let e0l : R.V ≃ₗ[ℂ] σ.V := e0.toLinearEquiv
  have he0 : ∀ y v, e0l (R.ρ y v) = σ.ρ y (e0l v) := fun y v => LinearMap.congr_fun (e0.isIntertwining' y) v
  have he0s : ∀ y v, e0l.symm (σ.ρ y v) = R.ρ y (e0l.symm v) := fun y v =>
    e0l.injective (by rw [he0, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  refine ⟨fun hcusp hdz => ?_, fun σ' τ τ' hcl hτ hτ' hinf hinf' => ?_⟩
  · obtain ⟨τ, hτ, hinf⟩ := exists_cusp i hi hn R hcusp.2 hdz
    exact ⟨τ, hτ, inflates_lemma _ _ e0l (fun x v => he0 _ v) τ hinf⟩
  · have hcl' : σ'.cl = σ.cl := eq_of_heq (Sigma.mk.inj hcl).2
    obtain ⟨e1⟩ := IrrRep.cl_eq_iff.1 hcl'
    let e1l : σ'.V ≃ₗ[ℂ] σ.V := e1.toLinearEquiv
    have he1 : ∀ y v, e1l (σ'.ρ y v) = σ.ρ y (e1l v) := fun y v => LinearMap.congr_fun (e1.isIntertwining' y) v
    have hR := inflates_lemma _ (R.ρ.comp (GeneralLinearGroup.map i.toRingHom)) e0l.symm (fun x v => he0s _ v) τ hinf
    have hR' := inflates_lemma _ (R.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (e1l.trans e0l.symm)
      (fun x v => by
        simp only [MonoidHom.comp_apply, LinearEquiv.trans_apply]
        rw [he1, he0s]) τ' hinf'
    obtain ⟨φ, h0, hφ⟩ := hR
    obtain ⟨φ', h0', hφ'⟩ := hR'
    obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles (w.adicCompletion E)).1 (GlobalTheory.LocLanglands.cls σ)
    have F := fixed_eq_range i hi τ hτ R ω hω φ h0 hφ
    have F' := fixed_eq_range i hi τ' hτ' R ω hω φ' h0' hφ'
    exact char_eq τ τ' φ φ' F.1 F'.1 (F.2.symm.trans F'.2)
      (fun k => R.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) hφ hφ'
