import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.VB.Summand

/- English proof (translation)
Use `set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) R').toRingEquiv`. Use `RingHomInvPair.of_ringEquiv e` as an intermediate fact. Use `RingHomInvPair.of_ringEquiv_symm e` as an intermediate fact. Use `Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* R')) { __ := IsLocalizedModule.iso (.powers r) f, map_smul' := ?_ }` and prove the remaining obligations. Introduce `a x`.

Take `⟨a, s, rfl⟩` from `IsLocalization.exists_mk'_eq (.powers r) a`. Apply `((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1` to reduce the goal to its premises. Simplify using `[e, ← map_smul, ← smul_assoc]`.
-/
theorem free_of_free_away {R M R' M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (r : R) [IsLocalization.Away r R'] (f : M →ₗ[R] M')
    [IsLocalizedModule (.powers r) f]
    [Module.Free (Localization (.powers r)) (LocalizedModule.Away r M)] : Module.Free R' M' := by
  set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) R').toRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* R'))
    { __ := IsLocalizedModule.iso (.powers r) f, map_smul' := ?_ }
  intro a x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) a
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens}

/- English proof (translation)
Use `isFrame_of_forall_exists fun V h x hx => ?_` and prove the remaining obligations. Take `⟨W, hW, hxW, hle⟩` from `QCoh.exists_affine_mem_le x hx`. Use `⟨W, hle, hxW, ?_⟩` and prove the remaining obligations. Use `letI := QCoh.resAlgebra (hle.trans h)`. Use `letI := QCoh.resModule G (hle.trans h)`.

Use `haveI := QCoh.res_isScalarTower G (hle.trans h)`. Set `b'` to `(QCoh.isBaseChange_resLinear G hU hW (hle.trans h)).basis b`. Establish `hb (i : ι) : b' i = resM G (hle.trans h) (b i)`. Rewrite using `[IsBaseChange.basis_apply]`. Both sides reduce to the same expression.

Establish `: Fintype.linearCombination Γ(X, W) (fun i => resM G (hle.trans h) (b i)) = b'.equivFun.symm.toLinearMap`. Use extensionality with `a : 1`. Simplify using `[Fintype.linearCombination_apply, hb]`. Rewrite using `[this]`. Conclude with `b'.equivFun.symm.bijective`.
-/
theorem isFrame_of_affine_basis [G.IsQuasicoherent] (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(G, U)) : IsFrame (F := G) (U := U) b := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  letI := QCoh.resAlgebra (hle.trans h)
  letI := QCoh.resModule G (hle.trans h)
  haveI := QCoh.res_isScalarTower G (hle.trans h)
  let b' := (QCoh.isBaseChange_resLinear G hU hW (hle.trans h)).basis b
  have hb (i : ι) : b' i = resM G (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => resM G (hle.trans h) (b i)) =
      b'.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact b'.equivFun.symm.bijective

/- English proof (translation)
Use `Module.finitePresentation_of_projective Γ(X, U) Γ(G, U)` as an intermediate fact. Use `hU.isLocalization_stalk y` as an intermediate fact. Use `QCoh.isLocalizedModule_germLinear G hU y` as an intermediate fact. Establish `hbc` using `QCoh.isBaseChange_germLinear G hU y`. Establish `: Module.Finite (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :)` using `.equiv hbc.equiv`.

Establish `: Module.Projective (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :)` using `.of_equiv hbc.equiv`. Establish `: Module.Free (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :)` using `Module.free_of_flat_of_isLocalRing`. Take `⟨f, hf, hfree, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear G y) (X.presheaf.stalk (y : X))`. Establish `hxf` using `(QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf`. Use `hU.isLocalization_basicOpen f` as an intermediate fact.

Use `QCoh.isLocalizedModule_resBasicOpen G hU f` as an intermediate fact. Establish `: Module.Free Γ(X, X.basicOpen f) Γ(G, X.basicOpen f)` using `free_of_free_away f (QCoh.resBasicOpen G f)`. Establish `: Module.Finite Γ(X, X.basicOpen f) Γ(G, X.basicOpen f)` using `Module.Finite.of_isLocalizedModule (.powers f) (QCoh.resBasicOpen G f)`. Conclude with `⟨_, _, _, hxf, (isFrame_of_affine_basis (hU.basicOpen f) (Module.Free.chooseBasis _ _)).comp_equiv (Fintype.equivFin _).symm⟩`.
-/
theorem exists_frame_of_projective [G.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(G, U)] [Module.Projective Γ(X, U) Γ(G, U)] (y : U) :
    ∃ (V : X.Opens) (n : ℕ) (e : Fin n → Γ(G, V)), (y : X) ∈ V ∧ IsFrame e := by
  have := Module.finitePresentation_of_projective Γ(X, U) Γ(G, U)
  have := hU.isLocalization_stalk y
  have := QCoh.isLocalizedModule_germLinear G hU y
  have hbc := QCoh.isBaseChange_germLinear G hU y
  have : Module.Finite (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .equiv hbc.equiv
  have : Module.Projective (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .of_equiv hbc.equiv
  have : Module.Free (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear G y) (X.presheaf.stalk (y : X))
  have hxf := (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen G hU f
  have : Module.Free Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    free_of_free_away f (QCoh.resBasicOpen G f)
  have : Module.Finite Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    Module.Finite.of_isLocalizedModule (.powers f) (QCoh.resBasicOpen G f)
  exact ⟨_, _, _, hxf, (isFrame_of_affine_basis (hU.basicOpen f)
    (Module.Free.chooseBasis _ _)).comp_equiv (Fintype.equivFin _).symm⟩

end GlobalTheory.VB.Summand

/- English proof (translation)
Introduce `X _ F G i q r hiq hF x`. Use `hF.isQuasicoherent` as an intermediate fact. Establish `hs : ∑ _ : Unit, i ≫ q = 𝟙 G` using `by simpa using hiq`. Establish `: G.IsQuasicoherent` using `QCoh.isQuasicoherent_of_sum_eq_id (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs`. Take `⟨U, e, hU, hx, -, he⟩` from `hF.exists_affine (V := ⊤) (x := x) trivial`.

Use `Module.Free.of_basis (he.basis le_rfl)` as an intermediate fact. Use `Module.Finite.of_basis (he.basis le_rfl)` as an intermediate fact. Establish `hc : QCoh.appLinear q U ∘ₗ QCoh.appLinear i U = LinearMap.id` using `LinearMap.ext fun s => by`. Simplify using `using QCoh.sum_app_app (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs s`. Establish `: Module.Projective Γ(X, U) Γ(G, U)` using `.of_split _ _ hc`.

Establish `: Module.Finite Γ(X, U) Γ(G, U)` using `.of_surjective (QCoh.appLinear q U) fun s => ⟨_, LinearMap.congr_fun hc s⟩`. Take `⟨V, n, e', hxV, he'⟩` from `Summand.exists_frame_of_projective (G := G) hU ⟨x, hx⟩`. Establish `hn : genRank G = n` using `(Module.finrank_eq_card_basis (he'.stalkBasis _ (genericPoint_mem hxV))).trans (Fintype.card_fin n)`. Substitute `hn` using the available equality. Conclude with `⟨V, e', hxV, he'⟩`.
-/
theorem GlobalTheory.VB.isVB_of_retract : ∀ (X : Scheme.{0}) [IsIntegral X] (F G : X.Modules) (i : G ⟶ F)
    (q : F ⟶ G) (r : ℕ), i ≫ q = 𝟙 G → IsVB F r → IsVB G (genRank G) := by
  intro X _ F G i q r hiq hF x
  have := hF.isQuasicoherent
  have hs : ∑ _ : Unit, i ≫ q = 𝟙 G := by simpa using hiq
  have : G.IsQuasicoherent :=
    QCoh.isQuasicoherent_of_sum_eq_id (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs
  obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
  have := Module.Free.of_basis (he.basis le_rfl)
  have := Module.Finite.of_basis (he.basis le_rfl)
  have hc : QCoh.appLinear q U ∘ₗ QCoh.appLinear i U = LinearMap.id := LinearMap.ext fun s => by
    simpa using QCoh.sum_app_app (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs s
  have : Module.Projective Γ(X, U) Γ(G, U) := .of_split _ _ hc
  have : Module.Finite Γ(X, U) Γ(G, U) :=
    .of_surjective (QCoh.appLinear q U) fun s => ⟨_, LinearMap.congr_fun hc s⟩
  obtain ⟨V, n, e', hxV, he'⟩ := Summand.exists_frame_of_projective (G := G) hU ⟨x, hx⟩
  have hn : genRank G = n :=
    (Module.finrank_eq_card_basis (he'.stalkBasis _ (genericPoint_mem hxV))).trans
      (Fintype.card_fin n)
  subst hn
  exact ⟨V, e', hxV, he'⟩
