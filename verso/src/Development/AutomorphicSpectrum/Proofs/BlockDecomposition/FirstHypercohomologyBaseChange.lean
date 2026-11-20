import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.HodgeAssembly

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun ω h ↦ ?_` and prove the remaining obligations. Take `⟨g, hg, hD⟩` from `ofForm_eq_zero.1 h`. Establish `h0 : d0 (OAff s) g = 0`. Use function extensionality and compare the values at `T T' φ`. Conclude with `sub_eq_zero.2 (hg φ)`.

Take `⟨r, rfl⟩` from `(hS.1 g).1 h0`. Use `Subtype.ext (Subtype.ext (funext fun T ↦ ?_))` and prove the remaining obligations. Use `(hD T).symm.trans ?_` and prove the remaining obligations. Conclude with `Derivation.map_algebraMap _ r`.
-/
theorem clForm_injective (s : X ⟶ Sp R) (hS : Stein (OAff s)) : Function.Injective (clForm s) := by
  refine (injective_iff_map_eq_zero _).2 fun ω h ↦ ?_
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 h
  have h0 : d0 (OAff s) g = 0 := by
    funext T T' φ
    exact sub_eq_zero.2 (hg φ)
  obtain ⟨r, rfl⟩ := (hS.1 g).1 h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  refine (hD T).symm.trans ?_
  exact Derivation.map_algebraMap _ r

/- English proof (translation)
Take `⟨f1, f2, f3⟩` from `hM`. Take `⟨g1, g2, g3⟩` from `hP`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property q LinearMap.id hq`. Set `e : N ≃ₗ[R] M × P` to `(hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩).1`. Use `⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, f3, g3]`.
-/
theorem vb_middle {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q) {a b : ℕ} (hM : VB R M a) (hP : VB R P b) : VB R N (a + b) := by
  obtain ⟨f1, f2, f3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := hP
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e : N ≃ₗ[R] M × P := (hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩).1
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, f3, g3]

/- English proof (translation)
Set `e : Over.mk s' ≅ (Over.pullback f).obj A` to `Over.isoMk h.isoPullback h.isoPullback_hom_snd`. Set `I : GrpObj (Over.mk s')` to `GrpObj.ofIso e.symm`. Establish `: IsMonHom e.symm.hom` using `CategoryTheory.isMonHom_ofIso e.symm`. Establish `: IsMonHom e.hom` using `inferInstanceAs (IsMonHom e.symm.inv)`. Conclude with `⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩`.
-/
theorem exists_abelian {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {s' : X' ⟶ S'}
    {φ : X' ⟶ A.left} {f : S' ⟶ S} (h : IsPullback φ s' A.hom f) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') := by
  let e : Over.mk s' ≅ (Over.pullback f).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  let I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact ⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩

/- English proof (translation)
Use `⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩` and prove the remaining obligations. Establish `h1 : q z = 0`. Apply `eP.injective` to reduce the goal to its premises. Rewrite using `[← s₂, hz, map_zero, map_zero]`. Take `⟨m, rfl⟩` from `(hex z).1 h1`.

Establish `h2 : eM m = 0` using `hi' (by rw [← s₁, hz, map_zero])`. Rewrite using `[(map_eq_zero_iff eM eM.injective).1 h2, map_zero]`. Take `⟨z, hz⟩` from `hq (eP.symm (q' x))`. Establish `h1 : q' (x - L z) = 0`. Rewrite using `[map_sub, s₂, hz, LinearEquiv.apply_symm_apply, sub_self]`.

Take `⟨m', hm'⟩` from `(hex' _).1 h1`. Use `⟨z + i (eM.symm m'), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, s₁, LinearEquiv.apply_symm_apply, hm']`. Normalize the expressions using the abelian group laws.
-/
theorem bijective_middle {M N P M' N' P' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    [AddCommGroup P'] [Module R P'] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (i' : M' →ₗ[R] N') (q' : N' →ₗ[R] P')
    (L : N →ₗ[R] N') (eM : M ≃ₗ[R] M') (eP : P ≃ₗ[R] P') (hex : Function.Exact i q)
    (hq : Function.Surjective q) (hex' : Function.Exact i' q') (hi' : Function.Injective i')
    (s₁ : ∀ m, L (i m) = i' (eM m)) (s₂ : ∀ n, q' (L n) = eP (q n)) : Function.Bijective L := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
  · have h1 : q z = 0 := by
      apply eP.injective
      rw [← s₂, hz, map_zero, map_zero]
    obtain ⟨m, rfl⟩ := (hex z).1 h1
    have h2 : eM m = 0 := hi' (by rw [← s₁, hz, map_zero])
    rw [(map_eq_zero_iff eM eM.injective).1 h2, map_zero]
  · obtain ⟨z, hz⟩ := hq (eP.symm (q' x))
    have h1 : q' (x - L z) = 0 := by
      rw [map_sub, s₂, hz, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨m', hm'⟩ := (hex' _).1 h1
    refine ⟨z + i (eM.symm m'), ?_⟩
    rw [map_add, s₁, LinearEquiv.apply_symm_apply, hm']
    abel

section BaseChange

variable [Algebra R R'] {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}

def clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : GlobForm s →ₗ[R] HH1 s :=
  clForm s ∘ₗ (LinearEquiv.ofTop _ hcl).symm.toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem clG_apply (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (ω : GlobForm s) :
    clG s hcl ω = clForm s ⟨ω, hcl ▸ trivial⟩ := rfl

/- English proof (translation)
The claim follows from `hi.comp (LinearEquiv.ofTop _ hcl).symm.injective`.
-/
theorem clG_injective (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hi : Function.Injective (clForm s)) :
    Function.Injective (clG s hcl) :=
  hi.comp (LinearEquiv.ofTop _ hcl).symm.injective

/- English proof (translation)
Introduce `c`. Express the relevant statement in the definitionally equal form `c ∈ CechHodgeFiltration s ↔ _`. Rewrite using `[cechHodgeFiltration_eq_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ω, rfl⟩`.

Conclude with `⟨ω.1, congrArg (clForm s) (Subtype.ext rfl)⟩`. Introduce and unpack `⟨ω, rfl⟩`. Conclude with `⟨_, rfl⟩`.
-/
theorem exact_clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : Function.Exact (clG s hcl) (toHO1 s) := by
  intro c
  change c ∈ CechHodgeFiltration s ↔ _
  rw [cechHodgeFiltration_eq_range]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω.1, congrArg (clForm s) (Subtype.ext rfl)⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨_, rfl⟩

/- English proof (translation)
Set `L : R' ⊗[R] HH1 s →ₗ[R'] HH1 s'` to `GlobalTheory.DeRham.liftSemi (pullHH1 w)`. Establish `hL : ∀ c, L (1 ⊗ₜ c) = pullHH1 w c` using `fun c ↦ by`. Rewrite using `[show L (1 ⊗ₜ c) = (1 : R') • pullHH1 w c from rfl, one_smul]`. Establish `k₁ : ∀ ω, pullHH1 w (clG s hcl ω) = clG s' hcl' (eF (1 ⊗ₜ ω))` using `fun ω ↦ (IsPull1.eq_pullHH1 w (IsPullForm.cl (ω := ⟨ω, hcl ▸ trivial⟩) (ω' := ⟨eF (1 ⊗ₜ ω), hcl' ▸ trivial⟩) (hF ω))).symm`. Establish `k₂ : ∀ c, toHO1 s' (pullHH1 w c) = eO (1 ⊗ₜ toHO1 s c)` using `fun c ↦ (IsPullO.eq_pullHO1 w (IsPull1.toO (isPull1_pullHH1 w c))).trans (IsPullO.eq_pullHO1 w (hO (toHO1 s c))).symm`.

Establish `hex : Function.Exact ((clG s hcl).baseChange R') ((toHO1 s).baseChange R')`. Use `lTensor_exact R' (exact_clG s hcl) hsurj` as an intermediate fact. Simplify `this` using `only [LinearMap.baseChange_eq_ltensor]`. Establish `hq : Function.Surjective ((toHO1 s).baseChange R')`. Use `LinearMap.lTensor_surjective R' hsurj` as an intermediate fact.

Simplify `this` using `only [LinearMap.baseChange_eq_ltensor]`. Establish `hb : Function.Bijective L`. Use `bijective_middle ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') (clG s' hcl') (toHO1 s') L eF eO hex hq (exact_clG s' hcl') (clG_injective s' hcl' hinj') (fun m ↦ ?_) fun n ↦ ?_` and prove the remaining obligations. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x ω`. Establish `e : x ⊗ₜ[R] ω = x • ((1 : R') ⊗ₜ[R] ω)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[LinearMap.baseChange_tmul, e, map_smul, map_smul, ← k₁]`.

Rewrite using `[show L (x ⊗ₜ clG s hcl ω) = x • pullHH1 w (clG s hcl ω) from rfl]`. Proceed by induction on `n using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x c`.

Establish `e : x ⊗ₜ[R] toHO1 s c = x • ((1 : R') ⊗ₜ[R] toHO1 s c)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[LinearMap.baseChange_tmul, e, map_smul, ← k₂]`. Rewrite using `[show L (x ⊗ₜ c) = x • pullHH1 w c from rfl, map_smul]`. Use `⟨LinearEquiv.ofBijective L hb, fun c ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearEquiv.ofBijective_apply, hL]`. Conclude with `isPull1_pullHH1 w c`.
-/
theorem first_hypercohomology_base_change (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (hcl : ClosedForm s = ⊤)
    (hcl' : ClosedForm s' = ⊤) (hsurj : Function.Surjective (toHO1 s))
    (hinj' : Function.Injective (clForm s'))
    (eF : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s') (hF : ∀ c, IsPullForm w c (eF (1 ⊗ₜ c)))
    (eO : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s') (hO : ∀ c, IsPullO w c (eO (1 ⊗ₜ c))) :
    ∃ e : R' ⊗[R] HH1 s ≃ₗ[R'] HH1 s', ∀ c, IsPull1 w c (e (1 ⊗ₜ c)) := by
  let L : R' ⊗[R] HH1 s →ₗ[R'] HH1 s' := GlobalTheory.DeRham.liftSemi (pullHH1 w)
  have hL : ∀ c, L (1 ⊗ₜ c) = pullHH1 w c := fun c ↦ by
    rw [show L (1 ⊗ₜ c) = (1 : R') • pullHH1 w c from rfl, one_smul]
  have k₁ : ∀ ω, pullHH1 w (clG s hcl ω) = clG s' hcl' (eF (1 ⊗ₜ ω)) := fun ω ↦
    (IsPull1.eq_pullHH1 w (IsPullForm.cl (ω := ⟨ω, hcl ▸ trivial⟩)
      (ω' := ⟨eF (1 ⊗ₜ ω), hcl' ▸ trivial⟩) (hF ω))).symm
  have k₂ : ∀ c, toHO1 s' (pullHH1 w c) = eO (1 ⊗ₜ toHO1 s c) := fun c ↦
    (IsPullO.eq_pullHO1 w (IsPull1.toO (isPull1_pullHH1 w c))).trans
      (IsPullO.eq_pullHO1 w (hO (toHO1 s c))).symm
  have hex : Function.Exact ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') := by
    have := lTensor_exact R' (exact_clG s hcl) hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hq : Function.Surjective ((toHO1 s).baseChange R') := by
    have := LinearMap.lTensor_surjective R' hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hb : Function.Bijective L := by
    refine bijective_middle ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') (clG s' hcl') (toHO1 s') L eF eO
      hex hq (exact_clG s' hcl') (clG_injective s' hcl' hinj') (fun m ↦ ?_) fun n ↦ ?_
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x ω =>
        have e : x ⊗ₜ[R] ω = x • ((1 : R') ⊗ₜ[R] ω) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, map_smul, ← k₁]
        rw [show L (x ⊗ₜ clG s hcl ω) = x • pullHH1 w (clG s hcl ω) from rfl]
    · induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x c =>
        have e : x ⊗ₜ[R] toHO1 s c = x • ((1 : R') ⊗ₜ[R] toHO1 s c) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, ← k₂]
        rw [show L (x ⊗ₜ c) = x • pullHH1 w c from rfl, map_smul]
  refine ⟨LinearEquiv.ofBijective L hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, hL]
  exact isPull1_pullHH1 w c

end BaseChange

/- English proof (translation)
Introduce `hS hP hH hD hW hO hF R _ A _ g hA hg`. Establish `s₀ : Stein (OAff A.hom)` using `hS R A g hA hg`. Establish `p₀ : VB R (GlobForm A.hom) g` using `(hP R A g hA hg).2`. Establish `h₀ : VB R (HO1 A.hom) g` using `hH R A g hA hg`. Take `⟨hcl, hsurj⟩ : ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom)` from `hD R A g hA hg`.

Establish `hinj` using `clForm_injective A.hom s₀`. Establish `v : VB R (HH1 A.hom) (g + g)` using `vb_middle (clG A.hom hcl) (toHO1 A.hom) (clG_injective A.hom hcl hinj) hsurj (exact_clG A.hom hcl) p₀ h₀`. Use `⟨⟨v.1, v.2.1, fun p ↦ by rw [two_mul]; exact v.2.2 p⟩, hW R A g hA hg, p₀, h₀, ⟨hcl, hinj, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩` and prove the remaining obligations. Take `⟨eO, heO⟩` from `hO R A g hA hg R' X' s' φ h`. Take `⟨eF, heF⟩` from `hF R A g hA hg R' X' s' φ h`.

Take `⟨_, hA'⟩` from `exists_abelian A hA h`. Establish `hg' : SmoothOfRelativeDimension g (Over.mk s').hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg`. Establish `s₁ : Stein (OAff s')` using `hS R' (Over.mk s') g hA' hg'`. Establish `hcl' : ClosedForm s' = ⊤` using `(hD R' (Over.mk s') g hA' hg').1`. Conclude with `⟨first_hypercohomology_base_change h.w hcl hcl' hsurj (clForm_injective s' s₁) eF heF eO heO, ⟨eF, heF⟩, ⟨eO, heO⟩⟩`.
-/
theorem abelianHodgeDeRham_of_statements : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt →
    GlobalTheory.Published.AbelianHodgeDeRham := by
  intro hS hP hH hD hW hO hF R _ A _ g hA hg
  have s₀ : Stein (OAff A.hom) := hS R A g hA hg
  have p₀ : VB R (GlobForm A.hom) g := (hP R A g hA hg).2
  have h₀ : VB R (HO1 A.hom) g := hH R A g hA hg
  obtain ⟨hcl, hsurj⟩ : ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom) := hD R A g hA hg
  have hinj := clForm_injective A.hom s₀
  have v : VB R (HH1 A.hom) (g + g) := vb_middle (clG A.hom hcl) (toHO1 A.hom) (clG_injective A.hom hcl hinj) hsurj
    (exact_clG A.hom hcl) p₀ h₀
  refine ⟨⟨v.1, v.2.1, fun p ↦ by rw [two_mul]; exact v.2.2 p⟩, hW R A g hA hg, p₀, h₀, ⟨hcl, hinj, hsurj⟩,
    fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨eO, heO⟩ := hO R A g hA hg R' X' s' φ h
  obtain ⟨eF, heF⟩ := hF R A g hA hg R' X' s' φ h
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  have s₁ : Stein (OAff s') := hS R' (Over.mk s') g hA' hg'
  have hcl' : ClosedForm s' = ⊤ := (hD R' (Over.mk s') g hA' hg').1
  exact ⟨first_hypercohomology_base_change h.w hcl hcl' hsurj (clForm_injective s' s₁) eF heF eO heO, ⟨eF, heF⟩, ⟨eO, heO⟩⟩

end GlobalTheory.CompanionTheory.HodgeAssembly
