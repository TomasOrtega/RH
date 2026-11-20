import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtensionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Use `show φ (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b a) = (((Formalism.UG.bc φ g)⁻¹ : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) b a`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem bc_invTr {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {N : ℕ} (g : GL (Fin N) A) :
    Formalism.UG.bc φ (inside₂ A N g) = inside₂ B N (Formalism.UG.bc φ g) := by
  apply Units.ext
  ext a b
  show φ (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b a) = (((Formalism.UG.bc φ g)⁻¹ : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) b a
  rw [← map_inv]
  rfl

/- English proof (translation)
Establish `h` using `mapVV_rhoK φ lam (invTrK (embGL emb γ)) x`. Use `h.trans (congrArg (fun g : ι → GL (Fin n) ℂ => rhoK lam g (mapVV φ lam x)) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Use `show Formalism.UG.bc φ (inside₂ K n (Formalism.UG.bc (emb τ) γ)) = inside₂ ℂ n (Formalism.UG.bc (φ.comp (emb τ)) γ)`. Rewrite using `[bc_invTr]`.

Use `congr 1`.
-/
theorem mapVV_rhoVr {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (x : VV K lam) :
    mapVV φ lam (rhoVr emb lam γ x) = rhoVr (fun τ => φ.comp (emb τ)) lam γ (mapVV φ lam x) := by
  have h := mapVV_rhoK φ lam (invTrK (embGL emb γ)) x
  refine h.trans (congrArg (fun g : ι → GL (Fin n) ℂ => rhoK lam g (mapVV φ lam x)) ?_)
  funext τ
  show Formalism.UG.bc φ (inside₂ K n (Formalism.UG.bc (emb τ) γ)) = inside₂ ℂ n (Formalism.UG.bc (φ.comp (emb τ)) γ)
  rw [bc_invTr]
  congr 1

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

def conjVV {ι : Type} [Fintype ι] {n : ℕ} (τ : ℂ ≃+* ℂ) (lam : ι → DomWeight n) : VV ℂ lam ≃+ VV ℂ lam where
  toFun := mapVV (τ : ℂ →+* ℂ) lam
  invFun := mapVV (τ.symm : ℂ →+* ℂ) lam
  left_inv x := Subtype.ext (by
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  right_inv x := Subtype.ext (by
    have e : (τ : ℂ →+* ℂ).comp (τ.symm : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  map_add' x y := map_add _ x y

/- English proof (translation)
Introduce `γ h k`. Establish `hk : (k : G) ∈ J` using `hJ ▸ k.2`. Establish `e` using `hF γ h ⟨k, hk⟩`. Use `show T (F (ι γ * h * (k : G))) = ((χ' k : ℂˣ) : ℂ) • ρ γ (T (F h))`. Establish `e' : F (ι γ * h * (k : G)) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • ρ γ (F h)` using `e`.

Rewrite using `[e', hs, hρ, ← hχ k hk k.2]`.
-/
theorem post_mem {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup G} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) : (fun g => T (F g)) ∈ Bridge.AdForms ι ρ J' χ' := by
  intro γ h k
  have hk : (k : G) ∈ J := hJ ▸ k.2
  have e := hF γ h ⟨k, hk⟩
  show T (F (ι γ * h * (k : G))) = ((χ' k : ℂˣ) : ℂ) • ρ γ (T (F h))
  have e' : F (ι γ * h * (k : G)) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • ρ γ (F h) := e
  rw [e', hs, hρ, ← hχ k hk k.2]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

/- English proof (translation)
Take `⟨gramR, c0R, c0L, hT, hbc⟩` from `hP.lift.c0`. Establish `hf : (inC M.c').comp M.jL = D.what₂.embLL` using `hP.lift.field`. Establish `key : ∀ w : VsV D i D.what₂.LL, c (mapVV D.what₂.embLL (lamV D i) w) = c0L i w`. Introduce `w`. Take `⟨w', hw', hw''⟩` from `hbc w`.

Use `(hc w' _ ?_).trans hw''` and prove the remaining obligations. Rewrite using `[mapVV_coe, hw', MvPolynomial.map_map, hf]`. Establish `hL : c ∘ₗ rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE = (R.cV i).coef.ρ γ ∘ₗ c`. Apply `LinearMap.ext_on_range (span_mapVV D.what₂.embLL (lamV D i))` to reduce the goal to its premises. Introduce `k`.

Use `show c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k))) = (R.cV i).coef.ρ γ (c (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k)))`. Rewrite using `[← mapVV_rhoVr]`. Use `(key _).trans (((hT.mapL i).1 γ γE hγ _).trans ?_)` and prove the remaining obligations. Conclude with `congrArg _ (key _).symm`. Conclude with `LinearMap.congr_fun hL x`.
-/
theorem c_rhoVr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E) (hγ : Bridge.IsRatMat (Vc D i) γ γE) (x : VsV D i ℂ) :
    c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE x) = (R.cV i).coef.ρ γ (c x) := by
  obtain ⟨gramR, c0R, c0L, hT, hbc⟩ := hP.lift.c0
  have hf : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have key : ∀ w : VsV D i D.what₂.LL, c (mapVV D.what₂.embLL (lamV D i) w) = c0L i w := by
    intro w
    obtain ⟨w', hw', hw''⟩ := hbc w
    refine (hc w' _ ?_).trans hw''
    rw [mapVV_coe, hw', MvPolynomial.map_map, hf]
  have hL : c ∘ₗ rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE = (R.cV i).coef.ρ γ ∘ₗ c := by
    apply LinearMap.ext_on_range (span_mapVV D.what₂.embLL (lamV D i))
    intro k
    show c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k))) =
      (R.cV i).coef.ρ γ (c (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k)))
    rw [← mapVV_rhoVr]
    refine (key _).trans (((hT.mapL i).1 γ γE hγ _).trans ?_)
    exact congrArg _ (key _).symm
  exact LinearMap.congr_fun hL x

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

/- English proof (translation)
Rewrite using `[mapVV_rhoVr]`. Establish `e : (fun τ' => (τ : ℂ →+* ℂ).comp (D.what₂.embLL.comp (labLL D τ'))) = fun τ' => D.what₂.embLL.comp (labLL D τ')`. Use function extensionality and compare the values at `τ'`. Use extensionality with `a`. Conclude with `hτ _ a`.

Rewrite using `[e]`.
-/
theorem mapVV_tau_rhoVr (D : D7) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x)
    (γE : GL (Fin (Vc D i).rank) D.host.E) (x : VsV D i ℂ) :
    mapVV (τ : ℂ →+* ℂ) (lamV D i) (rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE x) =
      rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := by
  rw [mapVV_rhoVr]
  have e : (fun τ' => (τ : ℂ →+* ℂ).comp (D.what₂.embLL.comp (labLL D τ'))) = fun τ' => D.what₂.embLL.comp (labLL D τ') := by
    funext τ'
    ext a
    exact hτ _ a
  rw [e]

/- English proof (translation)
Set `cb` to `LinearEquiv.ofBijective c hb`. Establish `hcb : ∀ x, cb.symm (c x) = x` using `fun x => cb.symm_apply_apply x`. Set `TW : (R.cV i).W ≃+ (R.cV i).W` to `cb.symm.toAddEquiv.trans ((conjVV τ (lamV D i)).trans cb.toAddEquiv)`. Establish `hTW : ∀ w, TW w = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) (cb.symm w))` using `fun w => rfl`. Establish `hTc : ∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x)` using `fun x => by rw [hTW, hcb]`.

Use `⟨TW, fun a w => ?_, hTc, fun γ w => ?_⟩` and prove the remaining obligations. Rewrite using `[hTW, hTW, map_smul, map_smulₛₗ, map_smul]`. Both sides reduce to the same expression. Take `⟨x, rfl⟩` from `hb.2 w`. Take `⟨γE, hγ⟩` from `GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ`.

Rewrite using `[← c_rhoVr M hP c hc γ γE hγ x, hTc, hTc, mapVV_tau_rhoVr D i τ hτ, c_rhoVr M hP c hc γ γE hγ]`.
-/
theorem exists_conjW {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (hb : Function.Bijective c) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x) :
    ∃ TW : (R.cV i).W ≃+ (R.cV i).W, (∀ (a : ℂ) w, TW (a • w) = τ a • TW w) ∧
      (∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x)) ∧
      ∀ γ w, TW ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW w) := by
  let cb := LinearEquiv.ofBijective c hb
  have hcb : ∀ x, cb.symm (c x) = x := fun x => cb.symm_apply_apply x
  let TW : (R.cV i).W ≃+ (R.cV i).W := cb.symm.toAddEquiv.trans ((conjVV τ (lamV D i)).trans cb.toAddEquiv)
  have hTW : ∀ w, TW w = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) (cb.symm w)) := fun w => rfl
  have hTc : ∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := fun x => by rw [hTW, hcb]
  refine ⟨TW, fun a w => ?_, hTc, fun γ w => ?_⟩
  · rw [hTW, hTW, map_smul, map_smulₛₗ, map_smul]
    rfl
  · obtain ⟨x, rfl⟩ := hb.2 w
    obtain ⟨γE, hγ⟩ := GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ
    rw [← c_rhoVr M hP c hc γ γE hγ x, hTc, hTc, mapVV_tau_rhoVr D i τ hτ, c_rhoVr M hP c hc γ γE hγ]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

set_option maxHeartbeats 8000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj`. Establish `hX` using `GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins`. Take `⟨c₁, -, hb₁, hu⟩` from `hX`. Establish `hb : Function.Bijective c` using `(congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hu c hc)).mpr hb₁`. Establish `hY` using `exists_conjW M hPins c hc hb τ hFix.host`.

Take `⟨TW, hs, hTc, hρ⟩` from `hY`. Establish `hZ` using `(GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix`. Take `⟨hJ, hχ⟩` from `hZ`. Establish `hV` using `hCore.models.HV i t`. Establish `hV'` using `hCore.models.HV i t'`.

Establish `hs' : ∀ (a : ℂ) w, TW.symm (a • w) = τ.symm a • TW.symm w`. Introduce `a w`. Apply `TW.injective` to reduce the goal to its premises. Rewrite using `[hs, TW.apply_symm_apply, TW.apply_symm_apply, RingEquiv.apply_symm_apply]`. Establish `hρ' : ∀ γ w, TW.symm ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW.symm w)`.

Introduce `γ w`. Apply `TW.injective` to reduce the goal to its premises. Use `(TW.apply_symm_apply _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (hρ γ (TW.symm w)).symm` and prove the remaining obligations. Conclude with `congrArg _ (TW.apply_symm_apply w).symm`.

Establish `hχ' : ∀ k (hk : k ∈ levJ R i t') (hk' : k ∈ levJ R i t), (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ.symm (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk⟩ : ℂˣ) : ℂ)`. Introduce `k hk hk'`. Conclude with `(τ.symm_apply_apply _).symm.trans (congrArg τ.symm (hχ k hk' hk).symm)`. Establish `hmem` using `fun y => hV.2.1.le (LinearMap.mem_range_self (R.HV i t).e y)`. Establish `hmem'` using `fun y => hV'.2.1.le (LinearMap.mem_range_self (R.HV i t').e y)`.

Establish `hfwd : ∀ y, ∃ y', (R.HV i t').e y' = fun g => TW ((R.HV i t).e y g)` using `fun y => LinearMap.mem_range.1 (hV'.2.1.ge (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ (hmem y)))`. Establish `hbwd : ∀ y', ∃ y, (R.HV i t).e y = fun g => TW.symm ((R.HV i t').e y' g)` using `fun y' => LinearMap.mem_range.1 (hV.2.1.ge (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ.symm _ _ τ.symm TW.symm.toAddMonoidHom hs' hρ' hχ' (hmem' y')))`. Use `choose φ hφ using hfwd`. Establish `hφadd : ∀ y z, φ (y + z) = φ y + φ z`. Introduce `y z`.

Apply `hV'.1` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `e1` using `congrFun (hφ (y + z)) g`. Establish `e2` using `congrFun (hφ y) g`. Establish `e3` using `congrFun (hφ z) g`.

Use `beta_reduce at e1 e2 e3`. Use `e1.trans ?_` and prove the remaining obligations. Conclude with `(congrArg TW (congrFun (map_add (R.HV i t).e y z) g)).trans ((map_add TW _ _).trans ((congrArg₂ (· + ·) e2 e3).symm.trans (congrFun (map_add (R.HV i t').e (φ y) (φ z)) g).symm))`. Establish `hφsmul : ∀ (a : ℂ) y, φ (a • y) = τ a • φ y`. Introduce `a y`.

Apply `hV'.1` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `e1` using `congrFun (hφ (a • y)) g`. Establish `e2` using `congrFun (hφ y) g`. Use `beta_reduce at e1 e2`.

Use `e1.trans ?_` and prove the remaining obligations. Conclude with `(congrArg TW (congrFun (map_smul (R.HV i t).e a y) g)).trans ((hs _ _).trans ((congrArg (τ a • ·) e2).symm.trans (congrFun (map_smul (R.HV i t').e (τ a) (φ y)) g).symm))`. Establish `hbij : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `y z h`.

Apply `hV.1` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `congrFun ((hφ y).symm.trans ((congrArg (R.HV i t').e h).trans (hφ z))) g` as an intermediate fact. Conclude with `TW.injective this`. Introduce `y'`.

Take `⟨y, hy⟩` from `hbwd y'`. Use `⟨y, hV'.1 ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Conclude with `(congrFun (hφ y) g).trans ((congrArg TW (congrFun hy g)).trans (TW.apply_symm_apply _))`. Use `⟨AddEquiv.ofBijective (AddMonoidHom.mk' φ hφadd) hbij, fun a y => hφsmul a y, fun y y' => ?_⟩` and prove the remaining obligations.

Use `show ConjForm R i τ c t t' y y' ↔ y' = φ y`. Prove the components needed by the constructor for the conclusion. Introduce `hC`. Establish `key : ∀ h, (R.HV i t').e y' (Formalism.IndefR.FWT.fin (Vc D i) h) = TW ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))`. Introduce `h`.

Establish `h0` using `hC h`. Take `⟨x, x', hx, h1, h2⟩` from `h0`. Establish `hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x` using `Subtype.ext (hx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)`. Conclude with `h2.trans ((congrArg c hx').trans ((hTc x).symm.trans (congrArg TW h1.symm)))`. Apply `hV'.1` to reduce the goal to its premises.

Use `Eq.trans ?_ (hφ y).symm` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `hs0` using `(finHom (Vc D i)).rangeRestrict_surjective g`. Take `⟨h, hh⟩` from `hs0`. Conclude with `Eq.subst (motive := fun g => (R.HV i t').e y' g = TW ((R.HV i t).e y g)) hh (key h)`.

Introduce and unpack `rfl h`. Establish `hs1` using `hb.2 ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))`. Take `⟨x, hx⟩` from `hs1`. Use `⟨x, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x, GlobalTheory.CoefModel.mapVV_coe _ _ _, hx.symm, ?_⟩` and prove the remaining obligations. Use `(congrFun (hφ y) (Formalism.IndefR.FWT.fin (Vc D i) h)).trans ?_` and prove the remaining obligations.

Conclude with `(congrArg TW hx.symm).trans (hTc x)`.
-/
theorem exists_conjForm_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∃ φ : (R.HV i t).H ≃+ (R.HV i t').H, (∀ (a : ℂ) y, φ (a • y) = τ a • φ y) ∧ ∀ y y', ConjForm R i τ c t t' y y' ↔ y' = φ y := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj
  have hX := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  obtain ⟨c₁, -, hb₁, hu⟩ := hX
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hu c hc)).mpr hb₁
  have hY := exists_conjW M hPins c hc hb τ hFix.host
  obtain ⟨TW, hs, hTc, hρ⟩ := hY
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  obtain ⟨hJ, hχ⟩ := hZ
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hs' : ∀ (a : ℂ) w, TW.symm (a • w) = τ.symm a • TW.symm w := by
    intro a w
    apply TW.injective
    rw [hs, TW.apply_symm_apply, TW.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ γ w, TW.symm ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW.symm w) := by
    intro γ w
    apply TW.injective
    refine (TW.apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (hρ γ (TW.symm w)).symm
    exact congrArg _ (TW.apply_symm_apply w).symm
  have hχ' : ∀ k (hk : k ∈ levJ R i t') (hk' : k ∈ levJ R i t),
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) =
        τ.symm (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    intro k hk hk'
    exact (τ.symm_apply_apply _).symm.trans (congrArg τ.symm (hχ k hk' hk).symm)
  have hmem := fun y => hV.2.1.le (LinearMap.mem_range_self (R.HV i t).e y)
  have hmem' := fun y => hV'.2.1.le (LinearMap.mem_range_self (R.HV i t').e y)
  have hfwd : ∀ y, ∃ y', (R.HV i t').e y' = fun g => TW ((R.HV i t).e y g) := fun y =>
    LinearMap.mem_range.1 (hV'.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ (hmem y)))
  have hbwd : ∀ y', ∃ y, (R.HV i t).e y = fun g => TW.symm ((R.HV i t').e y' g) := fun y' =>
    LinearMap.mem_range.1 (hV.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ.symm _ _ τ.symm TW.symm.toAddMonoidHom hs' hρ' hχ' (hmem' y')))
  choose φ hφ using hfwd
  have hφadd : ∀ y z, φ (y + z) = φ y + φ z := by
    intro y z
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (y + z)) g
    have e2 := congrFun (hφ y) g
    have e3 := congrFun (hφ z) g
    beta_reduce at e1 e2 e3
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_add (R.HV i t).e y z) g)).trans ((map_add TW _ _).trans
      ((congrArg₂ (· + ·) e2 e3).symm.trans (congrFun (map_add (R.HV i t').e (φ y) (φ z)) g).symm))
  have hφsmul : ∀ (a : ℂ) y, φ (a • y) = τ a • φ y := by
    intro a y
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (a • y)) g
    have e2 := congrFun (hφ y) g
    beta_reduce at e1 e2
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_smul (R.HV i t).e a y) g)).trans ((hs _ _).trans
      ((congrArg (τ a • ·) e2).symm.trans (congrFun (map_smul (R.HV i t').e (τ a) (φ y)) g).symm))
  have hbij : Function.Bijective φ := by
    constructor
    · intro y z h
      apply hV.1
      funext g
      have := congrFun ((hφ y).symm.trans ((congrArg (R.HV i t').e h).trans (hφ z))) g
      exact TW.injective this
    · intro y'
      obtain ⟨y, hy⟩ := hbwd y'
      refine ⟨y, hV'.1 ?_⟩
      funext g
      exact (congrFun (hφ y) g).trans ((congrArg TW (congrFun hy g)).trans (TW.apply_symm_apply _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' φ hφadd) hbij, fun a y => hφsmul a y, fun y y' => ?_⟩
  show ConjForm R i τ c t t' y y' ↔ y' = φ y
  constructor
  · intro hC
    have key : ∀ h, (R.HV i t').e y' (Formalism.IndefR.FWT.fin (Vc D i) h) = TW ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h)) := by
      intro h
      have h0 := hC h
      obtain ⟨x, x', hx, h1, h2⟩ := h0
      have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext (hx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
      exact h2.trans ((congrArg c hx').trans ((hTc x).symm.trans (congrArg TW h1.symm)))
    apply hV'.1
    refine Eq.trans ?_ (hφ y).symm
    funext g
    have hs0 := (finHom (Vc D i)).rangeRestrict_surjective g
    obtain ⟨h, hh⟩ := hs0
    exact Eq.subst (motive := fun g => (R.HV i t').e y' g = TW ((R.HV i t).e y g)) hh (key h)
  · rintro rfl h
    have hs1 := hb.2 ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))
    obtain ⟨x, hx⟩ := hs1
    refine ⟨x, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x, GlobalTheory.CoefModel.mapVV_coe _ _ _, hx.symm, ?_⟩
    refine (congrFun (hφ y) (Formalism.IndefR.FWT.fin (Vc D i) h)).trans ?_
    exact (congrArg TW hx.symm).trans (hTc x)

end GlobalTheory.ConjTwist
