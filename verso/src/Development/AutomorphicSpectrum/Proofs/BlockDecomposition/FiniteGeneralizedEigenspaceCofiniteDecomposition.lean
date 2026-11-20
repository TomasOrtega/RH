import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Formalism.L2.Host

namespace GlobalTheory.CompanionTheory.CuspTwist

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def conjChi (a : ℕ) (χ : HChar E) : Module.End ℂ (Sm E a) ≃ₐ[ℂ] Module.End ℂ (Sm E a) :=
  LinearEquiv.conjAlgEquiv ℂ (mulChi a χ)

/- English proof (translation)
Simplify using `[conjChi, LinearEquiv.conjAlgEquiv_apply]`.
-/
theorem conjChi_apply (χ : HChar E) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjChi a χ z (mulChi a χ φ) = mulChi a χ (z φ) := by
  simp [conjChi, LinearEquiv.conjAlgEquiv_apply]

/- English proof (translation)
Use `LinearMap.ext fun ψ => ?_` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `(mulChi a χ).surjective ψ`. Rewrite using `[conjChi_apply, cap_mulChi]`.
-/
theorem conjChi_cap (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) :
    conjChi a χ (cap τ (u + expo χ τ)) = cap τ u := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (mulChi a χ).surjective ψ
  rw [conjChi_apply, cap_mulChi]

/- English proof (translation)
Rewrite using `[Zalg, AlgHom.map_adjoin]`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨τ, u, rfl⟩, rfl⟩`.

Conclude with `⟨τ, u - expo χ τ, by`. Use `conjChi_cap (a := a) χ τ (u - expo χ τ)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this⟩`. Introduce and unpack `⟨τ, u, rfl⟩`.

Conclude with `⟨_, ⟨τ, u + expo χ τ, rfl⟩, conjChi_cap χ τ u⟩`.
-/
theorem map_Zalg (χ : HChar E) : (Zalg E a).map (conjChi a χ : _ →ₐ[ℂ] _) = Zalg E a := by
  rw [Zalg, AlgHom.map_adjoin]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u - expo χ τ, by
      have := conjChi_cap (a := a) χ τ (u - expo χ τ)
      rw [sub_add_cancel] at this
      exact this⟩
  · rintro ⟨τ, u, rfl⟩
    exact ⟨_, ⟨τ, u + expo χ τ, rfl⟩, conjChi_cap χ τ u⟩

/- English proof (translation)
Take `⟨hsub, V, hV, hz⟩` from `hJ`. Establish `hm : ∀ z ∈ Zalg E a, conjChi a χ z ∈ Zalg E a` using `fun z h => by`. Rewrite using `[← map_Zalg (a := a) χ]`. Conclude with `⟨z, h, rfl⟩`. Use `⟨?_, V.map (conjChi a χ).toLinearMap, inferInstance, fun z h => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, hj, rfl⟩`. Conclude with `hm _ (hsub hj)`. Rewrite `h` using `[← map_Zalg (a := a) χ]`. Take `⟨w, hw, rfl⟩` from `h`. Establish `h1` using `Submodule.mem_map_of_mem (f := (conjChi a χ).toLinearMap) (hz w hw)`.

Rewrite `h1` using `[Submodule.map_sup, Submodule.map_span]`. Take `⟨y, hy, y', hy', e⟩` from `Submodule.mem_sup.1 h1`. Use `Submodule.mem_sup.2 ⟨y, hy, y', Submodule.span_mono ?_ hy', e⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨x, hx, j, hj, rfl⟩, rfl⟩`. Conclude with `⟨conjChi a χ x, hm _ hx, conjChi a χ j, ⟨j, hj, rfl⟩, map_mul (conjChi a χ) x j⟩`.
-/
theorem cofin_conj (χ : HChar E) {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) :
    Cofin (conjChi a χ '' J) := by
  obtain ⟨hsub, V, hV, hz⟩ := hJ
  have hm : ∀ z ∈ Zalg E a, conjChi a χ z ∈ Zalg E a := fun z h => by
    rw [← map_Zalg (a := a) χ]
    exact ⟨z, h, rfl⟩
  refine ⟨?_, V.map (conjChi a χ).toLinearMap, inferInstance, fun z h => ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hm _ (hsub hj)
  · rw [← map_Zalg (a := a) χ] at h
    obtain ⟨w, hw, rfl⟩ := h
    have h1 := Submodule.mem_map_of_mem (f := (conjChi a χ).toLinearMap) (hz w hw)
    rw [Submodule.map_sup, Submodule.map_span] at h1
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨y, hy, y', Submodule.span_mono ?_ hy', e⟩
    rintro _ ⟨_, ⟨x, hx, j, hj, rfl⟩, rfl⟩
    exact ⟨conjChi a χ x, hm _ hx, conjChi a χ j, ⟨j, hj, rfl⟩, map_mul (conjChi a χ) x j⟩

/- English proof (translation)
Establish `h1 : chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) = (Model.absC E s).1 (infId E (Matrix.GeneralLinearGroup.det (Unitary.toUnits k)))` using `congrArg (Model.absC E s).1 (det_infGL _)`. Rewrite using `[h1]`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = 1`. Rewrite using `[Model.logNorm_infId]`.

Establish `hd : star (k.1.det) * k.1.det = 1` using `(Matrix.det_of_mem_unitary k.2).1`. Establish `hn : ∀ w, ‖(k.1.det : Cinf E) w‖ = 1` using `fun w => by`. Use `congrFun hd w` as an intermediate fact. Establish `h2 : ‖(k.1.det : Cinf E) w‖ * ‖(k.1.det : Cinf E) w‖ = 1`. Establish `h3` using `congrArg norm this`.

Simplify using `using h3`. Use polynomial arithmetic with `[norm_nonneg ((k.1.det : Cinf E) w)]`. Establish `e : ∀ w, ‖((Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) w‖ = 1` using `hn`. Simplify using `[e, hn]`.
-/
theorem chiDet_absC_cpt (s : ℂ) (k : Kinf E a) :
    chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) = 1 := by
  have h1 : chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) =
      (Model.absC E s).1 (infId E (Matrix.GeneralLinearGroup.det (Unitary.toUnits k))) :=
    congrArg (Model.absC E s).1 (det_infGL _)
  rw [h1]
  refine Units.ext ?_
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = 1
  rw [Model.logNorm_infId]
  have hd : star (k.1.det) * k.1.det = 1 := (Matrix.det_of_mem_unitary k.2).1
  have hn : ∀ w, ‖(k.1.det : Cinf E) w‖ = 1 := fun w => by
    have := congrFun hd w
    have h2 : ‖(k.1.det : Cinf E) w‖ * ‖(k.1.det : Cinf E) w‖ = 1 := by
      have h3 := congrArg norm this
      simpa using h3
    nlinarith [norm_nonneg ((k.1.det : Cinf E) w)]
  have e : ∀ w, ‖((Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) w‖ = 1 := hn
  simp [e, hn]

/- English proof (translation)
Establish `e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E)`. Express the relevant statement in the definitionally equal form `Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _`. Simplify using the standard rewrite rules. Rewrite using `[e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dchi_absC_trace (s : ℂ) :
    dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = s * (a * (2 * Fintype.card (InfinitePlace E))) := by
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one]
  simp
  ring

/- English proof (translation)
Introduce `E _ _ _ a ha L hL W _ _ _ ρ _ J hJ c`. Establish `hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Establish `ha' : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Use `set s : ℂ := -c / (a * (2 * Fintype.card (InfinitePlace E))) with hs`.

Establish `hd : dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = -c`. Rewrite using `[dchi_absC_trace, hs]`. Clear the denominators using the available nonvanishing facts. Use `⟨Model.absC E s, L ⊓ GlobalTheory.Published.AutFinGL.Model.kerL a (Model.absC E s), conjChi a (Model.absC E s) '' J, ?_, cofin_conj _ hJ, fun φ hφ hc he => ⟨⟨hφ.1.mulChi _, fun k hk => ?_, fun g => ?_, ?_⟩, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hL.inter (GlobalTheory.Published.AutFinGL.Model.isOpen_kerL _)`.

Establish `h2 : chiDet a (Model.absC E s) (finGL E a k) = 1` using `hk.2`. Express the relevant statement in the definitionally equal form `rt E a (finGL E a k) _ = _`. Rewrite using `[rt_mulChi, h2, Units.val_one, one_smul]`. Conclude with `congrArg (mulChi a (Model.absC E s)) (hφ.2.1 k hk.1)`. Establish `h3` using `hφ.2.2.1 g`.

Establish `e : (fun k : Kinf E a => (cptRep E a k (mulChi a (Model.absC E s) φ)).1 g) = ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E a => (cptRep E a k φ).1 g`. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `(mulChi a (Model.absC E s) φ).1 (g * infGL E a (Unitary.toUnits k)) = ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) * φ.1 (g * infGL E a (Unitary.toUnits k))`. Rewrite using `[mulChi_apply, map_mul, chiDet_absC_cpt, mul_one, mul_comm]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ h3`. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Rewrite using `[conjChi_apply, hφ.2.2.2 j hj, map_zero]`. Conclude with `(IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).2`. Rewrite using `[lie_mulChi, he, hd, neg_smul, add_neg_cancel, map_zero]`.
-/
theorem twist_central : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ,
    ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 →
        lie E a (oneL E a) φ = c • φ →
        mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  intro E _ _ _ a ha L hL W _ _ _ ρ _ J hJ c
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set s : ℂ := -c / (a * (2 * Fintype.card (InfinitePlace E))) with hs
  have hd : dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = -c := by
    rw [dchi_absC_trace, hs]
    field_simp
  refine ⟨Model.absC E s, L ⊓ GlobalTheory.Published.AutFinGL.Model.kerL a (Model.absC E s), conjChi a (Model.absC E s) '' J,
    ?_, cofin_conj _ hJ, fun φ hφ hc he => ⟨⟨hφ.1.mulChi _, fun k hk => ?_, fun g => ?_, ?_⟩, ?_, ?_⟩⟩
  · exact hL.inter (GlobalTheory.Published.AutFinGL.Model.isOpen_kerL _)
  · have h2 : chiDet a (Model.absC E s) (finGL E a k) = 1 := hk.2
    change rt E a (finGL E a k) _ = _
    rw [rt_mulChi, h2, Units.val_one, one_smul]
    exact congrArg (mulChi a (Model.absC E s)) (hφ.2.1 k hk.1)
  · have h3 := hφ.2.2.1 g
    have e : (fun k : Kinf E a => (cptRep E a k (mulChi a (Model.absC E s) φ)).1 g) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k
      change (mulChi a (Model.absC E s) φ).1 (g * infGL E a (Unitary.toUnits k)) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) * φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mulChi_apply, map_mul, chiDet_absC_cpt, mul_one, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ h3
  · rintro _ ⟨j, hj, rfl⟩
    rw [conjChi_apply, hφ.2.2.2 j hj, map_zero]
  · exact (IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).2
  · rw [lie_mulChi, he, hd, neg_smul, add_neg_cancel, map_zero]

end GlobalTheory.CompanionTheory.CuspTwist

end
