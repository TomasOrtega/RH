import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [ExpFrame.cj, RingHom.comp_apply]`. Conclude with `congrArg φ (IsCMField.complexConj_apply_apply E x)`.
-/
theorem cjE_cjE (φ : E →+* Formalism.ConjugateSelfDual.Qbar l) : ExpFrame.cj (cj φ) = φ := by
  ext x
  simp only [ExpFrame.cj, RingHom.comp_apply]
  exact congrArg φ (IsCMField.complexConj_apply_apply E x)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩` and prove the remaining obligations. Use `congrArg ExpFrame.cj hab` as an intermediate fact. Simplify `this` using `only [cjE_cjE]`. Simplify using `only [cjE_cjE] at e`.

Conclude with `e.symm`. Take `⟨τ, hτ | hτ⟩` from `h3 i`. Conclude with `⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩`. Conclude with `⟨τ, Or.inl hτ⟩`.
-/
theorem isHalf_cj {ι : Type} {inc : ι → (E →+* Formalism.ConjugateSelfDual.Qbar l)} (h : IsHalf inc) : IsHalf fun τ => ExpFrame.cj (inc τ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩
  · have := congrArg ExpFrame.cj hab
    simpa only [cjE_cjE] using this
  · simp only [cjE_cjE] at e
    exact e.symm
  · obtain ⟨τ, hτ | hτ⟩ := h3 i
    · exact ⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩
    · exact ⟨τ, Or.inl hτ⟩

end GlobalTheory.HalfLabels

namespace GlobalTheory.HalfLabels

/- English proof (translation)
Set `_ : Algebra E K` to `ι.toAlgebra`. Establish `: IsScalarTower ℚ E K` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]`. Set `φ : E →ₐ[ℚ] K` to `i.toRatAlgHom`. Use `⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Establish `h` using `AlgHom.restrictNormal_commutes φ E x`. Conclude with `h.symm`.
-/
theorem exists_aut {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K] (ι i : E →+* K) :
    ∃ σ : E ≃ₐ[ℚ] E, i = ι.comp (σ : E →+* E) := by
  let _ : Algebra E K := ι.toAlgebra
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let φ : E →ₐ[ℚ] K := i.toRatAlgHom
  refine ⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩
  ext x
  have h := AlgHom.restrictNormal_commutes φ E x
  exact h.symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `: IsGalois ℚ D.host.E` using `D.host.hostE_isGalois`. Use `set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι`. Establish `hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)` using `fun τ => rfl`. Establish `hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) = ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E)`. Introduce `g`.

Establish `hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj` using `map_mul (D.host.gal).symm g (D.R.cc)`. Use extensionality with `x`. Rewrite using `[hs]`. Use `show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))`. Use `congr 2`.

Conclude with `Formalism.BasicNotions.bridge_star_holds D.R D.host x`. Establish `hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) → g = g'`. Introduce `g g' h`. Establish `: D.host.sigmaOf g = D.host.sigmaOf g'` using `AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)`. Conclude with `(D.host.gal).symm.injective this`.

Use `⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hinc, hinc]`. Conclude with `D.eTau.injective (Subtype.ext (hinj _ _ h))`. Rewrite `h` using `[hinc, hinc, hcc]`. Establish `e` using `hinj _ _ h`.

Conclude with `(Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)`. Take `⟨σ, hσ⟩` from `exists_aut ι i`. Establish `hσg : D.host.sigmaOf (D.host.gal σ) = σ` using `(D.host.gal).symm_apply_apply σ`. Distinguish the cases in `hg : D.host.gal σ ∈ D.R.Psi`. Use `⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩` and prove the remaining obligations.

Rewrite using `[hinc, Equiv.apply_symm_apply, hσ, hσg]`. Establish `hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi`. Assume the negation of the conclusion as `h'`. Conclude with `hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')`. Use `⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩` and prove the remaining obligations.

Rewrite using `[hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]`.
-/
theorem isHalf_lab (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf (incOf D e0 false) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι
  have hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := fun τ => rfl
  have hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) =
      ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E) := by
    intro g
    have hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj :=
      map_mul (D.host.gal).symm g (D.R.cc)
    ext x
    rw [hs]
    show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))
    congr 2
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) →
      g = g' := by
    intro g g' h
    have : D.host.sigmaOf g = D.host.sigmaOf g' := AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)
    exact (D.host.gal).symm.injective this
  refine ⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩
  · rw [hinc, hinc] at h
    exact D.eTau.injective (Subtype.ext (hinj _ _ h))
  · rw [hinc, hinc, hcc] at h
    have e := hinj _ _ h
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)
  · obtain ⟨σ, hσ⟩ := exists_aut ι i
    have hσg : D.host.sigmaOf (D.host.gal σ) = σ :=
      (D.host.gal).symm_apply_apply σ
    by_cases hg : D.host.gal σ ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩
      rw [hinc, Equiv.apply_symm_apply, hσ, hσg]
    · have hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi := by
        by_contra h'
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')
      refine ⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩
      rw [hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]

/- English proof (translation)
Introduce `_ e0 b`. Consider the cases of `b`. Conclude with `isHalf_lab D (l := l) e0`. Conclude with `isHalf_cj (isHalf_lab D e0)`.
-/
theorem halfAt_all (D : D7) (l : ℕ) : HalfAt D l := by
  intro _ e0 b
  cases b
  · exact isHalf_lab D (l := l) e0
  · exact isHalf_cj (isHalf_lab D e0)

/- English proof (translation)
Use `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩` and prove the remaining obligations. Conclude with `EvPt.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)`.
-/
theorem halfAt_inRange : InRange fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact EvPt.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)

end GlobalTheory.HalfLabels

end
