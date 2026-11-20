import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.SubsingletonOfEvInj

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEval

def ConjMult : Prop := ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g)

def ConjModel : Prop := ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_label {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    ∃ τ, labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      labE σ (D.eTau.symm ⟨t, ht⟩) = D.host.emb (g * t) := fun t ht => by
    refine RingHom.ext fun x => ?_
    have h1 : D.host.sigmaOf (g * t) = D.host.sigmaOf g * D.host.sigmaOf t :=
      map_mul (D.host.gal).symm g t
    show (σ.comp D.embE) (D.host.sigmaOf (D.eTau (D.eTau.symm ⟨t, ht⟩)).1 x) = D.host.φ₀ (D.host.sigmaOf (g * t) x)
    rw [Equiv.apply_symm_apply, ← hg, h1]
    rfl
  by_cases h : g⁻¹ * (D.eTau ρ).1 ∈ D.R.Psi
  · refine ⟨D.eTau.symm ⟨_, h⟩, Or.inl ?_⟩
    rw [key, mul_inv_cancel_left]
    rfl
  · have h' : g⁻¹ * (D.eTau ρ).1 * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, mul_assoc, mul_inv_cancel_left, Formalism.L2.Geo.emb_mul_cc_comp]
    exact RingHom.ext fun x => D.host.conjE_apply (tauE D ρ) x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conj_comp_eq_iff {E : Type} [Field E] (a b : E →+* ℂ) :
    (starRingEnd ℂ).comp a = b ↔ a = (starRingEnd ℂ).comp b := by
  constructor
  · rintro rfl
    ext x; simp
  · rintro rfl
    ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem labE_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments.
-/
theorem lab_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ := by
  have e : (fun τ => labE ((starRingEnd ℂ).comp σ) τ = tauE D ρ ∨
        labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (tauE D ρ)) =
      fun τ => labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    funext τ
    rw [labE_conj, conj_comp_eq_iff, conj_comp_eq_iff, ← (conj_comp_eq_iff (tauE D ρ) _).1 rfl, or_comm]
  unfold lab
  rw [dif_pos (exists_label _ ρ), dif_pos (exists_label σ ρ)]
  congr 1

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem evEx_conj {K C H H' Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] (σ : K →+* ℂ) (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev') (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (φ : C → Y → ℂ)
    (h : EvEx ((starRingEnd ℂ).comp σ) ev φ) : EvEx σ ev' fun f g => starRingEnd ℂ (φ f g) := by
  obtain ⟨j, hj⟩ := h
  choose x hx using hx
  refine ⟨⟨⟨fun f => x (j f), fun f f' => hinj (funext fun g => ?_)⟩, fun a f => hinj (funext fun g => ?_)⟩,
    fun f => funext fun g => ?_⟩
  · rw [ha', hx, hx, hx, map_add, ha, map_add]
  · refine (hx _ g).trans ?_
    rw [j.map_smulₛₗ, hs, hs', hx, map_mul, RingHom.comp_apply, Complex.conj_conj]
  · exact (hx (j f) g).trans (congrArg (starRingEnd ℂ) (congrFun (hj f) g))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem levChi_principal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [h1]
  simp [LevCh.datWp, datY]

end GlobalTheory.ConjEval
