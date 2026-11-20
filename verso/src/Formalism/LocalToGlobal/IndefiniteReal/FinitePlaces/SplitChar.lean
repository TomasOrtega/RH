import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin

namespace SplitChar

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, ε, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ga_ext (V : HSp D) {g g' : GA D V} (h : mt V g = mt V g') : g = g' :=
  Subtype.ext (Units.ext h)

def RA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem haA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) :
    incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
  rw [← hsq_map (incA D) (flipTwoThree.sigE D) (cA D) (fun a => (flipTwoThree.cA_incA' a).symm), ← map_mul, ha, map_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hainvA (ainv : D.host.E) (hainv : flipTwoThree.sigE D ainv = ainv) : cA D (incA D ainv) = incA D ainv := by
  rw [flipTwoThree.cA_incA', hainv]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RA_idem (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) : RA V u ainv * RA V u ainv = RA V u ainv :=
  proj_idem' _ _ _ _ (haA V u ainv ha)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem mul_aux {n : Type} [Fintype n] [DecidableEq n] (R : Matrix n n (AE D)) (hRR : R * R = R)
    (a b : AE D) : (1 + (a - 1) • R) * (1 + (b - 1) • R) = 1 + (a * b - 1) • R := by
  simp only [add_mul, mul_add, one_mul, mul_one]
  rw [smul_mul_smul_comm, hRR, show a * b - 1 = (b - 1) + ((a - 1) + (a - 1) * (b - 1)) by ring, add_smul,
    add_smul]
  abel

def secM (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) (x : AE D) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  1 + (x - 1) • RA V u ainv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secM_unitary (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : AE D)
    (hx : cA D x * x = 1) :
    ((secM V u ainv x).map (cA D))ᵀ * V.gram.map (incA D) * secM V u ainv x = V.gram.map (incA D) :=
  proj_unitary (cA D) Formalism.L2.Theta.cA_cA (V.gram.map (incA D)) (flipTwoThree.gramA_herm V) _ _ (haA V u ainv ha)
    (hainvA ainv hainv) x hx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secM_det (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (x : AE D) : (secM V u ainv x).det = x :=
  det_proj' (cA D) _ _ _ (haA V u ainv ha) x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unitary_one_conj_mul_self (x : FirstPropositionFrame D) : cA D (((x : (AE D)ˣ)) : AE D) * (((x : (AE D)ˣ)) : AE D) = 1 := by
  rw [mul_comm]; exact x.2

def secG (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : FirstPropositionFrame D) : GA D V :=
  flipTwoThree.mkGA V (secM V u ainv ((x : (AE D)ˣ) : AE D)) (secM_unitary V u ainv ha hainv _ (unitary_one_conj_mul_self x))
    (by rw [secM_det V u ainv ha]; exact (x : (AE D)ˣ).isUnit)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_secG (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : FirstPropositionFrame D) :
    mt V (secG V u ainv ha hainv x) = secM V u ainv ((x : (AE D)ˣ) : AE D) := rfl

def secHom (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) : FirstPropositionFrame D →* GA D V where
  toFun := secG V u ainv ha hainv
  map_one' := by
    apply ga_ext V
    rw [mt_secG, flipTwoThree.mt_one']
    simp [secM]
  map_mul' x y := by
    apply ga_ext V
    rw [flipTwoThree.mt_mul', mt_secG, mt_secG, mt_secG]
    simp only [secM, Subgroup.coe_mul, Units.val_mul]
    exact (mul_aux _ (RA_idem V u ainv ha) _ _).symm

end SplitChar

end Formalism.IndefR.Fin

end
