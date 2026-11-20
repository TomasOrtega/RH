import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDense
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.RegClosure

variable {F : Type} [Field F] [NumberField F] {d β : F}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qmap_re {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).re = f x.re := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qmap_imI {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imI = f x.imI := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qmap_imJ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imJ = f x.imJ := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qmap_imK {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imK = f x.imK := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nhdsNE_neBot_Kp : ∀ u : Pl F, (𝓝[≠] (0 : Kp u)).NeBot
  | .inl w => by
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero _) 2
          rw [← this, map_ofNat]; norm_num⟩ }
    exact NormedField.nhdsNE_neBot (0 : w.Completion)
  | .inr v => by
    letI := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
    exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem two_ne_zero_Kp (u : Pl F) : (2 : Kp u) ≠ 0 := by
  have h : algebraMap F (Kp u) 2 ≠ 0 := (map_ne_zero (algebraMap F (Kp u))).2 two_ne_zero
  rwa [map_ofNat] at h

def psi (w : Pl F) (e : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (e.re - 1), inc w e.imI, inc w e.imJ, inc w e.imK⟩

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem qmap_proj_psi_same (w : Pl F) (e : Q d β (Kp w)) : qmap (proj w) (psi w e) = e := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_same]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem qmap_proj_psi_ne {u w : Pl F} (h : u ≠ w) (e : Q d β (Kp w)) :
    qmap (proj u) (psi w e) = 1 := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_ne h]

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem eq_of_qmap_proj {x y : Q d β (AF F)} (h : ∀ u, qmap (proj u) x = qmap (proj u) y) : x = y := by
  ext
  · exact adele_ext fun u => by simpa [qmap_re] using congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => by simpa [qmap_imI] using congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => by simpa [qmap_imJ] using congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => by simpa [qmap_imK] using congrArg QuaternionAlgebra.imK (h u)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  refine continuous_q_iff.2 ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem psi_mem {w : Pl F} {e : Q d β (Kp w)} (he : qn e = 1) : psi w e ∈ SuppAt d β {w} := by
  refine ⟨adele_ext fun u => ?_, fun u hu => qmap_proj_psi_ne (by simpa using hu) e⟩
  rw [← qn_qmap, map_one]
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same, he]
  · rw [qmap_proj_psi_ne h, qn_one]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem psi_proj {w : Pl F} {a : Q d β (AF F)} (ha : a ∈ SuppAt d β {w}) :
    a = psi w (qmap (proj w) a) := by
  refine eq_of_qmap_proj fun u => ?_
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same]
  · rw [qmap_proj_psi_ne h, ha.2 u (by simpa using h)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem reg_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  intro F _ _ d β hd hb w a ha
  rw [mem_closure_iff_nhds]
  intro U hU
  have hpa := psi_proj ha
  rw [hpa] at hU
  have hU' : psi w ⁻¹' U ∈ 𝓝 (qmap (proj w) a) := (continuous_psi w).continuousAt hU
  have hn : qn (qmap (proj w) a) = 1 := by rw [qn_qmap, ha.1, map_one]
  obtain ⟨b, hbU, hb1, hb2⟩ := RegDense.regular_dense d β (two_ne_zero_Kp w) hd hb
    (nhdsNE_neBot_Kp w) _ hn _ hU'
  exact ⟨psi w b, hbU, psi_mem hb1, by rw [qmap_proj_psi_same]; exact hb2⟩

end GlobalTheory.CompanionTheory.PlaneSA.RegClosure
