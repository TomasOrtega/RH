import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOrbitEqTop
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacquetFinGen

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top`. Consider the case `exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top`. Consider the case `(apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top ..)`.
-/
theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G => π g v) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top
  | (apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOrbitTop.span_orbit_eq_top ..)

/- English proof (translation)
Introduce `k _ _ _ _ a b n h V _ _ π hsm hirr`. Use `haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Use `set e := stdSum h`. Use `set N := unipRad k (two e)`.

Establish `hO` using `GlobalTheory.SmoothRiesz.finite_orbit π hsm (KO k (Fin n)) (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)) v`. Set `s : Finset (Jacquet π N)` to `hO.toFinset.image (Submodule.Quotient.mk (p := twKer π N 1))`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `set T := {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ x ∈ s, w = jac₂ e π g x}`. Establish `key : ∀ g : GL (Fin n) k, (Submodule.Quotient.mk (π g v) : Jacquet π N) ∈ Submodule.span ℂ T`.

Introduce `g`. Take `⟨p, w, hw, rfl⟩` from `GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two e) g`. Take `⟨u, hu, hp⟩` from `exists_levi_mul_unip k (two e) p`. Use `set m := leviProj k (two e) p`. Use `set y := π w v`.

Establish `hy : Submodule.Quotient.mk (p` using `twKer π N 1) y ∈ s := Finset.mem_image.2 ⟨y, hO.mem_toFinset.2 ⟨w, hw, rfl⟩, rfl⟩`. Establish `hu' : (Submodule.Quotient.mk (π u y) : Jacquet π N) = Submodule.Quotient.mk y`. Rewrite using `[Submodule.Quotient.eq]`. Conclude with `Submodule.subset_span ⟨⟨u, hu⟩, y, by simp⟩`. Establish `h1 : π (↑p * w) v = π (leviEmb k (two e) m) (π u y)`.

Rewrite using `[hp]`. Simplify using `only [map_mul, Module.End.mul_apply, y]`. Establish `h2 : (Submodule.Quotient.mk (π (leviEmb k (two e) m) (π u y)) : Jacquet π N) = ((deltaHalf k _ m : ℂˣ) : ℂ) • jac₂ e π ((leviTwo k (Fin a) (Fin b)).symm m) (Submodule.Quotient.mk y)` using `by show _ = _ • jac (two e) π (leviTwo k (Fin a) (Fin b) ((leviTwo k (Fin a) (Fin b)).symm m)) _`. Rewrite using `[MulEquiv.apply_symm_apply, ← hu', jac_mk, smul_smul, Units.mul_inv, one_smul]`. Rewrite using `[h1, h2]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hy, rfl⟩)`. Establish `hle : Submodule.span ℂ (Set.range fun g : GL (Fin n) k => π g v) ≤ (Submodule.span ℂ T).comap (twKer π N 1).mkQ` using `Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact key g)`. Rewrite `hle` using `[GlobalTheory.JacquetFinGen.span_orbit_eq_top π hirr hv, top_le_iff]`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `: y ∈ (Submodule.span ℂ T).comap (twKer π N 1).mkQ` using `hle ▸ Submodule.mem_top`. Conclude with `this`.
-/
theorem jacquet_fg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))),
      Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  intro k _ _ _ _ a b n h V _ _ π hsm hirr
  classical
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set e := stdSum h
  set N := unipRad k (two e)
  have hO := GlobalTheory.SmoothRiesz.finite_orbit π hsm (KO k (Fin n)) (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)) v
  let s : Finset (Jacquet π N) := hO.toFinset.image (Submodule.Quotient.mk (p := twKer π N 1))
  refine ⟨s, ?_⟩
  set T := {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ x ∈ s, w = jac₂ e π g x}
  have key : ∀ g : GL (Fin n) k,
      (Submodule.Quotient.mk (π g v) : Jacquet π N) ∈ Submodule.span ℂ T := by
    intro g
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two e) g
    obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k (two e) p
    set m := leviProj k (two e) p
    set y := π w v
    have hy : Submodule.Quotient.mk (p := twKer π N 1) y ∈ s :=
      Finset.mem_image.2 ⟨y, hO.mem_toFinset.2 ⟨w, hw, rfl⟩, rfl⟩
    have hu' : (Submodule.Quotient.mk (π u y) : Jacquet π N) = Submodule.Quotient.mk y := by
      rw [Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨⟨u, hu⟩, y, by simp⟩
    have h1 : π (↑p * w) v = π (leviEmb k (two e) m) (π u y) := by
      rw [hp]; simp only [map_mul, Module.End.mul_apply, y]
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (two e) m) (π u y)) : Jacquet π N) =
        ((deltaHalf k _ m : ℂˣ) : ℂ) • jac₂ e π ((leviTwo k (Fin a) (Fin b)).symm m)
          (Submodule.Quotient.mk y) := by
      show _ = _ • jac (two e) π (leviTwo k (Fin a) (Fin b) ((leviTwo k (Fin a) (Fin b)).symm m)) _
      rw [MulEquiv.apply_symm_apply, ← hu', jac_mk, smul_smul, Units.mul_inv, one_smul]
    rw [h1, h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hy, rfl⟩)
  have hle : Submodule.span ℂ (Set.range fun g : GL (Fin n) k => π g v) ≤
      (Submodule.span ℂ T).comap (twKer π N 1).mkQ :=
    Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact key g)
  rw [GlobalTheory.JacquetFinGen.span_orbit_eq_top π hirr hv, top_le_iff] at hle
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have : y ∈ (Submodule.span ℂ T).comap (twKer π N 1).mkQ := hle ▸ Submodule.mem_top
  exact this

end GlobalTheory.JacquetFinGen
