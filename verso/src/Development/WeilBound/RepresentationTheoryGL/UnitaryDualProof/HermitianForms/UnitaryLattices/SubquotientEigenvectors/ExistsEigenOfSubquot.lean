import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Eig

/- English proof (translation)
Set `U : Submodule ℂ V` to `F ⊓ S.toSubmodule`. Establish `: FiniteDimensional ℂ U` using `Submodule.finiteDimensional_of_le inf_le_left`. Set `E : V →ₗ[ℂ] V` to `ρ Z - c • LinearMap.id`. Establish `hEU : ∀ x ∈ U, E x ∈ U`. Introduce `x hx`.

Take `⟨hxF, hxS⟩` from `Submodule.mem_inf.1 hx`. Conclude with `Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hF x hxF) (Submodule.smul_mem _ _ hxF), Submodule.sub_mem _ (S.apply_mem_toSubmodule _ hxS) (Submodule.smul_mem _ _ hxS)⟩`. Set `E' : U →ₗ[ℂ] U` to `E.restrict hEU`. Establish `hsU : (s : V) ∈ U` using `Submodule.mem_inf.2 ⟨hsF, s.2⟩`. Establish `hns : ¬ Function.Surjective E'`.

Introduce `hsur`. Take `⟨y, hy⟩` from `hsur ⟨_, hsU⟩`. Establish `hyS : (y : V) ∈ S.toSubmodule` using `(Submodule.mem_inf.1 y.2).2`. Establish `hEy : E y = (s : V)` using `congrArg Subtype.val hy`. Establish `hs' : s = S.toRepresentation Z ⟨y, hyS⟩ - c • ⟨y, hyS⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hEy]`. Both sides reduce to the same expression. Apply `hs` to reduce the goal to its premises. Rewrite using `[hs', map_sub, map_smul, Representation.IntertwiningMap.isIntertwining, hσ, sub_self]`.

Establish `hni : LinearMap.ker E' ≠ ⊥` using `fun h => hns (LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 h))`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hni`. Use `⟨(x : V), fun h => hx0 (Subtype.ext h), ?_⟩` and prove the remaining obligations. Establish `hEx : ρ Z x - c • (x : V) = 0` using `congrArg Subtype.val (LinearMap.mem_ker.1 hx)`. Conclude with `sub_eq_zero.1 hEx`.
-/
theorem exists_eigen_of_subquot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (Z : G) (c : ℂ) (hσ : ∀ w, σ Z w = c • w)
    (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ) (s : S.toSubmodule) (hs : f s ≠ 0)
    (F : Submodule ℂ V) (hfin : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, ρ Z x ∈ F) (hsF : (s : V) ∈ F) :
    ∃ x : V, x ≠ 0 ∧ ρ Z x = c • x := by
  let U : Submodule ℂ V := F ⊓ S.toSubmodule
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left
  let E : V →ₗ[ℂ] V := ρ Z - c • LinearMap.id
  have hEU : ∀ x ∈ U, E x ∈ U := by
    intro x hx
    obtain ⟨hxF, hxS⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hF x hxF) (Submodule.smul_mem _ _ hxF),
      Submodule.sub_mem _ (S.apply_mem_toSubmodule _ hxS) (Submodule.smul_mem _ _ hxS)⟩
  let E' : U →ₗ[ℂ] U := E.restrict hEU
  have hsU : (s : V) ∈ U := Submodule.mem_inf.2 ⟨hsF, s.2⟩
  have hns : ¬ Function.Surjective E' := by
    intro hsur
    obtain ⟨y, hy⟩ := hsur ⟨_, hsU⟩
    have hyS : (y : V) ∈ S.toSubmodule := (Submodule.mem_inf.1 y.2).2
    have hEy : E y = (s : V) := congrArg Subtype.val hy
    have hs' : s = S.toRepresentation Z ⟨y, hyS⟩ - c • ⟨y, hyS⟩ := by
      apply Subtype.ext
      rw [← hEy]
      rfl
    apply hs
    rw [hs', map_sub, map_smul, Representation.IntertwiningMap.isIntertwining, hσ, sub_self]
  have hni : LinearMap.ker E' ≠ ⊥ := fun h =>
    hns (LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 h))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hni
  refine ⟨(x : V), fun h => hx0 (Subtype.ext h), ?_⟩
  have hEx : ρ Z x - c • (x : V) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hx)
  exact sub_eq_zero.1 hEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Consider the cases of `i with`. Consider the case `zero => exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n _ π.ρ hs hi`. Consider the case `succ j`. Establish `hD : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π.ρ)` using `GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs`. Conclude with `GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hD (PositivityTheory.RgGu.NR.derFin_of k (PositivityTheory.RgGu.NR.derEquiv k) ψ hc h1 n j _ π.ρ hs hi) fun Y _ _ τ hq hirr => PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n Y τ (hq.isSmooth hD) hirr`.
-/
theorem isAdmissible_derivB (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n i : ℕ) (π : GRep k (n + i))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible (derivB ψ i π).ρ := by
  cases i with
  | zero => exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n _ π.ρ hs hi
  | succ j =>
    have hD : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π.ρ) := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs
    exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hD
      (PositivityTheory.RgGu.NR.derFin_of k (PositivityTheory.RgGu.NR.derEquiv k) ψ hc h1 n j _ π.ρ hs hi)
      fun Y _ _ τ hq hirr => PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n Y τ (hq.isSmooth hD) hirr

variable (k) in

/- English proof (translation)
Introduce `ψ hc h1 n i π hs hi` and use `isAdmissible_derivB ψ hc h1 n i π hs hi`.
-/
theorem uAdm : UAdm k := fun ψ hc h1 n i π hs hi => isAdmissible_derivB ψ hc h1 n i π hs hi

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `: 1`. Simplify using `only [Units.val_mul]`. Conclude with `(Algebra.commutes _ _).symm`.
-/
theorem scalar_comm (n : ℕ) (z : kˣ) (g : GL (Fin n) k) :
    g * GeneralLinearGroup.scalar (Fin n) z = GeneralLinearGroup.scalar (Fin n) z * g := by
  ext : 1
  simp only [Units.val_mul]
  exact (Algebra.commutes _ _).symm

/- English proof (translation)
Use `show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _`. Simplify using the standard rewrite rules.
-/
theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (x : V) : x ∈ fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

variable (k) in

/- English proof (translation)
Introduce `ψ hc h1 n i π hs hi t W _ _ σ ω hW hsub hω z`. Establish `hadm` using `uAdm k ψ hc h1 n i π hs hi`. Take `⟨S, f, hf⟩` from `hsub`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Take `⟨s, rfl⟩` from `hf w`.

Take `⟨K, hKo, hKc, hKsub⟩` from `GlobalTheory.ContraProd.exists_compactOpen_GL (k := k) (Fin n) {g | (derivB ψ i π).ρ g s.1 = s.1} ((hadm.1 s.1).mem_nhds (by show (derivB ψ i π).ρ 1 s.1 = s.1; rw [map_one]; rfl))`. Establish `hfixZ : ∀ x ∈ fixed (derivB ψ i π).ρ K, (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_fixed_iff]`. Introduce `h`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, scalar_comm, map_mul, Module.End.mul_apply, hx h]`. Establish `hF : ∀ x ∈ fixed (derivB ψ i π).ρ K, ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K`. Introduce `x hx`. Use `show ((dpow n t (GeneralLinearGroup.scalar (Fin n) z) : ℂˣ) : ℂ) • (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K`. Conclude with `Submodule.smul_mem _ _ (hfixZ x hx)`.

Conclude with `exists_eigen_of_subquot ((derivB ψ i π).tw t).ρ σ (GeneralLinearGroup.scalar (Fin n) z) (ω z : ℂ) (hω z) S f s hw (fixed (derivB ψ i π).ρ K) (hadm.2 K hKo hKc) hF ((mem_fixed_iff _ _ _).2 fun h => hKsub h.2)`.
-/
theorem uEig : UEig k := by
  intro ψ hc h1 n i π hs hi t W _ _ σ ω hW hsub hω z
  have hadm := uAdm k ψ hc h1 n i π hs hi
  obtain ⟨S, f, hf⟩ := hsub
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨s, rfl⟩ := hf w
  obtain ⟨K, hKo, hKc, hKsub⟩ := GlobalTheory.ContraProd.exists_compactOpen_GL (k := k) (Fin n)
    {g | (derivB ψ i π).ρ g s.1 = s.1}
    ((hadm.1 s.1).mem_nhds (by show (derivB ψ i π).ρ 1 s.1 = s.1; rw [map_one]; rfl))
  have hfixZ : ∀ x ∈ fixed (derivB ψ i π).ρ K, (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    rw [mem_fixed_iff] at hx ⊢
    intro h
    rw [← Module.End.mul_apply, ← map_mul, scalar_comm, map_mul, Module.End.mul_apply, hx h]
  have hF : ∀ x ∈ fixed (derivB ψ i π).ρ K,
      ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    show ((dpow n t (GeneralLinearGroup.scalar (Fin n) z) : ℂˣ) : ℂ) • (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K
    exact Submodule.smul_mem _ _ (hfixZ x hx)
  exact exists_eigen_of_subquot ((derivB ψ i π).tw t).ρ σ (GeneralLinearGroup.scalar (Fin n) z) (ω z : ℂ) (hω z) S f s hw
    (fixed (derivB ψ i π).ρ K) (hadm.2 K hKo hKc) hF ((mem_fixed_iff _ _ _).2 fun h => hKsub h.2)

end PositivityTheory.RgUd.Form.U.Eig
