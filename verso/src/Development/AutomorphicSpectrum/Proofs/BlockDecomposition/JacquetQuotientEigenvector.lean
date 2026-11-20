import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacExp

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨-, hw⟩` from `(hasFiniteLength_iff_wellFounded ρ).1 h`. Use `haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hw.wf`. Take `h' | ⟨S, hS, hle⟩` from `eq_bot_or_exists_atom_le E`. Conclude with `absurd h' hE`. Conclude with `⟨S, hS, hle⟩`.
-/
theorem exists_atom_le {ρ : Representation ℂ G V} (h : HasFiniteLength ρ) {E : Subrepresentation ρ}
    (hE : E ≠ ⊥) : ∃ S : Subrepresentation ρ, IsAtom S ∧ S ≤ E := by
  obtain ⟨-, hw⟩ := (hasFiniteLength_iff_wellFounded ρ).1 h
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hw.wf
  obtain h' | ⟨S, hS, hle⟩ := eq_bot_or_exists_atom_le E
  · exact absurd h' hE
  · exact ⟨S, hS, hle⟩

def eigenSub (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, z * g = g * z) (ν : ℂ) : Subrepresentation ρ :=
  ⟨Module.End.eigenspace (ρ z) ν, fun g v hv => by
    have hv' : ρ z v = ν • v := Module.End.mem_eigenspace_iff.1 hv
    refine Module.End.mem_eigenspace_iff.2 ?_
    have : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
    rw [this, hv', map_smul]⟩

/- English proof (translation)
The claim follows from `Module.End.mem_eigenspace_iff`.
-/
theorem mem_eigenSub {ρ : Representation ℂ G V} {z : G} {hz : ∀ g, z * g = g * z} {ν : ℂ} {v : V} :
    v ∈ (eigenSub ρ z hz ν).toSubmodule ↔ ρ z v = ν • v :=
  Module.End.mem_eigenspace_iff

/- English proof (translation)
Introduce `v` and use `by have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g v.1 = v.1} := by ext g exact Subtype.ext_iff rw [this] exact h v.1`.
-/
theorem isSmooth_sub [TopologicalSpace G] {ρ : Representation ℂ G V} (h : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := fun v => by
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact h v.1

end General

section Tensor

variable {Γ X Y : Fin 2 → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

/- English proof (translation)
Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Rewrite using `[map_smul, piTensor_tprod, smul_comm]`. Use `congr 1`. Establish `: (fun a => ρ a (g a) (f a)) = Function.update f 0 (c • f 0)`.

Use function extensionality and compare the values at `a`. Use `fin_cases a`. Simplify using `[h0]`. Simplify using `[h1]`. Rewrite using `[this, MultilinearMap.map_update_smul, Function.update_eq_self]`.

Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.
-/
theorem piTensor_apply_of_scalar (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : ℂ)
    (h0 : ∀ v, ρ 0 (g 0) v = c • v) (h1 : ∀ v, ρ 1 (g 1) v = v) (z : PiTensorProduct ℂ X) :
    piTensor ρ g z = c • z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    have : (fun a => ρ a (g a) (f a)) = Function.update f 0 (c • f 0) := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [this, MultilinearMap.map_update_smul, Function.update_eq_self]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

def piTensorCongr {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {σ : ∀ a, Representation ℂ (Γ a) (Y a)}
    (φ : ∀ a, (ρ a).Equiv (σ a)) : (piTensor ρ).Equiv (piTensor σ) :=
  .mk (PiTensorProduct.congr fun a => (φ a).toLinearEquiv) fun g => by
    apply PiTensorProduct.ext
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      piTensor_tprod, PiTensorProduct.congr_tprod]
    exact congrArg _ (funext fun a => (φ a).toIntertwiningMap.isIntertwining _ _ (g a) (f a))

end Tensor

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def omegaLevi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) : Levi k (fun a => Fin (d a)) :=
  fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) (if a = 0 then Zls.unifU k else 1)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [omegaLevi, Matrix.GeneralLinearGroup.scalar, Pi.mul_apply, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Conclude with `Matrix.scalar_commute _ (fun r => Commute.all _ _) _`.
-/
theorem omegaLevi_comm (d : Fin 2 → ℕ) (h : Levi k (fun a => Fin (d a))) :
    omegaLevi k d * h = h * omegaLevi k d := by
  funext a
  apply Units.ext
  simp only [omegaLevi, Matrix.GeneralLinearGroup.scalar, Pi.mul_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ _) _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    (Zls.diagPow k N lam : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ lam i : kˣ) : k) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Take `⟨⟨a, i⟩, rfl⟩` from `(stdBlocks d hd).surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `(stdBlocks d hd).surjective j`. Rewrite using `[diagPow_val]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[leviEmb_apply_same]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Establish `hv` using `stdBlocks_val d hd a i`. Establish `: (((stdBlocks d hd ⟨a, i⟩ : Fin N) : ℕ) < d 0) ↔ a = 0`. Rewrite using `[hv]`. Use `fin_cases a`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using `[omegaLevi, Zls.omegaVec, this, Matrix.GeneralLinearGroup.scalar]`. Establish `: (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨a, j⟩)` using `by simpa using hij`. Simplify using `[omegaLevi, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply_ne _ this, hij]`. Establish `: (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨b, j⟩)` using `fun h => hab (congrArg Sigma.fst ((stdBlocks d hd).injective h))`.

Rewrite using `[leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ this]`.
-/
theorem leviEmb_omegaLevi {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) :
    leviEmb k (stdBlocks d hd) (omegaLevi k d) = Zls.diagPow k N (Zls.omegaVec N (d 0)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [diagPow_val]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      have hv := stdBlocks_val d hd a i
      have : (((stdBlocks d hd ⟨a, i⟩ : Fin N) : ℕ) < d 0) ↔ a = 0 := by
        rw [hv]
        fin_cases a
        · simp
        · simp
      simp [omegaLevi, Zls.omegaVec, this, Matrix.GeneralLinearGroup.scalar]
    · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨a, j⟩) := by simpa using hij
      simp [omegaLevi, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply_ne _ this, hij]
  · have : (stdBlocks d hd ⟨a, i⟩) ≠ (stdBlocks d hd ⟨b, j⟩) := fun h =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective h))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ this]

/- English proof (translation)
Establish `h0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1`. Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`. Establish `hd0 : Matrix.GeneralLinearGroup.det (omegaLevi k d 0) = Zls.unifU k ^ d 0`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[omegaLevi, Matrix.GeneralLinearGroup.scalar]`.

Establish `hd1 : Matrix.GeneralLinearGroup.det (omegaLevi k d 1) = 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[omegaLevi, Matrix.GeneralLinearGroup.scalar]`. Establish `hn : nabs k (Zls.unifU k) = (resCard k : ℝ)⁻¹` using `nabs_uniformiser Zls.irreducible_unif rfl`. Rewrite using `[deltaHalf_apply, Fin.prod_univ_two, hd0, hd1, map_one, mul_one, map_pow, h0]`.

Establish `hq : ((((resCard k : ℝ)⁻¹ : ℝ)) : ℂ) = ((Nat.card 𝓀[k] : ℂ))⁻¹` using `by simp [resCard]`. Establish `harg : Complex.arg (Nat.card 𝓀[k] : ℂ) ≠ Real.pi`. Rewrite using `[Complex.natCast_arg]`. Conclude with `Real.pi_pos.ne`. Rewrite using `[Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, val_absPow, hn, hq, Complex.inv_cpow _ _ harg, inv_pow, inv_inv, ← Complex.cpow_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaHalf_omegaLevi (d : Fin 2 → ℕ) :
    (((deltaHalf k (fun a => Fin (d a)) (omegaLevi k d))⁻¹ : ℂˣ) : ℂ) =
      (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) := by
  have h0 : modExp (fun a : Fin 2 => Fin (d a)) 0 = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hd0 : Matrix.GeneralLinearGroup.det (omegaLevi k d 0) = Zls.unifU k ^ d 0 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hd1 : Matrix.GeneralLinearGroup.det (omegaLevi k d 1) = 1 := by
    apply Units.ext
    simp [omegaLevi, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (Zls.unifU k) = (resCard k : ℝ)⁻¹ :=
    nabs_uniformiser Zls.irreducible_unif rfl
  rw [deltaHalf_apply, Fin.prod_univ_two, hd0, hd1, map_one, mul_one, map_pow, h0]
  have hq : ((((resCard k : ℝ)⁻¹ : ℝ)) : ℂ) = ((Nat.card 𝓀[k] : ℂ))⁻¹ := by simp [resCard]
  have harg : Complex.arg (Nat.card 𝓀[k] : ℂ) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, val_absPow, hn, hq, Complex.inv_cpow _ _ harg,
    inv_pow, inv_inv, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨ω, -, hω⟩` from `((schur_and_segments k).1 (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr).2`. Conclude with `⟨ω t, fun v => hω t v⟩`.
-/
theorem exists_scalarBy (x : IrrGL k) (t : kˣ) : ∃ c : ℂ, Zl.ScalarBy x t c := by
  obtain ⟨ω, -, hω⟩ := ((schur_and_segments k).1 (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr).2
  exact ⟨ω t, fun v => hω t v⟩

/- English proof (translation)
The claim follows from `jhMult_ne_zero_iff.2 ⟨S, Φ.toIntertwiningMap, Φ.surjective⟩`.
-/
theorem jm_ne_zero_of_equiv {h N : ℕ} (x : Fin h → IrrGL k) (hx : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (S : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hx) π))
    (Φ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep)) : Zc.jm x hx π ≠ 0 :=
  jhMult_ne_zero_iff.2 ⟨S, Φ.toIntertwiningMap, Φ.surjective⟩

/- English proof (translation)
Establish `hBZ` using `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`. Establish `hfl : HasFiniteLength (jac (stdBlocks d hd) π)` using `(hBZ k).2.1 (Fin 2) (Fin N) (fun a => Fin (d a)) (stdBlocks d hd) V π hs (hasFiniteLength_of_isIrreducible hi)`. Use `set ν : ℂ := μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) with hν`. Use `set w' : Jacquet π (unipRad k (stdBlocks d hd)) := Submodule.Quotient.mk w with hw'`. Establish `heig : jac (stdBlocks d hd) π (omegaLevi k d) w' = ν • w'`.

Rewrite using `[hw', jac_mk, leviEmb_omegaLevi, hμ, deltaHalf_omegaLevi, smul_smul, hν, mul_comm]`. Use `set E := eigenSub (jac (stdBlocks d hd) π) (omegaLevi k d) (omegaLevi_comm d) ν with hE`. Establish `hEne : E ≠ ⊥`. Introduce `h`. Establish `: w' ∈ E.toSubmodule` using `mem_eigenSub.2 heig`.

Rewrite `this` using `[h]`. Conclude with `hw ((Submodule.mem_bot ℂ).1 this)`. Take `⟨S, hS, hSE⟩` from `exists_atom_le hfl hEne`. Establish `hSirr : S.toRepresentation.IsIrreducible` using `GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS`. Set `τ : IrrRep (Levi k fun a => Fin (d a))` to `⟨S.toSubmodule, S.toRepresentation, isSmooth_sub (isSmooth_jac _ hs) S, hSirr⟩`.

Take `⟨s, ⟨Φ⟩⟩` from `GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 2) (fun a => Fin (d a)) τ`. Set `x : Fin 2 → IrrGL k` to `fun a => IrrGL.of (N := d a) (s a).ρ (s a).smooth (s a).irr`. Set `Ψ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep)` to `Φ.trans (piTensorCongr fun a => IrrGL.equivOf (N := d a) (s a).ρ (s a).smooth (s a).irr)`. Take `⟨c₀, hc₀⟩` from `exists_scalarBy (x 0) (Zls.unifU k)`. Take `⟨c₁, hc₁⟩` from `exists_scalarBy (x 1) (Zls.unifU k)`.

Use `⟨x, hd, fun a => rfl, jm_ne_zero_of_equiv x hd π S Ψ, ?_, c₁, hc₁⟩` and prove the remaining obligations. Establish `hSne : S.toSubmodule ≠ ⊥` using `fun h => hS.1 (Subrepresentation.ext h)`. Take `⟨v₀, hv₀, hv₀ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hSne`. Set `v : S.toSubmodule` to `⟨v₀, hv₀⟩`. Establish `hv : v ≠ 0` using `fun h => hv₀ne (congrArg Subtype.val h)`.

Establish `h1 : S.toRepresentation (omegaLevi k d) v = ν • v` using `Subtype.ext (mem_eigenSub.1 (hSE hv₀))`. Establish `h2 : piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) = c₀ • Ψ v`. Use `piTensor_apply_of_scalar _ _ c₀ (fun u => ?_) (fun u => ?_) _` and prove the remaining obligations. Establish `: omegaLevi k d 0 = Matrix.GeneralLinearGroup.scalar (Fin (x 0).1) (Zls.unifU k)`. Simplify using `[omegaLevi]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hc₀ u`. Establish `: omegaLevi k d 1 = 1` using `by simp [omegaLevi]`. Rewrite using `[this]`.

Conclude with `LinearMap.congr_fun (map_one (x 1).rep) u`. Establish `h3 : Ψ (S.toRepresentation (omegaLevi k d) v) = piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v)` using `Ψ.toIntertwiningMap.isIntertwining _ _ _ v`. Establish `h4 : Ψ v ≠ 0` using `fun h => hv (Ψ.toLinearEquiv.injective (by simpa using h))`. Establish `h5 : ν • Ψ v = c₀ • Ψ v`. Rewrite using `[← h2, ← h3, h1, map_smul]`.

Establish `h6 : c₀ = ν` using `(smul_left_injective ℂ h4 h5).symm`. Rewrite using `[← h6]`. Conclude with `hc₀`.
-/
theorem exists_constituent (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (d : Fin 2 → ℕ)
    (hd : ∑ a, d a = N) (μ : ℂ) (w : V)
    (hw : (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0)
    (hμ : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd)))) :
    ∃ (x : Fin 2 → IrrGL k) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧
      Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧
      ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hfl : HasFiniteLength (jac (stdBlocks d hd) π) :=
    (hBZ k).2.1 (Fin 2) (Fin N) (fun a => Fin (d a)) (stdBlocks d hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  set ν : ℂ := μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2) with hν
  set w' : Jacquet π (unipRad k (stdBlocks d hd)) := Submodule.Quotient.mk w with hw'
  have heig : jac (stdBlocks d hd) π (omegaLevi k d) w' = ν • w' := by
    rw [hw', jac_mk, leviEmb_omegaLevi, hμ, deltaHalf_omegaLevi, smul_smul, hν, mul_comm]
  set E := eigenSub (jac (stdBlocks d hd) π) (omegaLevi k d) (omegaLevi_comm d) ν with hE
  have hEne : E ≠ ⊥ := by
    intro h
    have : w' ∈ E.toSubmodule := mem_eigenSub.2 heig
    rw [h] at this
    exact hw ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨S, hS, hSE⟩ := exists_atom_le hfl hEne
  have hSirr : S.toRepresentation.IsIrreducible := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨S.toSubmodule, S.toRepresentation, isSmooth_sub (isSmooth_jac _ hs) S, hSirr⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k (Fin 2) (fun a => Fin (d a)) τ
  let x : Fin 2 → IrrGL k := fun a => IrrGL.of (N := d a) (s a).ρ (s a).smooth (s a).irr
  let Ψ : S.toRepresentation.Equiv (piTensor fun a => (x a).rep) :=
    Φ.trans (piTensorCongr fun a => IrrGL.equivOf (N := d a) (s a).ρ (s a).smooth (s a).irr)
  obtain ⟨c₀, hc₀⟩ := exists_scalarBy (x 0) (Zls.unifU k)
  obtain ⟨c₁, hc₁⟩ := exists_scalarBy (x 1) (Zls.unifU k)
  refine ⟨x, hd, fun a => rfl, jm_ne_zero_of_equiv x hd π S Ψ, ?_, c₁, hc₁⟩
  have hSne : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.ext h)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
  let v : S.toSubmodule := ⟨v₀, hv₀⟩
  have hv : v ≠ 0 := fun h => hv₀ne (congrArg Subtype.val h)
  have h1 : S.toRepresentation (omegaLevi k d) v = ν • v := Subtype.ext (mem_eigenSub.1 (hSE hv₀))
  have h2 : piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) = c₀ • Ψ v := by
    refine piTensor_apply_of_scalar _ _ c₀ (fun u => ?_) (fun u => ?_) _
    · have : omegaLevi k d 0 = Matrix.GeneralLinearGroup.scalar (Fin (x 0).1) (Zls.unifU k) := by
        simp [omegaLevi]
        rfl
      rw [this]
      exact hc₀ u
    · have : omegaLevi k d 1 = 1 := by simp [omegaLevi]
      rw [this]
      exact LinearMap.congr_fun (map_one (x 1).rep) u
  have h3 : Ψ (S.toRepresentation (omegaLevi k d) v) =
      piTensor (fun a => (x a).rep) (omegaLevi k d) (Ψ v) :=
    Ψ.toIntertwiningMap.isIntertwining _ _ _ v
  have h4 : Ψ v ≠ 0 := fun h => hv (Ψ.toLinearEquiv.injective (by simpa using h))
  have h5 : ν • Ψ v = c₀ • Ψ v := by
    rw [← h2, ← h3, h1, map_smul]
  have h6 : c₀ = ν := (smul_left_injective ℂ h4 h5).symm
  rw [← h6]
  exact hc₀

/- English proof (translation)
Introduce `_ _ _ _ _ N _ _ _ π hs hi _ _ d hd _ _ μ w hw hμ` and use `exists_constituent N π hs hi d hd μ w hw hμ`.
-/
theorem exists_constituent_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL k) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 :=
  fun _ _ _ _ _ N _ _ _ π hs hi _ _ d hd _ _ μ w hw hμ => exists_constituent N π hs hi d hd μ w hw hμ

end Local

end GlobalTheory.CompanionTheory.JacExp

end
