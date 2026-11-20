import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Vec

section Mat

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Take `⟨p, q, B, B', h1, h2, h3, h4⟩` from `GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2`. Establish `hn : p + q = n`. Establish `e` using `Matrix.trace_mul_comm B B'`. Rewrite `e` using `[h1, h2, Matrix.trace_one, Matrix.trace_one]`. Simplify using `only [Fintype.card_fin, Fintype.card_sum] at e`.

Conclude with `e.symm` after adjusting the coercions. Substitute `hn` using the available equality. Set `e : Fin p ⊕ Fin q ≃ Fin (p + q)` to `finSumFinEquiv`. Establish `hsig : Formalism.UG.HasSignature G p q`. Use `⟨e.symm, ⟨B.submatrix e id, B'.submatrix id e, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `: B.submatrix e id * B'.submatrix id e = (B * B').submatrix e e`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[this, h1, Matrix.submatrix_one_equiv]`. Rewrite using `[Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_id_id]`.

Rewrite using `[Formalism.UG.P.cT_conj_eq, Matrix.reindex_apply, Equiv.symm_symm] show (B.submatrix e id)ᴴ * G.submatrix e e * B.submatrix e id = _`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h3, Matrix.submatrix_id_id]`. Both sides reduce to the same expression. Take `⟨rfl, -⟩` from `Formalism.UG.P.signature_unique _ G _ _ _ _ hsig hs`. Set `ε : Fin (p + q) → ℝ` to `fun a => Sum.elim (fun _ => 1) (fun _ => -1) (e.symm a)`.

Establish `hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e.symm e.symm = Matrix.diagonal fun a => (ε a : ℂ)`. Use extensionality with `a b`. Take `⟨a, rfl⟩` from `e.surjective a`. Take `⟨b, rfl⟩` from `e.surjective b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Apply the tactic sequence `simp [ε, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp`. Use `⟨B.submatrix id e.symm, ε, fun a => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `e.surjective a`. Break down `a with a | a` into its components or cases. Conclude with `Or.inl ⟨by simp [ε], by simp [e]⟩`.

Conclude with `Or.inr ⟨by simp [ε], by simp [e]⟩`. Rewrite using `[← hd, ← h3]`. Both sides reduce to the same expression. Rewrite using `[← hd, Matrix.submatrix_mul_equiv]`. Conclude with `congrArg (fun M => Matrix.submatrix M id e.symm) h4`.
-/
theorem exists_isONBasis {n P Q : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s)
    (hs : Formalism.UG.HasSignature G P Q) : ∃ B : Matrix (Fin n) (Fin n) ℂ, IsONBasis G s B P := by
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hn : p + q = n := by
    have e := Matrix.trace_mul_comm B B'
    rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e
    exact_mod_cast e.symm
  subst hn
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  have hsig : Formalism.UG.HasSignature G p q := by
    refine ⟨e.symm, ⟨B.submatrix e id, B'.submatrix id e, ?_, ?_⟩, ?_⟩
    · have : B.submatrix e id * B'.submatrix id e = (B * B').submatrix e e := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, h1, Matrix.submatrix_one_equiv]
    · rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_id_id]
    · rw [Formalism.UG.P.cT_conj_eq, Matrix.reindex_apply, Equiv.symm_symm]
      show (B.submatrix e id)ᴴ * G.submatrix e e * B.submatrix e id = _
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h3,
        Matrix.submatrix_id_id]
      rfl
  obtain ⟨rfl, -⟩ := Formalism.UG.P.signature_unique _ G _ _ _ _ hsig hs
  let ε : Fin (p + q) → ℝ := fun a => Sum.elim (fun _ => 1) (fun _ => -1) (e.symm a)
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e.symm e.symm =
      Matrix.diagonal fun a => (ε a : ℂ) := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [ε, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  refine ⟨B.submatrix id e.symm, ε, fun a => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective a
    rcases a with a | a
    · exact Or.inl ⟨by simp [ε], by simp [e]⟩
    · exact Or.inr ⟨by simp [ε], by simp [e]⟩
  · rw [← hd, ← h3]
    rfl
  · rw [← hd, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M id e.symm) h4

/- English proof (translation)
Take `⟨e, he, h1, -⟩` from `h`. Establish `h2 : Bᴴ * G * B = 1`. Rewrite using `[h1, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Break down `he a with h | h` into its components or cases. Simplify using `[h.1]`. Conclude with `absurd a.2 (not_lt.2 h.2)`. Establish `hu : IsUnit B` using `IsUnit.of_mul_eq_one_right _ h2`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hu`.

Establish `h3 : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Establish `h4 : (B⁻¹)ᴴ * Bᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]`. Establish `hG : G = (B⁻¹)ᴴ * B⁻¹`. Combine the equalities or inequalities in the displayed calculation. Use `⟨by simp, by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_one, hG]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))`.
-/
theorem isCartanInv_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

end Mat

variable {D : D7}

/- English proof (translation)
Set `U : Submodule ℂ (WO S T → ℂ)` to `{ carrier := {g | IsThetaFunO ψ S T g} add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb zero_mem' := GlobalTheory.OrientedHeis.theta_zero smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }`. Set `H : WO S T → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)` to `fun w => { toFun := heisO ψ S T w map_add' := fun a b => funext fun x => mul_add _ _ _ map_smul' := fun a b => funext fun x => mul_left_comm _ _ _ }`. Use `show f ∈ U`. Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `l hl`.

Set `A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)` to `LinearMap.pi fun w => l ∘ₗ H w`. Establish `hA0 : ∀ g w, A g w = l (heisO ψ S T w g)` using `fun _ _ => rfl`. Establish `hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g)` using `fun u g => by`. Use function extensionality and compare the values at `w`. Rewrite using `[hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]`.

Both sides reduce to the same expression. Establish `hf0 : A f₀ = 0`. Use function extensionality and compare the values at `w`. Conclude with `(Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)`. Take `⟨⟨Tm, hT⟩, hall⟩` from `h`.

Establish `hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm)` using `{ trans := fun Φ hΦ x hx => by`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT.trans Φ hΦ x hx, hA x]`. Conclude with `((H x).map_add _ _).symm`. Use `modul := fun Φ hΦ y hy => by`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT.modul Φ hΦ y hy, hA y]`.

Conclude with `((H y).map_add _ _).symm`. Use `vac := by`. Rewrite using `[LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }`. Establish `e1 : f = Tm Φ` using `hall Tm hT`. Establish `e2 : f = (Tm + A ∘ₗ Tm) Φ` using `hall _ hT'`.

Rewrite `e2` using `[LinearMap.add_apply, LinearMap.comp_apply, ← e1]`. Establish `e3` using `congrFun (left_eq_add.1 e2) 0`. Rewrite `e3` using `[hA0, GlobalTheory.OrientedHeis.heisO_zero]`. Then use the resulting hypothesis.
-/
theorem theta_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  let H : WO S T → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun w =>
    { toFun := heisO ψ S T w
      map_add' := fun a b => funext fun x => mul_add _ _ _
      map_smul' := fun a b => funext fun x => mul_left_comm _ _ _ }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.pi fun w => l ∘ₗ H w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((H x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((H y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

/- English proof (translation)
The claim follows from `(GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _ (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1 (fun …`.
-/
theorem theta_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) :=
  (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ _`. Establish `hθ : IsInfFam R.θ` using `hC.models.inf`. Establish `hψ : IsStdChar D R.ψ (-1)` using `(hC.thP.ωP i A.μ0).std`. Establish `hQ : R.Q A.μ0 = ∅` using `Finset.eq_empty_iff_forall_notMem.2 fun PP hPP => (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)`. Establish `h0` using `(hC.thP.vP i A.μ0).2`.

Take `⟨e, he, -⟩` from `h0`. Rewrite `he` using `[hQ]`. Establish `sdV` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)`. Establish `sdW` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)`. Establish `hc` using `GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)`.

Establish `h1` using `GlobalTheory.Member.vacuum_oriented_exists D R.ψ R.θ hψ hθ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => isCartanInv_one (hC.models.BV i τ)) hc _ _ sdV sdW`. Take `⟨f₀, hf₀⟩` from `h1`. Establish `h2` using `GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) _ _ (R.βV i) (R.βW i) R.Pg ∅ (fun _ => 1) sdV sdW (hC.lev.βV i).choose_spec.1 (hC.lev.βW i).choose_spec.1 (Finset.disjoint_empty_right _) ⟨e, he⟩ f₀ hf₀`. Take `⟨f, hf⟩` from `h2`. Establish `h3` using `fun ρ => exists_isONBasis (hc ρ) (D.sp.W_sig _ (tauE D ρ))`.

Use `choose B hB using h3`. Establish `h4` using `hf.2`. Take `⟨e', -, h5⟩` from `h4`. Conclude with `⟨f₀, f, B, hf, hB, theta_pureTensorO hψ hθ _ _ _ _ (theta_of_thetaAt hψ hθ h5 hf₀.2.theta)⟩`.
-/
theorem exists_vecData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ _
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i A.μ0).std
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have h0 := (hC.thP.vP i A.μ0).2
  obtain ⟨e, he, -⟩ := h0
  rw [hQ] at he
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have h1 := GlobalTheory.Member.vacuum_oriented_exists D R.ψ R.θ hψ hθ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ))
    (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => isCartanInv_one (hC.models.BV i τ)) hc _ _ sdV sdW
  obtain ⟨f₀, hf₀⟩ := h1
  have h2 := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) _ _ (R.βV i) (R.βW i)
    R.Pg ∅ (fun _ => 1) sdV sdW (hC.lev.βV i).choose_spec.1 (hC.lev.βW i).choose_spec.1 (Finset.disjoint_empty_right _)
    ⟨e, he⟩ f₀ hf₀
  obtain ⟨f, hf⟩ := h2
  have h3 := fun ρ => exists_isONBasis (hc ρ) (D.sp.W_sig _ (tauE D ρ))
  choose B hB using h3
  have h4 := hf.2
  obtain ⟨e', -, h5⟩ := h4
  exact ⟨f₀, f, B, hf, hB, theta_pureTensorO hψ hθ _ _ _ _ (theta_of_thetaAt hψ hθ h5 hf₀.2.theta)⟩

end GlobalTheory.GalLift.Vec

end
