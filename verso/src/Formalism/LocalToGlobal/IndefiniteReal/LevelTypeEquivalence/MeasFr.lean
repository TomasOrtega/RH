import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix

namespace Formalism.IndefR.Eqv.MF

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {p q n : ℕ}

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Conclude with `(Formalism.L2.SG.InstExistsPf.Jpq_sub _ _ e _ fun _ => rfl).symm`.
-/
theorem Jm_sub (e : Fin n ≃ Fin p ⊕ Fin q) :
    Formalism.REAL.Jm (fun i => (e i).isLeft) = (Formalism.UG.Jpq p q).submatrix e e := by
  unfold Formalism.REAL.Jm
  exact (Formalism.L2.SG.InstExistsPf.Jpq_sub _ _ e _ fun _ => rfl).symm

/- English proof (translation)
Rewrite using `[Jm_sub, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]`.
-/
theorem sq_gram (e : Fin n ≃ Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (A.submatrix e id)ᴴ * Formalism.REAL.Jm (fun i => (e i).isLeft) * A.submatrix e id = Aᴴ * Formalism.UG.Jpq p q * A := by
  rw [Jm_sub, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

/- English proof (translation)
Take `⟨e, P', hP'⟩` from `h`. Rewrite `hP'` using `[Formalism.L2.SG.InstExistsPf.cT_eq]`. Set `A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `(P' : Matrix _ _ ℂ)`. Set `Ai : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `((P'⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)`. Use `⟨e, A.submatrix e e, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : A.submatrix e e * Ai.submatrix e e = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, show A * Ai = 1 from P'.mul_inv, Matrix.submatrix_one_equiv]`. Conclude with `Matrix.isUnit_det_of_right_inverse h1`. Establish `hM : M = (M.reindex e e).submatrix e e`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Rewrite using `[show Aᴴ * M.reindex e e * A = Formalism.UG.Jpq _ _ from hP']`. Conclude with `(Jm_sub e).symm`.
-/
theorem sig_frame (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature M p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det ∧
      Pᴴ * M * P = Formalism.REAL.Jm (fun i => (e i).isLeft) := by
  obtain ⟨e, P', hP'⟩ := h
  rw [Formalism.L2.SG.InstExistsPf.cT_eq] at hP'
  let A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P' : Matrix _ _ ℂ)
  let Ai : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P'⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
  refine ⟨e, A.submatrix e e, ?_, ?_⟩
  · have h1 : A.submatrix e e * Ai.submatrix e e = 1 := by
      rw [Matrix.submatrix_mul_equiv, show A * Ai = 1 from P'.mul_inv, Matrix.submatrix_one_equiv]
    exact Matrix.isUnit_det_of_right_inverse h1
  · have hM : M = (M.reindex e e).submatrix e e := by
      ext i j; simp
    rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rw [show Aᴴ * M.reindex e e * A = Formalism.UG.Jpq _ _ from hP']
    exact (Jm_sub e).symm

/- English proof (translation)
Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = M := by rw [mul_nonsing_inv _ hP, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem inv_frame {M J P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (h : Pᴴ * M * P = J) :
    (P⁻¹)ᴴ * J * P⁻¹ = M := by
  rw [← h]
  calc (P⁻¹)ᴴ * (Pᴴ * M * P) * P⁻¹ = (P * P⁻¹)ᴴ * M * (P * P⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = M := by rw [mul_nonsing_inv _ hP, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use `set J := Formalism.UG.Jpq p q`. Establish `hJ : Jᴴ = J` using `Formalism.BasicNotions.Examples₂.CD.J_star p q`. Use `set L₀ := G⁻¹ * A₀ᴴ * J`. Use `set L₁ := G⁻¹ * A₁ᴴ * J`. Establish `hL₀ : L₀ * A₀ = 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL₁ : L₁ * A₁ = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hA₀ : A₀ * L₀ = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).mp hL₀`. Establish `hA₁ : A₁ * L₁ = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).mp hL₁`.

Establish `m1 : (A₁ * L₀) * (A₀ * L₁) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `m2 : (A₀ * L₁) * (A₁ * L₀) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hGi : (G⁻¹)ᴴ = G⁻¹` using `by rw [conjTranspose_nonsing_inv, hGh]`.

Establish `hmem : star (A₁ * L₀) * J * (A₁ * L₀) = J`. Rewrite using `[show star (A₁ * L₀) = (A₁ * L₀)ᴴ from rfl]`. Establish `hL₀h : L₀ᴴ = J * A₀ * G⁻¹`. Simplify using `only [L₀, conjTranspose_mul, conjTranspose_conjTranspose, hJ, hGi, Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J * A₀ * (G⁻¹ * G) * (G⁻¹ * A₀ᴴ * J) := by rw [h₁, hL₀h]; simp only [L₀, Matrix.mul_assoc]`. Use `_ = J * (A₀ * L₀) := by rw [nonsing_inv_mul _ hG]; simp only [L₀, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = J := by rw [hA₀, Matrix.mul_one]`.

Set `g : GL (Fin p ⊕ Fin q) ℂ` to `⟨A₁ * L₀, A₀ * L₁, m1, m2⟩`. Establish `hg : g ∈ Formalism.UG.Upq p q` using `(Formalism.UG.P.mem_Upq_iff p q g).mpr hmem`. Use `⟨(⟨g, hg⟩ : Formalism.UG.Upq p q), ?_⟩` and prove the remaining obligations. Use `show A₁ = A₁ * L₀ * A₀`. Rewrite using `[Matrix.mul_assoc, hL₀, Matrix.mul_one]`.
-/
theorem frame_change (e : Fin n ≃ Fin p ⊕ Fin q) (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) (hGh : Gᴴ = G)
    (A₀ A₁ : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (h₀ : A₀ᴴ * Formalism.UG.Jpq p q * A₀ = G)
    (h₁ : A₁ᴴ * Formalism.UG.Jpq p q * A₁ = G) : ∃ u : UpqT p q, A₁ = UpqT.mat u * A₀ := by
  set J := Formalism.UG.Jpq p q
  have hJ : Jᴴ = J := Formalism.BasicNotions.Examples₂.CD.J_star p q
  set L₀ := G⁻¹ * A₀ᴴ * J
  set L₁ := G⁻¹ * A₁ᴴ * J
  have hL₀ : L₀ * A₀ = 1 := by
    calc L₀ * A₀ = G⁻¹ * (A₀ᴴ * J * A₀) := by simp only [L₀, Matrix.mul_assoc]
      _ = 1 := by rw [h₀, nonsing_inv_mul _ hG]
  have hL₁ : L₁ * A₁ = 1 := by
    calc L₁ * A₁ = G⁻¹ * (A₁ᴴ * J * A₁) := by simp only [L₁, Matrix.mul_assoc]
      _ = 1 := by rw [h₁, nonsing_inv_mul _ hG]
  have hA₀ : A₀ * L₀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp hL₀
  have hA₁ : A₁ * L₁ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp hL₁
  have m1 : (A₁ * L₀) * (A₀ * L₁) = 1 := by
    calc (A₁ * L₀) * (A₀ * L₁) = A₁ * (L₀ * A₀) * L₁ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL₀, Matrix.mul_one, hA₁]
  have m2 : (A₀ * L₁) * (A₁ * L₀) = 1 := by
    calc (A₀ * L₁) * (A₁ * L₀) = A₀ * (L₁ * A₁) * L₀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL₁, Matrix.mul_one, hA₀]
  have hGi : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hGh]
  have hmem : star (A₁ * L₀) * J * (A₁ * L₀) = J := by
    rw [show star (A₁ * L₀) = (A₁ * L₀)ᴴ from rfl]
    have hL₀h : L₀ᴴ = J * A₀ * G⁻¹ := by
      simp only [L₀, conjTranspose_mul, conjTranspose_conjTranspose, hJ, hGi, Matrix.mul_assoc]
    calc (A₁ * L₀)ᴴ * J * (A₁ * L₀) = L₀ᴴ * (A₁ᴴ * J * A₁) * L₀ := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J * A₀ * (G⁻¹ * G) * (G⁻¹ * A₀ᴴ * J) := by rw [h₁, hL₀h]; simp only [L₀, Matrix.mul_assoc]
      _ = J * (A₀ * L₀) := by rw [nonsing_inv_mul _ hG]; simp only [L₀, Matrix.mul_one, Matrix.mul_assoc]
      _ = J := by rw [hA₀, Matrix.mul_one]
  let g : GL (Fin p ⊕ Fin q) ℂ := ⟨A₁ * L₀, A₀ * L₁, m1, m2⟩
  have hg : g ∈ Formalism.UG.Upq p q := (Formalism.UG.P.mem_Upq_iff p q g).mpr hmem
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq p q), ?_⟩
  show A₁ = A₁ * L₀ * A₀
  rw [Matrix.mul_assoc, hL₀, Matrix.mul_one]

end Mat

variable {D : D7} {V : HSp D}

set_option quotPrecheck false in
local notation "ρv" v => (Formalism.L2.Host.tauPl D).symm v

structure FrA (V : HSp D) where
  e : ∀ ρ : D.what₂.Tau, Fin V.rank ≃ Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2
  A : ∀ ρ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ
  hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * A ρ = gramAt D V ρ

def sqA (F : FrA V) (ρ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (F.A ρ).submatrix (F.e ρ) id

/- English proof (translation)
Rewrite using `[sqA, sq_gram, F.hA]`.
-/
theorem sqA_gram (F : FrA V) (ρ : D.what₂.Tau) :
    (sqA F ρ)ᴴ * Formalism.REAL.Jm (fun i => (F.e ρ i).isLeft) * sqA F ρ = gramAt D V ρ := by
  rw [sqA, sq_gram, F.hA]

/- English proof (translation)
Use `show (V.gram.map (tauE D ρ)).det ≠ 0`. Rewrite using `[show (V.gram.map (tauE D ρ)).det = tauE D ρ V.gram.det from (RingHom.map_det _ _).symm]`. Conclude with `(map_ne_zero _).mpr (UI.J_det D V)`.
-/
theorem gramAt_det (ρ : D.what₂.Tau) : (gramAt D V ρ).det ≠ 0 := by
  show (V.gram.map (tauE D ρ)).det ≠ 0
  rw [show (V.gram.map (tauE D ρ)).det = tauE D ρ V.gram.det from (RingHom.map_det _ _).symm]
  exact (map_ne_zero _).mpr (UI.J_det D V)

/- English proof (translation)
Use extensionality with `i j`. Use `show star (tauE D ρ (V.gram j i)) = tauE D ρ (V.gram i j)`. Establish `hij : starRingEnd D.host.E (V.gram j i) = V.gram i j`. Use `congrFun (congrFun (UI.J_herm D V) i) j` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gramAt_herm (ρ : D.what₂.Tau) : (gramAt D V ρ)ᴴ = gramAt D V ρ := by
  ext i j
  show star (tauE D ρ (V.gram j i)) = tauE D ρ (V.gram i j)
  have hij : starRingEnd D.host.E (V.gram j i) = V.gram i j := by
    have := congrFun (congrFun (UI.J_herm D V) i) j
    simpa [Formalism.UG.cT] using this
  calc star (tauE D ρ (V.gram j i)) = tauE D ρ (star (V.gram j i)) := (tauE_star D ρ _).symm
    _ = tauE D ρ (V.gram i j) := by rw [← hij]; rfl

/- English proof (translation)
Establish `h` using `congrArg det (sqA_gram F ρ)`. Rewrite `h` using `[det_mul, det_mul]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`.

Conclude with `gramAt_det ρ h.symm`.
-/
theorem sqA_det (F : FrA V) (ρ : D.what₂.Tau) : IsUnit (sqA F ρ).det := by
  have h := congrArg det (sqA_gram F ρ)
  rw [det_mul, det_mul] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact gramAt_det ρ h.symm

def toFrames (F : FrA V) : UI.Frames D V where
  ε v i := (F.e (ρv v) i).isLeft
  P v := (sqA F (ρv v))⁻¹
  unit v := (isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ (sqA_det F _))
  spec v := by
    change ((sqA F (ρv v))⁻¹)ᴴ * gramAt D V (ρv v) * (sqA F (ρv v))⁻¹ = _
    rw [← sqA_gram F (ρv v)]
    exact inv_frame (sqA_det F _) rfl
  Λ := UI.Lv D V
  Λ_fg := UI.L_fg D V
  Λ_span := UI.L_span D V
  Λ_dual := UI.L_dual D V

def phiR (F : FrA V) (v : InfinitePlace D.host.F) :
    UpqT (V.sig (tauE D (ρv v))).1 (V.sig (tauE D (ρv v))).2 ≃ₜ* Formalism.REAL.UJ ((toFrames F).ε v) :=
  PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi (F.e (ρv v)).symm (fun i => by simp [toFrames]) (fun j => by simp [toFrames])

/- English proof (translation)
Use `show reindex _ _ (UpqT.mat b) = _`. Rewrite using `[reindex_apply, Equiv.symm_symm]`.
-/
theorem uMat_phiR (F : FrA V) (v : InfinitePlace D.host.F)
    (b : UpqT (V.sig (tauE D (ρv v))).1 (V.sig (tauE D (ρv v))).2) :
    (uMat (phiR F v b) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (UpqT.mat b).submatrix (F.e (ρv v)) (F.e (ρv v)) := by
  show reindex _ _ (UpqT.mat b) = _
  rw [reindex_apply, Equiv.symm_symm]

/- English proof (translation)
Use `set e := F.e (ρv v)`. Use `set A := F.A (ρv v)`. Use `set A' := sqA F (ρv v)`. Establish `hu` using `sqA_det F (ρv v)`. Establish `hX : infMat D.sp.cm.sig V.gram (thetaC D (ρv v)) (UI.brg (toFrames F) x) = A'⁻¹ * uM (toFrames F) x v * A'`.

Establish `h` using `infMat_brg (toFrames F) x (ρv v)`. Rewrite `h` using `[Equiv.apply_symm_apply]`. Rewrite using `[h]`. Use `show A'⁻¹ * _ * (A'⁻¹)⁻¹ = _`. Rewrite using `[nonsing_inv_nonsing_inv _ hu]`.

Establish `hS : ∀ M : Matrix (Fin (V.sig (tauE D (ρv v))).1 ⊕ Fin (V.sig (tauE D (ρv v))).2) (Fin V.rank) ℂ, (M.submatrix e id).submatrix e.symm id = M`. Introduce `M`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `key : ∀ b : UpqT (V.sig (tauE D (ρv v))).1 (V.sig (tauE D (ρv v))).2, UpqT.mat b * A = A * (A'⁻¹ * uM (toFrames F) x v * A') ↔ (uMat (phiR F v b) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = uM (toFrames F) x v`.

Introduce `b`. Rewrite using `[uMat_phiR]`. Use `set u : Matrix (Fin V.rank) (Fin V.rank) ℂ := uM (toFrames F) x v`. Establish `h1 : (UpqT.mat b * A).submatrix e id = (UpqT.mat b).submatrix e e * A'`. Rewrite using `[show A' = A.submatrix e id from rfl, submatrix_mul_equiv]`.

Establish `h2 : (A * (A'⁻¹ * u * A')).submatrix e id = A' * (A'⁻¹ * u * A')`. Rewrite using `[show A' = A.submatrix e id from rfl]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h3 : (UpqT.mat b).submatrix e e * A' = u * A'`. Rewrite using `[← h1, h, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]`.

Use `_ = u * A' * A'⁻¹ := by rw [h3]`. Use `_ = u := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]`. Introduce `h`. Rewrite using `[← hS (UpqT.mat b * A), ← hS (A * (A'⁻¹ * u * A')), h1, h2, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]`. Rewrite using `[hX]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hba⟩`. Conclude with `⟨b, hb, Subtype.ext (Units.ext ((key b).mp hba))⟩`. Introduce and unpack `⟨b, hb, hbx⟩`. Use `⟨b, hb, (key b).mpr ?_⟩` and prove the remaining obligations.

Rewrite using `[hbx]`. Both sides reduce to the same expression.
-/
theorem cond_iff (F : FrA V) (x : (UI.instV (toFrames F)).GA) (v : InfinitePlace D.host.F)
    (B : Set (UpqT (V.sig (tauE D (ρv v))).1 (V.sig (tauE D (ρv v))).2)) :
    (∃ b ∈ B, UpqT.mat b * F.A (ρv v) =
      F.A (ρv v) * infMat D.sp.cm.sig V.gram (thetaC D (ρv v)) (UI.brg (toFrames F) x)) ↔
      x.1 v ∈ phiR F v '' B := by
  set e := F.e (ρv v)
  set A := F.A (ρv v)
  set A' := sqA F (ρv v)
  have hu := sqA_det F (ρv v)
  have hX : infMat D.sp.cm.sig V.gram (thetaC D (ρv v)) (UI.brg (toFrames F) x) =
      A'⁻¹ * uM (toFrames F) x v * A' := by
    have h := infMat_brg (toFrames F) x (ρv v)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    show A'⁻¹ * _ * (A'⁻¹)⁻¹ = _
    rw [nonsing_inv_nonsing_inv _ hu]
  have hS : ∀ M : Matrix (Fin (V.sig (tauE D (ρv v))).1 ⊕ Fin (V.sig (tauE D (ρv v))).2) (Fin V.rank) ℂ,
      (M.submatrix e id).submatrix e.symm id = M := by
    intro M; ext i j; simp
  have key : ∀ b : UpqT (V.sig (tauE D (ρv v))).1 (V.sig (tauE D (ρv v))).2,
      UpqT.mat b * A = A * (A'⁻¹ * uM (toFrames F) x v * A') ↔
        (uMat (phiR F v b) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = uM (toFrames F) x v := by
    intro b
    rw [uMat_phiR]
    set u : Matrix (Fin V.rank) (Fin V.rank) ℂ := uM (toFrames F) x v
    have h1 : (UpqT.mat b * A).submatrix e id = (UpqT.mat b).submatrix e e * A' := by
      rw [show A' = A.submatrix e id from rfl, submatrix_mul_equiv]
    have h2 : (A * (A'⁻¹ * u * A')).submatrix e id = A' * (A'⁻¹ * u * A') := by
      rw [show A' = A.submatrix e id from rfl]
      ext i j
      simp [Matrix.mul_apply]
    constructor
    · intro h
      have h3 : (UpqT.mat b).submatrix e e * A' = u * A' := by
        rw [← h1, h, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
      calc (UpqT.mat b).submatrix e e = (UpqT.mat b).submatrix e e * A' * A'⁻¹ := by
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = u * A' * A'⁻¹ := by rw [h3]
        _ = u := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    · intro h
      rw [← hS (UpqT.mat b * A), ← hS (A * (A'⁻¹ * u * A')), h1, h2, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [hX]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ⟨b, hb, Subtype.ext (Units.ext ((key b).mp hba))⟩
  · rintro ⟨b, hb, hbx⟩
    refine ⟨b, hb, (key b).mpr ?_⟩
    rw [hbx]
    rfl

/- English proof (translation)
Establish `h : ∀ ρ : D.what₂.Tau, ∃ (e : Fin V.rank ≃ Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (A : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ), Aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * A = gramAt D V ρ` using `fun ρ => by`. Take `⟨e, Q, hQ, hQs⟩` from `sig_frame (V.gram.map (tauE D ρ)) (hS (tauE D ρ))`. Use `⟨e, (Q⁻¹).submatrix e.symm id, ?_⟩` and prove the remaining obligations. Rewrite using `[← sq_gram e]`. Establish `: ((Q⁻¹).submatrix e.symm id).submatrix e id = Q⁻¹` using `by ext i j; simp`.

Rewrite using `[this]`. Conclude with `inv_frame hQ hQs`. Use `choose e A hA using h`. Conclude with `⟨⟨e, A, hA⟩⟩`.
-/
theorem frA_nonempty (hS : V.SigOK) : Nonempty (FrA V) := by
  have h : ∀ ρ : D.what₂.Tau, ∃ (e : Fin V.rank ≃ Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2)
      (A : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ),
      Aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * A = gramAt D V ρ := fun ρ => by
    obtain ⟨e, Q, hQ, hQs⟩ := sig_frame (V.gram.map (tauE D ρ)) (hS (tauE D ρ))
    refine ⟨e, (Q⁻¹).submatrix e.symm id, ?_⟩
    rw [← sq_gram e]
    have : ((Q⁻¹).submatrix e.symm id).submatrix e id = Q⁻¹ := by ext i j; simp
    rw [this]
    exact inv_frame hQ hQs
  choose e A hA using h
  exact ⟨⟨e, A, hA⟩⟩

end Formalism.IndefR.Eqv.MF

end
