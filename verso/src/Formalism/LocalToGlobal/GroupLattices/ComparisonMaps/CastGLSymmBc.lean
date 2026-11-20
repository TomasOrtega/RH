import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem castGL_symm_bc {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin b) R) :
    (castGL h S).symm (bc f g) = bc f ((castGL h R).symm g) := by
  subst h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem castGL_bc {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin a) R) :
    castGL h S (bc f g) = bc f (castGL h R g) := by
  subst h; rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem bc_comp {m : ℕ} {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) (x : GL (Fin m) R) :
    bc g (bc f x) = bc (g.comp f) x := by
  apply Units.ext; ext i j; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ} {G : GAtP p}

def tPos (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : E →+* LL :=
  if Even s.val then tE (pos ⟨v, s⟩) else (tE (pos ⟨v, s⟩)).comp (σ : E →+* E)

/- English proof (translation)
Unfold `tPos`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem tPos_apply (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E) :
    tPos σ tE pos v s x = tE (pos ⟨v, s⟩) (if Even s.val then x else σ x) := by
  unfold tPos
  split_ifs <;> rfl

def blkLL (A : LocAt F E n G) (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (γ : GL (Fin n) E) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : GL (Fin (G.P.m + 1)) LL :=
  bc (tPos σ tE pos v s) ((castGL A.rk E).symm (A.B⁻¹ * γ * A.B))

/- English proof (translation)
Establish `h1 : (G.lev i).act v γ = bc (A.iw v) ((castGL A.rk E).symm (A.B⁻¹ * A.gamI i γ * A.B))`. Rewrite using `[← castGL_symm_bc, ← hA i v γ, MulEquiv.symm_apply_apply]`. Rewrite using `[h1]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`.

Use `show G.P.ι v ((G.P.σ v ^ s.val) (A.iw v _)) = e (tPos σ tE pos v s _)`. Rewrite using `[tPos_apply, hpos]`.
-/
theorem gPos_act (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    gPosGL G.P v s ((G.lev i).act v γ) = Matrix.GeneralLinearGroup.map e (blkLL A σ tE pos (A.gamI i γ) v s) := by
  have h1 : (G.lev i).act v γ = bc (A.iw v) ((castGL A.rk E).symm (A.B⁻¹ * A.gamI i γ * A.B)) := by
    rw [← castGL_symm_bc, ← hA i v γ, MulEquiv.symm_apply_apply]
  rw [h1]
  apply Units.ext
  ext a b
  show G.P.ι v ((G.P.σ v ^ s.val) (A.iw v _)) = e (tPos σ tE pos v s _)
  rw [tPos_apply, hpos]

/- English proof (translation)
Unfold `Level.actX`. Rewrite using `[natAct_eq, map_natActR]`. Use `congr 2`. Use function extensionality and compare the values at `v s`. Conclude with `gPos_act A tE pos e hA hpos i γ v s`.
-/
theorem actX_map (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (Q : XR G.P LL) :
    (G.lev i).actX γ (MvPolynomial.map e Q) =
      MvPolynomial.map e (natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) Q) := by
  unfold Level.actX
  rw [natAct_eq, map_natActR]
  congr 2
  funext v s
  exact gPos_act A tE pos e hA hpos i γ v s

def atInfGL (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) : Tau → GL (Fin n) ℂ := fun τ => bc (emb τ) γ

/- English proof (translation)
Establish `h1 : cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1 = 1`. Rewrite using `[← cT_mul, ← Units.val_mul, mul_inv_cancel]`. Conclude with `cT_one _`. Establish `hJ : J = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Use `_ = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (cT (σ : E →+* E) B.1 * J * B.1) * (B⁻¹ : GL (Fin n) E).1 := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hB, Matrix.mul_one]`.

Establish `hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J` using `hγ`. Simplify using `only [Units.val_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [← hJ, hγ', hB]`.
-/
theorem unit_of_std {J : Matrix (Fin n) (Fin n) E} (B γ : GL (Fin n) E) (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1)
    (hγ : γ ∈ UJ (σ : E →+* E) J) : cT (σ : E →+* E) (B⁻¹ * γ * B).1 * (B⁻¹ * γ * B).1 = 1 := by
  have h1 : cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1 = 1 := by
    rw [← cT_mul, ← Units.val_mul, mul_inv_cancel]
    exact cT_one _
  have hJ : J = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1 := by
    calc J = (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1) * J * (B.1 * (B⁻¹ : GL (Fin n) E).1) := by
          rw [h1, ← Units.val_mul, mul_inv_cancel]
          simp
      _ = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (cT (σ : E →+* E) B.1 * J * B.1) * (B⁻¹ : GL (Fin n) E).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one]
  have hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  simp only [Units.val_mul, cT_mul]
  calc _ = cT (σ : E →+* E) B.1 * (cT (σ : E →+* E) γ.1 *
        (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1) * γ.1) * B.1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hJ, hγ', hB]

/- English proof (translation)
Establish `hM : atInfGL emb A.B⁻¹ (pos ⟨v, s⟩) * atInfGL emb γ (pos ⟨v, s⟩) * (atInfGL emb A.B⁻¹ (pos ⟨v, s⟩))⁻¹ = bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B)`. Simplify using `[atInfGL, map_mul, map_inv]`. Unfold `hAt`. Rewrite using `[hM]`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `a b`. Distinguish the cases in `hs : Even s.val`. Simplify using `only [hs, if_true] show embLL (tPos σ tE pos v s _) = emb (pos ⟨v, s⟩) _`. Rewrite using `[tPos_apply, if_pos hs, htE]`. Both sides reduce to the same expression.

Simplify using `only [hs, if_false]`. Establish `hinv : ((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 = cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.inv_eq_left_inv hU`. Use `show embLL (tPos σ tE pos v s _) = ((reG G.P A.rk (bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B)))⁻¹ : GL (Fin (G.P.m + 1)) ℂ).1 b a`.

Rewrite using `[tPos_apply, if_neg hs, htE, ← map_inv, ← map_inv]`. Use `show _ = emb (pos ⟨v, s⟩) (((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 _ _)`. Rewrite using `[hinv]`. Both sides reduce to the same expression.
-/
theorem blk_hAt (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) v s := by
  have hM : atInfGL emb A.B⁻¹ (pos ⟨v, s⟩) * atInfGL emb γ (pos ⟨v, s⟩) * (atInfGL emb A.B⁻¹ (pos ⟨v, s⟩))⁻¹ =
      bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B) := by
    simp [atInfGL, map_mul, map_inv]
  unfold hAt
  rw [hM]
  apply Units.ext
  ext a b
  by_cases hs : Even s.val
  · simp only [hs, if_true]
    show embLL (tPos σ tE pos v s _) = emb (pos ⟨v, s⟩) _
    rw [tPos_apply, if_pos hs, htE]
    rfl
  · simp only [hs, if_false]
    have hinv : ((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 = cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_left_inv hU
    show embLL (tPos σ tE pos v s _) =
      ((reG G.P A.rk (bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B)))⁻¹ : GL (Fin (G.P.m + 1)) ℂ).1 b a
    rw [tPos_apply, if_neg hs, htE, ← map_inv, ← map_inv]
    show _ = emb (pos ⟨v, s⟩) (((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 _ _)
    rw [hinv]
    rfl

/- English proof (translation)
Rewrite using `[map_natActR]`. Establish `h1 : (fun v s => Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s)) = hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ)`. Use function extensionality and compare the values at `v s`. Conclude with `blk_hAt A tE pos emb embLL htE γ hU v s`. Rewrite using `[h1]`.

Conclude with `evC_natAct G.P A.rk pos Gm (atInfGL emb A.B⁻¹) (atInfGL emb γ) z z' hz (MvPolynomial.map embLL Q)`.
-/
theorem evC_blk (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (Gm : Tau → Matrix (Fin n) (Fin n) ℂ)
    (z z' : Frames Gm) (hz : IsTr (atInf emb γ) z z') (Q : XR G.P LL) :
    evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL (natActR G.P LL (blkLL A σ tE pos γ) Q)) z' =
      evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL Q) z := by
  rw [map_natActR]
  have h1 : (fun v s => Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s)) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) := by
    funext v s
    exact blk_hAt A tE pos emb embLL htE γ hU v s
  rw [h1]
  exact evC_natAct G.P A.rk pos Gm (atInfGL emb A.B⁻¹) (atInfGL emb γ) z z' hz (MvPolynomial.map embLL Q)

end Formalism.L2.G.Cmp

end
