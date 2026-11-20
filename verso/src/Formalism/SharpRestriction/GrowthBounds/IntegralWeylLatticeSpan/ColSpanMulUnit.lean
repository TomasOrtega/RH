import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.RestGramW
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Use `choose u hu using hU`. Establish `h : (fun i => (X * U) i c) = ∑ b, u b c • (fun i => X i b)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def, hu, mul_comm]`. Establish `hmem : (∑ b, u b c • (fun i => X i b)) ∈ Submodule.span O (Set.range fun c : Fin k => fun i => X i c)` using `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.

Rewrite `hmem` using `[← h]`. Conclude with `hmem`.
-/
theorem colSpan_mul_le {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} (X U : Matrix (Fin k) (Fin k) Kf)
    (hU : ∀ a b, U a b ∈ Set.range (algebraMap O Kf)) : colSpan O (X * U) ≤ colSpan O X := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  choose u hu using hU
  have h : (fun i => (X * U) i c) = ∑ b, u b c • (fun i => X i b) := by
    funext i
    rw [Finset.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, hu, mul_comm]
  have hmem : (∑ b, u b c • (fun i => X i b)) ∈ Submodule.span O (Set.range fun c : Fin k => fun i => X i c) :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  rw [← h] at hmem
  exact hmem

/- English proof (translation)
Use `le_antisymm (colSpan_mul_le X U hU) ?_` and prove the remaining obligations. Use `colSpan_mul_le (O := O) (X * U) U' hU'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, h, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem colSpan_mul_unit {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} (X U U' : Matrix (Fin k) (Fin k) Kf)
    (hU : ∀ a b, U a b ∈ Set.range (algebraMap O Kf)) (hU' : ∀ a b, U' a b ∈ Set.range (algebraMap O Kf)) (h : U * U' = 1) :
    colSpan O (X * U) = colSpan O X := by
  refine le_antisymm (colSpan_mul_le X U hU) ?_
  have := colSpan_mul_le (O := O) (X * U) U' hU'
  rwa [Matrix.mul_assoc, h, Matrix.mul_one] at this

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}

def rho (G : GAtP p) (v : Fin G.P.nV) (s : ℕ) : G.P.Qq v →+* G.Kf :=
  (G.P.ι v).comp ((G.P.σ v ^ s : G.P.Qq v ≃+* G.P.Qq v) : G.P.Qq v →+* G.P.Qq v)

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Take `⟨z, hz⟩` from `la_sigma_pow (G.P.σ v) (la_frob G v) s y`. Use `⟨G.P.j v z, ?_⟩` and prove the remaining obligations. Use `show _ = G.P.ι v ((G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) y))`. Rewrite using `[hz, (G.P.setting v).ι_comp]`.
-/
theorem rho_int (v : Fin G.P.nV) (s : ℕ) (x : G.P.Qq v) (hx : x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v))) :
    rho G v s x ∈ Set.range (algebraMap G.O G.Kf) := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := la_sigma_pow (G.P.σ v) (la_frob G v) s y
  refine ⟨G.P.j v z, ?_⟩
  show _ = G.P.ι v ((G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) y))
  rw [hz, (G.P.setting v).ι_comp]

/- English proof (translation)
Rewrite using `[hL v, la_extO_G]`. Use `set N : GL (Fin n) E := A.B⁻¹ * γ * B' with hN`. Establish `hX : la_tw (G.P.ι v) (G.P.σ v) s.val (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) N) : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = (N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk)`. Use extensionality with `a b`. Both sides reduce to the same expression.

Rewrite using `[hX]`. Unfold `nAt`. Distinguish the cases in `hs : Even s.val`. Rewrite using `[if_pos hs]`. Use `congr 1`.

Use extensionality with `a b`. Use `hpos v s (N.1 (finCongr A.rk a) (finCongr A.rk b))` as an intermediate fact. Rewrite `this` using `[if_pos hs]`. Conclude with `this.symm`. Rewrite using `[if_neg hs] set Gm := cT (σ : E →+* E) B'.1 * J * B'.1 with hGm`.

Establish `hJ : J = cT (σ : E →+* E) (A.B⁻¹).1 * (A.B⁻¹).1`. Establish `h0 : cT (σ : E →+* E) (A.B⁻¹).1 * (cT (σ : E →+* E) A.B.1 * J * A.B.1) * (A.B⁻¹).1 = J`. Establish `e1 : cT (σ : E →+* E) (A.B⁻¹).1 * cT (σ : E →+* E) A.B.1 = 1`. Rewrite using `[← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]`. Establish `e2 : A.B.1 * (A.B⁻¹).1 = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]`. Rewrite `h0` using `[hBs, Matrix.mul_one]`. Conclude with `h0.symm`.

Establish `h1 : cT (σ : E →+* E) N.1 * N.1 = Gm`. Establish `hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J` using `hγ`. Establish `eN : N.1 = (A.B⁻¹).1 * γ.1 * B'.1` using `rfl`. Rewrite using `[eN, cT_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Gm := by rw [← hJ, hγ']`. Establish `h2 : cT (σ : E →+* E) (N⁻¹).1 * Gm = N.1`. Rewrite using `[← h1, ← Matrix.mul_assoc, ← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul]`. Establish `hdet : IsUnit Gm.det`.

Establish `h3 : IsUnit (cT (σ : E →+* E) (N⁻¹).1 * Gm).det`. Rewrite using `[h2]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 N.isUnit`. Rewrite `h3` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h3`.

Establish `h3 : cT (σ : E →+* E) (N⁻¹).1 = N.1 * Gm⁻¹`. Rewrite using `[← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]`. Establish `hY : ((((bc (tE (pos ⟨v, s⟩)) N)⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr A.rk) (finCongr A.rk)).map e = ((N.1 * Gm⁻¹).map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk)`. Rewrite using `[← map_inv, ← h3]`. Use extensionality with `a b`.

Establish `h4` using `hpos v s ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b))`. Rewrite `h4` using `[if_neg hs]`. Establish `h5 : σ ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b)) = (N⁻¹).1 (finCongr A.rk b) (finCongr A.rk a)` using `hσσ _`. Rewrite `h4` using `[h5]`. Conclude with `h4`.

Rewrite using `[hY, Matrix.map_mul, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr A.rk) _]`. Use `(colSpan_mul_unit ((N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk)) ((Gm⁻¹.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk)) ((Gm.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk)) (fun …` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]`.
-/
theorem latO_of (tE : Tau → E →+* LL)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hσσ : ∀ x, σ (σ x) = x)
    (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (B' : GL (Fin n) E)
    (L : G.P.Tup)
    (hL : ∀ v, L v = colSpan (G.P.W v) (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')) :
      GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hG : ∀ v a b, A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1) a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹ a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)))
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
      colSpan G.O ((nAt G.P A.rk pos (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) v s).map e) := by
  rw [hL v, la_extO_G]
  set N : GL (Fin n) E := A.B⁻¹ * γ * B' with hN
  have hX : la_tw (G.P.ι v) (G.P.σ v) s.val (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) N) :
      GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      (N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk) := by
    ext a b; rfl
  rw [hX]
  unfold nAt
  by_cases hs : Even s.val
  · rw [if_pos hs]
    congr 1
    ext a b
    have := hpos v s (N.1 (finCongr A.rk a) (finCongr A.rk b))
    rw [if_pos hs] at this
    exact this.symm
  · rw [if_neg hs]
    set Gm := cT (σ : E →+* E) B'.1 * J * B'.1 with hGm
    have hJ : J = cT (σ : E →+* E) (A.B⁻¹).1 * (A.B⁻¹).1 := by
      have h0 : cT (σ : E →+* E) (A.B⁻¹).1 * (cT (σ : E →+* E) A.B.1 * J * A.B.1) * (A.B⁻¹).1 = J := by
        have e1 : cT (σ : E →+* E) (A.B⁻¹).1 * cT (σ : E →+* E) A.B.1 = 1 := by
          rw [← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
        have e2 : A.B.1 * (A.B⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        calc cT (σ : E →+* E) (A.B⁻¹).1 * (cT (σ : E →+* E) A.B.1 * J * A.B.1) * (A.B⁻¹).1
            = (cT (σ : E →+* E) (A.B⁻¹).1 * cT (σ : E →+* E) A.B.1) * J * (A.B.1 * (A.B⁻¹).1) := by
              simp only [Matrix.mul_assoc]
          _ = J := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      rw [hBs, Matrix.mul_one] at h0
      exact h0.symm
    have h1 : cT (σ : E →+* E) N.1 * N.1 = Gm := by
      have hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
      have eN : N.1 = (A.B⁻¹).1 * γ.1 * B'.1 := rfl
      rw [eN, cT_mul, cT_mul]
      calc cT (σ : E →+* E) B'.1 * (cT (σ : E →+* E) γ.1 * cT (σ : E →+* E) (A.B⁻¹).1) * ((A.B⁻¹).1 * γ.1 * B'.1)
          = cT (σ : E →+* E) B'.1 * (cT (σ : E →+* E) γ.1 * (cT (σ : E →+* E) (A.B⁻¹).1 * (A.B⁻¹).1) * γ.1) * B'.1 := by
            simp only [Matrix.mul_assoc]
        _ = Gm := by rw [← hJ, hγ']
    have h2 : cT (σ : E →+* E) (N⁻¹).1 * Gm = N.1 := by
      rw [← h1, ← Matrix.mul_assoc, ← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul]
    have hdet : IsUnit Gm.det := by
      have h3 : IsUnit (cT (σ : E →+* E) (N⁻¹).1 * Gm).det := by
        rw [h2]; exact (Matrix.isUnit_iff_isUnit_det _).1 N.isUnit
      rw [Matrix.det_mul] at h3
      exact isUnit_of_mul_isUnit_right h3
    have h3 : cT (σ : E →+* E) (N⁻¹).1 = N.1 * Gm⁻¹ := by
      rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    have hY : ((((bc (tE (pos ⟨v, s⟩)) N)⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr A.rk)
        (finCongr A.rk)).map e =
        ((N.1 * Gm⁻¹).map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk) := by
      rw [← map_inv, ← h3]
      ext a b
      have h4 := hpos v s ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b))
      rw [if_neg hs] at h4
      have h5 : σ ((cT (σ : E →+* E) (N⁻¹).1) (finCongr A.rk a) (finCongr A.rk b)) =
          (N⁻¹).1 (finCongr A.rk b) (finCongr A.rk a) := hσσ _
      rw [h5] at h4
      exact h4
    rw [hY, Matrix.map_mul, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr A.rk) _]
    refine (colSpan_mul_unit ((N.1.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      ((Gm⁻¹.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      ((Gm.map ((rho G v s.val).comp (A.iw v))).submatrix (finCongr A.rk) (finCongr A.rk))
      (fun a b => rho_int v s.val _ (hG v _ _).2) (fun a b => rho_int v s.val _ (hG v _ _).1) ?_).symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Introduce `u w hg i L c g γ κ hg' hγ hpt B' hB' v s`. Conclude with `latO_of (tEL D) (hpos u w hg) (fun x => by rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive] …`.
-/
theorem restLatO_of {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}
    (hpos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
      I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
        (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x)))
    (h1 : RestLatW T I) (h2 : RestGramW I) : RestLatO T Gt I := by
  intro u w hg i L c g γ κ hg' hγ hpt B' hB' v s
  exact latO_of (tEL D) (hpos u w hg) (fun x => by rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive]) (locAt_std u w hg I.B I.B_std) γ hγ B' L
    (h1 u w hg i L c g γ κ hg' hγ hpt B' hB') (h2 u w hg c B' hB') v s

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero`.

Introduce `x _`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.UG.hform]`. Consider the case `add y y' _ _ hy hy'`. Introduce `x hx`.

Establish `e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y'`. Simplify using `only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Rewrite using `[e]`. Conclude with `add_mem (hy x hx) (hy' x hx)`. Consider the case `smul r y _ hy`.

Introduce `x hx`. Establish `e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y`. Simplify using `only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `mul_mem ⟨r, rfl⟩ (hy x hx)`. Conclude with `Submodule.subset_span`.
-/
theorem span_dualSet {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) :
    ((Submodule.span (𝓞 K) (dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = dualSet σ J L := by
  apply le_antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero =>
      intro x _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add y y' _ _ hy hy' =>
      intro x hx
      have e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
        simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem (hy x hx) (hy' x hx)
    | smul r y _ hy =>
      intro x hx
      have e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact mul_mem ⟨r, rfl⟩ (hy x hx)
  · exact Submodule.subset_span

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB in
/- English proof (translation)
Introduce `u w _ c`. Establish `: Fact (D.what₂.places.resChar w).Prime` using `⟨D.what₂.places.resChar_prime w⟩`. Establish `hL` using `bwB_clsCrd_lat D u 0 (Nat.zero_le _) c`. Take `⟨d, hd, hle⟩` from `dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (bwB_gramN_det D 0 (Nat.zero_le _)) _ hL`. Establish `hLd : Ld D u 0 (Nat.zero_le _) c ≤ bnd d` using `hle`.

Establish `hLd_sp` using `dual_span (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) _ hL`. Take `⟨B, hB⟩` from `exists_isLocBasis (D.what₂.places.resChar w) _ _ (fg_of_le_bnd hd hLd) hLd_sp`. Use `⟨B, ?_⟩` and prove the remaining obligations. Establish `e : (Ld D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) = dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)` using `span_dualSet _ _ _`. Rewrite `hB` using `[e]`. Then use the resulting hypothesis.
-/
theorem restExB (D : D7) : RestExB D := by
  intro u w _ c
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hL := bwB_clsCrd_lat D u 0 (Nat.zero_le _) c
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (bwB_gramN_det D 0 (Nat.zero_le _)) _ hL
  have hLd : Ld D u 0 (Nat.zero_le _) c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) _ hL
  obtain ⟨B, hB⟩ := exists_isLocBasis (D.what₂.places.resChar w) _ _ (fg_of_le_bnd hd hLd) hLd_sp
  refine ⟨B, ?_⟩
  have e : (Ld D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c) := span_dualSet _ _ _
  rwa [e] at hB

def unitsW (D : D7) (w : D.what₂.places.Pl) : Submonoid ℂ where
  carrier := {z | ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = z}
  one_mem' := ⟨1, one_mem _, by rw [inv_one]; exact one_mem _, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨r, hr, hr', rfl⟩ ⟨s, hs, hs', rfl⟩
    exact ⟨r * s, mul_mem hr hs, by rw [mul_inv]; exact mul_mem hr' hs', map_mul _ _ _⟩

/- English proof (translation)
Take `⟨r, hr, hr', rfl⟩` from `h`. Conclude with `⟨r⁻¹, hr', by rwa [inv_inv], map_inv₀ _ _⟩`.
-/
theorem unitsW_inv {w : D.what₂.places.Pl} {z : ℂ} (h : z ∈ unitsW D w) : z⁻¹ ∈ unitsW D w := by
  obtain ⟨r, hr, hr', rfl⟩ := h
  exact ⟨r⁻¹, hr', by rwa [inv_inv], map_inv₀ _ _⟩

/- English proof (translation)
Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_pow hN.ne']`. Conclude with `zero_ne_one h`. Establish `hr : r ∈ intW D.what₂.places w`.

Establish `htop : D.what₂.places.val w r ≠ ⊤` using `by rw [Ne, AddValuation.top_iff]; exact hr0`. Take `⟨a, ha⟩ : ∃ a : ℤ, D.what₂.places.val w r = (a : WithTop ℤ)` from `⟨_, (WithTop.coe_untop _ htop).symm⟩`. Establish `h1 : N • D.what₂.places.val w r = 0` using `by rw [← AddValuation.map_pow, h, AddValuation.map_one]`. Rewrite `h1` using `[ha, ← WithTop.coe_nsmul, WithTop.coe_eq_zero]`. Establish `ha0 : a = 0`.

Break down `smul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 hN.ne'`. Conclude with `h2`. Use `show (0 : WithTop ℤ) ≤ D.what₂.places.val w r`. Rewrite using `[ha, ha0]`.

Conclude with `le_refl _`. Establish `hinv : r⁻¹ = r ^ (N - 1)` using `(eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hN.ne', h])).symm`. Conclude with `⟨r, hr, by rw [hinv]; exact pow_mem hr _, rfl⟩`.
-/
theorem unitsW_of_pow {w : D.what₂.places.Pl} {r : D.what₂.LL} {N : ℕ} (hN : 0 < N) (h : r ^ N = 1) :
    D.what₂.embLL r ∈ unitsW D w := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at h
    exact zero_ne_one h
  have hr : r ∈ intW D.what₂.places w := by
    have htop : D.what₂.places.val w r ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact hr0
    obtain ⟨a, ha⟩ : ∃ a : ℤ, D.what₂.places.val w r = (a : WithTop ℤ) := ⟨_, (WithTop.coe_untop _ htop).symm⟩
    have h1 : N • D.what₂.places.val w r = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
    rw [ha, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hN.ne'
      · exact h2
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w r
    rw [ha, ha0]
    exact le_refl _
  have hinv : r⁻¹ = r ^ (N - 1) := (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hN.ne', h])).symm
  exact ⟨r, hr, by rw [hinv]; exact pow_mem hr _, rfl⟩

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `u w _ κ`. Establish `key : ((((T u).cls0).lev.chi κ : ℂˣ) : ℂ) ∈ unitsW D w`. Rewrite using `[((T u).glev0).chi_eq κ]`. Use `prod_mem fun i _ => ?_` and prove the remaining obligations. Use `finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_` and prove the remaining obligations.

Use `finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_` and prove the remaining obligations. Use `unitsW_inv ?_` and prove the remaining obligations. Unfold `lamJ`. Rewrite using `[Finset.range_zero, Finset.prod_empty, mul_one]`. It suffices to establish `hall : ∀ t : kv D.host.F v, (T u).gl.psi0 i v hv t ∈ unitsW D w from hall _`.

Introduce `t`. Take `⟨r, hr⟩` from `h u i v hv t`. Rewrite using `[← hr]`. Use `unitsW_of_pow (N := D.host.g i) (D.host.g_prime i).pos ?_` and prove the remaining obligations. Apply `D.what₂.embLL.injective` to reduce the goal to its premises.

Establish `h0 : ((D.host.g i : ℕ) : kv D.host.F v) = 0`. Establish `h1 : algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) (D.host.g i : 𝓞 D.host.F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers D.host.F)` using `(Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.mem_maximal_ideal_completion_iff v _).2 hv`. Establish `h2` using `(IsLocalRing.residue_eq_zero_iff _).2 h1`. Rewrite `h2` using `[map_natCast, map_natCast]`. Conclude with `h2`.

Rewrite using `[map_pow, map_one, hr, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, h0, zero_mul, AddChar.map_zero_eq_one]`. Take `⟨r, hr, hr', e⟩` from `key`. Conclude with `⟨r, hr, hr', e⟩`.
-/
theorem restChi_of (T : ∀ u : D.what₂.Word, Forms0 D u) (h : ∀ u, LevelZeroCharacterRational T u) : RestChi T := by
  intro u w _ κ
  have key : ((((T u).cls0).lev.chi κ : ℂˣ) : ℂ) ∈ unitsW D w := by
    rw [((T u).glev0).chi_eq κ]
    refine prod_mem fun i _ => ?_
    refine finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
    refine finprod_induction (fun z : ℂ => z ∈ unitsW D w) (one_mem _) (fun _ _ hx hy => mul_mem hx hy) fun hv => ?_
    refine unitsW_inv ?_
    unfold lamJ
    rw [Finset.range_zero, Finset.prod_empty, mul_one]
    suffices hall : ∀ t : kv D.host.F v, (T u).gl.psi0 i v hv t ∈ unitsW D w from hall _
    intro t
    obtain ⟨r, hr⟩ := h u i v hv t
    rw [← hr]
    refine unitsW_of_pow (N := D.host.g i) (D.host.g_prime i).pos ?_
    apply D.what₂.embLL.injective
    have h0 : ((D.host.g i : ℕ) : kv D.host.F v) = 0 := by
      have h1 : algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) (D.host.g i : 𝓞 D.host.F) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers D.host.F) := (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.mem_maximal_ideal_completion_iff v _).2 hv
      have h2 := (IsLocalRing.residue_eq_zero_iff _).2 h1
      rw [map_natCast, map_natCast] at h2
      exact h2
    rw [map_pow, map_one, hr, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, h0, zero_mul, AddChar.map_zero_eq_one]
  obtain ⟨r, hr, hr', e⟩ := key
  exact ⟨r, hr, hr', e⟩

end Formalism.L2.G.RelativeIndexFlags
