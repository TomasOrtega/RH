import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.DsLow

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem dimV_cast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) :
    StandardLattice.dimV (fun i : Fin n => x (Fin.cast h i)) = StandardLattice.dimV x := by
  subst h; rfl

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hd : 2 * R.rS + R.k + 1 = R.k - 1 + R.m`. Rewrite using `[Formalism.MainNotions.S.dimS_eq R]`. Simplify using `only [Ranks.r]`. Use linear arithmetic over natural numbers and integers.

Unfold `Vol.trueDsig`. Rewrite using `[← StandardLattice.dimV_eq_fdegHC _ (Vol.lamSH_isHCParam R p).1, ← dimV_cast hd]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `key : ∀ (c : Fin (R.k - 1 + R.m)) (d : Fin R.r), d.val = c.val → Formalism.MainNotions.S.lamS R p d = Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ)) c`.

Introduce `c d hcd`. Unfold `Formalism.MainNotions.S.lamS`. Proceed by induction on `c using Fin.addCases with`. Consider the case `left i`. Establish `hi : d.val = i.val` using `hcd`.

Establish `h1 : d.val < R.k - 1` using `hi ▸ i.2`. Rewrite using `[Fin.append_left, dif_pos h1]`. Establish `e : (⟨d.val, h1⟩ : Fin (R.k - 1)) = i` using `Fin.ext hi`. Rewrite using `[e]`. Consider the case `right j`.

Establish `hj : d.val = R.k - 1 + j.val` using `hcd`. Establish `h1 : ¬ d.val < R.k - 1` using `by omega`. Establish `h2 : d.val - (R.k - 1) < R.m` using `by have := j.2; omega`. Rewrite using `[Fin.append_right, dif_neg h1, dif_pos h2]`. Establish `e : (⟨d.val - (R.k - 1), h2⟩ : Fin R.m) = j` using `Fin.ext (by simp only; omega)`.

Rewrite using `[e]`. Conclude with `key _ _ rfl`.
-/
theorem trueDsig_eq_dimV (R : Ranks) (p : HCParam R) :
    Vol.trueDsig R p =
      StandardLattice.dimV (Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ))) := by
  have hk := R.m_add_three_le_k
  have hd : 2 * R.rS + R.k + 1 = R.k - 1 + R.m := by
    rw [Formalism.MainNotions.S.dimS_eq R]; simp only [Ranks.r]; omega
  unfold Vol.trueDsig
  rw [← StandardLattice.dimV_eq_fdegHC _ (Vol.lamSH_isHCParam R p).1, ← dimV_cast hd]
  congr 1
  funext a
  have key : ∀ (c : Fin (R.k - 1 + R.m)) (d : Fin R.r), d.val = c.val → Formalism.MainNotions.S.lamS R p d =
      Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ)) c := by
    intro c d hcd
    unfold Formalism.MainNotions.S.lamS
    induction c using Fin.addCases with
    | left i =>
      have hi : d.val = i.val := hcd
      have h1 : d.val < R.k - 1 := hi ▸ i.2
      rw [Fin.append_left, dif_pos h1]
      have e : (⟨d.val, h1⟩ : Fin (R.k - 1)) = i := Fin.ext hi
      rw [e]
    | right j =>
      have hj : d.val = R.k - 1 + j.val := hcd
      have h1 : ¬ d.val < R.k - 1 := by omega
      have h2 : d.val - (R.k - 1) < R.m := by have := j.2; omega
      rw [Fin.append_right, dif_neg h1, dif_pos h2]
      have e : (⟨d.val - (R.k - 1), h2⟩ : Fin R.m) = j := Fin.ext (by simp only; omega)
      rw [e]
  exact key _ _ rfl

/- English proof (translation)
Use `haveI : NeZero g := ⟨hg.ne_zero⟩`. Unfold `StandardLattice.idxRowLoc StandardLattice.idxLoc`. Use `haveI : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) // StandardLattice.IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := by`. Use `⟨⟨1, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `i j h`.

Establish `: i ≠ j` using `by rintro rfl; exact lt_irrefl _ h`. Simplify using `[Matrix.one_apply_ne this]`. Introduce `i`. Simplify using the standard rewrite rules. Introduce `i j _ h`.

Simplify using `[Matrix.one_apply_ne h.ne']`. Introduce `i j _ h _`. Simplify using `[Matrix.one_apply_ne h]`. Apply `div_pos` to reduce the goal to its premises. Conclude with `Nat.card_pos` after adjusting the coercions.

Conclude with `Nat.card_pos` after adjusting the coercions.
-/
theorem idxRowLoc_pos (g k m : ℕ) (hg : g.Prime) : 0 < StandardLattice.idxRowLoc g k m := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  haveI : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      StandardLattice.IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := by
    refine ⟨⟨1, ?_, ?_, ?_, ?_⟩⟩
    · intro i j h
      have : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne this]
    · intro i; simp
    · intro i j _ h
      simp [Matrix.one_apply_ne h.ne']
    · intro i j _ h _
      simp [Matrix.one_apply_ne h]
  apply div_pos
  · exact_mod_cast Nat.card_pos
  · exact_mod_cast Nat.card_pos

/- English proof (translation)
Introduce `P`. Establish `hm : 0 < (letI` using `P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) := by`. Use `letI := P.H.cmStar`. Use `show 0 < Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)`. Rewrite using `[StandardLattice.standard_form_eq_telescope_form, StandardLattice.standard_lattice_eq_telescope_lattice]`.

Conclude with `Formalism.HermitianLatticesTheory.massTelescope_std_pos P.H.E (host_cmData P.R P.H).cmUnram _`. Establish `h0` using `idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 0)`. Establish `h1` using `idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 1)`. Establish `hp : 0 < ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ)` using `Finset.prod_pos fun τ _ => (Vol.lamSH_isHCParam_and_trueDsig_pos _ _).2`. Establish `hD : 0 < DsP P`.

Unfold `DsP`. Conclude with `mul_pos (mul_pos hm (mul_pos (pow_pos h0 _) (pow_pos h1 _))) hp`. Use `⟨hD, ?_⟩` and prove the remaining obligations. Establish `hc : (2 / 3 : ℝ) ^ P.R.f ≤ 1` using `pow_le_one₀ (by norm_num) (by norm_num)`. Establish `he : ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) = ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ)` using `Finset.prod_congr rfl fun τ _ => (trueDsig_eq_dimV _ _).symm`.

Rewrite using `[he]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem DsP_pos_and_lower : ∀ P : PreCh, 0 < DsP P ∧ (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) * (StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ DsP P := by
  intro P
  have hm : 0 < (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) := by
    letI := P.H.cmStar
    show 0 < Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)
    rw [StandardLattice.standard_form_eq_telescope_form, StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos P.H.E (host_cmData P.R P.H).cmUnram _
  have h0 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 0)
  have h1 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 1)
  have hp : 0 < ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_pos fun τ _ => (Vol.lamSH_isHCParam_and_trueDsig_pos _ _).2
  have hD : 0 < DsP P := by
    unfold DsP
    exact mul_pos (mul_pos hm (mul_pos (pow_pos h0 _) (pow_pos h1 _))) hp
  refine ⟨hD, ?_⟩
  have hc : (2 / 3 : ℝ) ^ P.R.f ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he : ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ))
      (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) = ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_congr rfl fun τ _ => (trueDsig_eq_dimV _ _).symm
  rw [he]
  calc _ = (2 / 3 : ℝ) ^ P.R.f * DsP P := by unfold DsP; ring
    _ ≤ DsP P := mul_le_of_le_one_left hD.le hc

end GlobalTheory.Mem.Top.DsLow
