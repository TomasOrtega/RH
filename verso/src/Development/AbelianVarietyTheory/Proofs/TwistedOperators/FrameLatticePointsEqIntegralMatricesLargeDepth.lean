import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun _ => p.e, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact hp.1, by simp⟩, p.split.2.1⟩`.
-/
theorem isIdemSum_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) : IsIdemSum p.e {w} :=
  ⟨⟨fun _ => p.e, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact hp.1, by simp⟩, p.split.2.1⟩

open Classical in

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Place.up]`. Rewrite using `[hp.2.2]`. Conclude with `(atPl_spec w _).2 Q`.
-/
theorem cpt_up {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y'] (FS : Frame (Kw w) S.rank Y') (FT : Frame (Kw w) T.rank Y) (x : Matrix Y Y' (Kw w))
    (Q : Pl D.host.E) :
    (((p.up FS FT x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map (cpt Q) =
      (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Place.up]
  rw [hp.2.2]
  exact (atPl_spec w _).2 Q

/- English proof (translation)
Substitute `hNS hNT` using the available equality. Rewrite using `[GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} p.e (isIdemSum_of_isPlc hp) (by simpa using hw) _ (Witness.up_half p _ _ x)]`. Use `set FS := frOf rfl βS w`. Use `set FT := frOf rfl βT w`. Establish `hmap : ∀ Q, (frMapO S T βS βT (p.up FS FT x)).map (cpt (D` using `D) Q) = (loc Q βT⁻¹).val * (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) * (loc Q βS).val := by`.

Introduce `Q`. Rewrite using `[← cpt_up hp FS FT x Q]`. Unfold `frMapO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression.

Establish `hw' : (loc w βT⁻¹).val * (FT.β * x * FS.γ) * (loc w βS).val = x`. Establish `e1 : (loc w βT⁻¹).val = FT.γ`. Rewrite using `[map_inv]`. Conclude with `(Matrix.submatrix_id_id _).symm`. Establish `e2 : (loc w βS).val = FS.β` using `(Matrix.submatrix_id_id _).symm`.

Rewrite using `[e1, e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]`. Establish `hval : ∀ Q i j, cpt (D` using `D) Q (frMapO S T βS βT (p.up FS FT x) i j) = if h : Q = w then h ▸ x i j else 0 := by`. Introduce `Q i j`. Use `congrFun (congrFun (hmap Q) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`.

Rewrite using `[this]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same, Matrix.map_id']`. Rewrite using `[hw']`.

Establish `h0 : (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) = 0` using `Matrix.ext fun _ _ => by simp [Pi.single_eq_of_ne h]`. Rewrite using `[h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]`. Unfold `IsIntM`. Use `⟨fun h a b => ?_, fun h a b => ?_⟩` and prove the remaining obligations. Use `(mem_OA_iff _).1 (h a b) w` as an intermediate fact.

Rewrite `this` using `[hval, dif_pos rfl]`. Rewrite using `[Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]`. Conclude with `this`. Use `(mem_OA_iff _).2 fun Q => ?_` and prove the remaining obligations. Rewrite using `[hval]`.

Use `split_ifs with hQ`. Substitute `hQ` using the available equality. Use `h a b` as an intermediate fact. Rewrite `this` using `[Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one]`. Conclude with `this`.

Conclude with `zero_mem _`.
-/
theorem up_mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (hw : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {p : Place D (Kw w)} (hp : IsPlc w p)
    {NS NT : ℕ} (hNS : NS = S.rank) (hNT : NT = T.rank) (x : Matrix (Fin NT) (Fin NS) (Kw w)) :
    p.up (frOf hNS βS w) (frOf hNT βT w) x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation (Kw w)) := by
  classical
  subst hNS hNT
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} p.e (isIdemSum_of_isPlc hp)
    (by simpa using hw) _ (Witness.up_half p _ _ x)]
  set FS := frOf rfl βS w
  set FT := frOf rfl βT w
  have hmap : ∀ Q, (frMapO S T βS βT (p.up FS FT x)).map (cpt (D := D) Q) =
      (loc Q βT⁻¹).val * (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) * (loc Q βS).val := by
    intro Q
    rw [← cpt_up hp FS FT x Q]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hw' : (loc w βT⁻¹).val * (FT.β * x * FS.γ) * (loc w βS).val = x := by
    have e1 : (loc w βT⁻¹).val = FT.γ := by
      rw [map_inv]; exact (Matrix.submatrix_id_id _).symm
    have e2 : (loc w βS).val = FS.β := (Matrix.submatrix_id_id _).symm
    rw [e1, e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hval : ∀ Q i j, cpt (D := D) Q (frMapO S T βS βT (p.up FS FT x) i j) = if h : Q = w then h ▸ x i j else 0 := by
    intro Q i j
    have := congrFun (congrFun (hmap Q) i) j
    rw [Matrix.map_apply] at this
    rw [this]
    split_ifs with h
    · subst h
      simp only [Pi.single_eq_same, Matrix.map_id']
      rw [hw']
    · have h0 : (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) = 0 :=
        Matrix.ext fun _ _ => by simp [Pi.single_eq_of_ne h]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [hval, dif_pos rfl] at this
    rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    rw [hval]
    split_ifs with hQ
    · subst hQ
      have := h a b
      rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · exact zero_mem _

/- English proof (translation)
Use `⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩` and prove the remaining obligations. Establish `hL : R.toLevCh.Is A.μ0` using `s.core.lev`. Establish `hde` using `GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s`. Introduce `t w hw p hp j hj`. Establish `hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `hch.guard t`.

Establish `hb` using `Good.badInt_notMem hL hde hc hw`. Establish `hm : D.R.m ≠ 0` using `by have := D.R.two_le_m; omega`. Use `⟨fun x => up_mem_latO_iff ?_ ?_ (ch.S.B.isFrame_β hL le_rfl hj.le) (ch.S.B.isFrame_β hL le_rfl hj) hb hp _ _ x, fun x => up_mem_latO_iff ?_ ?_ (ch.S.βp_is j hj.le) (ch.S.βp_is (j + 1) hj) hb hp _ _ x⟩` and prove the remaining obligations. Conclude with `(ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩ fun _ e => by injection e with h; exact hm h).sd`. Conclude with `(ch.G.isV (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩ fun _ e => by injection e with h; exact hm h).sd`.

Conclude with `(ch.G.isV (X := .top j) hj.le fun _ e => by cases e).sd`. Conclude with `(ch.G.isV (X := .top (j + 1)) hj fun _ e => by cases e).sd`.
-/
theorem big_latP : Big fun ch => LatP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  intro t w hw p hp j hj
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hb := Good.badInt_notMem hL hde hc hw
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  refine ⟨fun x => up_mem_latO_iff ?_ ?_ (ch.S.B.isFrame_β hL le_rfl hj.le) (ch.S.B.isFrame_β hL le_rfl hj) hb hp _ _ x,
    fun x => up_mem_latO_iff ?_ ?_ (ch.S.βp_is j hj.le) (ch.S.βp_is (j + 1) hj) hb hp _ _ x⟩
  · exact (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .top j) hj.le fun _ e => by cases e).sd
  · exact (ch.G.isV (X := .top (j + 1)) hj fun _ e => by cases e).sd

end GlobalTheory.FlatPlace
