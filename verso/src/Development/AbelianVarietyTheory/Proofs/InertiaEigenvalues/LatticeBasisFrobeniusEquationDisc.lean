import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisensteinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hdet : M.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ hc h1.symm`.

Establish `key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]`. Use `_ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]`.

Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun key i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h2`. Simplify `mul_left_cancel₀ hdet h2` using `[Matrix.smul_apply]`.
-/
theorem mul_eq_smul_one_comm {R : Type} [CommRing R] [IsDomain R] {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} {c : R} (hc : c ≠ 0) (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) R)) :
    M' * M = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc M.det • (M' * M) = (M.adjugate * M) * (M' * M) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa [Matrix.smul_apply] using mul_left_cancel₀ hdet h2

/- English proof (translation)
Establish `hdet : W.det ∈ nonZeroDivisors R`. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Establish `htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R` using `pow_mem ht _`. Rewrite `htp`, the goal using `[mem_nonZeroDivisors_iff]`.

Use `⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]), fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩` and prove the remaining obligations. Establish `key : W.det • M = 0`. Rewrite using `[← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]`. Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun key i) j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢`. Conclude with `(mem_nonZeroDivisors_iff.1 hdet).1 _ h2`.
-/
theorem eq_zero_of_mul_eq_zero_of_mul_eq_smul {R : Type} [CommRing R] {d : ℕ}
    {W W' M : Matrix (Fin d) (Fin d) R} {t : R} (ht : t ∈ nonZeroDivisors R)
    (h : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hM : W * M = 0) : M = 0 := by
  have hdet : W.det ∈ nonZeroDivisors R := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R := pow_mem ht _
    rw [mem_nonZeroDivisors_iff] at htp ⊢
    refine ⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]),
      fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩
  have key : W.det • M = 0 := by
    rw [← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢
  exact (mem_nonZeroDivisors_iff.1 hdet).1 _ h2

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_ringHom {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (f : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

end GlobalTheory.BSP

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk d ρ τ s ht hτ Φ hΦ`. Establish `hρ : (0 : ℝ≥0) < bk.ρ₀`. Unfold `BK.ρ₀`. Conclude with `NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)`. Establish `hρ1 : bk.ρ₀ ≤ 1`.

Unfold `BK.ρ₀`. Apply `NNReal.rpow_le_one_of_one_le_of_nonpos` to reduce the goal to its premises. Conclude with `(Fact.out : l.Prime).one_lt.le` after adjusting the coercions. Establish `: (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀`. Simplify using `using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ`. Establish `hXl : frobS l bk.a (X : bk.S) = X ^ l`. Simplify using `[frobS]`. Establish `hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀`.

Rewrite using `[← bk.ev_frob, hXl, map_pow]`. Use `(norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_` and prove the remaining obligations. Conclude with `pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero`. Use `set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def`. Establish `hi : IsDiscMap bk.ev i` using `isDiscMap_map _ _`.

Use `set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def`. Establish `hΦA : IsDiscMap WittVector.frobenius ΦA` using `isDiscMap_map _ _`. Establish `hcomm : i.comp Φ = ΦA.comp i`. Establish `h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (i.comp Φ)` using `⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩`. Establish `h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (ΦA.comp i)`.

Establish `e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev` using `RingHom.ext bk.ev_frob`. Rewrite using `[e]`. Conclude with `⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩`. Conclude with `h1.unique h2`. Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`.

Establish `hinj : Function.Injective i` using `(GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi`. Establish `hlS : (l : bk.S) ∈ nonZeroDivisors bk.S` using `(GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1`. Establish `hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀)` using `GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc l K bk τ hτ`. Establish `hφE : IsUnit (bk.iS (frobS l bk.a bk.E))`. Establish `h` using `(GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map i`.

Rewrite `h` using `[hi.ext]`. Conclude with `h`. Establish `hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀)` using `isUnit_l_disc l (bk.ev X) bk.ρ₀`. Establish `hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a` using `hi.ext`. Establish `hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a)` using `hΦA.ext`.

Establish `hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a)` using `fun a => by`. Simplify using `only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]`. Establish `hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)` using `mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul`. Establish `hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M'` using `fun M M' h => by`. Use extensionality with `a b`.

Conclude with `hinj (congrFun (congrFun h a) b)`. Apply `hmapinj` to reduce the goal to its premises. Establish `hcomm' : ∀ z, i (Φ z) = ΦA (i z)` using `RingHom.congr_fun hcomm`. Simplify using `only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow, map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]`. Use `set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def`.

Use `set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def`. Use `set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def`. Use `set XA := s.X.map bk.iS with hXA`. Use `set X'A := s.X'.map bk.iS with hX'A`. Use `set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA`.

Use `set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A`. Use `set FA := s.F.map (bk.iS.comp C) with hFA`. Use `set AA := ht.A.map bk.iS with hAA`. Use `set Zi := ht.Z.map i with hZi`. Use `set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ`.

Use `set YA := ht.Y.map bk.iA with hYA`. Establish `hW : s.W * Zi = YA` using `ht.W_mul i hi`. Establish `hZΦ' : ZΦ = Zi.map ΦA` using `by rw [hZΦ, hZi, Matrix.map_map]; rfl`. Establish `hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA` using `by rw [hZΦ', ← Matrix.map_mul, hW]`. Establish `hP : e ^ ht.a • YA.map ΦA = YA * AA`.

Establish `h` using `congrArg (fun M => M.map bk.iA) ht.φ`. Simplify using `only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h`. Establish `e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius)`. Rewrite using `[hYA, Matrix.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Conclude with `hΦiA x`. Rewrite using `[e1]`. Rewrite `h` using `[map_pow]`. Conclude with `h`.

Establish `hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA)`. Establish `h` using `s.φ ΦA hΦA`. Rewrite `h` using `[Matrix.map_mul]`. Establish `e1 : (s.X'.map bk.iS).map ΦA = φX'A`. Rewrite using `[Matrix.map_map, hφX'A]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `hΦiS x`. Rewrite `h` using `[e1]`. Simplify `h` using `only [map_natCast, map_pow]`.

Establish `hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Establish `h` using `congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX`. Simplify using `only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at h`. Conclude with `h`. Establish `hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`.

Establish `h` using `congrArg (fun M => M.map bk.iS) s.X_mul`. Simplify using `only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at h`. Conclude with `h`. Establish `hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA`. Apply `((hφE.pow s.N).smul_left_cancel).1` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hS, Matrix.smul_mul]`.

Establish `hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0`. Rewrite using `[Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ, smul_comm, ← Matrix.smul_mul, hQ]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hD'` using `eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD`. Rewrite `hD'` using `[sub_eq_zero]`.

Establish `hX` using `congrArg (fun M => XA * M) hD'`. Simplify using `only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX`. Establish `G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ))`. Apply `((hL.pow s.c₂).smul_left_cancel).1` to reduce the goal to its premises. Rewrite using `[smul_smul, smul_smul]`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring`. Conclude with `G`.
-/
theorem Height.bas_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  intro l _ K bk d ρ τ s ht hτ Φ hΦ
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := by
    unfold BK.ρ₀
    exact NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hρ1 : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    apply NNReal.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · have : (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith
  have hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ
  have hXl : frobS l bk.a (X : bk.S) = X ^ l := by
    simp [frobS]
  have hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [← bk.ev_frob, hXl, map_pow]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def
  have hi : IsDiscMap bk.ev i := isDiscMap_map _ _
  set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def
  have hΦA : IsDiscMap WittVector.frobenius ΦA := isDiscMap_map _ _
  have hcomm : i.comp Φ = ΦA.comp i := by
    have h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (i.comp Φ) :=
      ⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩
    have h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (ΦA.comp i) := by
      have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
        RingHom.ext bk.ev_frob
      rw [e]
      exact ⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩
    exact h1.unique h2
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective i := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi
  have hlS : (l : bk.S) ∈ nonZeroDivisors bk.S :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1
  have hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc l K bk τ hτ
  have hφE : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map i
    rw [hi.ext] at h; exact h
  have hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a := hi.ext
  have hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a) := hΦA.ext
  have hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a) := fun a => by
    simp only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]
  have hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
    mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul

  have hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M' := fun M M' h => by
    ext a b; exact hinj (congrFun (congrFun h a) b)
  apply hmapinj
  have hcomm' : ∀ z, i (Φ z) = ΦA (i z) := RingHom.congr_fun hcomm
  simp only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow,
    map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]

  set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def
  set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def
  set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def
  set XA := s.X.map bk.iS with hXA
  set X'A := s.X'.map bk.iS with hX'A
  set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA
  set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A
  set FA := s.F.map (bk.iS.comp C) with hFA
  set AA := ht.A.map bk.iS with hAA
  set Zi := ht.Z.map i with hZi
  set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ
  set YA := ht.Y.map bk.iA with hYA
  have hW : s.W * Zi = YA := ht.W_mul i hi
  have hZΦ' : ZΦ = Zi.map ΦA := by rw [hZΦ, hZi, Matrix.map_map]; rfl
  have hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA := by rw [hZΦ', ← Matrix.map_mul, hW]
  have hP : e ^ ht.a • YA.map ΦA = YA * AA := by
    have h := congrArg (fun M => M.map bk.iA) ht.φ
    simp only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h
    have e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius) := by
      rw [hYA, Matrix.map_map]; congr 1; funext x; exact hΦiA x
    rw [e1]; rw [map_pow] at h; exact h
  have hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA) := by
    have h := s.φ ΦA hΦA
    rw [Matrix.map_mul] at h
    have e1 : (s.X'.map bk.iS).map ΦA = φX'A := by
      rw [Matrix.map_map, hφX'A]; congr 1; funext x; exact hΦiS x
    rw [e1] at h
    simpa only [map_natCast, map_pow] using h
  have hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map bk.iS) s.X_mul
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA := by
    apply ((hφE.pow s.N).smul_left_cancel).1
    calc φe ^ s.N • (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA
        = (L ^ s.c₁ • (s.W.map ΦA * φX'A)) * φXA := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
          congr 1; ring
      _ = _ := by rw [hS, Matrix.smul_mul]
  have hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0 := by
    rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ,
      smul_comm, ← Matrix.smul_mul, hQ]
    simp only [Matrix.mul_assoc]
  have hD' := eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD
  rw [sub_eq_zero] at hD'
  have hX := congrArg (fun M => XA * M) hD'
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX
  have G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ)) := by
    apply ((hL.pow s.c₂).smul_left_cancel).1
    rw [smul_smul, smul_smul]
    calc (L ^ s.c₂ * (L ^ s.c₁ * φe ^ s.N)) • (XA * Zi * AA) = (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (XA * Zi * AA) := by
          congr 1; ring
      _ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring
  exact G

end GlobalTheory.BSP
