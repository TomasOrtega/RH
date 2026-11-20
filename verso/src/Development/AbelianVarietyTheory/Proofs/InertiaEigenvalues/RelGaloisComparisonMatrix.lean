import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.GalD

/- English proof (translation)
Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h1`. Conclude with `(mul_cancel_left_mem_nonZeroDivisors hc).1 h1`.
-/
theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {c : R} (hc : c ∈ nonZeroDivisors R)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 h1

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

/- English proof (translation)
Establish `hdet : X.det ∈ nonZeroDivisors R`. Establish `h4` using `congrArg Matrix.det h`. Rewrite `h4` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Establish `h5 : X.det * X'.det ∈ nonZeroDivisors R` using `h4 ▸ pow_mem hc _`. Conclude with `(mul_mem_nonZeroDivisors.1 h5).1`.

Establish `h2 : X * (X' * X - c • (1 : Matrix n n R)) = 0`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, sub_self]`. Establish `h3 : X.det • (X' * X - c • (1 : Matrix n n R)) = 0`. Rewrite using `[← Matrix.one_mul (X' * X - c • (1 : Matrix n n R)), ← smul_mul_assoc, ← Matrix.adjugate_mul, Matrix.mul_assoc, h2, Matrix.mul_zero]`. Rewrite `h3` using `[← smul_zero X.det]`.

Conclude with `sub_eq_zero.1 (smul_cancel hdet h3)`.
-/
theorem mul_eq_smul_comm {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    {X X' : Matrix n n R} {c : R} (hc : c ∈ nonZeroDivisors R) (h : X * X' = c • (1 : Matrix n n R)) :
    X' * X = c • (1 : Matrix n n R) := by
  have hdet : X.det ∈ nonZeroDivisors R := by
    have h4 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    have h5 : X.det * X'.det ∈ nonZeroDivisors R := h4 ▸ pow_mem hc _
    exact (mul_mem_nonZeroDivisors.1 h5).1
  have h2 : X * (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one,
      sub_self]
  have h3 : X.det • (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [← Matrix.one_mul (X' * X - c • (1 : Matrix n n R)), ← smul_mul_assoc, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h2, Matrix.mul_zero]
  rw [← smul_zero X.det] at h3
  exact sub_eq_zero.1 (smul_cancel hdet h3)

/- English proof (translation)
Use `smul_cancel hc ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_smul_comm, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (e ^ N * (e * t) ^ N) • (P * (UG * Bg)) := by rw [hYG]`. Use `_ = e ^ N • (((e * t) ^ N • (P * UG)) * Bg) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]`. Use `_ = e ^ N • (((ge * gt) ^ N • U) * Bg) := by rw [hgal]`. Use `_ = (ge * gt) ^ N • (U * (e ^ N • Bg)) := by`. Rewrite using `[smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm]`.

Use `_ = (ge * gt) ^ N • (U * (ge ^ N • (Bi * ε))) := by rw [hR]`. Use `_ = ((ge * gt) ^ N * ge ^ N) • ((U * Bi) * ε) := by rw [mul_smul_comm, smul_smul, Matrix.mul_assoc]`. Use `_ = ((ge * gt) ^ N * ge ^ N) • (((L * e ^ (2 * N)) • Ya) * ε) := by rw [hY]`. Use `_ = (L * ge ^ (2 * N) * e ^ (2 * N)) • (gt ^ N • (Ya * ε)) := by`. Rewrite using `[smul_mul_assoc, smul_smul, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key {R : Type} [CommRing R] {n : Type} [Fintype n] {P YG Ya U UG Bi Bg ε : Matrix n n R}
    {L e ge t gt : R} {N : ℕ} (hc : L * ge ^ (2 * N) * e ^ (2 * N) ∈ nonZeroDivisors R)
    (hY : U * Bi = (L * e ^ (2 * N)) • Ya) (hYG : UG * Bg = (L * ge ^ (2 * N)) • YG)
    (hgal : (e * t) ^ N • (P * UG) = (ge * gt) ^ N • U) (hR : ge ^ N • (Bi * ε) = e ^ N • Bg) :
    t ^ N • (P * YG) = gt ^ N • (Ya * ε) := by
  refine smul_cancel hc ?_
  calc (L * ge ^ (2 * N) * e ^ (2 * N)) • (t ^ N • (P * YG))
      = (e ^ N * (e * t) ^ N) • (P * ((L * ge ^ (2 * N)) • YG)) := by
        rw [smul_smul, mul_smul_comm, smul_smul]; congr 1; ring
    _ = (e ^ N * (e * t) ^ N) • (P * (UG * Bg)) := by rw [hYG]
    _ = e ^ N • (((e * t) ^ N • (P * UG)) * Bg) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]
    _ = e ^ N • (((ge * gt) ^ N • U) * Bg) := by rw [hgal]
    _ = (ge * gt) ^ N • (U * (e ^ N • Bg)) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm]
    _ = (ge * gt) ^ N • (U * (ge ^ N • (Bi * ε))) := by rw [hR]
    _ = ((ge * gt) ^ N * ge ^ N) • ((U * Bi) * ε) := by rw [mul_smul_comm, smul_smul, Matrix.mul_assoc]
    _ = ((ge * gt) ^ N * ge ^ N) • (((L * e ^ (2 * N)) • Ya) * ε) := by rw [hY]
    _ = (L * ge ^ (2 * N) * e ^ (2 * N)) • (gt ^ N • (Ya * ε)) := by
        rw [smul_mul_assoc, smul_smul, smul_smul]; congr 1; ring

end GlobalTheory.BSP.GalD

open GlobalTheory.BSP.GalD in

/- English proof (translation)
Introduce `l _ K bk d ρ τ s ht _hτ g ε hrel`. Establish `hl0 : (0 : ℝ≥0) < l` using `Nat.cast_pos.2 (Fact.out : l.Prime).pos`. Establish `hρ : (0 : ℝ≥0) < bk.ρ₀` using `NNReal.rpow_pos hl0`. Establish `h0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀`. Simplify using `using norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ`.

Establish `h1 : ‖toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev X))‖ ≤ bk.ρ₀` using `(GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).1`. Use `set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev h0 with hi_def`. Use `set G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (Per.σA (g : GQ l)) h1 with hG_def`. Establish `hi : IsDiscMap bk.ev i` using `isDiscMap_map _ _`. Establish `hG : IsDiscMap (Per.σA (g : GQ l)) G` using `isDiscMap_map _ _`.

Establish `hFg : IsDiscMap (BK.hf ((ainfHom K g).comp bk.ι)) (G.comp i)` using `⟨fun a => by`. Express the relevant statement in the definitionally equal form `G (i (toDisc l X bk.ρ₀ a)) = toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev a))`. Rewrite using `[hi.ext, hG.ext], fun x => (hG.norm_le _).trans (hi.norm_le x)⟩`. Establish `hR : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ s.N • (ht.bas.map i * ε) = bk.iA (bk.ev bk.E) ^ s.N • ht.bas.map (G.comp i)` using `hrel i (G.comp i) hi hFg`. Establish `hGA : ∀ a, G (bk.iA a) = bk.iA (Per.σA (g : GQ l) a)` using `hG.ext`.

Establish `hbi : ht.bas.map i = s.X.map bk.iS * ht.Z.map i`. Rewrite using `[Height.bas, Matrix.map_mul, Matrix.map_map]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `hi.ext _`.

Establish `hbg : ht.bas.map (G.comp i) = (s.X.map bk.iS).map G * (ht.Z.map i).map G`. Rewrite using `[← Matrix.map_mul, ← hbi, Matrix.map_map]`. Both sides reduce to the same expression. Take `⟨ιb, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `he : bk.iA (bk.ev bk.E) ∈ nonZeroDivisors (bk.DA bk.ρ₀)` using `(GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ιb tb).2.1`.

Establish `hL : ((l : bk.DA bk.ρ₀) ^ s.c₂) ∈ nonZeroDivisors (bk.DA bk.ρ₀)` using `((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow _).mem_nonZeroDivisors`. Take `⟨w, hw⟩` from `(GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).2.1`. Establish `hw' : bk.ev bk.E * (show Ainf l from (w : (ainfObj K).A)) = Per.σA (g : GQ l) (bk.ev bk.E)` using `hw`. Establish `hwu : IsUnit (bk.iA (show Ainf l from (w : (ainfObj K).A)))` using `w.isUnit.map bk.iA`. Establish `hge : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ∈ nonZeroDivisors (bk.DA bk.ρ₀)`.

Rewrite using `[← hw', map_mul]`. Conclude with `mul_mem he hwu.mem_nonZeroDivisors`. Establish `hXX1 : s.X.map bk.iS * s.X'.map bk.iS = ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Rewrite using `[← Matrix.map_mul, s.X_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using `only [map_mul, map_pow, map_natCast]`.

Establish `hXX` using `mul_eq_smul_comm (mul_mem hL (pow_mem he _)) hXX1`. Use `set U := s.W * s.X'.map bk.iS with hU`. Establish `hY : U * (s.X.map bk.iS * ht.Z.map i) = ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (bk.ev bk.E) ^ (2 * s.N)) • ht.Y.map bk.iA`. Rewrite using `[hU, Matrix.mul_assoc, ← Matrix.mul_assoc (s.X'.map bk.iS), hXX, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, ht.W_mul i hi]`. Establish `hYG : U.map G * ((s.X.map bk.iS).map G * (ht.Z.map i).map G) = ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ (2 * s.N)) • (ht.Y.map bk.iA).map G`.

Use `congrArg (fun M => Matrix.map M G) hY` as an intermediate fact. Simplify using `only [Matrix.map_mul, map_smul_hom] at this`. Rewrite using `[this, map_mul, map_pow, map_pow, map_natCast, hGA]`. Establish `hgal` using `s.gal g G hG`. Rewrite `hgal` using `[← hU, map_mul, map_mul]`.

Establish `hgoal : (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (ht.Y.map bk.iA).map G`. Rewrite using `[Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `(hGA _).symm`.

Rewrite using `[hgoal]`. Rewrite `hR` using `[hbg]`. Rewrite `hR` using `[hbi]`. Simplify using `only [map_mul] at hgal`. Conclude with `key (mul_mem (mul_mem hL (pow_mem hge _)) (pow_mem he _)) hY hYG hgal hR`.
-/
theorem GlobalTheory.BSP.Height.rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  intro l _ K bk d ρ τ s ht _hτ g ε hrel
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := NNReal.rpow_pos hl0
  have h0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  have h1 : ‖toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).1
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev h0 with hi_def
  set G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (Per.σA (g : GQ l)) h1 with hG_def
  have hi : IsDiscMap bk.ev i := isDiscMap_map _ _
  have hG : IsDiscMap (Per.σA (g : GQ l)) G := isDiscMap_map _ _
  have hFg : IsDiscMap (BK.hf ((ainfHom K g).comp bk.ι)) (G.comp i) :=
    ⟨fun a => by
      change G (i (toDisc l X bk.ρ₀ a)) = toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev a))
      rw [hi.ext, hG.ext], fun x => (hG.norm_le _).trans (hi.norm_le x)⟩
  have hR : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ s.N • (ht.bas.map i * ε) =
      bk.iA (bk.ev bk.E) ^ s.N • ht.bas.map (G.comp i) := hrel i (G.comp i) hi hFg
  have hGA : ∀ a, G (bk.iA a) = bk.iA (Per.σA (g : GQ l) a) := hG.ext

  have hbi : ht.bas.map i = s.X.map bk.iS * ht.Z.map i := by
    rw [Height.bas, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  have hbg : ht.bas.map (G.comp i) = (s.X.map bk.iS).map G * (ht.Z.map i).map G := by
    rw [← Matrix.map_mul, ← hbi, Matrix.map_map]; rfl

  obtain ⟨ιb, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have he : bk.iA (bk.ev bk.E) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ιb tb).2.1
  have hL : ((l : bk.DA bk.ρ₀) ^ s.c₂) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow _).mem_nonZeroDivisors
  obtain ⟨w, hw⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).2.1
  have hw' : bk.ev bk.E * (show Ainf l from (w : (ainfObj K).A)) = Per.σA (g : GQ l) (bk.ev bk.E) := hw
  have hwu : IsUnit (bk.iA (show Ainf l from (w : (ainfObj K).A))) := w.isUnit.map bk.iA
  have hge : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
    rw [← hw', map_mul]
    exact mul_mem he hwu.mem_nonZeroDivisors

  have hXX1 : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hXX := mul_eq_smul_comm (mul_mem hL (pow_mem he _)) hXX1
  set U := s.W * s.X'.map bk.iS with hU
  have hY : U * (s.X.map bk.iS * ht.Z.map i) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (bk.ev bk.E) ^ (2 * s.N)) • ht.Y.map bk.iA := by
    rw [hU, Matrix.mul_assoc, ← Matrix.mul_assoc (s.X'.map bk.iS), hXX, smul_mul_assoc, Matrix.one_mul,
      mul_smul_comm, ht.W_mul i hi]
  have hYG : U.map G * ((s.X.map bk.iS).map G * (ht.Z.map i).map G) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ (2 * s.N)) •
        (ht.Y.map bk.iA).map G := by
    have := congrArg (fun M => Matrix.map M G) hY
    simp only [Matrix.map_mul, map_smul_hom] at this
    rw [this, map_mul, map_pow, map_pow, map_natCast, hGA]
  have hgal := s.gal g G hG
  rw [← hU, map_mul, map_mul] at hgal
  have hgoal : (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) =
      (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (ht.Y.map bk.iA).map G := by
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
    congr 1
    ext a b
    exact (hGA _).symm
  rw [hgoal]
  rw [hbg] at hR
  rw [hbi] at hR
  simp only [map_mul] at hgal
  exact key (mul_mem (mul_mem hL (pow_mem hge _)) (pow_mem he _)) hY hYG hgal hR
