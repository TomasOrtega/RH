import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Poly

variable {K : Type} [Field K]

/- English proof (translation)
Use `first`. Consider the case `(simp [dualPoly]; done)`. Consider the case `rw [dualPoly, ← C_1, reverse_C, C_comp, leadingCoeff_C, inv_one, C_1, one_mul]`.
-/
theorem dualPoly_one (s : K) : dualPoly s (1 : K[X]) = 1 := by
  first
    | (simp [dualPoly]; done)
    | rw [dualPoly, ← C_1, reverse_C, C_comp, leadingCoeff_C, inv_one, C_1, one_mul]

/- English proof (translation)
Simplify using `only [dualPoly, leadingCoeff_mul, reverse_mul_of_domain, mul_comp, mul_inv, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualPoly_mul (s : K) (R S : K[X]) : dualPoly s (R * S) = dualPoly s R * dualPoly s S := by
  simp only [dualPoly, leadingCoeff_mul, reverse_mul_of_domain, mul_comp, mul_inv, C_mul]
  ring

def dualPolyHom (s : K) : K[X] →* K[X] where
  toFun := dualPoly s
  map_one' := dualPoly_one s
  map_mul' := dualPoly_mul s

/- English proof (translation)
Rewrite using `[dualPoly, coeff_C_mul, comp_C_mul_X_coeff, coeff_reverse]`.
-/
private theorem coeff_dualPoly' (s : K) (R : K[X]) (i : ℕ) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (revAt R.natDegree i) * s ^ i) := by
  rw [dualPoly, coeff_C_mul, comp_C_mul_X_coeff, coeff_reverse]

end Poly

/- English proof (translation)
Introduce `K _ _ _ G _ _ Pl0 B ℓ Z w`. Unfold `BlockDat.etaU BlockDat.etaW`. Rewrite using `[Col.lenUW_mul_eW, Col.lenW_toNat]`.
-/
theorem eta_units : EtaUnits := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w
  unfold BlockDat.etaU BlockDat.etaW
  rw [Col.lenUW_mul_eW, Col.lenW_toNat]

/- English proof (translation)
Establish `htop` using `Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B hB.span_eq_top`. Take `⟨δ, hδ, hδA⟩` from `Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors (𝓞 K)) A B hA.fg (by rw [htop]; exact le_top)`. Establish `hδ0 : δ ≠ 0` using `nonZeroDivisors.ne_zero hδ`. Establish `hI : Ideal.span {δ} ≠ (0 : Ideal (𝓞 K))`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hδ0`. Establish `hwu : ¬ IsUnit w.asIdeal`. Rewrite using `[Ideal.isUnit_iff]`. Conclude with `w.isPrime.ne_top`. Establish `hfin : FiniteMultiplicity w.asIdeal (Ideal.span {δ})` using `FiniteMultiplicity.of_not_isUnit hwu hI`.

Take `⟨c, hc, hnd⟩` from `hfin.exists_eq_pow_mul_and_not_dvd`. Establish `hcw : ¬ c ≤ w.asIdeal` using `fun h => hnd (Ideal.dvd_iff_le.2 h)`. Take `⟨s, hsc, hsw⟩` from `SetLike.not_le_iff_exists.1 hcw`. Use `⟨multiplicity w.asIdeal (Ideal.span {δ}), ?_⟩` and prove the remaining obligations. Introduce `a ha z hz`.

Use `⟨s, hsw, ?_⟩` and prove the remaining obligations. Establish `hmem : a * s ∈ Ideal.span {δ}`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_mul ha hsc`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Establish `: s • a • z = e • (δ • z)`. Rewrite using `[smul_smul, smul_smul, mul_comm s a, he]`. Rewrite using `[this]`. Conclude with `B.smul_mem e (hδA z hz)`.
-/
theorem expW_nonempty {K : Type} [Field K] [NumberField K] {d : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    {J : ℕ | ∀ a ∈ w.asIdeal ^ J, ∀ z ∈ A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B}.Nonempty := by
  have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B hB.span_eq_top
  obtain ⟨δ, hδ, hδA⟩ := Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors (𝓞 K)) A B hA.fg
    (by rw [htop]; exact le_top)
  have hδ0 : δ ≠ 0 := nonZeroDivisors.ne_zero hδ
  have hI : Ideal.span {δ} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hδ0
  have hwu : ¬ IsUnit w.asIdeal := by
    rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {δ}) := FiniteMultiplicity.of_not_isUnit hwu hI
  obtain ⟨c, hc, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hcw : ¬ c ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨s, hsc, hsw⟩ := SetLike.not_le_iff_exists.1 hcw
  refine ⟨multiplicity w.asIdeal (Ideal.span {δ}), ?_⟩
  intro a ha z hz
  refine ⟨s, hsw, ?_⟩
  have hmem : a * s ∈ Ideal.span {δ} := by
    rw [hc]; exact Ideal.mul_mem_mul ha hsc
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hmem
  have : s • a • z = e • (δ • z) := by
    rw [smul_smul, smul_smul, mul_comm s a, he]
  rw [this]
  exact B.smul_mem e (hδA z hz)

/- English proof (translation)
Unfold `ExpWSpec`. Introduce `K _ _ d w A B hA hB`. Use `⟨?_, fun J hJ => ?_⟩` and prove the remaining obligations. Conclude with `Nat.sInf_mem (expW_nonempty w A B hA hB)`. Conclude with `Nat.sInf_le hJ`.
-/
theorem exponent_weight_spectral : ExpWSpec := by
  unfold ExpWSpec
  intro K _ _ d w A B hA hB
  refine ⟨?_, fun J hJ => ?_⟩
  · exact Nat.sInf_mem (expW_nonempty w A B hA hB)
  · exact Nat.sInf_le hJ

section Alg

variable {K : Type} [Field K] [StarRing K] {n a b d : ℕ}

/- English proof (translation)
Establish `e1 : Vᴴ * H = Vᴴ * H * V * Vp`. Establish `h` using `b2`. Rewrite `h` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Rewrite using `[Matrix.mul_assoc (Vᴴ * H) V Vp]`. Conclude with `h`.

Establish `c2' : Zᴴ * (Vᴴ * H * V) * (1 - Z * Q) = 0`. Establish `h : c • (Zᴴ * (Vᴴ * H * V) * (1 - Z * Q)) = 0`. Rewrite using `[← c2, Matrix.mul_smul, Matrix.smul_mul]`. Establish `h'` using `congrArg (fun M => c⁻¹ • M) h`. Simplify `h'` using `[smul_smul, inv_mul_cancel₀ hc]`.

Establish `e2 : Zᴴ * (Vᴴ * H * V) = Zᴴ * (Vᴴ * H * V) * Z * Q`. Establish `h` using `c2'`. Rewrite `h` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Rewrite using `[Matrix.mul_assoc (Zᴴ * (Vᴴ * H * V)) Z Q]`. Conclude with `h`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem orthogonal_tower_projection (H : Matrix (Fin n) (Fin n) K) (V : Matrix (Fin n) (Fin b) K) (Vp : Matrix (Fin b) (Fin n) K)
    (Z : Matrix (Fin b) (Fin d) K) (Q : Matrix (Fin d) (Fin b) K) (c : K) (hc : c ≠ 0)
    (b2 : Vᴴ * H * (1 - V * Vp) = 0) (c2 : Zᴴ * (c • (Vᴴ * H * V)) * (1 - Z * Q) = 0) :
    (V * Z)ᴴ * H * (1 - V * Z * Q * Vp) = 0 := by
  have e1 : Vᴴ * H = Vᴴ * H * V * Vp := by
    have h := b2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    rw [Matrix.mul_assoc (Vᴴ * H) V Vp]
    exact h
  have c2' : Zᴴ * (Vᴴ * H * V) * (1 - Z * Q) = 0 := by
    have h : c • (Zᴴ * (Vᴴ * H * V) * (1 - Z * Q)) = 0 := by
      rw [← c2, Matrix.mul_smul, Matrix.smul_mul]
    have h' := congrArg (fun M => c⁻¹ • M) h
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  have e2 : Zᴴ * (Vᴴ * H * V) = Zᴴ * (Vᴴ * H * V) * Z * Q := by
    have h := c2'
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    rw [Matrix.mul_assoc (Zᴴ * (Vᴴ * H * V)) Z Q]
    exact h
  rw [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  calc Zᴴ * Vᴴ * H = Zᴴ * (Vᴴ * H) := Matrix.mul_assoc _ _ _
    _ = Zᴴ * (Vᴴ * H * V * Vp) := by rw [← e1]
    _ = Zᴴ * (Vᴴ * H * V) * Vp := by simp only [Matrix.mul_assoc]
    _ = Zᴴ * (Vᴴ * H * V) * Z * Q * Vp := by rw [← e2]
    _ = Zᴴ * Vᴴ * H * (V * Z * Q * Vp) := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hW : L * (Lp * V) = V` using `by rw [← Matrix.mul_assoc]; exact hd`. Establish `h1 : (Lp * V)ᴴ * (Lᴴ * H * L) = Vᴴ * H * L` using `by conv_rhs => rw [← hW]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `e1 : Vᴴ * H * (V * Vp) = Vᴴ * H`. Establish `h` using `b2`.

Rewrite `h` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Conclude with `h.symm`. Establish `hb : (Lp * V)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * (Vp * L)) = 0`. Rewrite using `[h1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : (Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V) = Vᴴ * H * V`. Rewrite using `[h1, Matrix.mul_assoc (Vᴴ * H) L (Lp * V), hW]`. Establish `hc2 : Zᴴ * (c • ((Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V))) * (1 - Z * Q) = 0`. Rewrite using `[h2]`. Conclude with `c2`.

Establish `key` using `orthogonal_tower_projection (Lᴴ * H * L) (Lp * V) (Vp * L) Z Q c hc hb hc2`. Establish `e : (Lp * (V * Z))ᴴ * (c • (Lᴴ * H * L)) * (1 - Lp * (V * Z) * (Q * Vp * L)) = c • ((Lp * V * Z)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * Z * Q * (Vp * L)))`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, key, smul_zero]`.
-/
theorem lf_orth_tower (H : Matrix (Fin n) (Fin n) K) (L : Matrix (Fin n) (Fin a) K) (Lp : Matrix (Fin a) (Fin n) K)
    (V : Matrix (Fin n) (Fin b) K) (Vp : Matrix (Fin b) (Fin n) K)
    (Z : Matrix (Fin b) (Fin d) K) (Q : Matrix (Fin d) (Fin b) K) (c : K) (hc : c ≠ 0)
    (b2 : Vᴴ * H * (1 - V * Vp) = 0) (c2 : Zᴴ * (c • (Vᴴ * H * V)) * (1 - Z * Q) = 0)
    (hd : L * Lp * V = V) :
    (Lp * (V * Z))ᴴ * (c • (Lᴴ * H * L)) * (1 - (Lp * (V * Z)) * (Q * Vp * L)) = 0 := by
  have hW : L * (Lp * V) = V := by rw [← Matrix.mul_assoc]; exact hd
  have h1 : (Lp * V)ᴴ * (Lᴴ * H * L) = Vᴴ * H * L := by
    conv_rhs => rw [← hW]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e1 : Vᴴ * H * (V * Vp) = Vᴴ * H := by
    have h := b2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have hb : (Lp * V)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * (Vp * L)) = 0 := by
    rw [h1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
    calc Vᴴ * H * L = Vᴴ * H * (V * Vp) * L := by rw [e1]
      _ = Vᴴ * H * (L * (Lp * V)) * Vp * L := by rw [hW, Matrix.mul_assoc (Vᴴ * H) V Vp]
      _ = Vᴴ * H * L * (Lp * V * (Vp * L)) := by simp only [Matrix.mul_assoc]
  have h2 : (Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V) = Vᴴ * H * V := by
    rw [h1, Matrix.mul_assoc (Vᴴ * H) L (Lp * V), hW]
  have hc2 : Zᴴ * (c • ((Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V))) * (1 - Z * Q) = 0 := by
    rw [h2]; exact c2
  have key := orthogonal_tower_projection (Lᴴ * H * L) (Lp * V) (Vp * L) Z Q c hc hb hc2
  have e : (Lp * (V * Z))ᴴ * (c • (Lᴴ * H * L)) * (1 - Lp * (V * Z) * (Q * Vp * L)) =
      c • ((Lp * V * Z)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * Z * Q * (Vp * L))) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  rw [e, key, smul_zero]

end Alg

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
Establish `hP` using `(level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1`. Conclude with `orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hP.idem hP.selfAdj`.
-/
theorem lf_lvl_proj (h : BlockHyp B ℓ v0 s) :
    IsOrthProj B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) (B.S.lvlPr B.r ℓ.P ℓ.ψ) ∧
      B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ = B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  exact orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hP.idem hP.selfAdj

/- English proof (translation)
Establish `hg` using `good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ`. Conclude with `orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hg.idem hg.selfAdj`.
-/
theorem lf_v_proj (h : BlockHyp B ℓ v0 s) :
    IsOrthProj B.S.H (B.vE ℓ) (B.vPr ℓ) ∧ B.vE ℓ * B.vPr ℓ = B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := by
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  exact orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hg.idem hg.selfAdj

/- English proof (translation)
Establish `hP` using `(level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1`. Establish `hc` using `(idempotent_spec K v0 h.conj G ℓ.X h.irr).2`. Unfold `goodAt`. Rewrite using `[← mul_assoc, hc, mul_assoc, hP.idem]`.
-/
theorem lf_lvl_mul_good (h : BlockHyp B ℓ v0 s) :
    lvlIdem ℓ.P ℓ.ψ * goodAt ℓ.X ℓ.P ℓ.ψ = goodAt ℓ.X ℓ.P ℓ.ψ := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2
  unfold goodAt
  rw [← mul_assoc, hc, mul_assoc, hP.idem]

/- English proof (translation)
Take `⟨⟨h1, -⟩, h2⟩` from `lf_v_proj h`. Establish `h3` using `(group_action_matrix_hom K B.S G B.r).2 (lvlIdem ℓ.P ℓ.ψ) (goodAt ℓ.X ℓ.P ℓ.ψ)`. Rewrite `h3` using `[lf_lvl_mul_good h]`. Rewrite using `[(lf_lvl_proj h).2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lf_lvl_vE (h : BlockHyp B ℓ v0 s) :
    B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  obtain ⟨⟨h1, -⟩, h2⟩ := lf_v_proj h
  have h3 := (group_action_matrix_hom K B.S G B.r).2 (lvlIdem ℓ.P ℓ.ψ) (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [lf_lvl_mul_good h] at h3
  rw [(lf_lvl_proj h).2]
  calc B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * B.vE ℓ
      = B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * (B.vE ℓ * (B.vPr ℓ * B.vE ℓ)) := by rw [h1, Matrix.mul_one]
    _ = (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * (B.vE ℓ * B.vPr ℓ)) * B.vE ℓ := by simp only [Matrix.mul_assoc]
    _ = B.vE ℓ * B.vPr ℓ * B.vE ℓ := by rw [h2, ← h3]
    _ = B.vE ℓ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_HV_eq : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_lvlH_eq : B.S.lvlH B.r ℓ.P ℓ.ψ =
    (Nat.card ℓ.P : K)⁻¹ • ((B.S.lvlE B.r ℓ.P ℓ.ψ)ᴴ * B.S.H * B.S.lvlE B.r ℓ.P ℓ.ψ) := rfl

/- English proof (translation)
The claim follows from `inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`.
-/
theorem lf_card_inv_ne : ((Nat.card ℓ.P : K)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/- English proof (translation)
The claim follows from `(good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ).2.2 v`.
-/
theorem lf_HV_pos (h : BlockHyp B ℓ v0 s) (v : InfinitePlace K) : ((B.HV ℓ).map v.embedding).PosDef :=
  (good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ).2.2 v

/- English proof (translation)
The claim follows from `(subspace_image_spec K _ (B.Z0 ℓ Z)).1`.
-/
theorem lf_zE_inj : Function.Injective (B.zE ℓ Z).mulVec := (subspace_image_spec K _ (B.Z0 ℓ Z)).1

/- English proof (translation)
The claim follows from `(image_idempotent_spec K _ _).1`.
-/
theorem lf_vE_inj : Function.Injective (B.vE ℓ).mulVec := (image_idempotent_spec K _ _).1

/- English proof (translation)
The claim follows from `(image_idempotent_spec K _ _).1`.
-/
theorem lf_lvlE_inj : Function.Injective (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec := (image_idempotent_spec K _ _).1

/- English proof (translation)
The claim follows from `(orthogonal_projection_exists K v0 h.conj _ _ (B.HV ℓ) (lf_HV_pos h v0) (B.zE ℓ Z) lf_zE_inj).2.2.2.1`.
-/
theorem lf_z_proj (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) :=
  (orthogonal_projection_exists K v0 h.conj _ _ (B.HV ℓ) (lf_HV_pos h v0) (B.zE ℓ Z) lf_zE_inj).2.2.2.1

/- English proof (translation)
Unfold `lE fE`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, lf_lvl_vE h]`.
-/
theorem lf_lvlE_lE (h : BlockHyp B ℓ v0 s) : B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z = B.fE ℓ Z := by
  unfold lE fE
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, lf_lvl_vE h]

/- English proof (translation)
Establish `e : B.lPr ℓ Z * B.lE ℓ Z = B.Pq ℓ Z * B.vPr ℓ * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)`. Unfold `lPr`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, lf_lvlE_lE (Z := Z) h]`. Unfold `fE`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul, (lf_z_proj (Z := Z) h).1]`.
-/
theorem lf_lPr_lE (h : BlockHyp B ℓ v0 s) : B.lPr ℓ Z * B.lE ℓ Z = 1 := by
  have e : B.lPr ℓ Z * B.lE ℓ Z = B.Pq ℓ Z * B.vPr ℓ * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z) := by
    unfold lPr
    simp only [Matrix.mul_assoc]
  rw [e, lf_lvlE_lE (Z := Z) h]
  unfold fE
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul, (lf_z_proj (Z := Z) h).1]

/- English proof (translation)
Use `⟨lf_lPr_lE (Z := Z) h, ?_⟩` and prove the remaining obligations. Establish `c2` using `(lf_z_proj (Z := Z) h).2`. Rewrite `c2` using `[lf_HV_eq]`. Conclude with `lf_orth_tower B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) (B.S.lvlPr B.r ℓ.P ℓ.ψ) (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) _ lf_card_inv_ne (lf_v_proj h).1.2 c2 (lf_lvl_vE h)`.
-/
theorem lf_l_proj (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.S.lvlH B.r ℓ.P ℓ.ψ) (B.lE ℓ Z) (B.lPr ℓ Z) := by
  refine ⟨lf_lPr_lE (Z := Z) h, ?_⟩
  have c2 := (lf_z_proj (Z := Z) h).2
  rw [lf_HV_eq] at c2
  exact lf_orth_tower B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) (B.S.lvlPr B.r ℓ.P ℓ.ψ) (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ Z) (B.Pq ℓ Z)
    _ lf_card_inv_ne (lf_v_proj h).1.2 c2 (lf_lvl_vE h)

/- English proof (translation)
Establish `e : (B.lE ℓ Z)ᴴ * B.S.lvlH B.r ℓ.P ℓ.ψ * B.lE ℓ Z = (Nat.card ℓ.P : K)⁻¹ • ((B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)ᴴ * B.S.H * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z))`. Rewrite using `[lf_lvlH_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, lf_lvlE_lE (Z := Z) h]`. Unfold `HZ fE`.

Rewrite using `[lf_HV_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem lf_lE_form (h : BlockHyp B ℓ v0 s) : (B.lE ℓ Z)ᴴ * B.S.lvlH B.r ℓ.P ℓ.ψ * B.lE ℓ Z = B.HZ ℓ Z := by
  have e : (B.lE ℓ Z)ᴴ * B.S.lvlH B.r ℓ.P ℓ.ψ * B.lE ℓ Z =
      (Nat.card ℓ.P : K)⁻¹ • ((B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)ᴴ * B.S.H * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)) := by
    rw [lf_lvlH_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, lf_lvlE_lE (Z := Z) h]
  unfold HZ fE
  rw [lf_HV_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `y`. Simplify using `[cutLat, Matrix.mulVec_mulVec]`.
-/
theorem lf_cutLat_mul {n a d : ℕ} (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin a) (Fin d) K)
    (A : Submodule (𝓞 K) (Fin n → K)) : cutLat E' (cutLat E A) = cutLat (E * E') A := by
  ext y
  simp [cutLat, Matrix.mulVec_mulVec]

/- English proof (translation)
Use `show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.nabLat) = cutLat (B.fE ℓ Z) B.S.nabLat`. Rewrite using `[lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]`.
-/
theorem lf_cut_nab (h : BlockHyp B ℓ v0 s) : cutLat (B.lE ℓ Z) (B.S.lvlNab B.r ℓ.P ℓ.ψ) = B.cutZ ℓ Z := by
  show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.nabLat) = cutLat (B.fE ℓ Z) B.S.nabLat
  rw [lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]

/- English proof (translation)
Use `show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.delLat) = cutLat (B.fE ℓ Z) B.S.delLat`. Rewrite using `[lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]`.
-/
theorem lf_cut_del (h : BlockHyp B ℓ v0 s) : cutLat (B.lE ℓ Z) (B.S.lvlDel B.r ℓ.P ℓ.ψ) = B.delZ ℓ Z := by
  show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.delLat) = cutLat (B.fE ℓ Z) B.S.delLat
  rw [lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]

end BlockDat

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

/- English proof (translation)
Use `⟨(hS.nab_lat c).fg.of_le (hS.del_le c), ?_⟩` and prove the remaining obligations. Establish `hD` using `(Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K S.V S.pair hS.symm hS.nondeg exponent_index_lattice.hstar (S.Nab c) (hS.nab_lat c)).1`. Rewrite using `[eq_top_iff, ← hD.span_eq_top, Submodule.span_le]`. Introduce `y hy`. Establish `hs0 : (algebraMap (𝓞 K) K (s : 𝓞 K)) ≠ 0`.

Rewrite using `[map_natCast]`. Conclude with `hS.s_pos.ne'` after adjusting the coercions. Establish `e : y = (algebraMap (𝓞 K) K (s : 𝓞 K))⁻¹ • ((s : 𝓞 K) • y)`. Rewrite using `[← algebraMap_smul K (s : 𝓞 K) y, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hS.dual_le c y hy))`.
-/
theorem lf_del_isLattice {s : ℕ} (hS : S.Good s) (c : S.Cl) : Submodule.IsLattice K (S.Del c) := by
  refine ⟨(hS.nab_lat c).fg.of_le (hS.del_le c), ?_⟩
  have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K S.V S.pair hS.symm hS.nondeg exponent_index_lattice.hstar (S.Nab c) (hS.nab_lat c)).1
  rw [eq_top_iff, ← hD.span_eq_top, Submodule.span_le]
  intro y hy
  have hs0 : (algebraMap (𝓞 K) K (s : 𝓞 K)) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hS.s_pos.ne'
  have e : y = (algebraMap (𝓞 K) K (s : 𝓞 K))⁻¹ • ((s : 𝓞 K) • y) := by
    rw [← algebraMap_smul K (s : 𝓞 K) y, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hS.dual_le c y hy))

/- English proof (translation)
The claim follows from `ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat`.
-/
theorem lf_nabLat_isLattice {s : ℕ} (hS : S.Good s) : Submodule.IsLattice K S.nabLat :=
  ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat

/- English proof (translation)
The claim follows from `ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Del (S.lf_del_isLattice hS)`.
-/
theorem lf_delLat_isLattice {s : ℕ} (hS : S.Good s) : Submodule.IsLattice K S.delLat :=
  ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Del (S.lf_del_isLattice hS)

/- English proof (translation)
The claim follows from `ValuationLatticeField.valLatF_mono S.I hS.del_le`.
-/
theorem lf_delLat_le {s : ℕ} (hS : S.Good s) : S.delLat ≤ S.nabLat := ValuationLatticeField.valLatF_mono S.I hS.del_le

end CSD

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only [Matrix.mulVecLin_apply, fE, ← Matrix.mulVec_mulVec] at hxy`. Conclude with `lf_zE_inj (lf_vE_inj hxy)`.
-/
theorem lf_fE_inj : Function.Injective (Matrix.mulVecLin (B.fE ℓ Z)) := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply, fE, ← Matrix.mulVec_mulVec] at hxy
  exact lf_zE_inj (lf_vE_inj hxy)

/- English proof (translation)
The claim follows from `exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => lf_lvlE_inj hxy) _ (B.S.lf_nabLat_isLattice h.ok.good)`.
-/
theorem lf_lvlNab_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.S.lvlNab B.r ℓ.P ℓ.ψ) :=
  exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => lf_lvlE_inj hxy) _ (B.S.lf_nabLat_isLattice h.ok.good)

/- English proof (translation)
Introduce `y`. Use `⟨(B.lE ℓ Z).mulVec y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]`.
-/
theorem lf_lPr_surj (h : BlockHyp B ℓ v0 s) : Function.Surjective (Matrix.mulVecLin (B.lPr ℓ Z)) := by
  intro y
  refine ⟨(B.lE ℓ Z).mulVec y, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]

/- English proof (translation)
The claim follows from `exponent_index_lattice.map_isLattice _ (lf_lPr_surj (Z := Z) h) _ (lf_lvlNab_isLattice h)`.
-/
theorem lf_Tl_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.Tl ℓ Z) :=
  exponent_index_lattice.map_isLattice _ (lf_lPr_surj (Z := Z) h) _ (lf_lvlNab_isLattice h)

/- English proof (translation)
The claim follows from `exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_nabLat_isLattice h.ok.good)`.
-/
theorem lf_cutZ_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.cutZ ℓ Z) :=
  exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_nabLat_isLattice h.ok.good)

/- English proof (translation)
The claim follows from `exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_delLat_isLattice h.ok.good)`.
-/
theorem lf_delZ_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.delZ ℓ Z) :=
  exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_delLat_isLattice h.ok.good)

/- English proof (translation)
The claim follows from `Submodule.comap_mono (B.S.lf_delLat_le h.ok.good)`.
-/
theorem lf_delZ_le (h : BlockHyp B ℓ v0 s) : B.delZ ℓ Z ≤ B.cutZ ℓ Z :=
  Submodule.comap_mono (B.S.lf_delLat_le h.ok.good)

/- English proof (translation)
Introduce `z hz`. Rewrite `hz` using `[← lf_cut_nab (Z := Z) h, exponent_index_lattice.mem_cutLat]`. Use `(exponent_index_lattice.mem_matLat _ _ _).2 ⟨_, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]`.
-/
theorem lf_cutZ_le (h : BlockHyp B ℓ v0 s) : B.cutZ ℓ Z ≤ B.Tl ℓ Z := by
  intro z hz
  rw [← lf_cut_nab (Z := Z) h, exponent_index_lattice.mem_cutLat] at hz
  refine (exponent_index_lattice.mem_matLat _ _ _).2 ⟨_, hz, ?_⟩
  rw [Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]

end BlockDat

/- English proof (translation)
Introduce `K _ _ _ G _ _ Pl0 B ℓ Z v0 s h`. Conclude with `⟨BlockDat.lf_Tl_isLattice (Z := Z) h, BlockDat.lf_cutZ_isLattice (Z := Z) h, BlockDat.lf_delZ_isLattice (Z := Z) h, BlockDat.lf_delZ_le (Z := Z) h, BlockDat.lf_cutZ_le (Z := Z) h⟩`.
-/
theorem lift_lattices : LiftLattices := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h
  exact ⟨BlockDat.lf_Tl_isLattice (Z := Z) h, BlockDat.lf_cutZ_isLattice (Z := Z) h, BlockDat.lf_delZ_isLattice (Z := Z) h, BlockDat.lf_delZ_le (Z := Z) h,
    BlockDat.lf_cutZ_le (Z := Z) h⟩

section Unif

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Take `⟨ϖ, h1, h2, h3, -⟩` from `idxChange_unif (K := K) w`. Conclude with `⟨ϖ, h1, h2, h3⟩`.
-/
theorem lf_exists_unif (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ∈ w.asIdeal ∧ ϖ ≠ 0 ∧ vw w (ϖ : K) = 1 := by
  obtain ⟨ϖ, h1, h2, h3, -⟩ := idxChange_unif (K := K) w
  exact ⟨ϖ, h1, h2, h3⟩

end Unif

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
Establish `hP` using `(level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1`. Establish `hE : ∀ i j, B.S.lvlE B.r ℓ.P ℓ.ψ i j ∈ cmMax K` using `image_idempotent_rational K B.S.dim (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)) (gaMat_rat B.S B.r h.ok.actRat _ hP.rat)`. Conclude with `cut_posDef B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) lf_lvlE_inj hE (Nat.card ℓ.P) Nat.card_pos v (h.ok.hpos v)`.
-/
theorem lf_lvlH_pos (h : BlockHyp B ℓ v0 s) (v : InfinitePlace K) :
    ((B.S.lvlH B.r ℓ.P ℓ.ψ).map v.embedding).PosDef := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  have hE : ∀ i j, B.S.lvlE B.r ℓ.P ℓ.ψ i j ∈ cmMax K :=
    image_idempotent_rational K B.S.dim (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)) (gaMat_rat B.S B.r h.ok.actRat _ hP.rat)
  exact cut_posDef B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) lf_lvlE_inj hE (Nat.card ℓ.P) Nat.card_pos v (h.ok.hpos v)

/- English proof (translation)
Introduce `z hz` and use `(hE K _ w (B.cutZ ℓ Z) (B.delZ ℓ Z) (lf_cutZ_isLattice (Z := Z) h) (lf_delZ_isLattice (Z := Z) h)).1 _ (Ideal.pow_mem_pow hϖ _) z hz`.
-/
theorem lf_exp_incl (hE : ExpWSpec) (h : BlockHyp B ℓ v0 s) (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K)
    (hϖ : ϖ ∈ w.asIdeal) :
    ∀ z ∈ B.cutZ ℓ Z, (ϖ ^ B.JexpW ℓ Z w) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := fun z hz =>
  (hE K _ w (B.cutZ ℓ Z) (B.delZ ℓ Z) (lf_cutZ_isLattice (Z := Z) h) (lf_delZ_isLattice (Z := Z) h)).1 _ (Ideal.pow_mem_pow hϖ _) z hz

end BlockDat

/- English proof (translation)
Introduce `K _ _ _ G _ _ Pl0 B ℓ Z v0 s h w`. Take `⟨ϖ, hϖ, -, hv⟩` from `lf_exists_unif w`. Take `⟨hH, hdet, -⟩` from `orthogonal_projection_exists K v0 h.conj _ 0 (B.S.lvlH B.r ℓ.P ℓ.ψ) (BlockDat.lf_lvlH_pos h v0) 0 (by intro x y _; exact Subsingleton.elim _ _)`. Take `⟨hinj, hCS, hnab, hdel⟩` from `level_class_sum K B.S G B.r ℓ.P ℓ.ψ`. Establish `hJ : ∀ z ∈ cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Nab), (ϖ ^ B.JexpW ℓ Z w) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Del))`.

Rewrite using `[← hnab, ← hdel, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_cut_del (Z := Z) h]`. Conclude with `BlockDat.lf_exp_incl hE h w ϖ hϖ`. Establish `key` using `(bounds_fourth_class_fixed K _ _ (B.S.lvlH B.r ℓ.P ℓ.ψ) hH hdet (B.lE ℓ Z) (B.lPr ℓ Z) (BlockDat.lf_l_proj (Z := Z) h) B.S.Cl B.S.V B.S.pair (B.S.lvlI B.r ℓ.P ℓ.ψ) (fun c => Nat.card ℓ.P * B.S.wt c) hinj (fun c => Nat.mul_pos Nat.card_pos (B.S.wt_pos c)) hCS B.S.Nab B.S.Del h.ok. …`. Rewrite `key` using `[← hnab, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_lE_form (Z := Z) h]`. Conclude with `key`.
-/
theorem boundsIVAt_of (hE : ExpWSpec) : BoundsIVAt := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h w
  obtain ⟨ϖ, hϖ, -, hv⟩ := lf_exists_unif w
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 h.conj _ 0 (B.S.lvlH B.r ℓ.P ℓ.ψ) (BlockDat.lf_lvlH_pos h v0) 0
    (by intro x y _; exact Subsingleton.elim _ _)
  obtain ⟨hinj, hCS, hnab, hdel⟩ := level_class_sum K B.S G B.r ℓ.P ℓ.ψ
  have hJ : ∀ z ∈ cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Nab),
      (ϖ ^ B.JexpW ℓ Z w) • z ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Del)) := by
    rw [← hnab, ← hdel, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_cut_del (Z := Z) h]
    exact BlockDat.lf_exp_incl hE h w ϖ hϖ
  have key := (bounds_fourth_class_fixed K _ _ (B.S.lvlH B.r ℓ.P ℓ.ψ) hH hdet (B.lE ℓ Z) (B.lPr ℓ Z) (BlockDat.lf_l_proj (Z := Z) h)
    B.S.Cl B.S.V B.S.pair (B.S.lvlI B.r ℓ.P ℓ.ψ) (fun c => Nat.card ℓ.P * B.S.wt c) hinj
    (fun c => Nat.mul_pos Nat.card_pos (B.S.wt_pos c)) hCS B.S.Nab B.S.Del h.ok.good.nab_lat s h.ok.good.s_pos
    h.ok.good.del_dual (B.DG ℓ) (Nat.mul_pos Nat.card_pos B.S.DGam_pos)
    (fun c => Nat.mul_dvd_mul_left _ (B.S.wt_dvd_DGam c)) w ϖ (B.JexpW ℓ Z w) hv hJ).2
  rw [← hnab, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_lE_form (Z := Z) h] at key
  exact key

/- English proof (translation)
The claim follows from `boundsIVAt_of exponent_weight_spectral`.
-/
theorem local_bounds_from_exponent : BoundsIVAt := boundsIVAt_of exponent_weight_spectral

namespace CyclotomicLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
The claim follows from `good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ`.
-/
theorem hv_spec (h : BlockHyp B ℓ v0 s) :
    (∀ i j, B.vE ℓ i j ∈ cmMax K) ∧ (∀ i j, B.HV ℓ i j ∈ cmMax K) ∧
      ∀ v : InfinitePlace K, ((B.HV ℓ).map v.embedding).PosDef :=
  good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ

/- English proof (translation)
The claim follows from `BlockDat.lf_zE_inj`.
-/
theorem zE_inj : Function.Injective (B.zE ℓ Z).mulVec := BlockDat.lf_zE_inj

/- English proof (translation)
The claim follows from `BlockDat.lf_z_proj h`.
-/
theorem pq_orth (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) := BlockDat.lf_z_proj h

/- English proof (translation)
Establish `hE : ∀ i a, B.zE ℓ Z i a ∈ cmMax K` using `fun i a => subE_rat (B.Z0 ℓ Z) hr i a`. Establish `e : B.XQ ℓ Z = restrFrame (B.zE ℓ Z) (B.HV ℓ)` using `quotEqRestrRat K (cmMax K) ConjugateWeightGram.isCMSub_cmMax _ _ (B.HV ℓ) (hv_spec h).2.2 (B.zE ℓ Z) (B.Pq ℓ Z) hE (pq_orth (Z := Z) h)`. Rewrite using `[e]`. Conclude with `(restrFrameRatHerm K (cmMax K) ConjugateWeightGram.isCMSub_cmMax (fun a ha => ConjugateWeightGram.star_mem_cmMax ha) _ _ (B.HV ℓ) (hv_spec h).2.1 (hv_spec h).2.2 (B.zE ℓ Z) zE_inj hE).1`.
-/
theorem xq_rat (h : BlockHyp B ℓ v0 s) (hr : SubHasRatBasis (B.Z0 ℓ Z)) :
    IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) := by
  have hE : ∀ i a, B.zE ℓ Z i a ∈ cmMax K := fun i a => subE_rat (B.Z0 ℓ Z) hr i a
  have e : B.XQ ℓ Z = restrFrame (B.zE ℓ Z) (B.HV ℓ) :=
    quotEqRestrRat K (cmMax K) ConjugateWeightGram.isCMSub_cmMax _ _ (B.HV ℓ) (hv_spec h).2.2 (B.zE ℓ Z) (B.Pq ℓ Z) hE
      (pq_orth (Z := Z) h)
  rw [e]
  exact (restrFrameRatHerm K (cmMax K) ConjugateWeightGram.isCMSub_cmMax (fun a ha => ConjugateWeightGram.star_mem_cmMax ha) _ _ (B.HV ℓ)
    (hv_spec h).2.1 (hv_spec h).2.2 (B.zE ℓ Z) zE_inj hE).1

/- English proof (translation)
Use `first`. Consider the case `rw [Basis.equivFun_apply, Basis.equivFun_apply, BlockDat.opMat, LinearMap.toMatrix_mulVec_repr]`. Consider the case `(simp only [Basis.equivFun_apply, BlockDat.opMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)`.
-/
theorem equivFun_op (i : B.Pl × ℕ) (f : B.S.Forms) :
    B.S.basis.equivFun (B.op i f) = (B.opMat i).mulVec (B.S.basis.equivFun f) := by
  first
  | rw [Basis.equivFun_apply, Basis.equivFun_apply, BlockDat.opMat, LinearMap.toMatrix_mulVec_repr]
  | (simp only [Basis.equivFun_apply, BlockDat.opMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)

/- English proof (translation)
Rewrite using `[CSD.I_apply]`. Use `congr 1`. Use `equivFun_op (B := B) i (B.S.basis.equivFun.symm x)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[← this, LinearEquiv.symm_apply_apply]`.
-/
theorem I_opMat (i : B.Pl × ℕ) (x : Fin B.S.dim → K) :
    B.S.I ((B.opMat i).mulVec x) = (B.op i (B.S.basis.equivFun.symm x) : B.S.Cl → B.S.V) := by
  rw [CSD.I_apply]
  congr 1
  have := equivFun_op (B := B) i (B.S.basis.equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [← this, LinearEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `B.S.isClassSum x y`.
-/
theorem hform_eq_csum (x y : Fin B.S.dim → K) :
    hform B.S.H x y = B.S.csum (B.S.I x) (B.S.I y) := B.S.isClassSum x y

/- English proof (translation)
Simplify using `only [BlockDat.opMat]`. Rewrite using `[← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]`.
-/
theorem opMat_comm (hc : Col.PairComm B.op) (i j : B.Pl × ℕ) :
    B.opMat i * B.opMat j = B.opMat j * B.opMat i := by
  simp only [BlockDat.opMat]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]

/- English proof (translation)
Simplify using `only [BlockDat.opMat, CSD.actMat]`. Rewrite using `[← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hG i g).eq]`.
-/
theorem opMat_actMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (i : B.Pl × ℕ) (g : G) :
    B.opMat i * B.S.actMat B.r g = B.S.actMat B.r g * B.opMat i := by
  simp only [BlockDat.opMat, CSD.actMat]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hG i g).eq]

/- English proof (translation)
Simplify using `only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[opMat_actMat hG i t]`.
-/
theorem opMat_gaMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (i : B.Pl × ℕ) (a : MonoidAlgebra K G) :
    B.opMat i * B.S.gaMat B.r a = B.S.gaMat B.r a * B.opMat i := by
  simp only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [opMat_actMat hG i t]

/- English proof (translation)
Simplify using `[hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Simplify using `only [starRingEnd_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
private theorem hform_eq_star_dotProduct_mulVec {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hform H u v = star u ⬝ᵥ (H *ᵥ v) := by
  simp [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  simp only [starRingEnd_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[hform_eq_star_dotProduct_mulVec, hform_eq_star_dotProduct_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]`.
-/
theorem hform_adj {n : ℕ} {H T T' : Matrix (Fin n) (Fin n) K} (h : Tᴴ * H = H * T') (x y : Fin n → K) :
    hform H (T.mulVec x) y = hform H x (T'.mulVec y) := by
  rw [hform_eq_star_dotProduct_mulVec, hform_eq_star_dotProduct_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

/- English proof (translation)
Rewrite using `[ConjugateWeightGram.mem_cmMax_iff_twist]`. Introduce `σ`. Establish `h1 : (E.map σ).mulVec (fun a => twist σ (x a)) = (E.map σ).mulVec (fun a => σ (x a))`. Establish `e1 : E.map (twist σ) = E.map σ`. Use extensionality with `i b`.

Conclude with `(ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hrat i b) σ`. Rewrite using `[← e1, ← emb_mulVec (twist σ) E x, e1, ← emb_mulVec σ E x]`. Use function extensionality and compare the values at `i`. Conclude with `(ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hz i) σ`. Conclude with `congrFun (map_injective_of_injective E hE σ h1) a`.
-/
theorem rat_of_mulVec {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (hE : Function.Injective E.mulVec)
    (hrat : ∀ i a, E i a ∈ cmMax K) (x : Fin d → K) (hz : ∀ i, E.mulVec x i ∈ cmMax K) (a : Fin d) :
    x a ∈ cmMax K := by
  rw [ConjugateWeightGram.mem_cmMax_iff_twist]
  intro σ
  have h1 : (E.map σ).mulVec (fun a => twist σ (x a)) = (E.map σ).mulVec (fun a => σ (x a)) := by
    have e1 : E.map (twist σ) = E.map σ := by
      ext i b
      exact (ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hrat i b) σ
    rw [← e1, ← emb_mulVec (twist σ) E x, e1, ← emb_mulVec σ E x]
    funext i
    exact (ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hz i) σ
  exact congrFun (map_injective_of_injective E hE σ h1) a

end CyclotomicLifting

open CyclotomicLifting

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.conj, h.irr, h.lifts j t⟩`.
-/
theorem DefFam.blockHyp_lift {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ)
    (j : J) (t : T) : BlockHyp (F.L j t) (F.lvlA P ψ) F.v0 s :=
  ⟨h.conj, h.irr, h.lifts j t⟩

namespace CyclotomicLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
Use `first`. Consider the case `rw [Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]`. Consider the case `(simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ g f).symm)`.
-/
theorem equivFun_end (g : Module.End K B.S.Forms) (f : B.S.Forms) :
    B.S.basis.equivFun (g f) = (LinearMap.toMatrix B.S.basis B.S.basis g).mulVec (B.S.basis.equivFun f) := by
  first
  | rw [Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  | (simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ g f).symm)

def spEnd (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) : Module.End K B.S.Forms :=
  Col.eigProj hc hs (Col.HasBlocks B.n B.q B.t B.bl)

def spMat (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (spEnd hc hs)

variable (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op)

/- English proof (translation)
The claim follows from `Col.eigProj_apply_mem hc hs _ f`.
-/
theorem spEnd_mem (f : B.S.Forms) : spEnd hc hs f ∈ B.ZH := Col.eigProj_apply_mem hc hs _ f

/- English proof (translation)
The claim follows from `Col.eigProj_apply_of_mem hc hs hf`.
-/
theorem spEnd_of_mem {f : B.S.Forms} (hf : f ∈ B.ZH) : spEnd hc hs f = f :=
  Col.eigProj_apply_of_mem hc hs hf

/- English proof (translation)
Establish `h : spEnd hc hs * spEnd hc hs = spEnd hc hs` using `LinearMap.ext fun f => spEnd_of_mem hc hs (spEnd_mem hc hs f)`. Rewrite using `[spMat, ← LinearMap.toMatrix_mul, h]`.
-/
theorem spMat_idem : spMat hc hs * spMat hc hs = spMat hc hs := by
  have h : spEnd hc hs * spEnd hc hs = spEnd hc hs :=
    LinearMap.ext fun f => spEnd_of_mem hc hs (spEnd_mem hc hs f)
  rw [spMat, ← LinearMap.toMatrix_mul, h]

/- English proof (translation)
Unfold `spMat`. Rewrite using `[← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]`. Use `congr 1`. Conclude with `(Col.commute_eigProj hc hs _ hg).eq`.
-/
theorem spMat_comm_of {g : Module.End K B.S.Forms} (hg : ∀ i, Commute (B.op i) g) :
    spMat hc hs * LinearMap.toMatrix B.S.basis B.S.basis g =
      LinearMap.toMatrix B.S.basis B.S.basis g * spMat hc hs := by
  unfold spMat
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  exact (Col.commute_eigProj hc hs _ hg).eq

/- English proof (translation)
The claim follows from `spMat_comm_of hc hs (fun j => hc j i)`.
-/
theorem spMat_opMat (i : B.Pl × ℕ) : spMat hc hs * B.opMat i = B.opMat i * spMat hc hs := spMat_comm_of hc hs (fun j => hc j i)

/- English proof (translation)
Simplify using `only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[show B.S.actMat B.r t = LinearMap.toMatrix B.S.basis B.S.basis (B.r t) from rfl, spMat_comm_of hc hs (fun i => hG i t)]`.
-/
theorem spMat_gaMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (a : MonoidAlgebra K G) :
    spMat hc hs * B.S.gaMat B.r a = B.S.gaMat B.r a * spMat hc hs := by
  simp only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show B.S.actMat B.r t = LinearMap.toMatrix B.S.basis B.S.basis (B.r t) from rfl,
    spMat_comm_of hc hs (fun i => hG i t)]

/- English proof (translation)
Use `⟨spEnd hc hs (B.S.basis.equivFun.symm y), spEnd_mem hc hs _, ?_⟩` and prove the remaining obligations. Use `equivFun_end (B := B) (spEnd hc hs) (B.S.basis.equivFun.symm y)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem spMat_mem (y : Fin B.S.dim → K) : (spMat hc hs).mulVec y ∈ B.coord B.ZH := by
  refine ⟨spEnd hc hs (B.S.basis.equivFun.symm y), spEnd_mem hc hs _, ?_⟩
  have := equivFun_end (B := B) (spEnd hc hs) (B.S.basis.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hz`. Use `equivFun_end (B := B) (spEnd hc hs) f` as an intermediate fact. Rewrite `this` using `[spEnd_of_mem hc hs hf]`. Conclude with `this.symm`.
-/
theorem spMat_of_mem {z : Fin B.S.dim → K} (hz : z ∈ B.coord B.ZH) : (spMat hc hs).mulVec z = z := by
  obtain ⟨f, hf, rfl⟩ := hz
  have := equivFun_end (B := B) (spEnd hc hs) f
  rw [spEnd_of_mem hc hs hf] at this
  exact this.symm

/- English proof (translation)
Take `⟨i', hi'⟩` from `hH.adj i`. Use `⟨i', FinitelyNonzeroLinear.adj_matrix fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[hform_eq_csum, hform_eq_csum, I_opMat, I_opMat, CSD.I_apply, CSD.I_apply]`. Conclude with `hi' _ _`.
-/
theorem opMat_adj (hH : B.OkH) (i : B.Pl × ℕ) : ∃ i', (B.opMat i)ᴴ * B.S.H = B.S.H * B.opMat i' := by
  obtain ⟨i', hi'⟩ := hH.adj i
  refine ⟨i', FinitelyNonzeroLinear.adj_matrix fun x y => ?_⟩
  rw [hform_eq_csum, hform_eq_csum, I_opMat, I_opMat, CSD.I_apply, CSD.I_apply]
  exact hi' _ _

/- English proof (translation)
Establish `hHh : B.S.Hᴴ = B.S.H` using `FinitelyNonzeroLinear.herm_of_pos hv0 hpos`. Establish `hU : IsUnit B.S.H` using `FinitelyNonzeroLinear.isUnit_of_pos hpos`. Establish `hdet : IsUnit B.S.H.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hU`. Use `set H := B.S.H with hHdef`. Use `set Pm := spMat hc hs with hPm`.

Set `Pst : Matrix (Fin B.S.dim) (Fin B.S.dim) K` to `H⁻¹ * (Pmᴴ * H)`. Establish `ha : Pmᴴ * H = H * Pst` using `by show Pmᴴ * H = H * (H⁻¹ * (Pmᴴ * H))`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]`. Establish `hb : ∀ i, Pst * B.opMat i = B.opMat i * Pst`. Introduce `i`.

Take `⟨i', hi'⟩` from `opMat_adj hH i`. Establish `h2 : H * B.opMat i = (B.opMat i')ᴴ * H`. Use `congrArg Matrix.conjTranspose hi'` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh]`. Conclude with `this`.

Apply `hU.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hcm : Pm * Pst = Pst * Pm`. Set `g : Module.End K B.S.Forms` to `Matrix.toLin B.S.basis B.S.basis Pst`. Establish `hg : ∀ i, Commute (B.op i) g`.

Introduce `i`. Establish `e : B.op i = Matrix.toLin B.S.basis B.S.basis (B.opMat i)` using `(Matrix.toLin_toMatrix B.S.basis B.S.basis (B.op i)).symm`. Use `show B.op i * g = g * B.op i`. Rewrite using `[e, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul, hb i]`. Use `spMat_comm_of hc hs hg` as an intermediate fact.

Rewrite `this` using `[LinearMap.toMatrix_toLin]`. Then use the resulting hypothesis. Establish `hconj : ∀ A : Matrix (Fin B.S.dim) (Fin B.S.dim) K, (A.map v0.embedding)ᴴ = (Aᴴ).map v0.embedding`. Introduce `A`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`.

Conclude with `(hv0 (A j i)).symm`. Establish `hE : Pst.map v0.embedding = Pm.map v0.embedding`. Use `FinitelyNonzeroLinear.normal_idem hpos (Pm.map v0.embedding) (Pst.map v0.embedding) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, spMat_idem]`. Rewrite using `[hconj, ← Matrix.map_mul, ← Matrix.map_mul, ha]`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hcm]`. Establish `hE' : Pst = Pm` using `Matrix.map_injective v0.embedding.injective hE`. Rewrite using `[ha, hE']`.
-/
theorem spMat_selfAdj (hv0 : IsConjAt v0) (hpos : (B.S.H.map v0.embedding).PosDef) (hH : B.OkH) :
    (spMat hc hs)ᴴ * B.S.H = B.S.H * spMat hc hs := by
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos hv0 hpos
  have hU : IsUnit B.S.H := FinitelyNonzeroLinear.isUnit_of_pos hpos
  have hdet : IsUnit B.S.H.det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  set H := B.S.H with hHdef
  set Pm := spMat hc hs with hPm
  let Pst : Matrix (Fin B.S.dim) (Fin B.S.dim) K := H⁻¹ * (Pmᴴ * H)
  have ha : Pmᴴ * H = H * Pst := by
    show Pmᴴ * H = H * (H⁻¹ * (Pmᴴ * H))
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hb : ∀ i, Pst * B.opMat i = B.opMat i * Pst := by
    intro i
    obtain ⟨i', hi'⟩ := opMat_adj hH i
    have h2 : H * B.opMat i = (B.opMat i')ᴴ * H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    apply hU.mul_left_cancel
    calc H * (Pst * B.opMat i) = (H * Pst) * B.opMat i := (Matrix.mul_assoc _ _ _).symm
      _ = Pmᴴ * (H * B.opMat i) := by rw [← ha, Matrix.mul_assoc]
      _ = (Pmᴴ * (B.opMat i')ᴴ) * H := by rw [h2, Matrix.mul_assoc]
      _ = (B.opMat i' * Pm)ᴴ * H := by rw [Matrix.conjTranspose_mul]
      _ = (Pm * B.opMat i')ᴴ * H := by rw [spMat_opMat hc hs i']
      _ = (B.opMat i')ᴴ * (Pmᴴ * H) := by rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((B.opMat i')ᴴ * H) * Pst := by rw [ha, Matrix.mul_assoc]
      _ = H * (B.opMat i * Pst) := by rw [← h2, Matrix.mul_assoc]
  have hcm : Pm * Pst = Pst * Pm := by
    let g : Module.End K B.S.Forms := Matrix.toLin B.S.basis B.S.basis Pst
    have hg : ∀ i, Commute (B.op i) g := by
      intro i
      have e : B.op i = Matrix.toLin B.S.basis B.S.basis (B.opMat i) :=
        (Matrix.toLin_toMatrix B.S.basis B.S.basis (B.op i)).symm
      show B.op i * g = g * B.op i
      rw [e, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul, hb i]
    have := spMat_comm_of hc hs hg
    rwa [LinearMap.toMatrix_toLin] at this
  have hconj : ∀ A : Matrix (Fin B.S.dim) (Fin B.S.dim) K,
      (A.map v0.embedding)ᴴ = (Aᴴ).map v0.embedding := by
    intro A
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    exact (hv0 (A j i)).symm
  have hE : Pst.map v0.embedding = Pm.map v0.embedding := by
    refine FinitelyNonzeroLinear.normal_idem hpos (Pm.map v0.embedding) (Pst.map v0.embedding) ?_ ?_ ?_
    · rw [← Matrix.map_mul, spMat_idem]
    · rw [hconj, ← Matrix.map_mul, ← Matrix.map_mul, ha]
    · rw [← Matrix.map_mul, ← Matrix.map_mul, hcm]
  have hE' : Pst = Pm := Matrix.map_injective v0.embedding.injective hE
  rw [ha, hE']

end CyclotomicLifting

open CyclotomicLifting

/- English proof (translation)
Use `set Pm := spMat h.ok.comm h.ok.split with hPm`. Use `set ε := B.vProj ℓ with hε`. Establish `hpos` using `h.ok.hpos v0`. Establish `hsa : Pmᴴ * B.S.H = B.S.H * Pm` using `spMat_selfAdj h.ok.comm h.ok.split h.conj hpos hH`. Establish `hg` using `good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ`.

Establish `hεadj : εᴴ * B.S.H = B.S.H * ε`. Use `group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)` as an intermediate fact. Rewrite `this` using `[hg.selfAdj]`. Then use the resulting hypothesis. Establish `hcomm : Pm * ε = ε * Pm` using `spMat_gaMat h.ok.comm h.ok.split h.ok.opG _`. Take `⟨⟨hv1, hv2⟩, hv3⟩` from `BlockDat.lf_v_proj h`.

Take `⟨hz1, hz2⟩` from `BlockDat.lf_z_proj (Z := B.ZH) h`. Establish `hεv : ε * B.vE ℓ = B.vE ℓ`. Rewrite using `[hε, BlockDat.vProj, ← hv3, Matrix.mul_assoc, hv1, Matrix.mul_one]`. Establish `hinj : Function.Injective (B.fE ℓ B.ZH).mulVec` using `fun a b hab => BlockDat.lf_fE_inj (B := B) (ℓ := ℓ) hab`. Take `⟨-, -, -, -, huniq⟩` from `orthogonal_projection_exists K v0 h.conj _ _ B.S.H hpos (B.fE ℓ B.ZH) hinj`.

Establish `hO : IsOrthProj B.S.H (B.fE ℓ B.ZH) (B.Pq ℓ B.ZH * B.vPr ℓ)`. Prove the components needed by the constructor for the conclusion. Use `show B.Pq ℓ B.ZH * B.vPr ℓ * (B.vE ℓ * B.zE ℓ B.ZH) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), hv1, Matrix.one_mul, hz1]`. Use `orthogonal_tower_projection B.S.H (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ B.ZH) (B.Pq ℓ B.ZH) _ (BlockDat.lf_card_inv_ne (ℓ := ℓ)) hv2 hz2 show (B.vE ℓ * B.zE ℓ B.ZH)ᴴ * B.S.H * (1 - B.vE ℓ * B.zE ℓ B.ZH * (B.Pq ℓ B.ZH * B.vPr ℓ)) = 0` as an intermediate fact.

Rewrite using `[← Matrix.mul_assoc (B.vE ℓ * B.zE ℓ B.ZH)]`. Conclude with `this`. Establish `hPr` using `huniq _ hO`. Establish `hfix : (ε * Pm) * B.fE ℓ B.ZH = B.fE ℓ B.ZH`. Apply `FinitelyNonzeroLinear.ext_mulVec` to reduce the goal to its premises.

Introduce `u`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `hmem : (B.fE ℓ B.ZH).mulVec u ∈ B.coord B.ZH`. Establish `h1 : (B.zE ℓ B.ZH).mulVec u ∈ B.Z0 ℓ B.ZH`. Rewrite using `[← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2]`.

Conclude with `⟨u, rfl⟩`. Establish `h2 : (B.vE ℓ).mulVec ((B.zE ℓ B.ZH).mulVec u) ∈ B.coord B.ZH` using `h1`. Rewrite `h2` using `[Matrix.mulVec_mulVec]`. Then use the resulting hypothesis. Rewrite using `[spMat_of_mem _ _ hmem]`. Use `show ε.mulVec ((B.vE ℓ * B.zE ℓ B.ZH).mulVec u) = (B.vE ℓ * B.zE ℓ B.ZH).mulVec u`.

Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hεv]`. Establish `hrange : LinearMap.range (ε * Pm).mulVecLin ≤ LinearMap.range (B.fE ℓ B.ZH).mulVecLin`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `h1 : (ε * Pm).mulVec y ∈ LinearMap.range (B.vE ℓ).mulVecLin`. Establish `hr : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range ε.mulVecLin` using `(image_idempotent_spec K B.S.dim (B.vProj ℓ)).2`.

Rewrite using `[hr, ← Matrix.mulVec_mulVec]`. Conclude with `⟨_, rfl⟩`. Take `⟨u, hu⟩` from `h1`. Establish `h2 : (ε * Pm).mulVec y ∈ B.coord B.ZH`. Rewrite using `[← hcomm, ← Matrix.mulVec_mulVec]`.

Conclude with `spMat_mem _ _ _`. Establish `h3 : u ∈ B.Z0 ℓ B.ZH` using `by show (B.vE ℓ).mulVecLin u ∈ B.coord B.ZH`. Rewrite using `[hu]`. Conclude with `h2`. Rewrite `h3` using `[← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2]`.

Take `⟨u', hu'⟩` from `h3`. Use `⟨u', ?_⟩` and prove the remaining obligations. Rewrite `hu`, `hu'`, the goal using `[Matrix.mulVecLin_apply]`. Use `show (B.vE ℓ * B.zE ℓ B.ZH).mulVec u' = _`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Use `show (B.vE ℓ).mulVec ((subE (B.Z0 ℓ B.ZH)).mulVec u') = _`. Rewrite using `[hu', hu]`. Both sides reduce to the same expression. Take `⟨M, hM⟩` from `exists_mul_of_range_le hrange`. Establish `hQadj : (ε * Pm)ᴴ * B.S.H = B.S.H * (ε * Pm)`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, hεadj, ← Matrix.mul_assoc, hsa, Matrix.mul_assoc, hcomm]`. Establish `hk : (B.fE ℓ B.ZH)ᴴ * B.S.H * (ε * Pm) = (B.fE ℓ B.ZH)ᴴ * B.S.H`. Rewrite using `[Matrix.mul_assoc, ← hQadj, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hfix]`. Establish `hPQ : (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = B.Pq ℓ B.ZH * B.vPr ℓ`. Combine the equalities or inequalities in the displayed calculation.

Establish `hMeq : M = B.Pq ℓ B.ZH * B.vPr ℓ`. Establish `: (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = M`. Rewrite using `[hM, ← Matrix.mul_assoc, hO.1, Matrix.one_mul]`. Rewrite using `[← this, hPQ]`. Rewrite using `[hM, hMeq]`.
-/
theorem CyclotomicLifting.proj_eq {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} (h : BlockHyp B ℓ v0 s) (hH : B.OkH) :
    B.fE ℓ B.ZH * (B.Pq ℓ B.ZH * B.vPr ℓ) = B.vProj ℓ * spMat h.ok.comm h.ok.split := by
  set Pm := spMat h.ok.comm h.ok.split with hPm
  set ε := B.vProj ℓ with hε
  have hpos := h.ok.hpos v0
  have hsa : Pmᴴ * B.S.H = B.S.H * Pm := spMat_selfAdj h.ok.comm h.ok.split h.conj hpos hH
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  have hεadj : εᴴ * B.S.H = B.S.H * ε := by
    have := group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)
    rwa [hg.selfAdj] at this
  have hcomm : Pm * ε = ε * Pm := spMat_gaMat h.ok.comm h.ok.split h.ok.opG _
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := BlockDat.lf_v_proj h
  obtain ⟨hz1, hz2⟩ := BlockDat.lf_z_proj (Z := B.ZH) h
  have hεv : ε * B.vE ℓ = B.vE ℓ := by
    rw [hε, BlockDat.vProj, ← hv3, Matrix.mul_assoc, hv1, Matrix.mul_one]

  have hinj : Function.Injective (B.fE ℓ B.ZH).mulVec := fun a b hab => BlockDat.lf_fE_inj (B := B) (ℓ := ℓ) hab
  obtain ⟨-, -, -, -, huniq⟩ := orthogonal_projection_exists K v0 h.conj _ _ B.S.H hpos (B.fE ℓ B.ZH) hinj
  have hO : IsOrthProj B.S.H (B.fE ℓ B.ZH) (B.Pq ℓ B.ZH * B.vPr ℓ) := by
    constructor
    · show B.Pq ℓ B.ZH * B.vPr ℓ * (B.vE ℓ * B.zE ℓ B.ZH) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), hv1, Matrix.one_mul, hz1]
    · have := orthogonal_tower_projection B.S.H (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ B.ZH) (B.Pq ℓ B.ZH) _ (BlockDat.lf_card_inv_ne (ℓ := ℓ)) hv2 hz2
      show (B.vE ℓ * B.zE ℓ B.ZH)ᴴ * B.S.H * (1 - B.vE ℓ * B.zE ℓ B.ZH * (B.Pq ℓ B.ZH * B.vPr ℓ)) = 0
      rw [← Matrix.mul_assoc (B.vE ℓ * B.zE ℓ B.ZH)]
      exact this
  have hPr := huniq _ hO

  have hfix : (ε * Pm) * B.fE ℓ B.ZH = B.fE ℓ B.ZH := by
    apply FinitelyNonzeroLinear.ext_mulVec
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hmem : (B.fE ℓ B.ZH).mulVec u ∈ B.coord B.ZH := by
      have h1 : (B.zE ℓ B.ZH).mulVec u ∈ B.Z0 ℓ B.ZH := by
        rw [← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2]
        exact ⟨u, rfl⟩
      have h2 : (B.vE ℓ).mulVec ((B.zE ℓ B.ZH).mulVec u) ∈ B.coord B.ZH := h1
      rwa [Matrix.mulVec_mulVec] at h2
    rw [spMat_of_mem _ _ hmem]
    show ε.mulVec ((B.vE ℓ * B.zE ℓ B.ZH).mulVec u) = (B.vE ℓ * B.zE ℓ B.ZH).mulVec u
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hεv]

  have hrange : LinearMap.range (ε * Pm).mulVecLin ≤ LinearMap.range (B.fE ℓ B.ZH).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    have h1 : (ε * Pm).mulVec y ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      have hr : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range ε.mulVecLin :=
        (image_idempotent_spec K B.S.dim (B.vProj ℓ)).2
      rw [hr, ← Matrix.mulVec_mulVec]
      exact ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := h1
    have h2 : (ε * Pm).mulVec y ∈ B.coord B.ZH := by
      rw [← hcomm, ← Matrix.mulVec_mulVec]
      exact spMat_mem _ _ _
    have h3 : u ∈ B.Z0 ℓ B.ZH := by
      show (B.vE ℓ).mulVecLin u ∈ B.coord B.ZH
      rw [hu]; exact h2
    rw [← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2] at h3
    obtain ⟨u', hu'⟩ := h3
    refine ⟨u', ?_⟩
    rw [Matrix.mulVecLin_apply] at hu hu' ⊢
    show (B.vE ℓ * B.zE ℓ B.ZH).mulVec u' = _
    rw [← Matrix.mulVec_mulVec]
    show (B.vE ℓ).mulVec ((subE (B.Z0 ℓ B.ZH)).mulVec u') = _
    rw [hu', hu]
    rfl
  obtain ⟨M, hM⟩ := exists_mul_of_range_le hrange
  have hQadj : (ε * Pm)ᴴ * B.S.H = B.S.H * (ε * Pm) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hεadj, ← Matrix.mul_assoc, hsa, Matrix.mul_assoc, hcomm]
  have hk : (B.fE ℓ B.ZH)ᴴ * B.S.H * (ε * Pm) = (B.fE ℓ B.ZH)ᴴ * B.S.H := by
    rw [Matrix.mul_assoc, ← hQadj, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hfix]
  have hPQ : (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = B.Pq ℓ B.ZH * B.vPr ℓ := by
    calc (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm)
        = (((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H)) * (ε * Pm) := by rw [← hPr]
      _ = ((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H * (ε * Pm)) := Matrix.mul_assoc _ _ _
      _ = ((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H) := by rw [hk]
      _ = _ := hPr.symm
  have hMeq : M = B.Pq ℓ B.ZH * B.vPr ℓ := by
    have : (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = M := by
      rw [hM, ← Matrix.mul_assoc, hO.1, Matrix.one_mul]
    rw [← this, hPQ]
  rw [hM, hMeq]

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)

/- English proof (translation)
The claim follows from `local_bounds_from_exponent K G Pl0 (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) F.v0 s (F.blockHyp_lift h P ψ j t) w`.
-/
theorem jw_le {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (j : J) (t : T)
    (w : HeightOneSpectrum (𝓞 K)) :
    jw ((F.side P ψ Zs).HT j t) w ((F.side P ψ Zs).Tl j t) ≤
      (F.etaJW P ψ Zs j t w : ℤ) + ((F.side P ψ Zs).dZ j t : ℤ) *
        ((F.JJW P ψ Zs j t w : ℤ) + vw w (((F.L j t).DG (F.lvlA P ψ) : ℕ) : K) + vw w (s : K)) :=
  local_bounds_from_exponent K G Pl0 (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) F.v0 s (F.blockHyp_lift h P ψ j t) w

/- English proof (translation)
The claim follows from `eta_units _ _ _ (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) w`.
-/
theorem etaJ_units (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    F.etaJ P ψ Zs j t w * (Col.eW w : ℚ) = (F.etaJW P ψ Zs j t w : ℚ) := eta_units _ _ _ (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) w

end DefFam

namespace FamIn

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

/- English proof (translation)
The claim follows from `A.fam.side_WF h P ψ Zs hst hin hsep`.
-/
theorem side_WF {s : ℕ} (h : A.fam.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A.fam.amb)
    (hst : Zs.Stable) (hin : Zs.InBlock) (hsep : A.fam.TypesSep) : (A.side P ψ Zs).WF :=
  A.fam.side_WF h P ψ Zs hst hin hsep

end FamIn

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
The claim follows from `Col.eq_prW_of_mem w (plc_prime w) (plc_mem w)`.
-/
theorem lf_plc_eq_prW (w : HeightOneSpectrum (𝓞 K)) : plc w = Col.prW w :=
  Col.eq_prW_of_mem w (plc_prime w) (plc_mem w)

/- English proof (translation)
Rewrite using `[← w.intValuation_le_pow_iff_mem, intValuation_eq_exp' w x hx, WithZero.exp_le_exp, neg_le_neg_iff]`.
-/
theorem lf_mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) (n : ℕ) :
    x ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vw w (x : K) := by
  rw [← w.intValuation_le_pow_iff_mem, intValuation_eq_exp' w x hx, WithZero.exp_le_exp, neg_le_neg_iff]

/- English proof (translation)
Establish `hp0 : ((Col.prW w : ℕ) : 𝓞 K) ≠ 0` using `by exact_mod_cast (Col.prW_prime w).ne_zero`. Establish `hcast : (((Col.prW w : ℕ) : 𝓞 K) : K) = ((Col.prW w : ℕ) : K)` using `by simp`. Establish `hnn : 0 ≤ vw w (((Col.prW w : ℕ) : 𝓞 K) : K)` using `Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w _`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le hnn`. Establish `hmap : (w.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((Col.prW w : ℕ) : 𝓞 K)}` using `by conv_lhs => rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ)]`.

Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`. Simplify using `[Col.prW]`. Establish `hne : w.asIdeal.under ℤ ≠ ⊥`. Introduce `h`.

Rewrite `hmap` using `[h, Ideal.map_bot]`. Conclude with `hp0 (Ideal.span_singleton_eq_bot.1 hmap.symm)`. Establish `h1 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = n`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises. Rewrite using `[hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]`.

Rewrite using `[hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx ℤ` using `Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne`. Unfold `Col.eW ramw`.

Rewrite using `[← h2, h1, lf_plc_eq_prW, ← hcast, hn]`.
-/
theorem lf_eW_eq_ramw (w : HeightOneSpectrum (𝓞 K)) : ((Col.eW w : ℕ) : ℤ) = ramw w := by
  have hp0 : ((Col.prW w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Col.prW_prime w).ne_zero
  have hcast : (((Col.prW w : ℕ) : 𝓞 K) : K) = ((Col.prW w : ℕ) : K) := by simp
  have hnn : 0 ≤ vw w (((Col.prW w : ℕ) : 𝓞 K) : K) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w _
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  have hmap : (w.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((Col.prW w : ℕ) : 𝓞 K)} := by
    conv_lhs => rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ)]
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Col.prW]
  have hne : w.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmap
    exact hp0 (Ideal.span_singleton_eq_bot.1 hmap.symm)
  have h1 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = n := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]
    · rw [hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]
      push_cast
      omega
  have h2 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne
  unfold Col.eW ramw
  rw [← h2, h1, lf_plc_eq_prW, ← hcast, hn]

end Units

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)

/- English proof (translation)
Rewrite using `[← lf_eW_eq_ramw]`. Establish `h` using `etaJ_units F P ψ Zs j t w`. Use `first`. Consider the case `exact_mod_cast h`. Consider the case `(have h' := congrArg (fun x : ℚ => (x : ℝ)) h`.

Move the coercions through the operations in `at h' ⊢`. Conclude with `h')`.
-/
theorem etaJ_ramw (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    ((F.etaJ P ψ Zs j t w : ℚ) : ℝ) * (ramw w : ℝ) = (F.etaJW P ψ Zs j t w : ℝ) := by
  rw [← lf_eW_eq_ramw]
  have h := etaJ_units F P ψ Zs j t w
  first
  | exact_mod_cast h
  | (have h' := congrArg (fun x : ℚ => (x : ℝ)) h
     push_cast at h' ⊢
     exact h')

/- English proof (translation)
Establish `h : F.JJ P ψ Zs j t w * ((Col.eW w : ℕ) : ℚ) = (F.JJW P ψ Zs j t w : ℚ)` using `div_mul_cancel₀ _ (Col.eW_ne_zero_rat w)`. Establish `e : ((ramw w : ℤ) : ℝ) = (((Col.eW w : ℕ) : ℚ) : ℝ)`. Rewrite using `[← lf_eW_eq_ramw]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e, ← Rat.cast_mul, h]`. Simplify using the standard rewrite rules.
-/
theorem JJ_ramw (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    ((F.JJ P ψ Zs j t w : ℚ) : ℝ) * (ramw w : ℝ) = (F.JJW P ψ Zs j t w : ℝ) := by
  have h : F.JJ P ψ Zs j t w * ((Col.eW w : ℕ) : ℚ) = (F.JJW P ψ Zs j t w : ℚ) :=
    div_mul_cancel₀ _ (Col.eW_ne_zero_rat w)
  have e : ((ramw w : ℤ) : ℝ) = (((Col.eW w : ℕ) : ℚ) : ℝ) := by
    rw [← lf_eW_eq_ramw]; push_cast; rfl
  rw [e, ← Rat.cast_mul, h]
  simp

end DefFam

section Poly

variable {K : Type} [Field K]

/- English proof (translation)
Conclude with `coeff_dualPoly' s R i`.
-/
theorem coeff_dualPoly (s : K) (R : K[X]) (i : ℕ) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (revAt R.natDegree i) * s ^ i) := by
  exact coeff_dualPoly' s R i

/- English proof (translation)
Rewrite using `[coeff_dualPoly, revAt_le hi]`.
-/
theorem coeff_dualPoly_of_le (s : K) (R : K[X]) {i : ℕ} (hi : i ≤ R.natDegree) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (R.natDegree - i) * s ^ i) := by
  rw [coeff_dualPoly, revAt_le hi]

/- English proof (translation)
Rewrite using `[coeff_dualPoly]`. Establish `h1 : revAt R.natDegree i = i` using `by first`. Consider the case `exact revAt_eq_self_of_lt hi`. Consider the case `(simp [revAt, revAtFun, not_le.mpr hi]; done)`. Consider the case `(simp only [revAt, revAtFun, Function.Embedding.coeFn_mk]; rw [if_neg (not_le.mpr hi)])`.

Rewrite using `[h1, coeff_eq_zero_of_natDegree_lt hi, zero_mul, mul_zero]`.
-/
theorem coeff_dualPoly_of_lt (s : K) (R : K[X]) {i : ℕ} (hi : R.natDegree < i) :
    (dualPoly s R).coeff i = 0 := by
  rw [coeff_dualPoly]
  have h1 : revAt R.natDegree i = i := by
    first
    | exact revAt_eq_self_of_lt hi
    | (simp [revAt, revAtFun, not_le.mpr hi]; done)
    | (simp only [revAt, revAtFun, Function.Embedding.coeFn_mk]; rw [if_neg (not_le.mpr hi)])
  rw [h1, coeff_eq_zero_of_natDegree_lt hi, zero_mul, mul_zero]

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at h0`.
-/
theorem ne_zero_of_coeff_zero {R : K[X]} (h0 : R.coeff 0 = 1) : R ≠ 0 := by
  rintro rfl
  simp at h0

/- English proof (translation)
Rewrite using `[coeff_dualPoly_of_le s R le_rfl, Nat.sub_self, h0, one_mul]`.
-/
theorem coeff_dualPoly_top {s : K} (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).coeff R.natDegree = R.leadingCoeff⁻¹ * s ^ R.natDegree := by
  rw [coeff_dualPoly_of_le s R le_rfl, Nat.sub_self, h0, one_mul]

/- English proof (translation)
Rewrite using `[coeff_dualPoly_top R h0]`. Conclude with `mul_ne_zero (inv_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_coeff_zero h0))) (pow_ne_zero _ hs)`.
-/
theorem coeff_dualPoly_top_ne {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).coeff R.natDegree ≠ 0 := by
  rw [coeff_dualPoly_top R h0]
  exact mul_ne_zero (inv_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_coeff_zero h0))) (pow_ne_zero _ hs)

/- English proof (translation)
Conclude with `natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => coeff_dualPoly_of_lt s R hi) (coeff_dualPoly_top_ne hs R h0)`.
-/
theorem natDegree_dualPoly {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).natDegree = R.natDegree := by
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => coeff_dualPoly_of_lt s R hi) (coeff_dualPoly_top_ne hs R h0)

/- English proof (translation)
Establish `hR` using `ne_zero_of_coeff_zero h0`. Establish `hlc : R.leadingCoeff ≠ 0` using `leadingCoeff_ne_zero.mpr hR`. Establish `hN` using `natDegree_dualPoly hs R h0`. Establish `hlcD : (dualPoly s R).leadingCoeff = R.leadingCoeff⁻¹ * s ^ R.natDegree` using `by show (dualPoly s R).coeff (dualPoly s R).natDegree = _`. Rewrite using `[hN]`.

Conclude with `coeff_dualPoly_top R h0`. Use extensionality with `i`. Break down `Nat.lt_or_ge R.natDegree i with hi | hi` into its components or cases. Establish `hi' : (dualPoly s R).natDegree < i` using `by rw [hN]; exact hi`. Rewrite using `[coeff_dualPoly_of_lt s (dualPoly s R) hi', coeff_eq_zero_of_natDegree_lt hi]`.

Establish `hi' : i ≤ (dualPoly s R).natDegree` using `by rw [hN]; exact hi`. Rewrite using `[coeff_dualPoly_of_le s (dualPoly s R) hi', hN, coeff_dualPoly_of_le s R (Nat.sub_le _ _), Nat.sub_sub_self hi, hlcD]`. Establish `e : s ^ R.natDegree = s ^ (R.natDegree - i) * s ^ i`. Rewrite using `[← pow_add, Nat.sub_add_cancel hi]`. Rewrite using `[e]`.

Establish `ha : s ^ (R.natDegree - i) ≠ 0` using `pow_ne_zero _ hs`. Establish `hb : s ^ i ≠ 0` using `pow_ne_zero _ hs`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dualPoly_dualPoly {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    dualPoly s (dualPoly s R) = R := by
  have hR := ne_zero_of_coeff_zero h0
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  have hN := natDegree_dualPoly hs R h0
  have hlcD : (dualPoly s R).leadingCoeff = R.leadingCoeff⁻¹ * s ^ R.natDegree := by
    show (dualPoly s R).coeff (dualPoly s R).natDegree = _
    rw [hN]
    exact coeff_dualPoly_top R h0
  ext i
  rcases Nat.lt_or_ge R.natDegree i with hi | hi
  · have hi' : (dualPoly s R).natDegree < i := by rw [hN]; exact hi
    rw [coeff_dualPoly_of_lt s (dualPoly s R) hi', coeff_eq_zero_of_natDegree_lt hi]
  · have hi' : i ≤ (dualPoly s R).natDegree := by rw [hN]; exact hi
    rw [coeff_dualPoly_of_le s (dualPoly s R) hi', hN,
      coeff_dualPoly_of_le s R (Nat.sub_le _ _), Nat.sub_sub_self hi, hlcD]
    have e : s ^ R.natDegree = s ^ (R.natDegree - i) * s ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [e]
    have ha : s ^ (R.natDegree - i) ≠ 0 := pow_ne_zero _ hs
    have hb : s ^ i ≠ 0 := pow_ne_zero _ hs
    calc _ = (R.leadingCoeff * R.leadingCoeff⁻¹) * (s ^ (R.natDegree - i) * (s ^ (R.natDegree - i))⁻¹) *
          (s ^ i * (s ^ i)⁻¹) * R.coeff i := by rw [mul_inv, inv_inv]; ring
      _ = R.coeff i := by rw [mul_inv_cancel₀ hlc, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb]; ring

/- English proof (translation)
Rewrite using `[← dualPoly_dualPoly hs R h0, h, dualPoly_dualPoly hs R' h0']`.
-/
theorem dualPoly_inj {s : K} (hs : s ≠ 0) {R R' : K[X]} (h0 : R.coeff 0 = 1) (h0' : R'.coeff 0 = 1)
    (h : dualPoly s R = dualPoly s R') : R = R' := by
  rw [← dualPoly_dualPoly hs R h0, h, dualPoly_dualPoly hs R' h0']

/- English proof (translation)
Simplify using `[Col.blockPoly, eval_prod]`.
-/
theorem blockPoly_eval_zero (ν : K) (q t : ℕ) : (Col.blockPoly ν q t).eval 0 = 1 := by
  simp [Col.blockPoly, eval_prod]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons p l ih`. Rewrite using `[List.prod_cons, eval_mul, h p (by simp), ih (fun q hq => h q (by simp [hq])), one_mul]`.
-/
theorem list_prod_eval_zero (l : List K[X]) (h : ∀ p ∈ l, p.eval 0 = 1) : l.prod.eval 0 = 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.prod_cons, eval_mul, h p (by simp), ih (fun q hq => h q (by simp [hq])), one_mul]

/- English proof (translation)
Use `first`. Consider the case `(simp only [Col.heckePoly, Col.heckePolyOf]`. Rewrite using `[eval_finset_sum, Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => by simp at h)]`. Simplify using `[h1])`. Consider the case `(simp only [Col.heckePoly, Col.heckePolyOf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]`.

Rewrite using `[Finset.sum_range_succ']`. Simplify using `[h1])`.
-/
theorem heckePoly_eval_zero {Pl : Type} (n : ℕ) (q : Pl → ℕ) (x : Pl × ℕ → K) (P : Pl) (h1 : x (P, 0) = 1) :
    (Col.heckePoly n q x P).eval 0 = 1 := by
  first
  | (simp only [Col.heckePoly, Col.heckePolyOf]
     rw [eval_finset_sum, Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => by simp at h)]
     simp [h1])
  | (simp only [Col.heckePoly, Col.heckePolyOf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
     rw [Finset.sum_range_succ']
     simp [h1])

end Poly

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

/- English proof (translation)
Establish `hl : ∀ p ∈ B.bl.map (fun ν => Col.blockPoly (ν P) (B.q P) B.t), p.eval 0 = 1`. Introduce `p hp`. Rewrite `hp` using `[List.mem_map]`. Take `⟨ν, -, rfl⟩` from `hp`. Conclude with `blockPoly_eval_zero _ _ _`.

Conclude with `list_prod_eval_zero _ hl`.
-/
theorem lf_blockProd_eval_zero (P : B.Pl) : (B.blockProd P).eval 0 = 1 := by
  have hl : ∀ p ∈ B.bl.map (fun ν => Col.blockPoly (ν P) (B.q P) B.t), p.eval 0 = 1 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨ν, -, rfl⟩ := hp
    exact blockPoly_eval_zero _ _ _
  exact list_prod_eval_zero _ hl

/- English proof (translation)
Unfold `BlockDat.ixFin at h`. Use `split_ifs at h with hf`. Conclude with `hf.mem_toFinset.1 h`. Simplify using `at h`.
-/
theorem lf_mem_resSet_of_mem_ixFin {X : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.ixFin X) :
    Sg ∈ B.resSet X := by
  unfold BlockDat.ixFin at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `h.2` to reduce the goal to its premises. Establish `hbot : B.partF Sg = ⊥`. Unfold `BlockDat.partF Col.eigSum`.

Use `iSup₂_eq_bot.2 fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hcon x hx hne`. Establish `hinj : Function.Injective (B.vE (Lvl.full X)).mulVec` using `(image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt (Lvl.full X).X (Lvl.full X).P (Lvl.full X).ψ))).1`. Unfold `BlockDat.inV0 BlockDat.coord`.

Rewrite using `[hbot, Submodule.map_bot, eq_bot_iff]`. Introduce `u hu`. Establish `hu' : (B.vE (Lvl.full X)).mulVec u = 0` using `(Submodule.mem_bot K).1 hu`. Rewrite using `[Submodule.mem_bot]`. Conclude with `hinj (by rw [hu', Matrix.mulVec_zero])`.
-/
theorem lf_exists_occurs_of_mem_resSet {X : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.resSet X) :
    ∃ x, B.HasRes Sg x ∧ Col.Occurs B.op x := by
  by_contra hcon
  push Not at hcon
  apply h.2
  have hbot : B.partF Sg = ⊥ := by
    unfold BlockDat.partF Col.eigSum
    refine iSup₂_eq_bot.2 fun x hx => ?_
    by_contra hne
    exact hcon x hx hne
  have hinj : Function.Injective (B.vE (Lvl.full X)).mulVec :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt (Lvl.full X).X (Lvl.full X).P (Lvl.full X).ψ))).1
  unfold BlockDat.inV0 BlockDat.coord
  rw [hbot, Submodule.map_bot, eq_bot_iff]
  intro u hu
  have hu' : (B.vE (Lvl.full X)).mulVec u = 0 := (Submodule.mem_bot K).1 hu
  rw [Submodule.mem_bot]
  exact hinj (by rw [hu', Matrix.mulVec_zero])

/- English proof (translation)
Distinguish the cases in `hP : P0 ∈ Set.range B.pl`. Use `swap`. Rewrite using `[h.1 P0 hP, coeff_one_zero]`. Take `⟨P, rfl⟩` from `hP`. Take `⟨x, hres, hocc⟩` from `B.lf_exists_occurs_of_mem_resSet h`.

Establish `h1 : x (P, 0) = 1` using `hocc.eq_one (h0 P)`. Establish `h2` using `congrArg (Polynomial.eval 0) (hres P)`. Rewrite `h2` using `[heckePoly_eval_zero _ _ _ _ h1, eval_mul, B.lf_blockProd_eval_zero, mul_one]`. Rewrite using `[coeff_zero_eq_eval_zero]`. Conclude with `h2.symm`.
-/
theorem lf_coeff_zero_of_mem_resSet (h0 : ∀ P, B.op (P, 0) = 1) {X : Finset (G → K)} {Sg : Pl0 → K[X]}
    (h : Sg ∈ B.resSet X) (P0 : Pl0) : (Sg P0).coeff 0 = 1 := by
  by_cases hP : P0 ∈ Set.range B.pl
  swap
  · rw [h.1 P0 hP, coeff_one_zero]
  obtain ⟨P, rfl⟩ := hP
  obtain ⟨x, hres, hocc⟩ := B.lf_exists_occurs_of_mem_resSet h
  have h1 : x (P, 0) = 1 := hocc.eq_one (h0 P)
  have h2 := congrArg (Polynomial.eval 0) (hres P)
  rw [heckePoly_eval_zero _ _ _ _ h1, eval_mul, B.lf_blockProd_eval_zero, mul_one] at h2
  rw [coeff_zero_eq_eval_zero]
  exact h2.symm

end BlockDat

namespace FamIn

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

/- English proof (translation)
The claim follows from `mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 (hq P)))`.
-/
theorem trScale_ne_zero (hq : ∀ P, A.q P ≠ 0) (P : Pl0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 (hq P)))

/- English proof (translation)
Introduce `Sg hSg Sg' hSg' hne j`. Take `⟨P, hP⟩` from `(A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne`. Conclude with `⟨P, fun h => hP (dualPoly_inj (A.trScale_ne_zero hq _) (hconst Sg hSg _) (hconst Sg' hSg' _) h)⟩`.
-/
theorem typesSep_of (hq : ∀ P, A.q P ≠ 0)
    (hconst : ∀ Sg ∈ (A.fam.R A.fam.μ0).ixFin A.fam.X, ∀ P, (Sg P).coeff 0 = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (A.trScale_ne_zero hq _) (hconst Sg hSg _) (hconst Sg' hSg' _) h)⟩

/- English proof (translation)
Introduce `Sg hSg P`. Conclude with `(A.fam.R A.fam.μ0).lf_coeff_zero_of_mem_resSet h0 ((A.fam.R A.fam.μ0).lf_mem_resSet_of_mem_ixFin hSg) P`.
-/
theorem const_of (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) :
    ∀ Sg ∈ (A.fam.R A.fam.μ0).ixFin A.fam.X, ∀ P, (Sg P).coeff 0 = 1 := by
  intro Sg hSg P
  exact (A.fam.R A.fam.μ0).lf_coeff_zero_of_mem_resSet h0 ((A.fam.R A.fam.μ0).lf_mem_resSet_of_mem_ixFin hSg) P

/- English proof (translation)
The claim follows from `typesSep_of A hq (const_of A h0)`.
-/
theorem typesSep_of' (hq : ∀ P, A.q P ≠ 0) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := typesSep_of A hq (const_of A h0)

end FamIn

end Formalism.L2.DIV

namespace Formalism.L2.DIV.LiftTest

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.DIV.Test

variable (G : Type) [Group G] [Fintype G]

/- English proof (translation)
Use `first`. Consider the case `(show ∀ σ : ℚ →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)`. Introduce `σ`. Simplify using `[eq_ratCast σ])`. Consider the case `(intro σ; simp [eq_ratCast σ])`.

Consider the case `(intro σ; rw [star_trivial, eq_ratCast σ]; simp)`.
-/
theorem lf_mem_cmMax_rat (a : ℚ) : a ∈ cmMax ℚ := by
  first
  | (show ∀ σ : ℚ →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
     intro σ
     simp [eq_ratCast σ])
  | (intro σ; simp [eq_ratCast σ])
  | (intro σ; rw [star_trivial, eq_ratCast σ]; simp)

def exampleB : BlockDat ℚ G Unit :=
  liftDat (regCSD ℚ G) (regAct ℚ G) Set.univ (fun i => (gaussBin 2 2 i.2 : ℚ) • 1) 1 1 (fun _ => 2)
    (fun _ => 1) (fun _ => 1)

def trivialCharacterLevel (P : Subgroup G) : Lvl ℚ G := ⟨{fun _ => 1}, P, 1⟩

def toyX : (exampleB G).Pl × ℕ → ℚ := fun i => (gaussBin 2 2 i.2 : ℚ)

/- English proof (translation)
Introduce `P`. Establish `h` using `heckePolyOf_gaussBin (L := ℚ) 2 2 1`. Simplify using `only [one_pow, one_mul] at h`. Use `show ([fun P : (Set.univ : Set Unit) => firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit)].map fun ν => blockPoly (ν P) 2 1).prod ∣ heckePolyOf (1 + 1) 2 fun i => (gaussBin 2 2 i : ℚ)`. Rewrite using `[show (1 + 1 : ℕ) = 2 from rfl, h]`.

Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`. Establish `e : firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit) = 2`. Simplify using `[firstValA]`. Rewrite using `[e, blockPoly_succ' (1 : ℚ) 2 1]`. Establish `e2 : (1 : ℚ) * ((2 : ℕ) : ℚ) = 2` using `by norm_num`.

Rewrite using `[e2]`. Conclude with `Dvd.intro_left _ rfl`.
-/
theorem toy_hasBlocks_gaussBin : HasBlocks (1 + 1) (fun _ : (Set.univ : Set Unit) => 2) 1
    [fun P : (Set.univ : Set Unit) => firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit)]
    (fun i => (gaussBin 2 2 i.2 : ℚ)) := by
  intro P
  have h := heckePolyOf_gaussBin (L := ℚ) 2 2 1
  simp only [one_pow, one_mul] at h
  show ([fun P : (Set.univ : Set Unit) => firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit)].map
    fun ν => blockPoly (ν P) 2 1).prod ∣ heckePolyOf (1 + 1) 2 fun i => (gaussBin 2 2 i : ℚ)
  rw [show (1 + 1 : ℕ) = 2 from rfl, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have e : firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit) = 2 := by
    simp [firstValA]
  rw [e, blockPoly_succ' (1 : ℚ) 2 1]
  have e2 : (1 : ℚ) * ((2 : ℕ) : ℚ) = 2 := by norm_num
  rw [e2]
  exact Dvd.intro_left _ rfl

/- English proof (translation)
The claim follows from `toy_hasBlocks_gaussBin`.
-/
theorem toyB_hasBlocks : HasBlocks (exampleB G).n (exampleB G).q (exampleB G).t (exampleB G).bl (toyX G) := toy_hasBlocks_gaussBin

/- English proof (translation)
Use `first`. Consider the case `exact (Commute.one_left g).smul_left a`. Consider the case `exact Commute.smul_left (Commute.one_left g) a`. Consider the case `(show a • (1 : Module.End ℚ V) * g = g * (a • 1)`. Use extensionality with `x`.

Use the proof step `simp)`.
-/
theorem comm1 {V : Type} [AddCommGroup V] [Module ℚ V] (a : ℚ) (g : Module.End ℚ V) :
    Commute (a • (1 : Module.End ℚ V)) g := by
  first
  | exact (Commute.one_left g).smul_left a
  | exact Commute.smul_left (Commute.one_left g) a
  | (show a • (1 : Module.End ℚ V) * g = g * (a • 1)
     ext x
     simp)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Use `le_trans ?_ (eigAt_le_eigSum (op := (exampleB G).op) (toyB_hasBlocks G))` and prove the remaining obligations. Introduce `f _`. Conclude with `mem_eigAt_of_forall_apply fun i => rfl`.
-/
theorem toyB_ZH_eq_top : (exampleB G).ZH = ⊤ := by
  rw [eq_top_iff]
  refine le_trans ?_ (eigAt_le_eigSum (op := (exampleB G).op) (toyB_hasBlocks G))
  intro f _
  exact mem_eigAt_of_forall_apply fun i => rfl

/- English proof (translation)
The claim follows from `reg_good ℚ G hrat := fun _ _ => lf_mem_cmMax_rat _ hpos := fun v => reg_H_posDef ℚ G v (rat_isConjAt v) act := regAct_good ℚ G actRat := fun _ _ _ => lf_mem_cmMax_rat _ comm := fun i j => comm1 (V := (regCSD ℚ G).Forms) _ _ split := by intro i rw [eq_top_iff] refine le_trans ?_ ( …`.
-/
theorem toyB_ok : (exampleB G).Ok 1 where
  good := reg_good ℚ G
  hrat := fun _ _ => lf_mem_cmMax_rat _
  hpos := fun v => reg_H_posDef ℚ G v (rat_isConjAt v)
  act := regAct_good ℚ G
  actRat := fun _ _ _ => lf_mem_cmMax_rat _
  comm := fun i j => comm1 (V := (regCSD ℚ G).Forms) _ _
  split := by
    intro i
    rw [eq_top_iff]
    refine le_trans ?_ (le_iSup _ ((gaussBin 2 2 i.2 : ℚ)))
    exact (Formalism.L2.NCov.maxGen_smul_one (K := ℚ) (V := (regCSD ℚ G).Forms) _).ge
  opG := fun i g => comm1 (V := (regCSD ℚ G).Forms) _ _
  blocks := ⟨le_rfl, List.cons_ne_nil _ _, fun ν hν P => by
    have hν' := List.mem_singleton.1 hν
    subst hν'
    simp [firstValA]⟩
  q_pos _ := show 0 < 2 by norm_num
  pl_inj := Subtype.val_injective

/- English proof (translation)
Rewrite using `[reg_csum, reg_csum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_trivial]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem regular_scalar_selfAdjoint (a : ℚ) (f g : (regCSD ℚ G).Forms) :
    (regCSD ℚ G).csum (((a • (1 : Module.End ℚ (regCSD ℚ G).Forms)) f).1 : G → ℚ) (g.1 : G → ℚ) =
      (regCSD ℚ G).csum (f.1 : G → ℚ) (((a • (1 : Module.End ℚ (regCSD ℚ G).Forms)) g).1 : G → ℚ) := by
  rw [reg_csum, reg_csum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    star_trivial]
  ring

/- English proof (translation)
Introduce `_ _ _` and use `lf_mem_cmMax_rat _ adj := fun i => ⟨i, fun f g => regular_scalar_selfAdjoint G _ f g⟩`.
-/
theorem toyB_okH : (exampleB G).OkH where
  rat := fun _ _ _ => lf_mem_cmMax_rat _
  adj := fun i => ⟨i, fun f g => regular_scalar_selfAdjoint G _ f g⟩

/- English proof (translation)
The claim follows from `rat_isConjAt v0 irr := by intro χ hχ rw [show (trivialCharacterLevel G P).X = {fun _ => 1} from rfl, Finset.mem_singleton] at hχ rw [hχ] exact isAbsIrrChar_one ℚ _ ok := toyB_ok G`.
-/
theorem toyB_blockHyp (P : Subgroup G) (v0 : InfinitePlace ℚ) : BlockHyp (exampleB G) (trivialCharacterLevel G P) v0 1 where
  conj := rat_isConjAt v0
  irr := by
    intro χ hχ
    rw [show (trivialCharacterLevel G P).X = {fun _ => 1} from rfl, Finset.mem_singleton] at hχ
    rw [hχ]
    exact isAbsIrrChar_one ℚ _
  ok := toyB_ok G

/- English proof (translation)
Unfold `BlockDat.Z0 BlockDat.inV0 BlockDat.coord`. Rewrite using `[toyB_ZH_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 (LinearEquiv.surjective _), Submodule.comap_top]`.
-/
theorem example_invariant_subspace_top (P : Subgroup G) : (exampleB G).Z0 (trivialCharacterLevel G P) (exampleB G).ZH = ⊤ := by
  unfold BlockDat.Z0 BlockDat.inV0 BlockDat.coord
  rw [toyB_ZH_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 (LinearEquiv.surjective _), Submodule.comap_top]

/- English proof (translation)
Unfold `BlockDat.dZ subDim`. Rewrite using `[example_invariant_subspace_top, finrank_top, Module.finrank_fin_fun]`. Conclude with `reg_V0dim_pos_lvl ℚ G P`.
-/
theorem toyB_dZ_pos (P : Subgroup G) : 0 < (exampleB G).dZ (trivialCharacterLevel G P) (exampleB G).ZH := by
  unfold BlockDat.dZ subDim
  rw [example_invariant_subspace_top, finrank_top, Module.finrank_fin_fun]
  exact reg_V0dim_pos_lvl ℚ G P

end Formalism.L2.DIV.LiftTest

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

/- English proof (translation)
Apply `Matrix.mulVec_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Establish `hr : LinearMap.range (B.zE ℓ Z).mulVecLin = ⊤`. Rewrite using `[← hZ]`. Conclude with `(subspace_image_spec K _ (B.Z0 ℓ Z)).2`.

Take `⟨y, rfl⟩` from `LinearMap.range_eq_top.1 hr x`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, (lf_z_proj (Z := Z) h).1, Matrix.mul_one, Matrix.one_mulVec]`.
-/
theorem tt_zE_Pq (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) : B.zE ℓ Z * B.Pq ℓ Z = 1 := by
  apply Matrix.mulVec_injective
  funext x
  have hr : LinearMap.range (B.zE ℓ Z).mulVecLin = ⊤ := by
    rw [← hZ]; exact (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.1 hr x
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, (lf_z_proj (Z := Z) h).1, Matrix.mul_one,
    Matrix.one_mulVec]

/- English proof (translation)
Establish `e : B.fE ℓ Z * B.lPr ℓ Z = B.vE ℓ * (B.zE ℓ Z * B.Pq ℓ Z) * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ`. Unfold `fE lPr`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, tt_zE_Pq h hZ, Matrix.mul_one, (lf_v_proj h).2]`. Both sides reduce to the same expression.
-/
theorem tt_fE_lPr (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) :
    B.fE ℓ Z * B.lPr ℓ Z = B.vProj ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
  have e : B.fE ℓ Z * B.lPr ℓ Z = B.vE ℓ * (B.zE ℓ Z * B.Pq ℓ Z) * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
    unfold fE lPr
    simp only [Matrix.mul_assoc]
  rw [e, tt_zE_Pq h hZ, Matrix.mul_one, (lf_v_proj h).2]
  rfl

/- English proof (translation)
Establish `e : B.vProj ℓ * B.fE ℓ Z = B.fE ℓ Z`. Establish `h2 : B.vProj ℓ = B.vE ℓ * B.vPr ℓ` using `(lf_v_proj h).2.symm`. Rewrite using `[h2]`. Unfold `fE`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul]`.

Rewrite using `[Matrix.mulVec_mulVec, e]`.
-/
theorem tt_fix (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    (B.vProj ℓ).mulVec ((B.fE ℓ Z).mulVec z) = (B.fE ℓ Z).mulVec z := by
  have e : B.vProj ℓ * B.fE ℓ Z = B.fE ℓ Z := by
    have h2 : B.vProj ℓ = B.vE ℓ * B.vPr ℓ := (lf_v_proj h).2.symm
    rw [h2]
    unfold fE
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e]

/- English proof (translation)
Establish `hNK : (N : K) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hfl : ∀ y, (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec y) = (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y)`. Introduce `y`. Rewrite using `[Matrix.mulVec_mulVec, tt_fE_lPr h hZ, Matrix.mulVec_mulVec]`. Establish `hcut : B.cutZ ℓ Z = exponent_index_lattice.smLat (N : K) (B.Tl ℓ Z)`.

Use extensionality with `x`. Rewrite using `[exponent_index_lattice.mem_smLat]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : (B.fE ℓ Z).mulVec x ∈ B.S.nabLat` using `hx`.

Take `⟨y, hy, hyu⟩` from `hb ((N : K)⁻¹ • (B.fE ℓ Z).mulVec x) (by rw [Matrix.mulVec_smul, tt_fix h]) (by rw [smul_smul, mul_inv_cancel₀ hNK, one_smul]; exact hx')`. Use `⟨(B.lPr ℓ Z).mulVec y, (exponent_index_lattice.mem_matLat _ _ _).2 ⟨y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `lf_fE_inj (B := B) (ℓ := ℓ)` to reduce the goal to its premises. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_smul, hfl, hyu, smul_smul, mul_inv_cancel₀ hNK, one_smul]`. Introduce and unpack `⟨z, hz, rfl⟩`.

Take `⟨y, hy, rfl⟩` from `(exponent_index_lattice.mem_matLat _ _ _).1 hz`. Use `show (B.fE ℓ Z).mulVec ((N : K) • (B.lPr ℓ Z).mulVec y) ∈ B.S.nabLat`. Rewrite using `[Matrix.mulVec_smul, hfl]`. Conclude with `ha y hy`. Establish `hT` using `lf_Tl_isLattice (Z := Z) h`.

Establish `hC` using `lf_cutZ_isLattice (Z := Z) h`. Establish `h1` using `exponent_index_lattice.idx_smLat w (B.Tl ℓ Z) hT hNK`. Rewrite `h1` using `[← hcut]`. Establish `h2` using `(exponent_index_lattice.idxB w (B.Tl ℓ Z) (B.cutZ ℓ Z) (B.Tl ℓ Z) hT hC hT).2.2 (lf_cutZ_le (Z := Z) h)`. Unfold `etaW`.

Rewrite using `[← h2, h1]`.
-/
theorem tt_eta (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) (N : ℕ) (hN : 0 < N)
    (ha : ∀ y ∈ B.S.lvlNab B.r ℓ.P ℓ.ψ,
      (N : K) • (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) ∈ B.S.nabLat)
    (hb : ∀ u : Fin B.S.dim → K, (B.vProj ℓ).mulVec u = u → (N : K) • u ∈ B.S.nabLat →
      ∃ y ∈ B.S.lvlNab B.r ℓ.P ℓ.ψ, (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) = u)
    (w : HeightOneSpectrum (𝓞 K)) : (B.etaW ℓ Z w : ℤ) = (B.dZ ℓ Z : ℤ) * vw w (N : K) := by
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hfl : ∀ y, (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec y) =
      (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) := by
    intro y
    rw [Matrix.mulVec_mulVec, tt_fE_lPr h hZ, Matrix.mulVec_mulVec]
  have hcut : B.cutZ ℓ Z = exponent_index_lattice.smLat (N : K) (B.Tl ℓ Z) := by
    ext x
    rw [exponent_index_lattice.mem_smLat]
    constructor
    · intro hx
      have hx' : (B.fE ℓ Z).mulVec x ∈ B.S.nabLat := hx
      obtain ⟨y, hy, hyu⟩ := hb ((N : K)⁻¹ • (B.fE ℓ Z).mulVec x)
        (by rw [Matrix.mulVec_smul, tt_fix h]) (by rw [smul_smul, mul_inv_cancel₀ hNK, one_smul]; exact hx')
      refine ⟨(B.lPr ℓ Z).mulVec y, (exponent_index_lattice.mem_matLat _ _ _).2 ⟨y, hy, rfl⟩, ?_⟩
      apply lf_fE_inj (B := B) (ℓ := ℓ)
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_smul, hfl, hyu, smul_smul,
        mul_inv_cancel₀ hNK, one_smul]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).1 hz
      show (B.fE ℓ Z).mulVec ((N : K) • (B.lPr ℓ Z).mulVec y) ∈ B.S.nabLat
      rw [Matrix.mulVec_smul, hfl]
      exact ha y hy
  have hT := lf_Tl_isLattice (Z := Z) h
  have hC := lf_cutZ_isLattice (Z := Z) h
  have h1 := exponent_index_lattice.idx_smLat w (B.Tl ℓ Z) hT hNK
  rw [← hcut] at h1
  have h2 := (exponent_index_lattice.idxB w (B.Tl ℓ Z) (B.cutZ ℓ Z) (B.Tl ℓ Z) hT hC hT).2.2 (lf_cutZ_le (Z := Z) h)
  unfold etaW
  rw [← h2, h1]

/- English proof (translation)
Establish `hinj : Function.Injective (φ ∘ₗ (B.fE ℓ Z).mulVecLin)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Use `hφ _ (tt_fix h z) hz` as an intermediate fact. Apply `lf_fE_inj (B := B) (ℓ := ℓ)` to reduce the goal to its premises.

Rewrite using `[Matrix.mulVecLin_apply, this, map_zero]`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact. Simplify using `using this`.
-/
theorem tt_dZ_le_one (h : BlockHyp B ℓ v0 s) (φ : (Fin B.S.dim → K) →ₗ[K] K)
    (hφ : ∀ u, (B.vProj ℓ).mulVec u = u → φ u = 0 → u = 0) : B.dZ ℓ Z ≤ 1 := by
  have hinj : Function.Injective (φ ∘ₗ (B.fE ℓ Z).mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have := hφ _ (tt_fix h z) hz
    apply lf_fE_inj (B := B) (ℓ := ℓ)
    rw [Matrix.mulVecLin_apply, this, map_zero]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end BlockDat

end Formalism.L2.DIV

namespace Formalism.L2.DIV.LiftTest

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.DIV.Test

variable (G : Type) [Group G] [Fintype G]

abbrev regE : Matrix (Fin (regCSD ℚ G).dim) (Fin (regCSD ℚ G).dim) ℚ :=
  (regCSD ℚ G).gaMat (regAct ℚ G) (goodAt ({fun _ => 1} : Finset (G → ℚ)) ⊥ 1)

/- English proof (translation)
Unfold `goodAt`. Rewrite using `[lvlIdem_bot ℚ G, mul_one, idemOf_one_coeff]`.
-/
theorem reg_coeff (t : G) :
    (goodAt ({fun _ => 1} : Finset (G → ℚ)) (⊥ : Subgroup G) 1).coeff t = 1 / (Fintype.card G : ℚ) := by
  unfold goodAt
  rw [lvlIdem_bot ℚ G, mul_one, idemOf_one_coeff]

/- English proof (translation)
Unfold `regE CSD.gaMat`. Rewrite using `[Matrix.sum_mulVec, map_sum, Finset.sum_apply, Finset.mul_sum]`. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft c) (fun g => (Fintype.card G : ℚ)⁻¹ * ((regCSD ℚ G).I x : G → ℚ) g)]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, map_smul, reg_coeff, CSD.I_actMat]`.

Use `show (1 / (Fintype.card G : ℚ)) * (((regAct ℚ G t ((regCSD ℚ G).basis.equivFun.symm x)).1 : G → ℚ) c) = _`. Rewrite using `[regAct_apply, one_div]`. Both sides reduce to the same expression.
-/
theorem reg_avg (x : Fin (regCSD ℚ G).dim → ℚ) (c : G) :
    ((regCSD ℚ G).I ((regE G).mulVec x) : G → ℚ) c =
      (Fintype.card G : ℚ)⁻¹ * ∑ g : G, ((regCSD ℚ G).I x : G → ℚ) g := by
  unfold regE CSD.gaMat
  rw [Matrix.sum_mulVec, map_sum, Finset.sum_apply, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft c) (fun g => (Fintype.card G : ℚ)⁻¹ * ((regCSD ℚ G).I x : G → ℚ) g)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.smul_mulVec, map_smul, reg_coeff, CSD.I_actMat]
  show (1 / (Fintype.card G : ℚ)) * (((regAct ℚ G t ((regCSD ℚ G).basis.equivFun.symm x)).1 : G → ℚ) c) = _
  rw [regAct_apply, one_div]
  rfl

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`.
-/
theorem mem_one_iff (a : ℚ) : a ∈ (1 : Submodule (𝓞 ℚ) ℚ) ↔ ∃ n : 𝓞 ℚ, (n : ℚ) = a := by
  rw [Submodule.mem_one]

/- English proof (translation)
The claim follows from `mem_valLatF _ _ x`.
-/
theorem reg_mem_nab (x : Fin (regCSD ℚ G).dim → ℚ) :
    x ∈ (regCSD ℚ G).nabLat ↔ ∀ c : G, ((regCSD ℚ G).I x : G → ℚ) c ∈ (1 : Submodule (𝓞 ℚ) ℚ) :=
  mem_valLatF _ _ x

/- English proof (translation)
Establish `h` using `(image_idempotent_spec ℚ _ ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1))).2`. Establish `e : (regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1) = 1`. Rewrite using `[lvlIdem_bot ℚ G, (group_action_matrix_hom ℚ (regCSD ℚ G) G (regAct ℚ G)).1]`. Establish `htop : LinearMap.range ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1)).mulVecLin = ⊤`. Rewrite using `[e]`.

Conclude with `LinearMap.range_eq_top.2 fun x => ⟨x, by simp⟩`. Establish `h2` using `h.trans htop`. Introduce `x`. Take `⟨y, hy⟩` from `LinearMap.range_eq_top.1 h2 x`. Conclude with `⟨y, hy⟩`.
-/
theorem reg_lvlE_surj : Function.Surjective ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec := by
  have h := (image_idempotent_spec ℚ _ ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1))).2
  have e : (regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1) = 1 := by
    rw [lvlIdem_bot ℚ G, (group_action_matrix_hom ℚ (regCSD ℚ G) G (regAct ℚ G)).1]
  have htop : LinearMap.range ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1)).mulVecLin = ⊤ := by
    rw [e]
    exact LinearMap.range_eq_top.2 fun x => ⟨x, by simp⟩
  have h2 := h.trans htop
  intro x
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1 h2 x
  exact ⟨y, hy⟩

/- English proof (translation)
Conclude with `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`.
-/
theorem card_ne : (Fintype.card G : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- English proof (translation)
Establish `h1` using `reg_avg G u c`. Establish `h2` using `reg_avg G u 1`. Rewrite `h1`, `h2` using `[hu]`. Rewrite using `[h1, h2]`.
-/
theorem reg_const (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u) (c : G) :
    ((regCSD ℚ G).I u : G → ℚ) c = ((regCSD ℚ G).I u : G → ℚ) 1 := by
  have h1 := reg_avg G u c
  have h2 := reg_avg G u 1
  rw [hu] at h1 h2
  rw [h1, h2]

/- English proof (translation)
Establish `hy' : ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat` using `hy`. Rewrite `hy'`, the goal using `[reg_mem_nab]`. Introduce `c`. Rewrite using `[map_smul]`. Use `show ((Fintype.card G : ℕ) : ℚ) * ((regCSD ℚ G).I ((regE G).mulVec _) : G → ℚ) c ∈ _`.

Rewrite using `[reg_avg, ← mul_assoc, mul_inv_cancel₀ (card_ne G), one_mul]`. Conclude with `Submodule.sum_mem _ fun g _ => hy' g`.
-/
theorem reg_ha (y : Fin ((regCSD ℚ G).lvlDim (regAct ℚ G) ⊥ 1) → ℚ)
    (hy : y ∈ (regCSD ℚ G).lvlNab (regAct ℚ G) ⊥ 1) :
    ((Fintype.card G : ℕ) : ℚ) • (regE G).mulVec (((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y) ∈
      (regCSD ℚ G).nabLat := by
  have hy' : ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat := hy
  rw [reg_mem_nab] at hy' ⊢
  intro c
  rw [map_smul]
  show ((Fintype.card G : ℕ) : ℚ) * ((regCSD ℚ G).I ((regE G).mulVec _) : G → ℚ) c ∈ _
  rw [reg_avg, ← mul_assoc, mul_inv_cancel₀ (card_ne G), one_mul]
  exact Submodule.sum_mem _ fun g _ => hy' g

/- English proof (translation)
Use `set a0 : ℚ := ((regCSD ℚ G).I u : G → ℚ) 1 with ha0`. Establish `hint : (Fintype.card G : ℚ) * a0 ∈ (1 : Submodule (𝓞 ℚ) ℚ)`. Use `(reg_mem_nab G _).1 hN 1` as an intermediate fact. Rewrite `this` using `[map_smul]`. Conclude with `this`.

Set `f : G → ℚ` to `Pi.single 1 ((Fintype.card G : ℚ) * a0)`. Take `⟨x, hx⟩` from `((regCSD ℚ G).I_onto f).2 (fun c γ => rfl)`. Take `⟨y, hy⟩` from `reg_lvlE_surj G x`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Use `show ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat`.

Rewrite using `[hy, reg_mem_nab, hx]`. Introduce `c`. Distinguish the cases in `hc : c = 1`. Substitute `hc` using the available equality. Simplify `hint` using `[f]`.

Establish `: f c = 0` using `by simp [f, hc]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[hy]`. Apply `(regCSD ℚ G).I_injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `c`. Rewrite using `[reg_avg, hx, reg_const G u hu c]`. Establish `: ∑ g : G, f g = (Fintype.card G : ℚ) * a0` using `by simp [f]`. Rewrite using `[this, ← mul_assoc, inv_mul_cancel₀ (card_ne G), one_mul]`.
-/
theorem reg_hb (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u)
    (hN : ((Fintype.card G : ℕ) : ℚ) • u ∈ (regCSD ℚ G).nabLat) :
    ∃ y ∈ (regCSD ℚ G).lvlNab (regAct ℚ G) ⊥ 1,
      (regE G).mulVec (((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y) = u := by
  classical
  set a0 : ℚ := ((regCSD ℚ G).I u : G → ℚ) 1 with ha0
  have hint : (Fintype.card G : ℚ) * a0 ∈ (1 : Submodule (𝓞 ℚ) ℚ) := by
    have := (reg_mem_nab G _).1 hN 1
    rw [map_smul] at this
    exact this
  let f : G → ℚ := Pi.single 1 ((Fintype.card G : ℚ) * a0)
  obtain ⟨x, hx⟩ := ((regCSD ℚ G).I_onto f).2 (fun c γ => rfl)
  obtain ⟨y, hy⟩ := reg_lvlE_surj G x
  refine ⟨y, ?_, ?_⟩
  · show ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat
    rw [hy, reg_mem_nab, hx]
    intro c
    by_cases hc : c = 1
    · subst hc
      simpa [f] using hint
    · have : f c = 0 := by simp [f, hc]
      rw [this]
      exact Submodule.zero_mem _
  · rw [hy]
    apply (regCSD ℚ G).I_injective
    funext c
    rw [reg_avg, hx, reg_const G u hu c]
    have : ∑ g : G, f g = (Fintype.card G : ℚ) * a0 := by simp [f]
    rw [this, ← mul_assoc, inv_mul_cancel₀ (card_ne G), one_mul]

def regPhi : (Fin (regCSD ℚ G).dim → ℚ) →ₗ[ℚ] ℚ :=
  (LinearMap.proj (1 : G) : (G → ℚ) →ₗ[ℚ] ℚ) ∘ₗ (regCSD ℚ G).I

/- English proof (translation)
Apply `(regCSD ℚ G).I_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Rewrite using `[map_zero]`. Conclude with `(reg_const G u hu c).trans h0`.
-/
theorem reg_hphi (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u)
    (h0 : regPhi G u = 0) : u = 0 := by
  apply (regCSD ℚ G).I_injective
  funext c
  rw [map_zero]
  exact (reg_const G u hu c).trans h0

/- English proof (translation)
Establish `h1 : (exampleB G).dZ (trivialCharacterLevel G ⊥) (exampleB G).ZH ≤ 1` using `BlockDat.tt_dZ_le_one (toyB_blockHyp G ⊥ v0) (regPhi G) (reg_hphi G)`. Establish `h2` using `toyB_dZ_pos G ⊥`. Use linear arithmetic over natural numbers and integers.
-/
theorem toyB_dZ_eq_one (v0 : InfinitePlace ℚ) : (exampleB G).dZ (trivialCharacterLevel G ⊥) (exampleB G).ZH = 1 := by
  have h1 : (exampleB G).dZ (trivialCharacterLevel G ⊥) (exampleB G).ZH ≤ 1 :=
    BlockDat.tt_dZ_le_one (toyB_blockHyp G ⊥ v0) (regPhi G) (reg_hphi G)
  have h2 := toyB_dZ_pos G ⊥
  omega

/- English proof (translation)
Take `⟨v0⟩ : Nonempty (InfinitePlace ℚ)` from `inferInstance`. Establish `h` using `BlockDat.tt_eta (toyB_blockHyp G ⊥ v0) (example_invariant_subspace_top G ⊥) (Fintype.card G) Fintype.card_pos (reg_ha G) (reg_hb G) w`. Rewrite `h` using `[toyB_dZ_eq_one G v0]`. Simplify using `using h`.
-/
theorem toyB_etaW_eq_vw_card (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((exampleB G).etaW (trivialCharacterLevel G ⊥) (exampleB G).ZH w : ℤ) = vw w ((Fintype.card G : ℕ) : ℚ) := by
  obtain ⟨v0⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  have h := BlockDat.tt_eta (toyB_blockHyp G ⊥ v0) (example_invariant_subspace_top G ⊥) (Fintype.card G) Fintype.card_pos
    (reg_ha G) (reg_hb G) w
  rw [toyB_dZ_eq_one G v0] at h
  simpa using h

/- English proof (translation)
Unfold `BlockDat.JexpW expW`. Apply `Nat.eq_zero_of_le_zero` to reduce the goal to its premises. Apply `Nat.sInf_le` to reduce the goal to its premises. Introduce `a _ z hz`. Establish `hz' : z ∈ (exampleB G).delZ (trivialCharacterLevel G P) (exampleB G).ZH` using `hz`.

Conclude with `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.smul_mem _ a hz'⟩`.
-/
theorem toyB_JexpW_eq_zero (P : Subgroup G) (w : HeightOneSpectrum (𝓞 ℚ)) : (exampleB G).JexpW (trivialCharacterLevel G P) (exampleB G).ZH w = 0 := by
  unfold BlockDat.JexpW expW
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  intro a _ z hz
  have hz' : z ∈ (exampleB G).delZ (trivialCharacterLevel G P) (exampleB G).ZH := hz
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.smul_mem _ a hz'⟩

end Formalism.L2.DIV.LiftTest
