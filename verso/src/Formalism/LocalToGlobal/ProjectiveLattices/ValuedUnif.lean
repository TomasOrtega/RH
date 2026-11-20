import Formalism.LocalToGlobal.ProjectiveLattices.RealPt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain WithZero

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

/- English proof (translation)
Establish `hu : Irreducible (unif X la)` using `Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.intValuation_exists_uniformizer la`. Establish `hπv : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = exp (-1 : ℤ)`. Establish `h` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := B.KO) (v := la) π`. Rewrite `h` using `[HeightOneSpectrum.valuation_of_algebraMap, hπ]`.

Conclude with `h`. Use `set o : X.Ol la := algebraMap (𝓞 B.KO) (X.Ol la) π with ho`. Establish `ho0 : o ≠ 0`. Introduce `h0`. Establish `: Valued.v ((o : X.Ol la) : X.Kl la) = 0` using `by rw [h0]; simp`.

Establish `h2 : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = 0` using `this`. Rewrite `h2` using `[hπv]`. Conclude with `exp_ne_zero h2`. Take `⟨k, u, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu`. Establish `hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit`.

Establish `hv0 : Valued.v ((unif X la : X.Ol la) : X.Kl la) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Introduce `h0`. Conclude with `hu.ne_zero (Subtype.ext h0)`. Establish `e1 : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-1 : ℤ)` using `hπv`.

Rewrite `e1` using `[hk]`. Move the coercions through the operations in `at e1`. Rewrite `e1` using `[map_mul, map_pow, hu1, one_mul, ← exp_log hv0, ← exp_nsmul, exp_inj]`. Establish `h2 : (k : ℤ) * (-log (Valued.v ((unif X la : X.Ol la) : X.Kl la))) = 1`. Rewrite `e1` using `[nsmul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (k : ℤ) = 1` using `Int.eq_one_of_mul_eq_one_right (by positivity) h2`. Rewrite `h2` using `[hk1, one_mul]`. Rewrite using `[← exp_log hv0]`. Use `congr 1`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem valued_unif (la : HeightOneSpectrum (𝓞 B.KO)) :
    Valued.v ((unif X la : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.intValuation_exists_uniformizer la
  have hπv : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = exp (-1 : ℤ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := B.KO) (v := la) π
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ] at h
    exact h
  set o : X.Ol la := algebraMap (𝓞 B.KO) (X.Ol la) π with ho
  have ho0 : o ≠ 0 := by
    intro h0
    have : Valued.v ((o : X.Ol la) : X.Kl la) = 0 := by rw [h0]; simp
    have h2 : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = 0 := this
    rw [hπv] at h2
    exact exp_ne_zero h2
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  have hv0 : Valued.v ((unif X la : X.Ol la) : X.Kl la) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h0
    exact hu.ne_zero (Subtype.ext h0)
  have e1 : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := hπv
  rw [hk] at e1
  push_cast at e1
  rw [map_mul, map_pow, hu1, one_mul, ← exp_log hv0, ← exp_nsmul, exp_inj] at e1
  have h2 : (k : ℤ) * (-log (Valued.v ((unif X la : X.Ol la) : X.Kl la))) = 1 := by
    rw [nsmul_eq_mul] at e1; linarith
  have hk1 : (k : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
  rw [hk1, one_mul] at h2
  rw [← exp_log hv0]
  congr 1
  linarith

/- English proof (translation)
Establish `hu : Irreducible (unif X la)` using `Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))`. Establish `ho0 : o ≠ 0`. Introduce and unpack `rfl`. Rewrite `hm` using `[IsDiscreteValuationRing.addVal_zero]`. Conclude with `ENat.top_ne_natCast m hm`.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu`. Rewrite `hm` using `[IsDiscreteValuationRing.addVal_def' u hu n, Nat.cast_inj]`. Substitute `hm` using the available equality. Establish `hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit`. Use `push_cast`.

Rewrite using `[map_mul, map_pow, hu1, one_mul, valued_unif, ← exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem valued_Ol (la : HeightOneSpectrum (𝓞 B.KO)) (o : X.Ol la) (m : ℕ)
    (hm : IsDiscreteValuationRing.addVal (X.Ol la) o = m) : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-(m : ℤ)) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have ho0 : o ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hm; exact ENat.top_ne_natCast m hm
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  rw [IsDiscreteValuationRing.addVal_def' u hu n, Nat.cast_inj] at hm
  subst hm
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  push_cast
  rw [map_mul, map_pow, hu1, one_mul, valued_unif, ← exp_nsmul]
  congr 1
  simp

section Kap

variable {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
  {la : HeightOneSpectrum (𝓞 B.KO)} (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
  (ζ : PtsG G la) [IsDVRAt ζ] (T : CDVR) (ι : Loc ζ →+* T.V) (hι : AddValPres ζ ι)

def kapA : Kp (xplus X E hM) la G.N →+* T.Fr :=
  (phiAt ζ T.Fr ι h hι).comp (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))

/- English proof (translation)
Use `show phiAt ζ T.Fr ι h hι (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) y)) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)]`. Establish `e : algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) y = ((algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) : OsK (xplus X E hM) la G.w)` using `rfl`. Rewrite using `[e, phiAt_coe]`. Use `show algebraMap T.V T.Fr (ι (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y))) = _`.

Rewrite using `[← IsScalarTower.algebraMap_apply]`.
-/
theorem kapA_Op (y : Op (xplus X E hM) la G.N) :
    kapA h ζ T ι hι (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) y) =
      algebraMap T.V T.Fr (ι (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) y)) := by
  show phiAt ζ T.Fr ι h hι (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)
    (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) y)) = _
  rw [← IsScalarTower.algebraMap_apply (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)]
  have e : algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) y =
      ((algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y :
        ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) : OsK (xplus X E hM) la G.w) := rfl
  rw [e, phiAt_coe]
  show algebraMap T.V T.Fr (ι (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ)
    (algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y))) = _
  rw [← IsScalarTower.algebraMap_apply]

/- English proof (translation)
The claim follows from `Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la)))`.
-/
theorem unifO_irr : Irreducible (unifO (xplus X E hM) la G.N) :=
  Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la)))

/- English proof (translation)
Establish `hϖ` using `unifO_irr (E := E) (hM := hM) (G := G) (la := la)`. Establish `hy : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hk` using `[IsDiscreteValuationRing.addVal_zero]`. Conclude with `ENat.top_ne_natCast k hk`.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Rewrite `hk` using `[IsDiscreteValuationRing.addVal_def' u hϖ n, Nat.cast_inj]`. Substitute `hk` using the available equality. Rewrite using `[kapA_Op]`. Apply `vV_alg_of_addVal` to reduce the goal to its premises.

Establish `hep : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (unifO (xplus X E hM) la G.N)) = (ep (unifO (xplus X E hM) la G.N) ζ : ℕ∞)`. Rewrite using `[coe_ep ζ h, vL_eq_addVal, ← IsScalarTower.algebraMap_apply]`. Establish `hu0 : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (u : Op (xplus X E hM) la G.N)) = 0`. Rewrite using `[← IsUnit.unit_spec (u.isUnit.map (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ)))]`. Conclude with `IsDiscreteValuationRing.addVal_eq_zero_of_unit _`.

Rewrite using `[hι, map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow, hep, hu0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vV_kapA_Op (y : Op (xplus X E hM) la G.N) (k : ℕ) (hk : IsDiscreteValuationRing.addVal _ y = k) :
    vV T.V (kapA h ζ T ι hι (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) y)) =
      ((ep (unifO (xplus X E hM) la G.N) ζ * k : ℕ) : ℤ) := by
  have hϖ := unifO_irr (E := E) (hM := hM) (G := G) (la := la)
  have hy : y ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hk; exact ENat.top_ne_natCast k hk
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, Nat.cast_inj] at hk
  subst hk
  rw [kapA_Op]
  apply vV_alg_of_addVal
  have hep : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (unifO (xplus X E hM) la G.N)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℕ∞) := by
    rw [coe_ep ζ h, vL_eq_addVal, ← IsScalarTower.algebraMap_apply]
  have hu0 : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (u : Op (xplus X E hM) la G.N)) = 0 := by
    rw [← IsUnit.unit_spec (u.isUnit.map (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ)))]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  rw [hι, map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow, hep, hu0]
  push_cast
  ring

/- English proof (translation)
Use `set io := (kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp (algebraMap B.KO ((xplus X E hM).Kl la))) with hio`. Establish `hint : ∀ x : 𝓞 B.KO, x ≠ 0 → vV T.V (io (algebraMap (𝓞 B.KO) B.KO x)) = (ep (unifO (xplus X E hM) la G.N) ζ : ℤ) * vLa la (algebraMap (𝓞 B.KO) B.KO x)`. Introduce `x hx`. Use `set o : (xplus X E hM).Ol la := algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la) x with ho`. Establish `ho0 : o ≠ 0`.

Rewrite using `[ho, Ne, ← map_zero (algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la))]`. Conclude with `fun h => hx (FaithfulSMul.algebraMap_injective _ _ h)`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 ho0)`. Establish `hu` using `Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))`. Establish `hOp : IsDiscreteValuationRing.addVal (Op (xplus X E hM) la G.N) (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o) = m`.

Take `⟨n, u, hn⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu`. Rewrite `hm` using `[hn, IsDiscreteValuationRing.addVal_def' u hu n]`. Rewrite using `[hn, map_mul, map_pow]`. Establish `e : algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (u : (xplus X E hM).Ol la) * algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (unif (xplus X E hM) la) ^ n = ((u.isUnit.map (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N))).unit : Op (xplu …`. Rewrite using `[IsUnit.unit_spec]`.

Both sides reduce to the same expression. Use `erw [e, IsDiscreteValuationRing.addVal_def' _ (unifO_irr (E := E) (hM := hM) (G := G) (la := la)) n]`. Conclude with `hm.symm`. Establish `e1 : io (algebraMap (𝓞 B.KO) B.KO x) = kapA h ζ T ι hι (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o))` using `by show kapA h ζ T ι hι (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la)) = _`. Rewrite using `[show ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = algebraMap ((xplus X E hM).Ol la) ((xplus X E hM).Kl la) o from rfl, ← IsScalarTower.algebraMap_apply]`.

Both sides reduce to the same expression. Establish `e2 : vLa la (algebraMap (𝓞 B.KO) B.KO x) = m`. Establish `h1` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := la) (algebraMap (𝓞 B.KO) B.KO x)`. Establish `h2 : Valued.v ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = exp (-(m : ℤ))` using `valued_Ol la o m hm.symm`. Unfold `vLa`.

Rewrite using `[← h1]`. Use `erw [h2]`. Simplify using the standard rewrite rules. Rewrite using `[e1, vV_kapA_Op h ζ T ι hι _ m hOp, e2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨ep_pos ζ h, fun a => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using `[vV, vLa]`.

Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 B.KO) a`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at ha`. Establish `hX : algebraMap (𝓞 B.KO) B.KO x ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hx0`. Establish `hY : algebraMap (𝓞 B.KO) B.KO y ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hy0`.

Establish `hiX : io (algebraMap (𝓞 B.KO) B.KO x) ≠ 0` using `(map_ne_zero io).2 hX`. Establish `hiY : io (algebraMap (𝓞 B.KO) B.KO y) ≠ 0` using `(map_ne_zero io).2 hY`. Rewrite using `[map_div₀, div_eq_mul_inv, vV_mul hiX (inv_ne_zero hiY), vV_inv' hiY, hint x hx0, hint y hy0]`. Establish `hvX : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO x) ≠ 0` using `(Valuation.ne_zero_iff _).2 hX`. Establish `hvY : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO y) ≠ 0` using `(Valuation.ne_zero_iff _).2 hY`.

Unfold `vLa`. Rewrite using `[map_div₀, WithZero.log_div hvX hvY]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem overLa_kapA : OverLa la T.V ((kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la)))) (ep (unifO (xplus X E hM) la G.N) ζ) := by
  set io := (kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la))) with hio
  have hint : ∀ x : 𝓞 B.KO, x ≠ 0 → vV T.V (io (algebraMap (𝓞 B.KO) B.KO x)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℤ) * vLa la (algebraMap (𝓞 B.KO) B.KO x) := by
    intro x hx
    set o : (xplus X E hM).Ol la := algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la) x with ho
    have ho0 : o ≠ 0 := by
      rw [ho, Ne, ← map_zero (algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la))]
      exact fun h => hx (FaithfulSMul.algebraMap_injective _ _ h)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 ho0)
    have hu := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))
    have hOp : IsDiscreteValuationRing.addVal (Op (xplus X E hM) la G.N) (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o) = m := by
      obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
      rw [hn, IsDiscreteValuationRing.addVal_def' u hu n] at hm
      rw [hn, map_mul, map_pow]
      have e : algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (u : (xplus X E hM).Ol la) *
          algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (unif (xplus X E hM) la) ^ n =
          ((u.isUnit.map (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N))).unit : Op (xplus X E hM) la G.N) *
            unifO (xplus X E hM) la G.N ^ n := by
        rw [IsUnit.unit_spec]; rfl
      erw [e, IsDiscreteValuationRing.addVal_def' _ (unifO_irr (E := E) (hM := hM) (G := G) (la := la)) n]
      exact hm.symm
    have e1 : io (algebraMap (𝓞 B.KO) B.KO x) = kapA h ζ T ι hι (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N)
        (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o)) := by
      show kapA h ζ T ι hι (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la)) = _
      rw [show ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = algebraMap ((xplus X E hM).Ol la) ((xplus X E hM).Kl la) o from rfl,
        ← IsScalarTower.algebraMap_apply]
      rfl
    have e2 : vLa la (algebraMap (𝓞 B.KO) B.KO x) = m := by
      have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := la) (algebraMap (𝓞 B.KO) B.KO x)
      have h2 : Valued.v ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = exp (-(m : ℤ)) := valued_Ol la o m hm.symm
      unfold vLa
      rw [← h1]
      erw [h2]
      simp
    rw [e1, vV_kapA_Op h ζ T ι hι _ m hOp, e2]
    push_cast; ring
  refine ⟨ep_pos ζ h, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 B.KO) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha
  have hX : algebraMap (𝓞 B.KO) B.KO x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hx0
  have hY : algebraMap (𝓞 B.KO) B.KO y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hy0
  have hiX : io (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (map_ne_zero io).2 hX
  have hiY : io (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (map_ne_zero io).2 hY
  rw [map_div₀, div_eq_mul_inv, vV_mul hiX (inv_ne_zero hiY), vV_inv' hiY, hint x hx0, hint y hy0]
  have hvX : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (Valuation.ne_zero_iff _).2 hX
  have hvY : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (Valuation.ne_zero_iff _).2 hY
  unfold vLa
  rw [map_div₀, WithZero.log_div hvX hvY]
  ring

end Kap

section EvRp

variable {X' : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {Fd : Type} [Field Fd]
  (kap : Kp X' la N →+* Fd) (χ : X'.Forms →+* Fd)
  (hχ : ∀ (a : B.KO) (f : X'.Forms),
    χ (a • f) = kap (algebraMap (X'.Kl la) (Kp X' la N) (algebraMap B.KO (X'.Kl la) a)) * χ f)

def evRp : Rp X' la N →+* Fd :=
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X'.Forms →ₐ[B.KO] Fd :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X'.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X'.Vl la →ₐ[X'.Kl la] Fd :=
    Algebra.TensorProduct.lift (Algebra.ofId (X'.Kl la) Fd) g (fun _ _ => Commute.all _ _)
  (Algebra.TensorProduct.lift (Algebra.ofId (Kp X' la N) Fd) vl (fun _ _ => Commute.all _ _)).toRingHom

/- English proof (translation)
Use `letI : Algebra (Kp X' la N) Fd := kap.toAlgebra`. Use `letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra`. Use `letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra`. Use `haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Unfold `evRp`. Use `erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]`. Use `erw [map_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem evRp_alg (k : Kp X' la N) : evRp la N kap χ hχ (algebraMap (Kp X' la N) (Rp X' la N) k) = kap k := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold evRp
  erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]
  erw [map_one, mul_one]
  rfl

/- English proof (translation)
Use `letI : Algebra (Kp X' la N) Fd := kap.toAlgebra`. Use `letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra`. Use `letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra`. Use `haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `e : emb X' la N F = ((1 : Kp X' la N) ⊗ₜ[X'.Kl la] ((1 : X'.Kl la) ⊗ₜ[B.KO] F : X'.Vl la) : TensorProduct (X'.Kl la) (Kp X' la N) (X'.Vl la))` using `rfl`. Simplify using `only [evRp, e]`. Use `(Algebra.TensorProduct.lift_tmul _ _ _ 1 _).trans ?_` and prove the remaining obligations. Rewrite using `[map_one, one_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem evRp_emb (F : X'.Forms) : evRp la N kap χ hχ (emb X' la N F) = χ F := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd :=
    (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have e : emb X' la N F =
      ((1 : Kp X' la N) ⊗ₜ[X'.Kl la] ((1 : X'.Kl la) ⊗ₜ[B.KO] F : X'.Vl la) :
        TensorProduct (X'.Kl la) (Kp X' la N) (X'.Vl la)) := rfl
  simp only [evRp, e]
  refine (Algebra.TensorProduct.lift_tmul _ _ _ 1 _).trans ?_
  rw [map_one, one_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end EvRp

end Formalism.L2.Pj
