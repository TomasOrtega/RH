import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SideXCen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0`. Simplify `w.ne_bot` using `[Ideal.absNorm_eq_zero_iff]`. Conclude with `h0` after adjusting the coercions.
-/
private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

/- English proof (translation)
Unfold `eulerL`. Use `tprod_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

/- English proof (translation)
Unfold `eulerLd eulerL`. Use `tprod_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map, Multiset.map_map, Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

/- English proof (translation)
Unfold `cnt`. Use `congr 1`. Use `Multiset.filter_congr fun y _ => ?_` and prove the remaining obligations. Establish `key : ∀ ξ : kˣ →* ℂˣ, IsUnram (ξ * χ) ↔ IsUnram (ξ * 1)` using `fun ξ => forall_congr' fun x => forall_congr' fun hx => by`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.mul_apply, h x hx, MonoidHom.one_apply]`.

Simplify using `only [key]`.
-/
private theorem cnt_unram {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL k)) {χ : kˣ →* ℂˣ} (h : IsUnram χ) : cnt s χ = cnt s 1 := by
  unfold cnt
  congr 1
  refine Multiset.filter_congr fun y _ => ?_
  have key : ∀ ξ : kˣ →* ℂˣ, IsUnram (ξ * χ) ↔ IsUnram (ξ * 1) := fun ξ =>
    forall_congr' fun x => forall_congr' fun hx => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h x hx, MonoidHom.one_apply]
  simp only [key]

/- English proof (translation)
Introduce `x hx`. Use `haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `h x ((ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).eq_one_iff_eq_one.1 hx)`.
-/
private theorem unram_loc {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt v) : IsUnram (χ.loc v) := by
  intro x hx
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact h x ((ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).eq_one_iff_eq_one.1 hx)

/- English proof (translation)
Use `haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Establish `E` using `ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))`. Take `⟨h1, h2⟩` from `(polFacts (v.adicCompletion K)).1`. Establish `hp : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ)` using `unif_spec v`. Establish `a1` using `E.lt_one_iff_lt_one.1 h1`.

Establish `a2` using `(E _ _).1 (h2 ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) (E.lt_one_iff_lt_one.2 (by rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)))`. Establish `a3 : Valued.v ((unif (v.adicCompletion K) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ)`. Use `le_antisymm ((WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).1 ?_) (hp ▸ a2)` and prove the remaining obligations. Rewrite using `[← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]` and apply the resulting hypothesis. Establish `a4` using `h (unif (v.adicCompletion K) * (atFin v (Formalism.L2.Host.unif v))⁻¹) (by`.

Express the relevant statement in the definitionally equal form `Valued.v _ = 1`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, a3, hp, mul_inv_cancel₀ WithZero.exp_ne_zero])`. Rewrite `a4` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `a4`.
-/
private theorem loc_unif {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt v) :
    χ.loc v (unif (v.adicCompletion K)) = χ.val v := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have E := ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))
  obtain ⟨h1, h2⟩ := (polFacts (v.adicCompletion K)).1
  have hp : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    unif_spec v
  have a1 := E.lt_one_iff_lt_one.1 h1
  have a2 := (E _ _).1 (h2 ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
    (E.lt_one_iff_lt_one.2 (by rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)))
  have a3 : Valued.v ((unif (v.adicCompletion K) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    refine le_antisymm ((WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).1 ?_) (hp ▸ a2)
    rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have a4 := h (unif (v.adicCompletion K) * (atFin v (Formalism.L2.Host.unif v))⁻¹) (by
    change Valued.v _ = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, a3, hp, mul_inv_cancel₀ WithZero.exp_ne_zero])
  rw [map_mul, map_inv, mul_inv_eq_one] at a4
  exact a4

/- English proof (translation)
Distinguish the cases in `e : d = 0`. Rewrite using `[eq_C_of_natDegree_eq_zero (hd.trans e)]`. Simplify using the standard rewrite rules. Establish `hq0 : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `: (N : ℂ) ^ (-z) * (((q : ℝ) : ℂ) ^ z) ^ f = 1`.

Rewrite using `[h e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.ofReal_natCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]`. Simplify using the standard rewrite rules. Rewrite using `[comp_assoc, comp_assoc]`. Use `congr 1`. Simplify using `only [mul_comp, C_comp, X_comp, pow_comp, mul_pow, ← C_pow]`.

Rewrite using `[← mul_assoc, ← C_mul, this, C_1, one_mul]`.
-/
private theorem pol_shift (P : ℂ[X]) (N q f d : ℕ) (z : ℂ) (hq : 1 < q) (h0 : P.eval 0 = 1) (hd : P.natDegree = d)
    (h : d ≠ 0 → N = q ^ f) :
    ((P.comp (C ((N : ℂ) ^ (-z)) * X)).comp (X ^ f)).comp (C (((q : ℝ) : ℂ) ^ z) * X) = P.comp (X ^ f) := by
  by_cases e : d = 0
  · rw [eq_C_of_natDegree_eq_zero (hd.trans e)]
    simp
  · have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : (N : ℂ) ^ (-z) * (((q : ℝ) : ℂ) ^ z) ^ f = 1 := by
      rw [h e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.ofReal_natCast, ← Complex.cpow_nat_mul,
        ← Complex.cpow_add _ _ hq0]
      simp
    rw [comp_assoc, comp_assoc]
    congr 1
    simp only [mul_comp, C_comp, X_comp, pow_comp, mul_pow, ← C_pow]
    rw [← mul_assoc, ← C_mul, this, C_1, one_mul]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter in
/- English proof (translation)
Introduce `K _ _ _ n hn σ S hS B hB s q f hq hs`. Set `x : GlobalTheory.ResW.Letter K` to `⟨n, σ⟩`. Establish `hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')`. Set `z : ℂ` to `-GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))`. Set `χ : HChar K` to `Model.absC K z`.

Establish `hspec` using `(GlobalTheory.ResW.letter_centralExponent K x).1`. Establish `htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K)`. Express the relevant statement in the definitionally equal form `(Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _`. Simplify using `[Matrix.trace, Nat.cast_smul_eq_nsmul]`. Establish `hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0`.

Introduce and unpack `_ ⟨ψ, hψ, rfl⟩`. Establish `e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ` using `hspec ψ hψ`. Establish `e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x`. Rewrite using `[htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]`. Establish `hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x` using `div_mul_cancel₀ _ hd`.

Simplify using `only [Complex.real_smul, Complex.ofReal_natCast]`. Take the linear combination `hzd`. Express the relevant statement in the definitionally equal form `lie K n (oneL K n) (mulChi n χ ψ) = 0`. Rewrite using `[lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]`. Establish `hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)` using `fun v => by`.

Use `⟨fun y hy => Units.ext ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1`. Rewrite using `[GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp`. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (Formalism.L2.Host.unif v)))) = _`. Establish `h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0` using `by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot`.

Rewrite using `[GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0), ← Complex.natCast_log]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hex : ∀ v, ∃ s', v ∈ S → SuppAt (σ.twist χ) v s' ∧ cnt s' 1 = cnt (s v) 1 ∧ pol s' 1 = (pol (s v) 1).comp (C (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) * X)` using `fun v => by`.

Distinguish the cases in `hv : v ∈ S`. Take `⟨s', h1, h2, -⟩` from `suppTw K n (by omega) σ v χ (s v) (hs v hv).1`. Establish `hF` using `(polFacts (v.adicCompletion K)).2.2.2`. Use `⟨s', fun _ => ⟨h1, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← (hF s' 1).2.1, h2, (hF _ _).2.1, mul_one, cnt_unram _ (unram_loc (hval v).1)]`.

Rewrite using `[h2, mul_comm, (hF (s v) 1).2.2.2 _ (unram_loc (hval v).1), loc_unif (hval v).1, (hval v).2]`. Conclude with `⟨0, fun h => absurd h hv⟩`. Use `choose s' hs' using hex`. Take `⟨β, hβ, hP⟩` from `sideXCen K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) S hS (fun w => (B w).map (· * χ.val w)) (fun w hw => by`. Establish `h` using `(hB w hw).twist (hval w).1`.

Rewrite using `[CG.twist_mk] at h) s' q f hq` and apply the resulting hypothesis. Use the proof step `(fun v hv => ⟨(hs' v hv).1, fun h => (hs v hv).2 (by rwa [← (hs' v hv).2.1])⟩)`. Establish `hP2` using `pairGOps.2.2.2 _ _ _ _ _ z (by exact_mod_cast hq) hP`. Establish `e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w = (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)` using `fun w => by`. Simplify using `only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]`.

Establish `e' : cx (fun w => (B w).map (· * χ.val w)) = fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)` using `funext e`. Establish `e'' : (∏ v ∈ S, (pol (s' v) 1).comp (X ^ f v)).comp (C (((q : ℝ) : ℂ) ^ z) * X) = ∏ v ∈ S, (pol (s v) 1).comp (X ^ f v)`. Rewrite using `[Polynomial.prod_comp]`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hF` using `(polFacts (v.adicCompletion K)).2.2.2 (s v) 1`.

Rewrite using `[(hs' v hv).2.2]`. Conclude with `pol_shift _ _ q _ _ z hq hF.1 hF.2.1 (hs v hv).2`. Rewrite `hP2` using `[e', e'']`. Use `⟨β.comp (X - C z), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hβ` to reduce the goal to its premises. Use `congrArg (fun p => p.comp (X + C z)) h` as an intermediate fact. Simplify `this` using `[comp_assoc]`. Simplify `hP2` using `only [euler_shift, eulerd_shift]`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sideX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SideX := by
  intro K _ _ _ n hn σ S hS B hB s q f hq hs
  let x : GlobalTheory.ResW.Letter K := ⟨n, σ⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))
  let χ : HChar K := Model.absC K z
  have hspec := (GlobalTheory.ResW.letter_centralExponent K x).1
  have htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change lie K n (oneL K n) (mulChi n χ ψ) = 0
    rw [lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  have hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z) := fun v => by
    refine ⟨fun y hy => Units.ext ?_, ?_⟩
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (Formalism.L2.Host.unif v)))) = _
      have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
        ← Complex.natCast_log]
      congr 1; push_cast; ring
  have hex : ∀ v, ∃ s', v ∈ S → SuppAt (σ.twist χ) v s' ∧ cnt s' 1 = cnt (s v) 1 ∧
      pol s' 1 = (pol (s v) 1).comp (C (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) * X) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨s', h1, h2, -⟩ := suppTw K n (by omega) σ v χ (s v) (hs v hv).1
      have hF := (polFacts (v.adicCompletion K)).2.2.2
      refine ⟨s', fun _ => ⟨h1, ?_, ?_⟩⟩
      · rw [← (hF s' 1).2.1, h2, (hF _ _).2.1, mul_one, cnt_unram _ (unram_loc (hval v).1)]
      · rw [h2, mul_comm, (hF (s v) 1).2.2.2 _ (unram_loc (hval v).1), loc_unif (hval v).1, (hval v).2]
    · exact ⟨0, fun h => absurd h hv⟩
  choose s' hs' using hex
  obtain ⟨β, hβ, hP⟩ := sideXCen K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) S hS
    (fun w => (B w).map (· * χ.val w)) (fun w hw => by
      have h := (hB w hw).twist (hval w).1
      rwa [CG.twist_mk] at h) s' q f hq
    (fun v hv => ⟨(hs' v hv).1, fun h => (hs v hv).2 (by rwa [← (hs' v hv).2.1])⟩)
  have hP2 := pairGOps.2.2.2 _ _ _ _ _ z (by exact_mod_cast hq) hP
  have e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w =
      (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := fun w => by
    simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]
  have e' : cx (fun w => (B w).map (· * χ.val w)) =
      fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := funext e
  have e'' : (∏ v ∈ S, (pol (s' v) 1).comp (X ^ f v)).comp (C (((q : ℝ) : ℂ) ^ z) * X) =
      ∏ v ∈ S, (pol (s v) 1).comp (X ^ f v) := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hF := (polFacts (v.adicCompletion K)).2.2.2 (s v) 1
    rw [(hs' v hv).2.2]
    exact pol_shift _ _ q _ _ z hq hF.1 hF.2.1 (hs v hv).2
  rw [e', e''] at hP2
  refine ⟨β.comp (X - C z), ?_, ?_⟩
  · intro h
    apply hβ
    have := congrArg (fun p => p.comp (X + C z)) h
    simpa [comp_assoc] using this
  · simpa only [euler_shift, eulerd_shift] using hP2
