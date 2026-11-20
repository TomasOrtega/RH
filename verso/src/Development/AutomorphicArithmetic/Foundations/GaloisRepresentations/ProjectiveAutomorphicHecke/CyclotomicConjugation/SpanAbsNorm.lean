import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.KPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal GroundTheory.Global.IdeleGroup

namespace UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.CentralCharacterExamples

/- English proof (translation)
Establish `h` using `GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w y`. Establish `hm` using `GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)`. Rewrite `hm` using `[h]`. Establish `hm'` using `congrArg Subtype.val hm`. Rewrite `hm'` using `[GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]`.

Use `⟨_, ?_, fun f hf => GlobalTheory.LiftPolar.val_of_norm _ w _ y hm' f hf⟩` and prove the remaining obligations. Establish `h0 : Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y) = finiteEmbedding w y`. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Use `show (Units.val (GroundTheory.Global.ideleNorm K L (Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y)))).2 = _`.

Rewrite using `[h0, h]`. Both sides reduce to the same expression.
-/
private theorem fN_sgl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : Plc L) (y : (w.adicCompletion L)ˣ) : ∃ n : ((below K w).adicCompletion K)ˣ,
      ((fN K L (sgl w y) : (Af K)ˣ) : Af K) = finiteAdeleSingle (below K w) (n : (below K w).adicCompletion K) ∧
      ∀ f : ℕ, Ideal.absNorm w.asIdeal = Ideal.absNorm (below K w).asIdeal ^ f →
        Valued.v (n : (below K w).adicCompletion K) = Valued.v (y : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w y
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  refine ⟨_, ?_, fun f hf => GlobalTheory.LiftPolar.val_of_norm _ w _ y hm' f hf⟩
  have h0 : Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y) = finiteEmbedding w y := by
    apply Units.ext
    rfl
  show (Units.val (GroundTheory.Global.ideleNorm K L (Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y)))).2 = _
  rw [h0, h]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[finiteAdeleSingle_apply_self]`.
-/
private theorem v_single {K : Type} [Field K] [NumberField K] {v p : Plc K} (h : p = v) (n : v.adicCompletion K) :
    Valued.v (finiteAdeleSingle v n p) = Valued.v n := by
  subst h
  rw [finiteAdeleSingle_apply_self]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem v_nat {K : Type} [Field K] [NumberField K] {v p : Plc K} (h : p = v) (m : ℕ) :
    Valued.v ((m : ℕ) : p.adicCompletion K) = Valued.v ((m : ℕ) : v.adicCompletion K) := by
  subst h
  rfl

/- English proof (translation)
Set `e : 𝓞 ℚ ≃+* ℤ` to `Rat.ringOfIntegersEquiv`. Establish `h1 : Ideal.absNorm (b.asIdeal.map (e : 𝓞 ℚ →+* ℤ)) = Ideal.absNorm b.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv b.asIdeal _ e rfl).symm.toEquiv`. Establish `h2` using `Int.ideal_span_absNorm_eq_self (b.asIdeal.map (e : 𝓞 ℚ →+* ℤ))`.

Rewrite `h2` using `[h1]`. Establish `h3` using `Ideal.map_of_equiv (I := b.asIdeal) e`. Rewrite `h3` using `[← h2, Ideal.map_span, Set.image_singleton]`. Use `h3.symm.trans ?_` and prove the remaining obligations. Use `congr 2`.

Simplify using the standard rewrite rules.
-/
private theorem span_absNorm (b : Plc ℚ) :
    b.asIdeal = Ideal.span {((Ideal.absNorm b.asIdeal : ℕ) : 𝓞 ℚ)} := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have h1 : Ideal.absNorm (b.asIdeal.map (e : 𝓞 ℚ →+* ℤ)) = Ideal.absNorm b.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv b.asIdeal _ e rfl).symm.toEquiv
  have h2 := Int.ideal_span_absNorm_eq_self (b.asIdeal.map (e : 𝓞 ℚ →+* ℤ))
  rw [h1] at h2
  have h3 := Ideal.map_of_equiv (I := b.asIdeal) e
  rw [← h2, Ideal.map_span, Set.image_singleton] at h3
  refine h3.symm.trans ?_
  congr 2
  simp

/- English proof (translation)
Establish `h` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (m : 𝓞 ℚ)`. Establish `h2 : HeightOneSpectrum.valuation ℚ v (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) = v.intValuation (m : 𝓞 ℚ)` using `HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v _`. Use `Eq.trans ?_ (h.trans h2)` and prove the remaining obligations. Use `congr 1`. Simplify using the standard rewrite rules.
-/
private theorem v_nat_int (v : Plc ℚ) (m : ℕ) :
    Valued.v ((m : ℕ) : v.adicCompletion ℚ) = v.intValuation (m : 𝓞 ℚ) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (m : 𝓞 ℚ)
  have h2 : HeightOneSpectrum.valuation ℚ v (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) = v.intValuation (m : 𝓞 ℚ) :=
    HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v _
  refine Eq.trans ?_ (h.trans h2)
  congr 1
  simp

/- English proof (translation)
Rewrite using `[v_nat_int]`. Use `HeightOneSpectrum.intValuation_singleton b ?_ (span_absNorm b)` and prove the remaining obligations. Introduce `h`. Use `span_absNorm b` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `b.ne_bot (by simpa using this)`.
-/
private theorem v_nat_self (b : Plc ℚ) :
    Valued.v ((Ideal.absNorm b.asIdeal : ℕ) : b.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [v_nat_int]
  refine HeightOneSpectrum.intValuation_singleton b ?_ (span_absNorm b)
  intro h
  have := span_absNorm b
  rw [h] at this
  exact b.ne_bot (by simpa using this)

/- English proof (translation)
Rewrite using `[v_nat_int, HeightOneSpectrum.intValuation_eq_one_iff]`. Introduce `hm`. Establish `hle : b.asIdeal ≤ v.asIdeal`. Rewrite using `[span_absNorm b]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 (by simpa using hm)`.

Conclude with `h (HeightOneSpectrum.ext (b.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)`.
-/
private theorem v_nat_ne {b v : Plc ℚ} (h : v ≠ b) :
    Valued.v ((Ideal.absNorm b.asIdeal : ℕ) : v.adicCompletion ℚ) = 1 := by
  rw [v_nat_int, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hm
  have hle : b.asIdeal ≤ v.asIdeal := by
    rw [span_absNorm b]
    exact (Ideal.span_singleton_le_iff_mem _).2 (by simpa using hm)
  exact h (HeightOneSpectrum.ext (b.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

end UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.CentralCharacterExamples

namespace UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.CentralCharacterExamples

/- English proof (translation)
Take `⟨m, hm, hv⟩` from `fN_sgl ℚ K P y`. Establish `hN : Ideal.absNorm P.asIdeal = Ideal.absNorm (below ℚ P).asIdeal ^ P.asIdeal.inertiaDeg (𝓞 ℚ)` using `GlobalTheory.LiftPolar.normV_under (K := ℚ) P`. Establish `e1 : Valued.v ((Ideal.absNorm (below ℚ P).asIdeal : ℕ) : P.adicCompletion K) = WithZero.exp (-1 : ℤ) ^ P.asIdeal.ramificationIdx (𝓞 ℚ)`. Rewrite using `[← map_natCast (completionMap (below ℚ P) P), valued_completionMap, v_nat_self]`. Establish `e2` using `hP`.

Rewrite `e2` using `[hN, Nat.cast_pow, map_pow, e1, ← pow_mul, ← WithZero.exp_nsmul, WithZero.exp_inj]`. Establish `e3 : P.asIdeal.ramificationIdx (𝓞 ℚ) * P.asIdeal.inertiaDeg (𝓞 ℚ) = 1`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one] at e2`. Use linear arithmetic over natural numbers and integers. Establish `e4` using `Nat.eq_one_of_mul_eq_one_right e3`.

Establish `e5` using `Nat.eq_one_of_mul_eq_one_left e3`. Rewrite using `[hm]`. Distinguish the cases in `h : v = below ℚ P`. Rewrite using `[v_single h, hv _ hN, hy, v_nat h, hN, e5, pow_one, pow_one, Nat.cast_pow, Nat.cast_pow, map_pow, map_pow, e1, v_nat_self, e4, pow_one]`. Rewrite using `[finiteAdeleSingle_apply_of_ne h, map_one, hN, ← pow_mul, Nat.cast_pow, map_pow, v_nat_ne h, one_pow]`.
-/
private theorem sim_val {K : Type} [Field K] [NumberField K] [Algebra ℚ K] (P : Plc K)
    (hP : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (y : (P.adicCompletion K)ˣ) (g : ℕ)
    (hy : (y : P.adicCompletion K) = ((Ideal.absNorm P.asIdeal ^ g : ℕ) : P.adicCompletion K)) (v : Plc ℚ) :
    Valued.v (((fN ℚ K (sgl P y) : (Af ℚ)ˣ) : Af ℚ) v) =
      Valued.v ((Ideal.absNorm P.asIdeal ^ g : ℕ) : v.adicCompletion ℚ) := by
  obtain ⟨m, hm, hv⟩ := fN_sgl ℚ K P y
  have hN : Ideal.absNorm P.asIdeal = Ideal.absNorm (below ℚ P).asIdeal ^ P.asIdeal.inertiaDeg (𝓞 ℚ) :=
    GlobalTheory.LiftPolar.normV_under (K := ℚ) P
  have e1 : Valued.v ((Ideal.absNorm (below ℚ P).asIdeal : ℕ) : P.adicCompletion K) =
      WithZero.exp (-1 : ℤ) ^ P.asIdeal.ramificationIdx (𝓞 ℚ) := by
    rw [← map_natCast (completionMap (below ℚ P) P), valued_completionMap, v_nat_self]
  have e2 := hP
  rw [hN, Nat.cast_pow, map_pow, e1, ← pow_mul, ← WithZero.exp_nsmul, WithZero.exp_inj] at e2
  have e3 : P.asIdeal.ramificationIdx (𝓞 ℚ) * P.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
    simp only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one] at e2
    omega
  have e4 := Nat.eq_one_of_mul_eq_one_right e3
  have e5 := Nat.eq_one_of_mul_eq_one_left e3
  rw [hm]
  by_cases h : v = below ℚ P
  · rw [v_single h, hv _ hN, hy, v_nat h, hN, e5, pow_one, pow_one, Nat.cast_pow, Nat.cast_pow, map_pow, map_pow, e1, v_nat_self, e4, pow_one]
  · rw [finiteAdeleSingle_apply_of_ne h, map_one, hN, ← pow_mul, Nat.cast_pow, map_pow, v_nat_ne h, one_pow]

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[← hy]`. Conclude with `finiteAdeleSingle_apply_self p _`.
-/
private theorem sgl_eq {K : Type} [Field K] [NumberField K] {P p : Plc K} (h : p = P) (y : (P.adicCompletion K)ˣ) (c : ℕ)
    (hy : (y : P.adicCompletion K) = (c : P.adicCompletion K)) :
    ((sgl P y : (Af K)ˣ) : Af K) p = (c : p.adicCompletion K) := by
  subst h
  rw [← hy]
  exact finiteAdeleSingle_apply_self p _

/- English proof (translation)
The claim follows from `finiteAdeleSingle_apply_of_ne h _`.
-/
private theorem sgl_ne {K : Type} [Field K] [NumberField K] {P p : Plc K} (h : p ≠ P) (y : (P.adicCompletion K)ˣ) :
    ((sgl P y : (Af K)ˣ) : Af K) p = 1 :=
  finiteAdeleSingle_apply_of_ne h _

/- English proof (translation)
Establish `h : (c : P.adicCompletion K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap K (P.adicCompletion K))]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 hc)`. Conclude with `⟨Units.mk0 _ h, rfl⟩`.
-/
private theorem unit_nat {K : Type} [Field K] [NumberField K] (P : Plc K) (c : ℕ) (hc : c ≠ 0) :
    ∃ y : (P.adicCompletion K)ˣ, (y : P.adicCompletion K) = (c : P.adicCompletion K) := by
  have h : (c : P.adicCompletion K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (P.adicCompletion K))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hc)
  exact ⟨Units.mk0 _ h, rfl⟩

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, h, Matrix.one_apply]`.
-/
private theorem scalar_val {A : Type} [CommRing A] (n : ℕ) (t : Aˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : A) • (1 : Matrix (Fin n) (Fin n) A) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, h, Matrix.one_apply]

/- English proof (translation)
Use `mem_Sim.2 ?_` and prove the remaining obligations. Rewrite using `[scalar_val, ← h]`. Use extensionality with `a b`. Apply the tactic sequence `by_cases e : a = b <;> simp [e, Matrix.one_apply, Matrix.mul_apply, apply_ite σ, eq_comm]`.
-/
private theorem sim_scalar {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) (t : Aˣ) (s : Bˣ)
    (h : σ t * t = i s) : (GeneralLinearGroup.scalar (Fin n) t, s) ∈ Sim σ i n := by
  refine mem_Sim.2 ?_
  rw [scalar_val, ← h]
  ext a b
  by_cases e : a = b <;> simp [e, Matrix.one_apply, Matrix.mul_apply, apply_ite σ, eq_comm]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[scalar_val]`. Use extensionality with `i j : 1`. Express the relevant statement in the definitionally equal form `pLoc E u ((GeneralLinearGroup.scalar (Fin n) t).val i j) = _`. Rewrite using `[scalar_val]`.

Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply]`.
-/
private theorem comp_mk {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (t : (Af E)ˣ) (s : AfQˣ)
    (h : (GeneralLinearGroup.scalar (Fin n) t, s) ∈ GUf E n) (u : Plc E) :
    comp u (⟨_, h⟩ : GUf E n) = GeneralLinearGroup.scalar (Fin n) (Units.map (pLoc E u).toMonoidHom t) := by
  refine Units.ext ?_
  rw [scalar_val]
  ext i j : 1
  change pLoc E u ((GeneralLinearGroup.scalar (Fin n) t).val i j) = _
  rw [scalar_val]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

end UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.CentralCharacterExamples

open UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.CentralCharacterExamples in
/- English proof (translation)
Introduce `E _ _ _ n d x hd hx w`. Take `⟨k1, k2⟩` from `kPlace E d x hd hx`. Establish `hc : Ideal.absNorm w.asIdeal ≠ 0` using `fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Take `⟨y, hy⟩` from `unit_nat (w.under (𝓞 (Kx x))) _ hc`. Set `a : (Af (Kx x))ˣ` to `sgl (w.under (𝓞 (Kx x))) y`.

Set `t : (Af E)ˣ` to `Units.map ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).toMonoidHom a`. Establish `hm : (GeneralLinearGroup.scalar (Fin n) t, fN ℚ (Kx x) a) ∈ GUf E n` using `sim_scalar _ _ n _ _ (by`. Express the relevant statement in the definitionally equal form `conjFin (conjE E) (conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x)))) * conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x))) = _`. Rewrite using `[(conjLoc E _ w).2.2.2.1]`. Conclude with `quadConj E d x hd hx a)`.

Use `⟨⟨_, hm⟩, fun u => ⟨fun h => ?_, fun h => ?_⟩, fun g => ?_, fun h v => ?_⟩` and prove the remaining obligations. Rewrite using `[comp_mk, scalar_val]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `pLoc E u (conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x)))) = _`. Rewrite using `[pLoc_conjFin]`.

Express the relevant statement in the definitionally equal form `GlobalTheory.CuspRep.conjLoc (conjE E) u (finiteAdeleMap (Kx x) E (a : Af (Kx x)) (cj u)) = _`. Establish `ha : (a : Af (Kx x)) (below (Kx x) (cj u)) = ((Ideal.absNorm w.asIdeal : ℕ) : (below (Kx x) (cj u)).adicCompletion (Kx x))` using `sgl_eq ((k1 _ _).1 h) y _ hy`. Rewrite using `[finiteAdeleMap_apply, ha, map_natCast, map_natCast]`. Establish `ha : (a : Af (Kx x)) (below (Kx x) (cj u)) = 1` using `sgl_ne (fun e => h ((k1 _ _).2 e)) y`. Establish `h1 : Units.map (pLoc E u).toMonoidHom t = 1` using `Units.ext ((conjLoc E _ u).1 (by`.

Rewrite using `[finiteAdeleMap_apply, ha, map_one]))`. Rewrite using `[comp_mk, h1, map_one]`. Use `Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GeneralLinearGroup.scalar (Fin n) t).val * _ = _ * (GeneralLinearGroup.scalar (Fin n) t).val`. Rewrite using `[scalar_val, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]`.

Establish `hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 (Kx x))).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 (Kx x))` using `GlobalTheory.LiftPolar.normV_under (K := Kx x) w`. Use `sim_val (w.under (𝓞 (Kx x))) (k2 w h) y _ (by rw [← hN, hy]) v` as an intermediate fact. Rewrite `this` using `[← hN]`. Conclude with `this`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.cenEx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) → ∀ w : Plc E,
          ∃ z : GUf E n, IsCen x w z ∧ (∀ g, z * g = g * z) ∧ (¬ SameK x (cj w) w → ∀ v : Plc ℚ,
            Valued.v (((sim z : AfQˣ) : AfQ) v) = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : v.adicCompletion ℚ)) := by
  intro E _ _ _ n d x hd hx w
  obtain ⟨k1, k2⟩ := kPlace E d x hd hx
  have hc : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨y, hy⟩ := unit_nat (w.under (𝓞 (Kx x))) _ hc
  let a : (Af (Kx x))ˣ := sgl (w.under (𝓞 (Kx x))) y
  let t : (Af E)ˣ := Units.map ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).toMonoidHom a
  have hm : (GeneralLinearGroup.scalar (Fin n) t, fN ℚ (Kx x) a) ∈ GUf E n := sim_scalar _ _ n _ _ (by
    change conjFin (conjE E) (conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x)))) *
      conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x))) = _
    rw [(conjLoc E _ w).2.2.2.1]
    exact quadConj E d x hd hx a)
  refine ⟨⟨_, hm⟩, fun u => ⟨fun h => ?_, fun h => ?_⟩, fun g => ?_, fun h v => ?_⟩
  · rw [comp_mk, scalar_val]
    congr 1
    change pLoc E u (conjFin (conjE E) (finiteAdeleMap (Kx x) E (a : Af (Kx x)))) = _
    rw [pLoc_conjFin]
    change GlobalTheory.CuspRep.conjLoc (conjE E) u (finiteAdeleMap (Kx x) E (a : Af (Kx x)) (cj u)) = _
    have ha : (a : Af (Kx x)) (below (Kx x) (cj u)) = ((Ideal.absNorm w.asIdeal : ℕ) : (below (Kx x) (cj u)).adicCompletion (Kx x)) :=
      sgl_eq ((k1 _ _).1 h) y _ hy
    rw [finiteAdeleMap_apply, ha, map_natCast, map_natCast]
  · have ha : (a : Af (Kx x)) (below (Kx x) (cj u)) = 1 := sgl_ne (fun e => h ((k1 _ _).2 e)) y
    have h1 : Units.map (pLoc E u).toMonoidHom t = 1 := Units.ext ((conjLoc E _ u).1 (by
      rw [finiteAdeleMap_apply, ha, map_one]))
    rw [comp_mk, h1, map_one]
  · refine Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))
    change (GeneralLinearGroup.scalar (Fin n) t).val * _ = _ * (GeneralLinearGroup.scalar (Fin n) t).val
    rw [scalar_val, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 (Kx x))).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 (Kx x)) :=
      GlobalTheory.LiftPolar.normV_under (K := Kx x) w
    have := sim_val (w.under (𝓞 (Kx x))) (k2 w h) y _ (by rw [← hN, hy]) v
    rw [← hN] at this
    exact this
