import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

/- English proof (translation)
Use `eq_of_castHom_ordProj_eq (NeZero.ne N) fun p hp ↦ ?_` and prove the remaining obligations. Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors hp`. Establish `hv : prime (placeOf ⟨p, hpp⟩) = p` using `prime_placeOf ⟨p, hpp⟩`. Establish `hdvd : prime (placeOf ⟨p, hpp⟩) ∣ N`. Rewrite using `[hv]`.

Conclude with `Nat.dvd_of_mem_primeFactors hp`. Establish `h'` using `h (placeOf ⟨p, hpp⟩) hdvd`. Use `clear hdvd`. Generalize the expression as in `placeOf ⟨p, hpp⟩ = v at hv h'`. Substitute `hv` using the available equality.

Rewrite `h'` using `[toZModPow_toPadicInt]`. Rewrite using `[← h']`. Conclude with `ProfiniteInteger.castHom_proj (m := primePowPNat (prime v) (N.factorization (prime v))) (n := modulus N) (Nat.ordProj_dvd N (prime v)) z`.
-/
theorem proj_eq_of_forall {N : ℕ} [NeZero N] {z : ℤ̂} {a : ZMod N}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), prime v ∣ N →
      PadicInt.toZModPow (N.factorization (prime v)) (toPadicInt (prime v) z) =
        ZMod.castHom (Nat.ordProj_dvd N (prime v)) _ a) :
    ProfiniteInteger.proj (modulus N) z = a := by
  refine eq_of_castHom_ordProj_eq (NeZero.ne N) fun p hp ↦ ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hv : prime (placeOf ⟨p, hpp⟩) = p := prime_placeOf ⟨p, hpp⟩
  have hdvd : prime (placeOf ⟨p, hpp⟩) ∣ N := by
    rw [hv]
    exact Nat.dvd_of_mem_primeFactors hp
  have h' := h (placeOf ⟨p, hpp⟩) hdvd
  clear hdvd
  generalize placeOf ⟨p, hpp⟩ = v at hv h'
  subst hv
  rw [toZModPow_toPadicInt] at h'
  rw [← h']
  exact ProfiniteInteger.castHom_proj (m := primePowPNat (prime v) (N.factorization (prime v)))
    (n := modulus N) (Nat.ordProj_dvd N (prime v)) z

/- English proof (translation)
Take `⟨y, hy, hyx⟩` from `(Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn ((PadicInt.mem_subring_iff _).2 hx)`. Establish `: y = x` using `(padicRingEquiv v).injective hyx`. Conclude with `this ▸ hy`.
-/
theorem mem_adicCompletionIntegers_of_norm_le (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ}
    (hx : ‖padicRingEquiv v x‖ ≤ 1) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, hy, hyx⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn
    ((PadicInt.mem_subring_iff _).2 hx)
  have : y = x := (padicRingEquiv v).injective hyx
  exact this ▸ hy

/- English proof (translation)
Use `RationalIdeles.mem_positiveSubgroup.2 ⟨(mem_standardOpenSubgroup ℚ).2 fun w ↦ ⟨?_, ?_⟩, hre⟩` and prove the remaining obligations. Rewrite using `[← coe_finiteProj]`. Conclude with `mem_adicCompletionIntegers_of_norm_le w (hfin w).le`. Rewrite using `[← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]`. Use `mem_adicCompletionIntegers_of_norm_le w ?_` and prove the remaining obligations.

Rewrite using `[map_inv₀, norm_inv, hfin w, inv_one]`.
-/
theorem mem_positiveSubgroup_of {x : IdeleGroup ℚ}
    (hfin : ∀ w : HeightOneSpectrum (𝓞 ℚ), ‖padicRingEquiv w (finiteProj w x : w.adicCompletion ℚ)‖ = 1)
    (hre : 0 < (RationalIdeles.realPart x : ℝ)) : x ∈ RationalIdeles.positiveSubgroup := by
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(mem_standardOpenSubgroup ℚ).2 fun w ↦ ⟨?_, ?_⟩, hre⟩
  · rw [← coe_finiteProj]
    exact mem_adicCompletionIntegers_of_norm_le w (hfin w).le
  · rw [← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]
    refine mem_adicCompletionIntegers_of_norm_le w ?_
    rw [map_inv₀, norm_inv, hfin w, inv_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom (toInfinite ℚ (finiteEmbedding v a)) = 1`. Rewrite using `[toInfinite_finiteEmbedding, map_one]`.
-/
theorem realPart_finiteEmbedding (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ) :
    RationalIdeles.realPart (finiteEmbedding v a) = 1 := by
  change RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom (toInfinite ℚ (finiteEmbedding v a)) = 1
  rw [toInfinite_finiteEmbedding, map_one]

/- English proof (translation)
Rewrite using `[padicRingEquiv_finiteProj, pow_zero, mul_one]`.
-/
theorem coe_unitAt (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((unitAt y v : ℤ_[prime v]ˣ) : ℤ_[prime v]) : ℚ_[prime v]) =
      padicRingEquiv v (finiteProj v (y : IdeleGroup ℚ) : v.adicCompletion ℚ) := by
  rw [padicRingEquiv_finiteProj, pow_zero, mul_one]

/- English proof (translation)
Establish `h' : Units.map (toPadicInt (prime v)).toMonoidHom (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v` using `Units.ext (toPadicInt_unitPart_mk y v)`. Rewrite using `[← h', Units.coe_map_inv]`. Both sides reduce to the same expression.
-/
theorem toPadicInt_unitPart_inv_mk (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPadicInt (prime v) (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) =
      (((unitAt y v)⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v]) := by
  have h' : Units.map (toPadicInt (prime v)).toMonoidHom
      (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v :=
    Units.ext (toPadicInt_unitPart_mk y v)
  rw [← h', Units.coe_map_inv]
  rfl

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Rewrite using `[coe_heckeCharacter_apply, proj_eq_of_forall fun v hv ↦ by`. Rewrite using `[toPadicInt_unitPart_inv_mk]`. Conclude with `h v hv]`.
-/
theorem coe_heckeCharacter_mk_of_forall (y : RationalIdeles.positiveSubgroup) {a : ZMod N}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), prime v ∣ N →
      PadicInt.toZModPow (N.factorization (prime v)) (((unitAt y v)⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v]) =
        ZMod.castHom (Nat.ordProj_dvd N (prime v)) _ a) :
    (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ a := by
  rw [coe_heckeCharacter_apply, proj_eq_of_forall fun v hv ↦ by
    rw [toPadicInt_unitPart_inv_mk]
    exact h v hv]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(Submonoid.mem_units_iff _ _).1 ha`. Establish `n1 : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ ≤ 1` using `(PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h1)`. Establish `n2 : ‖padicRingEquiv v ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≤ 1` using `(PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h2)`. Rewrite `n2` using `[Units.val_inv_eq_inv_val, map_inv₀, norm_inv]`. Establish `hpos : 0 < ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖` using `norm_pos_iff.2 ((map_ne_zero _).2 a.ne_zero)`.

Conclude with `le_antisymm n1 ((inv_le_one₀ hpos).1 n2)`.
-/
theorem norm_padicRingEquiv_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers ℚ)).units) :
    ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 := by
  obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 ha
  have n1 : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h1)
  have n2 : ‖padicRingEquiv v ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h2)
  rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv] at n2
  have hpos : 0 < ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ :=
    norm_pos_iff.2 ((map_ne_zero _).2 a.ne_zero)
  exact le_antisymm n1 ((inv_le_one₀ hpos).1 n2)

/- English proof (translation)
Establish `h2 : ‖padicRingEquiv v ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≤ 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, norm_inv, ha, inv_one]`. Conclude with `(Submonoid.mem_units_iff _ _).2 ⟨mem_adicCompletionIntegers_of_norm_le v ha.le, mem_adicCompletionIntegers_of_norm_le v h2⟩`.
-/
theorem mem_units_of_norm_padicRingEquiv_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (ha : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1) :
    a ∈ (Submonoid.ofClass (v.adicCompletionIntegers ℚ)).units := by
  have h2 : ‖padicRingEquiv v ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv, ha, inv_one]
  exact (Submonoid.mem_units_iff _ _).2
    ⟨mem_adicCompletionIntegers_of_norm_le v ha.le, mem_adicCompletionIntegers_of_norm_le v h2⟩

/- English proof (translation)
Use `mem_positiveSubgroup_of (fun w ↦ ?_) (by rw [realPart_finiteEmbedding, Units.val_one]; exact one_pos)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[finiteProj_finiteEmbedding]`. Conclude with `ha`.

Rewrite using `[finiteProj_finiteEmbedding_of_ne hw, Units.val_one, map_one, norm_one]`.
-/
theorem finiteEmbedding_mem_positiveSubgroup {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (ha : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1) :
    finiteEmbedding v a ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w ↦ ?_) (by rw [realPart_finiteEmbedding, Units.val_one]; exact one_pos)
  by_cases hw : w = v
  · subst hw
    rw [finiteProj_finiteEmbedding]
    exact ha
  · rw [finiteProj_finiteEmbedding_of_ne hw, Units.val_one, map_one, norm_one]

/- English proof (translation)
The claim follows from `Units.ext (Subtype.ext (by rw [coe_unitAt, h, Units.val_one, map_one, Units.val_one, PadicInt.coe_one]))`.
-/
theorem unitAt_eq_one {y : RationalIdeles.positiveSubgroup} {w : HeightOneSpectrum (𝓞 ℚ)}
    (h : finiteProj w (y : IdeleGroup ℚ) = 1) : unitAt y w = 1 :=
  Units.ext (Subtype.ext (by rw [coe_unitAt, h, Units.val_one, map_one, Units.val_one, PadicInt.coe_one]))

/- English proof (translation)
Use `Circle.ext ?_` and prove the remaining obligations. Rewrite using `[Circle.coe_one, ← map_one χ]`. Use `coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha⟩ fun w hw ↦ ?_` and prove the remaining obligations. Establish `hwv : w ≠ v` using `fun h ↦ hv (h ▸ hw)`. Rewrite using `[unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one, map_one]`.
-/
theorem heckeCharacter_finiteEmbedding_of_not_dvd {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N)
    {a : (v.adicCompletion ℚ)ˣ} (ha : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1) :
    heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v a)) = 1 := by
  refine Circle.ext ?_
  rw [Circle.coe_one, ← map_one χ]
  refine coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha⟩ fun w hw ↦ ?_
  have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
  rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one, map_one]

/- English proof (translation)
The claim follows from `((heckeCharacter χ).not_dvd_conductor_iff v).2 fun _ ha ↦ heckeCharacter_finiteEmbedding_of_not_dvd χ hv (norm_padicRingEquiv_eq_one ha)`.
-/
theorem not_dvd_conductor_of_not_dvd {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N) :
    ¬ v.asIdeal ∣ (heckeCharacter χ).conductor :=
  ((heckeCharacter χ).not_dvd_conductor_iff v).2 fun _ ha ↦
    heckeCharacter_finiteEmbedding_of_not_dvd χ hv (norm_padicRingEquiv_eq_one ha)

def uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ :=
  finiteProj v (diagonal ℚ (primeRat v))

/- English proof (translation)
Establish `h` using `Rat.HeightOneSpectrum.span_natGenerator v`. Establish `h' : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm` using `(Ideal.map_of_equiv _).symm`. Rewrite using `[h', ← h, Ideal.map_span, Set.image_singleton, map_natCast]`. Both sides reduce to the same expression.
-/
theorem asIdeal_eq_span (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((prime v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  have h' : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).map
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := (Ideal.map_of_equiv _).symm
  rw [h', ← h, Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

/- English proof (translation)
Rewrite using `[uniformizer, coe_finiteProj_diagonal, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', coe_primeRat, show ((prime v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((prime v : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_singleton _ (Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero) (asIdeal_eq_span v)`.
-/
theorem valued_uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (uniformizer v : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [uniformizer, coe_finiteProj_diagonal, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    coe_primeRat, show ((prime v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((prime v : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _
    (Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero) (asIdeal_eq_span v)

/- English proof (translation)
Use `mem_positiveSubgroup_of (fun w ↦ ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[map_mul, map_inv, finiteProj_finiteEmbedding, uniformizer, inv_mul_cancel, Units.val_one, map_one, norm_one]`. Rewrite using `[map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hw, mul_one, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, padicRingEquiv_finiteProj_diagonal, coe_primeRat, Rat.cast_natCast, Padic.norm_natCast_eq_one_iff.2 (coprime_prime hw), inv_one]`.

Rewrite using `[map_mul, map_inv, realPart_finiteEmbedding, mul_one, Units.val_inv_eq_inv_val, RationalIdeles.realPart_diagonal, coe_primeRat]`. Conclude with `inv_pos.2 (by exact_mod_cast (Fact.out : (prime v).Prime).pos)`.
-/
theorem frobIdele_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    (diagonal ℚ (primeRat v))⁻¹ * finiteEmbedding v (uniformizer v) ∈
      RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w ↦ ?_) ?_
  · by_cases hw : w = v
    · subst hw
      rw [map_mul, map_inv, finiteProj_finiteEmbedding, uniformizer, inv_mul_cancel, Units.val_one,
        map_one, norm_one]
    · rw [map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hw, mul_one, Units.val_inv_eq_inv_val,
        map_inv₀, norm_inv, padicRingEquiv_finiteProj_diagonal, coe_primeRat, Rat.cast_natCast,
        Padic.norm_natCast_eq_one_iff.2 (coprime_prime hw), inv_one]
  · rw [map_mul, map_inv, realPart_finiteEmbedding, mul_one, Units.val_inv_eq_inv_val,
      RationalIdeles.realPart_diagonal, coe_primeRat]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : (prime v).Prime).pos)

/- English proof (translation)
Set `y : RationalIdeles.positiveSubgroup` to `⟨_, frobIdele_mem v⟩`. Establish `hmk : IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)) = IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)` using `by show _ = IdeleClassGroup.mk ℚ ((diagonal ℚ (primeRat v))⁻¹ * finiteEmbedding v (uniformizer v))`. Rewrite using `[map_mul, map_inv, IdeleClassGroup.mk_diagonal, inv_one]`. Conclude with `(one_mul (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)))).symm`. Rewrite using `[hmk]`.

Use `proj_eq_of_forall fun w hw ↦ ?_` and prove the remaining obligations. Establish `hwv : w ≠ v` using `fun h ↦ hv (h ▸ hw)`. Establish `e1 : (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = ((prime v : ℚ_[prime w]))⁻¹`. Rewrite using `[coe_unitAt]`. Simplify using `only [y, map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hwv, mul_one, Units.val_inv_eq_inv_val, map_inv₀, padicRingEquiv_finiteProj_diagonal, coe_primeRat, Rat.cast_natCast]`.

Establish `e2 : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) * (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = 1`. Rewrite using `[← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]`. Establish `hp0 : (prime v : ℚ_[prime w]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero`. Establish `hu : (((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) = (prime v : ℤ_[prime w])`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite `e2` using `[e1]`. Rewrite using `[PadicInt.coe_natCast]`. Conclude with `(mul_inv_eq_one₀ hp0).1 e2`. Rewrite using `[toPadicInt_unitPart_inv_mk, hu, map_natCast, map_natCast]`.
-/
theorem proj_unitPart_inv_uniformizer {N : ℕ} [NeZero N] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬ prime v ∣ N) :
    ProfiniteInteger.proj (modulus N)
      (((unitPart (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v))))⁻¹ : ℤ̂ˣ) : ℤ̂) =
      (prime v : ZMod N) := by
  let y : RationalIdeles.positiveSubgroup := ⟨_, frobIdele_mem v⟩
  have hmk : IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)) =
      IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ) := by
    show _ = IdeleClassGroup.mk ℚ ((diagonal ℚ (primeRat v))⁻¹ * finiteEmbedding v (uniformizer v))
    rw [map_mul, map_inv, IdeleClassGroup.mk_diagonal, inv_one]
    exact (one_mul (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)))).symm
  rw [hmk]
  refine proj_eq_of_forall fun w hw ↦ ?_
  have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
  have e1 : (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = ((prime v : ℚ_[prime w]))⁻¹ := by
    rw [coe_unitAt]
    simp only [y, map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hwv, mul_one,
      Units.val_inv_eq_inv_val, map_inv₀, padicRingEquiv_finiteProj_diagonal, coe_primeRat,
      Rat.cast_natCast]
  have e2 : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
      (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  have hp0 : (prime v : ℚ_[prime w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero
  have hu : (((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) = (prime v : ℤ_[prime w]) := by
    apply Subtype.ext
    rw [e1] at e2
    rw [PadicInt.coe_natCast]
    exact (mul_inv_eq_one₀ hp0).1 e2
  rw [toPadicInt_unitPart_inv_mk, hu, map_natCast, map_natCast]

/- English proof (translation)
Rewrite using `[coe_heckeCharacter_apply, proj_unitPart_inv_uniformizer hv]`.
-/
theorem coe_heckeCharacter_uniformizer {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N) :
    (heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v))) : ℂ) = χ (prime v) := by
  rw [coe_heckeCharacter_apply, proj_unitPart_inv_uniformizer hv]

/- English proof (translation)
Rewrite using `[(heckeCharacter χ).idealCharacter_primeIdealUnit (not_dvd_conductor_of_not_dvd χ hv) (valued_uniformizer v)]`. Conclude with `coe_heckeCharacter_uniformizer χ hv`.
-/
theorem coe_idealCharacter_primeIdealUnit {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N) :
    ((heckeCharacter χ).idealCharacter
      ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo (not_dvd_conductor_of_not_dvd χ hv)⟩ : ℂ) =
      χ (prime v) := by
  rw [(heckeCharacter χ).idealCharacter_primeIdealUnit (not_dvd_conductor_of_not_dvd χ hv)
    (valued_uniformizer v)]
  exact coe_heckeCharacter_uniformizer χ hv

/- English proof (translation)
Establish `e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1`. Rewrite using `[← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]`. Rewrite `e` using `[h]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[PadicInt.coe_natCast]`.

Conclude with `(mul_inv_eq_one₀ hm).1 e`.
-/
theorem coe_inv_eq_natCast {p : ℕ} [Fact p.Prime] {u : ℤ_[p]ˣ} {m : ℕ} (hm : (m : ℚ_[p]) ≠ 0)
    (h : ((u : ℤ_[p]) : ℚ_[p]) = (m : ℚ_[p])⁻¹) : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = m := by
  have e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  rw [h] at e
  apply Subtype.ext
  rw [PadicInt.coe_natCast]
  exact (mul_inv_eq_one₀ hm).1 e

/- English proof (translation)
Use `set m : ℕ := (b : ZMod N).val with hm`. Establish `hcop : (prime v).Coprime m` using `(Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm`. Establish `hnm : ‖(m : ℚ_[prime v])‖ = 1` using `Padic.norm_natCast_eq_one_iff.2 hcop`. Establish `hm0 : (m : ℚ_[prime v]) ≠ 0` using `norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)`. Set `a : (v.adicCompletion ℚ)ˣ` to `Units.map (padicRingEquiv v).symm.toMonoidHom (Units.mk0 (m : ℚ_[prime v]) hm0)⁻¹`.

Establish `ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (m : ℚ_[prime v])⁻¹`. Simplify using `only [a, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]`. Conclude with `RingEquiv.apply_symm_apply _ _`. Establish `hnorm : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1` using `by rw [ha, norm_inv, hnm, inv_one]`. Use `⟨a, hnorm, coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ fun w hw ↦ ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Establish `hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = (m : ℚ_[prime w])⁻¹`. Rewrite using `[coe_unitAt]`. Express the relevant statement in the definitionally equal form `padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _`.

Rewrite using `[finiteProj_finiteEmbedding, ha]`. Rewrite using `[coe_inv_eq_natCast hm0 hu, map_natCast]`. Use `conv_rhs => rw [← ZMod.natCast_zmod_val (b : ZMod N), ← hm]`. Rewrite using `[map_natCast]`. Rewrite using `[unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]`.

Establish `hcp : Nat.Coprime (prime w ^ N.factorization (prime w)) (prime v ^ N.factorization (prime v))` using `Nat.Coprime.pow _ _ (coprime_prime hwv)`. Establish `h1 : prime w ^ N.factorization (prime w) ∣ prime v ^ N.factorization (prime v) * (N / prime v ^ N.factorization (prime v))`. Rewrite using `[Nat.ordProj_mul_ordCompl_eq_self]`. Conclude with `Nat.ordProj_dvd _ _`. Establish `hdvd` using `hcp.dvd_of_dvd_mul_left h1`.

Rewrite using `[← castHom_castHom hdvd (Nat.ordCompl_dvd N (prime v)) (Nat.ordProj_dvd N (prime w))]`. Establish `hb' : ZMod.castHom (Nat.ordCompl_dvd N (prime v)) (ZMod (N / prime v ^ N.factorization (prime v))) (b : ZMod N) = 1` using `congrArg Units.val hb`. Rewrite using `[hb', map_one]`.
-/
theorem exists_coe_heckeCharacter_finiteEmbedding {v : HeightOneSpectrum (𝓞 ℚ)} (hv : prime v ∣ N)
    (b : (ZMod N)ˣ) (hb : ZMod.unitsMap (Nat.ordCompl_dvd N (prime v)) b = 1) :
    ∃ a : (v.adicCompletion ℚ)ˣ, ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 ∧
      (heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v a)) : ℂ) = χ b := by
  set m : ℕ := (b : ZMod N).val with hm
  have hcop : (prime v).Coprime m :=
    (Nat.Coprime.coprime_dvd_right hv (ZMod.val_coe_unit_coprime b)).symm
  have hnm : ‖(m : ℚ_[prime v])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop
  have hm0 : (m : ℚ_[prime v]) ≠ 0 := norm_ne_zero_iff.1 (by rw [hnm]; exact one_ne_zero)
  let a : (v.adicCompletion ℚ)ˣ :=
    Units.map (padicRingEquiv v).symm.toMonoidHom (Units.mk0 (m : ℚ_[prime v]) hm0)⁻¹
  have ha : padicRingEquiv v (a : v.adicCompletion ℚ) = (m : ℚ_[prime v])⁻¹ := by
    simp only [a, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact RingEquiv.apply_symm_apply _ _
  have hnorm : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 := by rw [ha, norm_inv, hnm, inv_one]
  refine ⟨a, hnorm, coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩
    fun w hw ↦ ?_⟩
  by_cases hwv : w = v
  · subst hwv
    have hu : (((unitAt ⟨_, finiteEmbedding_mem_positiveSubgroup hnorm⟩ w : ℤ_[prime w]ˣ) :
        ℤ_[prime w]) : ℚ_[prime w]) = (m : ℚ_[prime w])⁻¹ := by
      rw [coe_unitAt]
      change padicRingEquiv w (finiteProj w (finiteEmbedding w a) : w.adicCompletion ℚ) = _
      rw [finiteProj_finiteEmbedding, ha]
    rw [coe_inv_eq_natCast hm0 hu, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (b : ZMod N), ← hm]
    rw [map_natCast]
  · rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one]
    have hcp : Nat.Coprime (prime w ^ N.factorization (prime w)) (prime v ^ N.factorization (prime v)) :=
      Nat.Coprime.pow _ _ (coprime_prime hwv)
    have h1 : prime w ^ N.factorization (prime w) ∣
        prime v ^ N.factorization (prime v) * (N / prime v ^ N.factorization (prime v)) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact Nat.ordProj_dvd _ _
    have hdvd := hcp.dvd_of_dvd_mul_left h1
    rw [← castHom_castHom hdvd (Nat.ordCompl_dvd N (prime v)) (Nat.ordProj_dvd N (prime w))]
    have hb' : ZMod.castHom (Nat.ordCompl_dvd N (prime v)) (ZMod (N / prime v ^ N.factorization (prime v)))
        (b : ZMod N) = 1 := congrArg Units.val hb
    rw [hb', map_one]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hker` using `((heckeCharacter χ).not_dvd_conductor_iff v).1 h`. Establish `hf : χ.FactorsThrough (N / prime v ^ N.factorization (prime v))`. Use `(DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N (prime v))).2 fun b hb ↦ ?_` and prove the remaining obligations. Take `⟨a, ha, hval⟩` from `exists_coe_heckeCharacter_finiteEmbedding χ hv b hb`.

Establish `hunit : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers ℚ)).units` using `mem_units_of_norm_padicRingEquiv_eq_one ha`. Establish `h1 : (heckeCharacter χ).localComponent v a = 1` using `hker hunit`. Rewrite `h1` using `[HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, ← hval, h1, Circle.coe_one]`. Establish `hdvd` using `χ.conductor_dvd_of_mem_conductorSet hf`.

Rewrite `hdvd` using `[hχ]`. Establish `heq : N / prime v ^ N.factorization (prime v) = N` using `Nat.dvd_antisymm (Nat.ordCompl_dvd N (prime v)) hdvd`. Establish `hpos : 0 < N.factorization (prime v)` using `(Fact.out : (prime v).Prime).factorization_pos_of_dvd (NeZero.ne N) hv`. Establish `h2` using `Nat.ordProj_mul_ordCompl_eq_self N (prime v)`. Rewrite `h2` using `[heq]`.

Establish `h3 : prime v ^ N.factorization (prime v) = 1`. Establish `hN : 0 < N` using `Nat.pos_of_neZero N`. Use polynomial arithmetic with `[Nat.one_le_pow (N.factorization (prime v)) (prime v) (Fact.out : (prime v).Prime).pos]`. Break down `pow_eq_one_iff.1 h3 with h4 | h4` into its components or cases. Conclude with `(Fact.out : (prime v).Prime).one_lt.ne' h4`.

Conclude with `hpos.ne' h4`.
-/
theorem dvd_conductor_of_dvd (hχ : χ.IsPrimitive) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : prime v ∣ N) :
    v.asIdeal ∣ (heckeCharacter χ).conductor := by
  by_contra h
  have hker := ((heckeCharacter χ).not_dvd_conductor_iff v).1 h
  have hf : χ.FactorsThrough (N / prime v ^ N.factorization (prime v)) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N (prime v))).2
      fun b hb ↦ ?_
    obtain ⟨a, ha, hval⟩ := exists_coe_heckeCharacter_finiteEmbedding χ hv b hb
    have hunit : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers ℚ)).units :=
      mem_units_of_norm_padicRingEquiv_eq_one ha
    have h1 : (heckeCharacter χ).localComponent v a = 1 := hker hunit
    rw [HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply] at h1
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, ← hval, h1,
      Circle.coe_one]
  have hdvd := χ.conductor_dvd_of_mem_conductorSet hf
  rw [hχ] at hdvd
  have heq : N / prime v ^ N.factorization (prime v) = N :=
    Nat.dvd_antisymm (Nat.ordCompl_dvd N (prime v)) hdvd
  have hpos : 0 < N.factorization (prime v) :=
    (Fact.out : (prime v).Prime).factorization_pos_of_dvd (NeZero.ne N) hv
  have h2 := Nat.ordProj_mul_ordCompl_eq_self N (prime v)
  rw [heq] at h2
  have h3 : prime v ^ N.factorization (prime v) = 1 := by
    have hN : 0 < N := Nat.pos_of_neZero N
    nlinarith [Nat.one_le_pow (N.factorization (prime v)) (prime v) (Fact.out : (prime v).Prime).pos]
  rcases pow_eq_one_iff.1 h3 with h4 | h4
  · exact (Fact.out : (prime v).Prime).one_lt.ne' h4
  · exact hpos.ne' h4

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h ↦ by_contra fun h' ↦ not_dvd_conductor_of_not_dvd χ h' h, dvd_conductor_of_dvd χ hχ⟩`.
-/
theorem dvd_conductor_iff (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal ∣ (heckeCharacter χ).conductor ↔ prime v ∣ N :=
  ⟨fun h ↦ by_contra fun h' ↦ not_dvd_conductor_of_not_dvd χ h' h, dvd_conductor_of_dvd χ hχ⟩

end DirichletHecke

end

end GroundTheory.Global
