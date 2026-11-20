import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.SigRTmulOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
Use `letI := Ideal.Quotient.field P`. Use `set p := ringChar (𝓞 E ⧸ P)`. Use `haveI : CharP (𝓞 E ⧸ P) p := ringChar.charP _`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)`. Establish `hmem : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P` using `Ideal.absNorm_mem P`.

Establish `hN0 : Ideal.absNorm P ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hdvd : p ∣ Ideal.absNorm P` using `(CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p _).1 (by`. Rewrite using `[← map_natCast (Ideal.Quotient.mk P)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hmem)`. Establish `hp0 : p ≠ 0` using `fun h => hN0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)`.

Establish `hpr : p.Prime` using `(CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right hp0`. Use `⟨p, hpr, fun m hm hmP => hm ?_⟩` and prove the remaining obligations. Conclude with `(CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p m).1 (by`. Rewrite using `[← map_natCast (Ideal.Quotient.mk P)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hmP)`.
-/
theorem resChar {E : Type} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 E) ∉ P := by
  letI := Ideal.Quotient.field P
  set p := ringChar (𝓞 E ⧸ P)
  haveI : CharP (𝓞 E ⧸ P) p := ringChar.charP _
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hmem : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hdvd : p ∣ Ideal.absNorm P := (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p _).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hp0 : p ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)
  have hpr : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right hp0
  refine ⟨p, hpr, fun m hm hmP => hm ?_⟩
  exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p m).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmP)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g P hP`. Set `J` to `gramOf h b`. Use `set L := crdOf b L0 with hLd`. Establish `hσσ : ∀ e, σ (σ e) = e` using `fun e => by rw [hσ, hσ, star_star]`. Establish `hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J` using `by show PI.UnitaryApproxDefs.cT (σ : E →+* E) (gramOf h b) = gramOf h b`.

Use extensionality with `i j`. Simplify using `only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, gramOf]`. Use `hs.eq (b j) (b i)` as an intermediate fact. Rewrite `this` using `[starRingEnd_apply]`. Rewrite using `[show (σ : E →+* E) (h (b j) (b i)) = σ (h (b j) (b i)) from rfl, hσ]`.

Conclude with `this`. Establish `hJdet : J.det ≠ 0`. Introduce `h0`. Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Establish `hu'` using `(Matrix.isUnit_iff_isUnit_det _).1 (posDefOfDefiniteSignature_holds M _ (hsig τ)).isUnit`.

Establish `e : (J.map τ).det = τ J.det` using `(RingHom.map_det τ J).symm`. Rewrite `hu'` using `[e, h0, map_zero]`. Conclude with `not_isUnit_zero hu'`. Take `⟨dJ, hdJ, hdJi⟩` from `mat_den J`. Take `⟨dI, hdI, hdIi⟩` from `mat_den J⁻¹`.

Take `⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩` from `crdBounds F E V M b L0 hL`. Take `⟨u, hu, hu'⟩` from `up_nat L ⟨c1, hc1, hup⟩`. Take `⟨k, hk, hk'⟩` from `low_nat L ⟨c2, hc2, hlow⟩`. Take `⟨m', hm', hmO'⟩` from `den_mat (F := F) (E := E) (finMat σ J g⁻¹)`. Take `⟨p, hpr, hpm⟩` from `resChar P hP`.

Use `set T : Set (HeightOneSpectrum (𝓞 F)) := {w | (p : 𝓞 F) ∈ w.asIdeal} with hTd`. Establish `hpF : (p : 𝓞 F) ≠ 0` using `by exact_mod_cast hpr.ne_zero`. Establish `hfin : T.Finite` using `(Ideal.finite_factors (I := Ideal.span {(p : 𝓞 F)}) (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hpF)).subset (fun w hw => Ideal.dvd_span_singleton.2 hw)`. Establish `hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal` using `fun w hw => hw`. Use `set N1 := u * k with hN1`.

Use `set N0 := dI * dJ * N1 with hN0`. Take `⟨γ, hγ⟩` from `approxT σ J hσσ hθ hH (isUnit_iff_ne_zero.2 hJdet) g hfin.toFinset (m' * N0) (by positivity)`. Rewrite `hγ` using `[Set.Finite.coe_toFinset]`. Use `set ε : Af F ⊗[F] E := evT T ⊗ₜ[F] (1 : E) with hε`. Establish `small1 : ∀ i j, ∃ o ∈ Oh F E, ε * (finMat σ J (g⁻¹ * emb σ J γ) - 1) i j = (dI * dJ * N1) • o` using `by choose o ho hoe using hγ`.

Introduce `i j`. Use `⟨∑ l, -((m' • finMat σ J g⁻¹ i l) * o l j), AddSubgroup.sum_mem _ fun l _ => neg_mem (Oh_mul (hmO' i l) (ho l j)), ?_⟩` and prove the remaining obligations. Establish `hPQ : finMat σ J g⁻¹ * finMat σ J g = 1` using `by rw [← finMat_mul, inv_mul_cancel, finMat_one]`. Establish `e1 : finMat σ J (g⁻¹ * emb σ J γ) - 1 = finMat σ J g⁻¹ * (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F` using `F) (Af F)) - finMat σ J g) := by`. Rewrite using `[finMat_mul, finMat_emb, Matrix.mul_sub, hPQ]`.

Rewrite using `[e1, Matrix.mul_apply, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hl` using `hoe l j`. Simplify using `only [Matrix.sub_apply, Matrix.map_apply] at hl ⊢`. Establish `e2 : ε * (finMat σ J g⁻¹ i l * (inclR (F` using `F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j) - finMat σ J g l j)) = -(finMat σ J g⁻¹ i l * (ε * (finMat σ J g l j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j)))) := by`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, hl, hN0]`. Simplify using `only [nsmul_eq_mul, smul_neg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `small2` using `invSmall σ J hJdet hdIi hdJi (evT T) ((emb σ J γ)⁻¹ * g) N1 (by`. Rewrite using `[mul_inv_rev, inv_inv]`. Conclude with `small1)`. Establish `hεI : evT T ∈ intAf F` using `evT_int T`. Establish `condA : ∀ y ∈ latHat F E L, ε • (finMat σ J (g⁻¹ * emb σ J γ)).mulVec y ∈ latHat F E L` using `fun y hy => stabT L hu' hk' hεI _ (fun i j => by`.

Take `⟨o, ho, hoe⟩` from `small1 i j`. Conclude with `⟨(dI * dJ) • o, AddSubgroup.nsmul_mem _ ho _, by rw [hoe, smul_smul]; congr 1; rw [hN1]; ring⟩) hy`. Establish `condB : ∀ y ∈ latHat F E L, ε • (finMat σ J ((emb σ J γ)⁻¹ * g)).mulVec y ∈ latHat F E L` using `fun y hy => stabT L hu' hk' hεI _ small2 hy`. Establish `hgen : ∀ m : ℕ, ¬ p ∣ m → ((m : 𝓞 E)) ∈ hcompl (K` using `E) P := fun m hm => Submonoid.subset_closure ⟨hpm m hm, fun t ht => by`. Establish `: t = (m : 𝓞 E)`.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `ht' : algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (m : 𝓞 E)`. Rewrite using `[ht, map_natCast, star_natCast]`. Simplify using `using ht'`. Rewrite using `[this]`.

Conclude with `hpm m hm⟩`. Use `⟨⟨emb σ J γ, emb_mem σ J γ⟩, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨s, hs, hsx⟩`. Take `⟨m2, hm2, hmx⟩` from `locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT g (emb σ J γ) condB hsx`. Use `⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_natCast, mul_comm, mul_smul]`. Conclude with `hmx`. Introduce and unpack `⟨s, hs, hsx⟩`. Take `⟨m2, hm2, hmx⟩` from `locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT (emb σ J γ) g (fun y hy => by simpa using condA y hy) hsx`. Use `⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_natCast, mul_comm, mul_smul]`. Conclude with `hmx`.
-/
theorem lsLoc : LSLoc := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g P hP
  classical
  let J := gramOf h b
  set L := crdOf b L0 with hLd

  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  have hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J := by
    show PI.UnitaryApproxDefs.cT (σ : E →+* E) (gramOf h b) = gramOf h b
    ext i j
    simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, gramOf]
    have := hs.eq (b j) (b i)
    rw [starRingEnd_apply] at this
    rw [show (σ : E →+* E) (h (b j) (b i)) = σ (h (b j) (b i)) from rfl, hσ]
    exact this
  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (posDefOfDefiniteSignature_holds M _ (hsig τ)).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹

  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) (finMat σ J g⁻¹)

  obtain ⟨p, hpr, hpm⟩ := resChar P hP
  set T : Set (HeightOneSpectrum (𝓞 F)) := {w | (p : 𝓞 F) ∈ w.asIdeal} with hTd
  have hpF : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hfin : T.Finite := (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 F)})
    (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hpF)).subset
      (fun w hw => Ideal.dvd_span_singleton.2 hw)
  have hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal := fun w hw => hw

  set N1 := u * k with hN1
  set N0 := dI * dJ * N1 with hN0
  obtain ⟨γ, hγ⟩ := approxT σ J hσσ hθ hH (isUnit_iff_ne_zero.2 hJdet) g hfin.toFinset (m' * N0)
    (by positivity)
  rw [Set.Finite.coe_toFinset] at hγ
  set ε : Af F ⊗[F] E := evT T ⊗ₜ[F] (1 : E) with hε

  have small1 : ∀ i j, ∃ o ∈ Oh F E,
      ε * (finMat σ J (g⁻¹ * emb σ J γ) - 1) i j = (dI * dJ * N1) • o := by
    choose o ho hoe using hγ
    intro i j
    refine ⟨∑ l, -((m' • finMat σ J g⁻¹ i l) * o l j),
      AddSubgroup.sum_mem _ fun l _ => neg_mem (Oh_mul (hmO' i l) (ho l j)), ?_⟩
    have hPQ : finMat σ J g⁻¹ * finMat σ J g = 1 := by rw [← finMat_mul, inv_mul_cancel, finMat_one]
    have e1 : finMat σ J (g⁻¹ * emb σ J γ) - 1 =
        finMat σ J g⁻¹ * (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) - finMat σ J g) := by
      rw [finMat_mul, finMat_emb, Matrix.mul_sub, hPQ]
    rw [e1, Matrix.mul_apply, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := hoe l j
    simp only [Matrix.sub_apply, Matrix.map_apply] at hl ⊢
    have e2 : ε * (finMat σ J g⁻¹ i l * (inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j) - finMat σ J g l j)) =
        -(finMat σ J g⁻¹ i l * (ε * (finMat σ J g l j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j)))) := by
      ring
    rw [e2, hl, hN0]
    simp only [nsmul_eq_mul, smul_neg]
    push_cast
    ring
  have small2 := invSmall σ J hJdet hdIi hdJi (evT T) ((emb σ J γ)⁻¹ * g) N1 (by
    rw [mul_inv_rev, inv_inv]; exact small1)
  have hεI : evT T ∈ intAf F := evT_int T
  have condA : ∀ y ∈ latHat F E L, ε • (finMat σ J (g⁻¹ * emb σ J γ)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ (fun i j => by
      obtain ⟨o, ho, hoe⟩ := small1 i j
      exact ⟨(dI * dJ) • o, AddSubgroup.nsmul_mem _ ho _, by rw [hoe, smul_smul]; congr 1; rw [hN1]; ring⟩) hy
  have condB : ∀ y ∈ latHat F E L, ε • (finMat σ J ((emb σ J γ)⁻¹ * g)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ small2 hy

  have hgen : ∀ m : ℕ, ¬ p ∣ m → ((m : 𝓞 E)) ∈ hcompl (K := E) P := fun m hm =>
    Submonoid.subset_closure ⟨hpm m hm, fun t ht => by
      have : t = (m : 𝓞 E) := by
        apply RingOfIntegers.coe_injective
        have ht' : algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (m : 𝓞 E) := by
          rw [ht, map_natCast, star_natCast]
        simpa using ht'
      rw [this]; exact hpm m hm⟩
  refine ⟨⟨emb σ J γ, emb_mem σ J γ⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT g (emb σ J γ)
      condB hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT (emb σ J γ) g
      (fun y hy => by simpa using condA y hy) hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx

end PI.UnitaryGroupMassFormula.UJClassMass
