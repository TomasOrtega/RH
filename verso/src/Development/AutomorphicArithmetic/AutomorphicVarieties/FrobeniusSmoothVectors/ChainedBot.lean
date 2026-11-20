import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EnnrealVolumeRatioStepCancel
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `hs : Function.Surjective ((Ideal.Quotient.mk Q).comp p)` using `Ideal.Quotient.mk_surjective.comp hp`. Establish `hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p`. Use extensionality with `a`. Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs).symm, ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hk)]`.
-/
private theorem ringKrullDim_quotient_eq_quotient_comap_of_surjective' {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Surjective p) (Q : Ideal B) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap p) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk Q).comp p) :=
    Ideal.Quotient.mk_surjective.comp hp
  have hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs).symm,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hk)]

/- English proof (translation)
Establish `hmin : (RingHom.ker p).minimalPrimes = Ideal.comap p '' (⊥ : Ideal B).minimalPrimes`. Rewrite using `[← Ideal.comap_minimalPrimes_eq_of_surjective hp]`. Both sides reduce to the same expression. Establish `hc : ∀ Q ∈ (⊥ : Ideal B).minimalPrimes, Q.comap p ∈ (RingHom.ker p).minimalPrimes` using `fun Q hQ => hmin ▸ ⟨Q, hQ, rfl⟩`. Take `⟨h1, h2⟩` from `h`.

Use `⟨fun Q hQ => ?_, fun P hP Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp]`. Conclude with `h1 _ (hc Q hQ)`. Establish `key` using `h2 _ (hc P hP) _ (hc Q hQ)`. Rewrite using `[← Ideal.map_comap_of_surjective p hp P, ← Ideal.map_comap_of_surjective p hp Q]`.

Use `Relation.ReflTransGen.lift (Ideal.map p) (fun a b hab => ?_) _ _ key` and prove the remaining obligations. Take `⟨ha, hb, hd⟩` from `hab`. Rewrite `ha`, `hb` using `[hmin]`. Take `⟨a', ha', rfl⟩` from `ha`. Take `⟨b', hb', rfl⟩` from `hb`.

Use `show _ ∈ _ ∧ _ ∈ _ ∧ _`. Rewrite using `[Ideal.map_comap_of_surjective p hp, Ideal.map_comap_of_surjective p hp]`. Use `⟨ha', hb', ?_⟩` and prove the remaining obligations. Establish `hsup : (a' ⊔ b').comap p = a'.comap p ⊔ b'.comap p` using `by conv_lhs => rw [← Ideal.map_comap_of_surjective p hp a', ← Ideal.map_comap_of_surjective p hp b', ← Ideal.map_sup, Ideal.comap_map_of_surjective p hp]`. Conclude with `sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)`.

Rewrite using `[ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp, hsup]`. Conclude with `hd`.
-/
private theorem chained_bot_of_chained_ker_of_surjective {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Surjective p) (D : ℕ) (h : Chained (RingHom.ker p) D) :
    Chained (⊥ : Ideal B) D := by
  have hmin : (RingHom.ker p).minimalPrimes = Ideal.comap p '' (⊥ : Ideal B).minimalPrimes := by
    rw [← Ideal.comap_minimalPrimes_eq_of_surjective hp]
    rfl
  have hc : ∀ Q ∈ (⊥ : Ideal B).minimalPrimes, Q.comap p ∈ (RingHom.ker p).minimalPrimes :=
    fun Q hQ => hmin ▸ ⟨Q, hQ, rfl⟩
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun Q hQ => ?_, fun P hP Q hQ => ?_⟩
  · rw [ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp]
    exact h1 _ (hc Q hQ)
  · have key := h2 _ (hc P hP) _ (hc Q hQ)
    rw [← Ideal.map_comap_of_surjective p hp P, ← Ideal.map_comap_of_surjective p hp Q]
    refine Relation.ReflTransGen.lift (Ideal.map p) (fun a b hab => ?_) _ _ key
    obtain ⟨ha, hb, hd⟩ := hab
    rw [hmin] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    show _ ∈ _ ∧ _ ∈ _ ∧ _
    rw [Ideal.map_comap_of_surjective p hp, Ideal.map_comap_of_surjective p hp]
    refine ⟨ha', hb', ?_⟩
    have hsup : (a' ⊔ b').comap p = a'.comap p ⊔ b'.comap p := by
      conv_lhs => rw [← Ideal.map_comap_of_surjective p hp a', ← Ideal.map_comap_of_surjective p hp b',
        ← Ideal.map_sup, Ideal.comap_map_of_surjective p hp]
      exact sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)
    rw [ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp, hsup]
    exact hd

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hok S x L hbig hx`. Take `⟨N, N', p, f, hN, hs, hk⟩` from `pres hok (Or.inl rfl) S x L`. Use `haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete (l := l)`. Use `haveI : IsCO L.O' (MvPowerSeries (Fin N) L.O') := co_mvps _ _ _`. Establish `hdim` using `((UpperTheory.V.CA.cl_cm).1 L.O' N).2`.

Establish `hch : Chained (Ideal.span (Set.range f)) (2 * F.d + 1)`. Apply `c1ch _ N' (2 * F.d + 1) f` to reduce the goal to its premises. Rewrite using `[nilradical_eq_zero, Ideal.zero_eq_bot]`. Conclude with `Ideal.bot_prime`. Conclude with `⟨L.O', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩`.

Introduce `i`. Establish `hi : f i ∈ RingHom.ker p` using `hk ▸ Ideal.subset_span ⟨i, rfl⟩`. Conclude with `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p) hi`. Rewrite using `[hdim]`. Conclude with `le_of_eq (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by omega))`.

Establish `h1 : Chained (⊥ : Ideal L.R) (2 * F.d + 1)`. Use `chained_bot_of_chained_ker_of_surjective (p : MvPowerSeries (Fin N) L.O' →+* L.R) hs _ ?_` and prove the remaining obligations. Rewrite `hch` using `[← hk]`. Conclude with `hch`. Use `⟨h1, fun P hP => ?_⟩` and prove the remaining obligations.

Establish `hr` using `(loc_rho hok (Or.inl rfl) S x L).2.2.2 hx`. Establish `hl` using `(krull_dim_lt_of_not_le_triangular hok (Or.inl rfl) S x L hbig hx).1`. Establish `hPp : P.IsPrime` using `hP.1.1`. Use `⟨⟨?_, ?_⟩, fun h => absurd h (by decide)⟩` and prove the remaining obligations. Rewrite using `[hr.1, top_le_iff]`.

Conclude with `hPp.ne_top`. Introduce `hle`. Establish `hge` using `h1.1 P hP`. Establish `hmono : ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (L.R ⧸ L.ρ.triM)` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)`. Establish `hlt : ((2 * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) < ((2 * F.d : ℕ) : WithBot ℕ∞)` using `lt_of_le_of_lt (hge.trans hmono) hl`.

Establish `: 2 * F.d + 1 + 1 < 2 * F.d` using `by exact_mod_cast hlt`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Fr.sharp2 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 2, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → Chained (⊥ : Ideal L.R) (2 * F.d + 1) ∧ ∀ P ∈ minimalPrimes L.R, L.ρ.TI P := by
  intro l _ O _ _ _ _ F C₀ hok S x L hbig hx
  obtain ⟨N, N', p, f, hN, hs, hk⟩ := pres hok (Or.inl rfl) S x L
  haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete (l := l)
  haveI : IsCO L.O' (MvPowerSeries (Fin N) L.O') := co_mvps _ _ _
  have hdim := ((UpperTheory.V.CA.cl_cm).1 L.O' N).2
  have hch : Chained (Ideal.span (Set.range f)) (2 * F.d + 1) := by
    apply c1ch _ N' (2 * F.d + 1) f
    · rw [nilradical_eq_zero, Ideal.zero_eq_bot]
      exact Ideal.bot_prime
    · exact ⟨L.O', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
    · intro i
      have hi : f i ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨i, rfl⟩
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p) hi
    · rw [hdim]
      exact le_of_eq (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by omega))
  have h1 : Chained (⊥ : Ideal L.R) (2 * F.d + 1) := by
    refine chained_bot_of_chained_ker_of_surjective (p : MvPowerSeries (Fin N) L.O' →+* L.R) hs _ ?_
    rw [← hk] at hch
    exact hch
  refine ⟨h1, fun P hP => ?_⟩
  have hr := (loc_rho hok (Or.inl rfl) S x L).2.2.2 hx
  have hl := (krull_dim_lt_of_not_le_triangular hok (Or.inl rfl) S x L hbig hx).1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
  · rw [hr.1, top_le_iff]
    exact hPp.ne_top
  · intro hle
    have hge := h1.1 P hP
    have hmono : ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (L.R ⧸ L.ρ.triM) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    have hlt : ((2 * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) < ((2 * F.d : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt (hge.trans hmono) hl
    have : 2 * F.d + 1 + 1 < 2 * F.d := by exact_mod_cast hlt
    omega
