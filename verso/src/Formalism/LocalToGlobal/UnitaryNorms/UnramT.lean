import Formalism.LocalToGlobal.UnitaryNorms.RamificationIdxEqOneOfNotDvd
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationDetBasisChange

noncomputable section

open NumberField Ideal

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.L2.Forms

section Gen

variable {E : Type*} [Field E] [NumberField E]

/- English proof (translation)
Set `v` to `AddValuation.toValuation ν`. Establish `h1 : IsIntegral v.integer (x : E)` using `(RingOfIntegers.isIntegral_coe x).tower_top`. Establish `h2` using `(Valuation.integer.integers v).mem_of_integral h1`. Rewrite `h2` using `[Valuation.mem_integer_iff]`. Establish `h3 : Multiplicative.ofAdd (OrderDual.toDual (ν (x : E))) ≤ Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ))` using `h2`.

Conclude with `OrderDual.toDual_le_toDual.mp (Multiplicative.ofAdd_le.mp h3)`.
-/
theorem addVal_nonneg (ν : AddValuation E (WithTop ℤ)) (x : 𝓞 E) : 0 ≤ ν (x : E) := by
  let v := AddValuation.toValuation ν
  have h1 : IsIntegral v.integer (x : E) := (RingOfIntegers.isIntegral_coe x).tower_top
  have h2 := (Valuation.integer.integers v).mem_of_integral h1
  rw [Valuation.mem_integer_iff] at h2
  have h3 : Multiplicative.ofAdd (OrderDual.toDual (ν (x : E))) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) := h2
  exact OrderDual.toDual_le_toDual.mp (Multiplicative.ofAdd_le.mp h3)

/- English proof (translation)
Take `⟨a, b, hb, hab⟩` from `hP.exists_inv hs`. Use `le_antisymm ?_ (addVal_nonneg ν s)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : 0 < ν ((a : E) * s + b)`.

Use `lt_of_lt_of_le (lt_min ?_ (hPν b hb)) (ν.map_add _ _)` and prove the remaining obligations. Rewrite using `[ν.map_mul]`. Conclude with `lt_of_lt_of_le h (le_add_of_nonneg_left (addVal_nonneg ν a))`. Establish `h2 : ((a : E) * s + b) = 1` using `by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hab`. Rewrite `h1` using `[h2, ν.map_one]`.

Conclude with `lt_irrefl _ h1`.
-/
theorem addVal_eq_zero_of_not_mem (ν : AddValuation E (WithTop ℤ)) (P : Ideal (𝓞 E)) (hP : P.IsMaximal)
    (hPν : ∀ y ∈ P, 0 < ν (y : E)) (s : 𝓞 E) (hs : s ∉ P) : ν (s : E) = 0 := by
  obtain ⟨a, b, hb, hab⟩ := hP.exists_inv hs
  refine le_antisymm ?_ (addVal_nonneg ν s)
  by_contra h
  push Not at h
  have h1 : 0 < ν ((a : E) * s + b) := by
    refine lt_of_lt_of_le (lt_min ?_ (hPν b hb)) (ν.map_add _ _)
    rw [ν.map_mul]
    exact lt_of_lt_of_le h (le_add_of_nonneg_left (addVal_nonneg ν a))
  have h2 : ((a : E) * s + b) = 1 := by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hab
  rw [h2, ν.map_one] at h1
  exact lt_irrefl _ h1

end Gen

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Take `⟨T⟩` from `Frame.exists H`. Apply `(T.ι.injective.comp T.j.injective)` to reduce the goal to its premises. Use `show T.ι (T.j (H.conj (H.conj z))) = T.ι (T.j z)`. Rewrite using `[T.conj, T.conj, Complex.conj_conj]`.
-/
theorem conj_conj (H : Formalism.BasicNotions.Host D.R) (z : H.E) : H.conj (H.conj z) = z := by
  obtain ⟨T⟩ := Frame.exists H
  apply (T.ι.injective.comp T.j.injective)
  show T.ι (T.j (H.conj (H.conj z))) = T.ι (T.j z)
  rw [T.conj, T.conj, Complex.conj_conj]

/- English proof (translation)
Establish `: Fact (D.mem u).A.T.Prime` using `⟨(D.mem u).A.T_prime⟩`. Establish `: CharP ((D.mem u).A.Fv v) (D.mem u).A.T` using `charP_of_card_eq_prime ((D.mem u).A.card_Fv v)`. Establish `hN : ¬ (D.mem u).A.T ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2`. Introduce `hd`. Take `⟨k, hk⟩` from `Ideal.mem_span_singleton'.mp A.piU_cong`.

Establish `h2` using `congrArg (A.res v) hk`. Rewrite `h2` using `[map_mul, map_sub, A.res_pi, map_one, map_natCast, (CharP.cast_eq_zero_iff _ (D.mem u).A.T _).2 hd, mul_zero, zero_sub]`. Conclude with `one_ne_zero (neg_eq_zero.mp h2.symm)`. Conclude with `fun h => hN (Dvd.dvd.mul_right h _)`.
-/
theorem T_ne (A : AtTTied u) (v : (D.mem u).A.vT) :
    ¬ (D.mem u).A.T ∣ D.host.condN := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have hN : ¬ (D.mem u).A.T ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    intro hd
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp A.piU_cong
    have h2 := congrArg (A.res v) hk
    rw [map_mul, map_sub, A.res_pi, map_one, map_natCast, (CharP.cast_eq_zero_iff _ (D.mem u).A.T _).2 hd,
      mul_zero, zero_sub] at h2
    exact one_ne_zero (neg_eq_zero.mp h2.symm)
  exact fun h => hN (Dvd.dvd.mul_right h _)

/- English proof (translation)
Introduce `w hw hseen v x hx`. Establish `hw' : D.what₂.places.resChar w = (D.mem u).A.T` using `hw`. Establish `: Fact (D.mem u).A.T.Prime` using `⟨(D.mem u).A.T_prime⟩`. Establish `: CharP ((D.mem u).A.Fv v) (D.mem u).A.T` using `charP_of_card_eq_prime ((D.mem u).A.card_Fv v)`. Set `σ : D.host.E ≃ₐ[ℚ] D.host.E` to `D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)`.

Set `ν : AddValuation D.host.E (WithTop ℤ)` to `(D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))`. Establish `hν : ∀ y, ν y = D.what₂.places.val w (D.embE (σ y))` using `fun y => rfl`. Express the relevant statement in the definitionally equal form `_ ≤ ν (x : D.host.E)`. Set `cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E` to `RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv`. Establish `hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E)` using `fun y => rfl`.

Establish `hinv` using `conj_conj D.host`. Establish `mkF : ∀ z : 𝓞 D.host.E, D.host.conj (z : D.host.E) = z → ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z`. Introduce `z hz`. Establish `hF : (z : D.host.E) ∈ D.host.F` using `(D.host.conjE_mem_hostF_iff _).2 hz`. Use `⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp (RingOfIntegers.isIntegral_coe z)`. Both sides reduce to the same expression. Establish `hcoe : ∀ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) D.host.E zF = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)` using `fun _ => rfl`. Establish `hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔ 0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)`. Introduce `zF`.

Rewrite using `[A.tauOf w hw' v zF, hcoe]`. Conclude with `Iff.rfl`. Establish `hπ : 0 < ν (A.piU : D.host.E)`. Use `A.seenP w hw' ((D.fm u).tauOf w v)` as an intermediate fact. Rewrite `this` using `[if_pos hseen]`.

Conclude with `this`. Establish `hpb : A.res v (cO A.piU) ≠ 0` using `A.res_conj v (cO A.piU) rfl`. Establish `hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0`. Take `⟨zF, hzF⟩` from `mkF (A.piU + cO A.piU) (by push_cast; simp only [hcO, map_add, hinv]; ring)`. Establish `hnot : zF ∉ (A.eV v).1.asIdeal`.

Rewrite using `[A.res_v, hzF, map_add, A.res_pi, zero_add]`. Conclude with `hpb`. Rewrite `hnot` using `[hTau, hzF]`. Use `le_antisymm (not_lt.mp fun h => hnot ?_) (addVal_nonneg ν _)` and prove the remaining obligations. Use `push_cast`.

Conclude with `lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)`. Establish `hPν : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E)`. Introduce `y hy`. Establish `hy' : A.res v y = 0` using `hy`. Take `⟨zF, hzF⟩` from `mkF (y * cO A.piU + cO y * A.piU) (by push_cast; simp only [hcO, map_add, map_mul, hinv]; ring)`.

Establish `hin : zF ∈ (A.eV v).1.asIdeal`. Rewrite using `[A.res_v, hzF, map_add, map_mul, map_mul, hy', A.res_pi]`. Simplify using the standard rewrite rules. Rewrite `hin` using `[hTau, hzF]`. Move the coercions through the operations in `at hin`.

Establish `h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU)`. Rewrite using `[ν.map_mul]`. Conclude with `lt_of_lt_of_le hπ (le_add_of_nonneg_left (addVal_nonneg ν _))`. Establish `h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E))`. Establish `: (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) = ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) - ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU` using `by ring`.

Rewrite using `[this]`. Conclude with `lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)`. Rewrite `h3` using `[ν.map_mul, hπb, add_zero]`. Then use the resulting hypothesis. Establish `hPmax : (A.Pv v).IsMaximal` using `RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)`. Establish `hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s`.

Introduce `s`. Rewrite using `[map_natCast]`. Conclude with `CharP.cast_eq_zero_iff _ (D.mem u).A.T s`. Use `span_isPrime (D.mem u).A.T` as an intermediate fact. Establish `hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)})`.

Use `⟨?_⟩` and prove the remaining obligations. Establish `hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E))`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0`. Rewrite using `[map_natCast]`.

Conclude with `(hres_nat _).2 dvd_rfl`. Establish `hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal`. Use `this.isMaximal ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(D.mem u).A.T_prime.ne_zero` after adjusting the coercions.

Conclude with `hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle`. Take `⟨I, hI, hIP⟩` from `map_eq_mul_coprime D.host (D.mem u).A.T (T_ne A v) (A.Pv v)`. Take `⟨s, hsI, hsP⟩` from `Set.not_subset.mp hIP`. Establish `hxP : x ∈ A.Pv v` using `hx`. Establish `hxs : x * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E))`.

Rewrite using `[hI]`. Conclude with `Ideal.mul_mem_mul hxP hsI`. Rewrite `hxs` using `[Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast]`. Take `⟨z, hz⟩` from `hxs`. Establish `hz' : (z : D.host.E) * ((D.mem u).A.T : D.host.E) = (x : D.host.E) * s`.

Conclude with `congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) hz` after adjusting the coercions. Establish `hνs : ν (s : D.host.E) = 0` using `addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hPν s hsP`. Establish `hνT : ν ((D.mem u).A.T : D.host.E) = (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ)`. Rewrite using `[hν, map_natCast, map_natCast, ← hw']`. Conclude with `D.what₂.places.val_resChar w`.

Establish `key : ν ((z : D.host.E) * ((D.mem u).A.T : D.host.E)) = ν ((x : D.host.E) * s)` using `by rw [hz']`. Rewrite `key` using `[ν.map_mul, ν.map_mul, hνs, add_zero, hνT]`. Rewrite using `[← key]`. Conclude with `le_add_of_nonneg_left (addVal_nonneg ν z)`.
-/
theorem second_unramified_condition_holds (A : AtTTied u) : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.UnramifiedAtLevelPrimes D u A := by
  intro w hw hseen v x hx
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  let σ : D.host.E ≃ₐ[ℚ] D.host.E :=
    D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hν : ∀ y, ν y = D.what₂.places.val w (D.embE (σ y)) := fun y => rfl
  change _ ≤ ν (x : D.host.E)
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  have hinv := conj_conj D.host

  have mkF : ∀ z : 𝓞 D.host.E, D.host.conj (z : D.host.E) = z →
      ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
    intro z hz
    have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
    refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
    · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
        (RingOfIntegers.isIntegral_coe z)
    · rfl
  have hcoe : ∀ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) D.host.E zF =
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun _ => rfl
  have hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := by
    intro zF
    rw [A.tauOf w hw' v zF, hcoe]
    exact Iff.rfl

  have hπ : 0 < ν (A.piU : D.host.E) := by
    have := A.seenP w hw' ((D.fm u).tauOf w v)
    rw [if_pos hseen] at this
    exact this
  have hpb : A.res v (cO A.piU) ≠ 0 := A.res_conj v (cO A.piU) rfl
  have hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0 := by
    obtain ⟨zF, hzF⟩ := mkF (A.piU + cO A.piU) (by
      push_cast; simp only [hcO, map_add, hinv]; ring)
    have hnot : zF ∉ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add, A.res_pi, zero_add]; exact hpb
    rw [hTau, hzF] at hnot
    refine le_antisymm (not_lt.mp fun h => hnot ?_) (addVal_nonneg ν _)
    push_cast
    exact lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)

  have hPν : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E) := by
    intro y hy
    have hy' : A.res v y = 0 := hy
    obtain ⟨zF, hzF⟩ := mkF (y * cO A.piU + cO y * A.piU) (by
      push_cast; simp only [hcO, map_add, map_mul, hinv]; ring)
    have hin : zF ∈ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add, map_mul, map_mul, hy', A.res_pi]; simp
    rw [hTau, hzF] at hin
    push_cast at hin
    have h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) := by
      rw [ν.map_mul]; exact lt_of_lt_of_le hπ (le_add_of_nonneg_left (addVal_nonneg ν _))
    have h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E)) := by
      have : (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) =
          ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) -
            ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU := by ring
      rw [this]
      exact lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)
    rwa [ν.map_mul, hπb, add_zero] at h3

  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  have hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s := by
    intro s; rw [map_natCast]; exact CharP.cast_eq_zero_iff _ (D.mem u).A.T s
  have := span_isPrime (D.mem u).A.T
  have hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)}) := by
    refine ⟨?_⟩
    have hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0
      rw [map_natCast]
      exact (hres_nat _).2 dvd_rfl
    have hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal := by
      refine this.isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (D.mem u).A.T_prime.ne_zero
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle

  obtain ⟨I, hI, hIP⟩ := map_eq_mul_coprime D.host (D.mem u).A.T (T_ne A v) (A.Pv v)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hxP : x ∈ A.Pv v := hx
  have hxs : x * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E)) := by
    rw [hI]; exact Ideal.mul_mem_mul hxP hsI
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at hxs
  obtain ⟨z, hz⟩ := hxs
  have hz' : (z : D.host.E) * ((D.mem u).A.T : D.host.E) = (x : D.host.E) * s := by
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) hz
  have hνs : ν (s : D.host.E) = 0 := addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hPν s hsP
  have hνT : ν ((D.mem u).A.T : D.host.E) = (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hν, map_natCast, map_natCast, ← hw']
    exact D.what₂.places.val_resChar w
  have key : ν ((z : D.host.E) * ((D.mem u).A.T : D.host.E)) = ν ((x : D.host.E) * s) := by rw [hz']
  rw [ν.map_mul, ν.map_mul, hνs, add_zero, hνT] at key
  rw [← key]
  exact le_add_of_nonneg_left (addVal_nonneg ν z)

end Formalism.L2.Host
