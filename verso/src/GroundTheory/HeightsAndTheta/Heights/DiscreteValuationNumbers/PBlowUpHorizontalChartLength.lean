import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalSat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section ChartLength

/- English proof (translation)
Set `g` to `Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl (Algebra.linearMap A (Localization.AtPrime W)) K`. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl g (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)`. Establish `hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W))`. Rewrite using `[Submodule.localized'_eq_span]`. Both sides reduce to the same expression.

Rewrite using `[← e.length_eq]`. Conclude with `(Submodule.quotEquivOfEq _ _ hK).length_eq`.
-/
theorem chartLength_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

/- English proof (translation)
Set `_` to `RingHomInvPair.of_ringEquiv τ`. Set `_` to `RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)`. Apply `WithBot.coe_injective` to reduce the goal to its premises. Rewrite using `[Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]`.
-/
theorem chartLength_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  let _ := RingHomInvPair.of_ringEquiv τ
  let _ := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

/- English proof (translation)
The claim follows from `Module.length_eq_of_surjective Ideal.Quotient.mk_surjective`.
-/
theorem chartLength_quotient_self {A : Type*} [CommRing A] (I : Ideal A) :
    Module.length A (A ⧸ I) = Module.length (A ⧸ I) (A ⧸ I) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

/- English proof (translation)
Use `⟨h.natDegree, ∑ k ∈ Finset.range (h.natDegree + 1), liftForm (h.coeff k * a j₀ ^ (h.natDegree - k)) * newVar j₀ ^ k, ?_⟩` and prove the remaining obligations. Establish `hs : Polynomial.C (a j₀ ^ h.natDegree) * h = ∑ k ∈ Finset.range (h.natDegree + 1), Polynomial.C (a j₀ ^ h.natDegree) * (Polynomial.C (h.coeff k) * Polynomial.X ^ k)`. Rewrite using `[← Finset.mul_sum, ← h.as_sum_range_C_mul_X_pow]`. Rewrite using `[hs, map_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `hk' : k ≤ h.natDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Establish `e : a j₀ ^ h.natDegree = a j₀ ^ (h.natDegree - k) * a j₀ ^ k`. Rewrite using `[← pow_add, Nat.sub_add_cancel hk']`. Rewrite using `[map_mul, map_pow, aeval_chartSubst_liftForm, e]`. Simplify using `only [newVar, aeval_X, chartSubst, map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_aeval_chartSubst_eq_C_pow_mul (a : J → MRing ι R) (j₀ : J) (h : Polynomial (MRing ι R)) :
    ∃ (d : ℕ) (H : MRing (extIdx ι J) R),
      aeval (chartSubst a) H = Polynomial.C (a j₀ ^ d) * h := by
  refine ⟨h.natDegree, ∑ k ∈ Finset.range (h.natDegree + 1),
    liftForm (h.coeff k * a j₀ ^ (h.natDegree - k)) * newVar j₀ ^ k, ?_⟩
  have hs : Polynomial.C (a j₀ ^ h.natDegree) * h = ∑ k ∈ Finset.range (h.natDegree + 1),
      Polynomial.C (a j₀ ^ h.natDegree) * (Polynomial.C (h.coeff k) * Polynomial.X ^ k) := by
    rw [← Finset.mul_sum, ← h.as_sum_range_C_mul_X_pow]
  rw [hs, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ h.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : a j₀ ^ h.natDegree = a j₀ ^ (h.natDegree - k) * a j₀ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [map_mul, map_pow, aeval_chartSubst_liftForm, e]
  simp only [newVar, aeval_X, chartSubst, map_mul, map_pow]
  ring

end ChartLength

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes`. Unfold `divCycle at hW`. Use `split_ifs at hW with h`.

Conclude with `h.1`. Conclude with `absurd rfl hW`. Take `⟨-, hBW, hWrel⟩` from `le_and_isRelevant_of_divCycle_ne_zero hW`. Use `set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀`. Take `⟨hW₀p, hPW₀, hrel₀, -⟩` from `comap_liftForm_facts hWp hBW hWrel`.

Establish `hϖW₀ : (C ϖ : MRing ι O) ∉ W₀` using `by rw [Ideal.mem_comap, liftForm_C]; exact hϖW`. Take `⟨j₀, hj₀⟩` from `hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀`. Use `choose v w hv hvw using hj₀`. Establish `huj₀ : u j₀ ∉ P`. Introduce `h`.

Take `⟨j, hj⟩` from `hex`. Establish `h1 : v j * u j ∈ P`. Use `P.add_mem (hvw j) (P.mul_mem_left (w j) h)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))`.

Choose the witnesses or unpack the hypotheses as in `⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧ ∀ j, u₀ * u j - u j₀ * a j ∈ P := by`. Use `hW₀p` as an intermediate fact. Use `⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j', fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩` and prove the remaining obligations. Establish `e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') = (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `P.mul_mem_left _ (hvw j)`. Establish `hu₀P : u₀ ∉ P` using `fun h => hu₀W (hPW₀ h)`. Establish `ha₀ : a j₀ ∉ W₀`.

Introduce `h`. Establish `h1 : u j₀ * (u₀ - a j₀) ∈ P`. Use `hrelP j₀` as an intermediate fact. Rewrite `this` using `[show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring]`. Then use the resulting hypothesis. Establish `h2 : u₀ - a j₀ ∈ W₀` using `hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)`.

Conclude with `hu₀W (by simpa using W₀.add_mem h2 h)`. Establish `hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u`. Introduce `j`. Apply `mem_blowUpOf_of_sub` to reduce the goal to its premises. Establish `e : u₀ * (u j * a j₀ - u j₀ * a j) = a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀)` using `by ring`.

Establish `h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P`. Rewrite using `[e]`. Conclude with `P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))`. Conclude with `(hPp.mem_or_mem h1).resolve_left hu₀P`. Use `hW₀p` as an intermediate fact.

Use `set 𝔮 := W₀.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with h𝔮`. Use `set Jx := (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with hJx`. Use `set I := blowUpOf P u ⊔ Ideal.span {liftForm x} with hI`. Set `φ : MRing (extIdx ι J) O →+* Polynomial (MRing ι O)` to `(aeval (R := O) (chartSubst a)).toRingHom`. Establish `hφ : ∀ F, φ F = aeval (chartSubst a) F` using `fun _ => rfl`.

Establish `hxW : liftForm x ∈ W` using `hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hW𝔮 : W = 𝔮.comap φ`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ (fun G hG => ?_)` and prove the remaining obligations. Conclude with `Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)`.

Rewrite using `[Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]`. Conclude with `Ideal.mem_map_of_mem _ hxW`. Conclude with `mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG`. Introduce `G hG`. Conclude with `mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG`.

Establish `hlfa : ∀ m : ℕ, liftForm (a j₀ ^ m) ∉ W` using `fun m h => ha₀ (hW₀p.mem_of_pow_mem m (show a j₀ ^ m ∈ W₀ from h))`. Establish `hCa : ∀ e : ℕ, Polynomial.C (a j₀ ^ e) ∉ 𝔮`. Introduce `e h`. Establish `h1` using `Ideal.mem_map_C_iff.mp h 0`. Rewrite `h1` using `[Polynomial.coeff_C_zero]`.

Conclude with `ha₀ (hW₀p.mem_of_pow_mem _ h1)`. Establish `hq : 𝔮.IsPrime` using `inferInstance`. Establish `hlift : ∀ t, t ∉ 𝔮 → ∃ (e : ℕ) (T : MRing (extIdx ι J) O), φ T = Polynomial.C (a j₀ ^ e) * t ∧ T ∉ W`. Introduce `t ht`. Take `⟨e, T, hT⟩` from `exists_aeval_chartSubst_eq_C_pow_mul a j₀ t`.

Use `⟨e, T, hT, fun hTW => ?_⟩` and prove the remaining obligations. Establish `h1 : φ T ∈ 𝔮` using `by rw [hW𝔮] at hTW; exact hTW`. Rewrite `h1` using `[hφ, hT]`. Conclude with `(hq.mem_or_mem h1).elim (hCa e) ht`. Establish `hIJ : I ≤ Jx.comap φ`.

Use `sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Conclude with `Ideal.map_mono le_sup_left (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)`. Rewrite using `[Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))`. Establish `memI : ∀ G, φ G ∈ Jx → ∃ m : ℕ, liftForm (a j₀ ^ m) * G ∈ I`.

Introduce `G hG`. Rewrite `hG` using `[hJx, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, hyz⟩` from `hG`. Take `⟨h, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`. Take `⟨d, H, hH⟩` from `exists_aeval_chartSubst_eq_C_pow_mul a j₀ h`.

Establish `h1 : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P`. Establish `e : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) = Polynomial.C (a j₀ ^ d) * y`. Rewrite using `[map_sub, map_mul, map_mul, aeval_chartSubst_liftForm, aeval_chartSubst_liftForm, hH, ← hφ G, ← hyz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_left _ _ hy`. Take `⟨m, hm⟩` from `exists_pow_mul_mem_of_aeval_chartSubst_mem (P := P) (u := u) j₀ hrelB h1`. Establish `hPB : Ideal.map (liftForm (J` using `J) : MRing ι O →ₐ[O] MRing (extIdx ι J) O) P ≤ blowUpOf P u := Ideal.map_le_iff_le_comap.mpr fun p hp => liftForm_mem_blowUpOf hp`. Establish `hm'` using `sup_le le_rfl hPB hm`. Use `⟨m + d, ?_⟩` and prove the remaining obligations.

Establish `e : liftForm (a j₀ ^ (m + d)) * G = liftForm (a j₀ ^ m) * (liftForm (a j₀ ^ d) * G - H * liftForm x) + (liftForm (a j₀ ^ m) * H) * liftForm x`. Rewrite using `[pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hm') (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))`.

Set `Φ` to `Localization.localRingHom W 𝔮 φ hW𝔮`. Establish `hsurj : Function.Surjective Φ`. Introduce `z`. Take `⟨⟨h, t⟩, rfl⟩` from `IsLocalization.mk'_surjective 𝔮.primeCompl z`. Take `⟨d, H, hH⟩` from `exists_aeval_chartSubst_eq_C_pow_mul a j₀ h`.

Take `⟨e, T, hT, hTW⟩` from `hlift t t.2`. Establish `hs : T * liftForm (a j₀ ^ d) ∈ W.primeCompl` using `W.primeCompl.mul_mem hTW (hlfa d)`. Use `⟨IsLocalization.mk' _ (H * liftForm (a j₀ ^ e)) ⟨_, hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `(t : Polynomial (MRing ι O)) * φ (H * liftForm (a j₀ ^ e)) = φ (T * liftForm (a j₀ ^ d)) * h`. Rewrite using `[map_mul, map_mul, hT]`. Simplify using `only [hφ, aeval_chartSubst_liftForm, hH]`. Expand and normalize the polynomial expressions, which then agree. Establish `hker : I.map (algebraMap _ (Localization.AtPrime W)) = (Jx.map (algebraMap _ (Localization.AtPrime 𝔮))).comap Φ`.

Use extensionality with `z`. Take `⟨⟨F, T⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl z`. Rewrite using `[Ideal.mem_comap, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsF⟩`.

Use `⟨φ s, fun h => hs (by rw [hW𝔮]; exact h), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Conclude with `hIJ hsF`. Introduce and unpack `⟨t, ht, htF⟩`. Take `⟨e, T', hT', hT'W⟩` from `hlift t ht`.

Take `⟨m, hm⟩` from `memI (T' * F) (by`. Rewrite using `[map_mul, hT', mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ htF)`. Conclude with `⟨liftForm (a j₀ ^ m) * T', W.primeCompl.mul_mem (hlfa m) hT'W, by rw [mul_assoc]; exact hm⟩`. Establish `hsurj' : Function.Surjective ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ)` using `Ideal.Quotient.mk_surjective.comp hsurj`.

Establish `hker' : I.map (algebraMap _ (Localization.AtPrime W)) = RingHom.ker ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ)`. Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker]`. Conclude with `hker`. Set `τ` to `(Ideal.quotEquivOfEq hker').trans (RingHom.quotientKerEquivOfSurjective hsurj')`. Unfold `multAt`.

Rewrite using `[chartLength_localizedModule_quotient, chartLength_localizedModule_quotient, chartLength_quotient_self, chartLength_quotient_self]`. Conclude with `chartLength_self_eq_of_ringEquiv τ`.
-/
theorem BlowUpHorizontalChartLength.full : BlowUpHorizontalChartLength.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨-, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  set 𝔮 := W₀.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with h𝔮
  set Jx := (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with hJx
  set I := blowUpOf P u ⊔ Ideal.span {liftForm x} with hI
  let φ : MRing (extIdx ι J) O →+* Polynomial (MRing ι O) := (aeval (R := O) (chartSubst a)).toRingHom
  have hφ : ∀ F, φ F = aeval (chartSubst a) F := fun _ => rfl
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hW𝔮 : W = 𝔮.comap φ := by
    refine le_antisymm ?_ ?_
    · refine hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩
        (fun G hG => ?_)
      · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
      · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
        exact Ideal.mem_map_of_mem _ hxW
      · exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
    · intro G hG
      exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hlfa : ∀ m : ℕ, liftForm (a j₀ ^ m) ∉ W := fun m h =>
    ha₀ (hW₀p.mem_of_pow_mem m (show a j₀ ^ m ∈ W₀ from h))
  have hCa : ∀ e : ℕ, Polynomial.C (a j₀ ^ e) ∉ 𝔮 := by
    intro e h
    have h1 := Ideal.mem_map_C_iff.mp h 0
    rw [Polynomial.coeff_C_zero] at h1
    exact ha₀ (hW₀p.mem_of_pow_mem _ h1)
  have hq : 𝔮.IsPrime := inferInstance

  have hlift : ∀ t, t ∉ 𝔮 → ∃ (e : ℕ) (T : MRing (extIdx ι J) O),
      φ T = Polynomial.C (a j₀ ^ e) * t ∧ T ∉ W := by
    intro t ht
    obtain ⟨e, T, hT⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ t
    refine ⟨e, T, hT, fun hTW => ?_⟩
    have h1 : φ T ∈ 𝔮 := by rw [hW𝔮] at hTW; exact hTW
    rw [hφ, hT] at h1
    exact (hq.mem_or_mem h1).elim (hCa e) ht

  have hIJ : I ≤ Jx.comap φ := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono le_sup_left (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  have memI : ∀ G, φ G ∈ Jx → ∃ m : ℕ, liftForm (a j₀ ^ m) * G ∈ I := by
    intro G hG
    rw [hJx, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at hG
    obtain ⟨y, hy, z, hz, hyz⟩ := hG
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    have h1 : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) ∈
        Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P := by
      have e : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) =
          Polynomial.C (a j₀ ^ d) * y := by
        rw [map_sub, map_mul, map_mul, aeval_chartSubst_liftForm, aeval_chartSubst_liftForm, hH, ← hφ G,
          ← hyz]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hy
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem (P := P) (u := u) j₀ hrelB h1
    have hPB : Ideal.map (liftForm (J := J) : MRing ι O →ₐ[O] MRing (extIdx ι J) O) P ≤ blowUpOf P u :=
      Ideal.map_le_iff_le_comap.mpr fun p hp => liftForm_mem_blowUpOf hp
    have hm' := sup_le le_rfl hPB hm
    refine ⟨m + d, ?_⟩
    have e : liftForm (a j₀ ^ (m + d)) * G =
        liftForm (a j₀ ^ m) * (liftForm (a j₀ ^ d) * G - H * liftForm x) +
          (liftForm (a j₀ ^ m) * H) * liftForm x := by
      rw [pow_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hm')
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

  let Φ := Localization.localRingHom W 𝔮 φ hW𝔮
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨h, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    obtain ⟨e, T, hT, hTW⟩ := hlift t t.2
    have hs : T * liftForm (a j₀ ^ d) ∈ W.primeCompl := W.primeCompl.mul_mem hTW (hlfa d)
    refine ⟨IsLocalization.mk' _ (H * liftForm (a j₀ ^ e)) ⟨_, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    change (t : Polynomial (MRing ι O)) * φ (H * liftForm (a j₀ ^ e)) = φ (T * liftForm (a j₀ ^ d)) * h
    rw [map_mul, map_mul, hT]
    simp only [hφ, aeval_chartSubst_liftForm, hH]
    ring
  have hker : I.map (algebraMap _ (Localization.AtPrime W)) =
      (Jx.map (algebraMap _ (Localization.AtPrime 𝔮))).comap Φ := by
    ext z
    obtain ⟨⟨F, T⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [Ideal.mem_comap, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨s, hs, hsF⟩
      refine ⟨φ s, fun h => hs (by rw [hW𝔮]; exact h), ?_⟩
      rw [← map_mul]
      exact hIJ hsF
    · rintro ⟨t, ht, htF⟩
      obtain ⟨e, T', hT', hT'W⟩ := hlift t ht
      obtain ⟨m, hm⟩ := memI (T' * F) (by
        rw [map_mul, hT', mul_assoc]
        exact Ideal.mul_mem_left _ _ htF)
      exact ⟨liftForm (a j₀ ^ m) * T', W.primeCompl.mul_mem (hlfa m) hT'W, by rw [mul_assoc]; exact hm⟩
  have hsurj' : Function.Surjective
      ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) :=
    Ideal.Quotient.mk_surjective.comp hsurj
  have hker' : I.map (algebraMap _ (Localization.AtPrime W)) =
      RingHom.ker ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hker
  let τ := (Ideal.quotEquivOfEq hker').trans (RingHom.quotientKerEquivOfSurjective hsurj')
  unfold multAt
  rw [chartLength_localizedModule_quotient, chartLength_localizedModule_quotient,
    chartLength_quotient_self, chartLength_quotient_self]
  exact chartLength_self_eq_of_ringEquiv τ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
