import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]`. Establish `h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B)`. Use extensionality with `q`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]`. Conclude with `SetLike.coe_subset_coe`.

Rewrite using `[h]`.
-/
theorem ringKrullDim_quotient_eq_coheight {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]

/- English proof (translation)
Establish `: Nonempty (PrimeSpectrum B)` using `⟨⟨P, hP⟩⟩`. Rewrite using `[ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]`. Conclude with `le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩`.
-/
theorem height_add_ringKrullDim_quotient_le {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩

/- English proof (translation)
Use `set I := Ideal.span {y} with hI`. Establish `hIP : I ≤ P` using `(Ideal.span_singleton_le_iff_mem P).mpr hyP`. Establish `hP' : (P.map (Ideal.Quotient.mk I)).IsPrime` using `Ideal.isPrime_map_quotientMk_of_isPrime hIP`. Take `⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n` from `ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm`. Rewrite using `[hn]`.

Take `⟨l, hlast, hlen⟩` from `Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I)) (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)`. Set `f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B` to `PrimeSpectrum.comap (Ideal.Quotient.mk I)`. Establish `hf : StrictMono f`. Use `Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)` and prove the remaining obligations. Rewrite `hab`, the goal using `[← PrimeSpectrum.asIdeal_le_asIdeal]`.

Conclude with `Ideal.comap_mono hab`. Use `ext1`. Use `congrArg PrimeSpectrum.asIdeal hab` as an intermediate fact. Conclude with `Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this`. Set `L` to `l.map f hf`.

Establish `hyhead : y ∈ L.head.asIdeal`. Express the relevant statement in the definitionally equal form `y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]`. Conclude with `Ideal.zero_mem _`. Take `⟨p, hp, hple⟩` from `Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le`.

Set `p0 : PrimeSpectrum B` to `⟨p, hp.1.1⟩`. Establish `hlt : p0 < L.head`. Use `lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_` and prove the remaining obligations. Establish `hyp : y ∈ p`. Establish `: p = L.head.asIdeal` using `congrArg PrimeSpectrum.asIdeal h`.

Rewrite using `[this]`. Conclude with `hyhead`. Conclude with `Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩`. Set `L'` to `L.cons p0 hlt`. Establish `hLlast : L'.last = ⟨P, hP⟩`.

Simplify using `only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]`. Use `ext1`. Conclude with `Ideal.comap_map_mk hIP`. Establish `hlen' : L'.length = n + 1`. Simplify using `[L', L, hlen]`.

Use `Order.length_le_height_last (p := L')` as an intermediate fact. Rewrite `this` using `[hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight]`. Conclude with `this` after adjusting the coercions.
-/
theorem height_map_add_one_le_of_mem_nonZeroDivisors {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by
  set I := Ideal.span {y} with hI
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm
  rw [hn]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I))
    (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)
  let f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hab ⊢
      exact Ideal.comap_mono hab
    · ext1
      have := congrArg PrimeSpectrum.asIdeal hab
      exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
  let L := l.map f hf
  have hyhead : y ∈ L.head.asIdeal := by
    change y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le
  let p0 : PrimeSpectrum B := ⟨p, hp.1.1⟩
  have hlt : p0 < L.head := by
    refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_
    have hyp : y ∈ p := by
      have : p = L.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [this]
      exact hyhead
    exact Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩
  let L' := L.cons p0 hlt
  have hLlast : L'.last = ⟨P, hP⟩ := by
    simp only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]
    ext1
    exact Ideal.comap_map_mk hIP
  have hlen' : L'.length = n + 1 := by
    simp [L', L, hlen]
  have := Order.length_le_height_last (p := L')
  rw [hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight] at this
  exact_mod_cast this

end GroundTheory.Heights₂.Heights
