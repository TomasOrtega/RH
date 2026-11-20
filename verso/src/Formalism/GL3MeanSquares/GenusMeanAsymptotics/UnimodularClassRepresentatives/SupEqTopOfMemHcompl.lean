import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.OrthogonalBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨Q, hQ, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hu'` using `(Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu`. Establish `huQ : u ∈ Q` using `hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))`. Establish `hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q` using `le_trans le_sup_right hle`.

Establish `hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K))` using `Ideal.map_le_iff_le_comap.1 hext`. Establish `hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Use `haveI := hQ.isPrime`. Establish `heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K))` using `hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ`. Break down `(comap_eq_comap_iff hK hF hP hQ).1 heq with h | h` into its components or cases.

Conclude with `hu'.1 (h ▸ huQ)`. Conclude with `hu'.2 (h ▸ huQ)`.
-/
theorem sup_eq_top_of_mem_hcompl (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hu' := (Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu
  have huQ : u ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q := le_trans le_sup_right hle
  have hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.map_le_iff_le_comap.1 hext
  have hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  haveI := hQ.isPrime
  have heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ
  rcases (comap_eq_comap_iff hK hF hP hQ).1 heq with h | h
  · exact hu'.1 (h ▸ huQ)
  · exact hu'.2 (h ▸ huQ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩`.
-/
private theorem isUnitIn_mul' {S : Subring K} {a b : K} (ha : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S a)
    (hb : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S b) : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `exists_maximal_over hK hF h𝔭`. Establish `hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L` using `(isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv`. Establish `hSD` using `Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hP.isPrime hU`. Establish `hdd : ∀ x, h x x = 0 → x = 0`. Introduce `x hx`.

Assume the negation of the conclusion as `hx0`. Use `hd x hx0 (Classical.arbitrary (NumberField.InfinitePlace K)).embedding` as an intermediate fact. Rewrite `this` using `[hx, map_zero, Complex.zero_re]`. Conclude with `lt_irrefl 0 this`. Take `⟨x, hxM, hxo, hxu⟩` from `Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame (Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing hK hP) (Formalism.HermitianLattices.Ext.L3.LocF.locRing_local hP.isPrime) hs hdd hSD`.

Establish `hx' : ∀ i, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P, s • x i ∈ L := fun i => hxM i`. Use `choose s hsP hsL using hx'`. Use `set b0 : Fin (finrank K V) → V := fun i => algebraMap (𝓞 K) K (s i) • x i with hb0`. Establish `hb0L : ∀ i, b0 i ∈ L`. Introduce `i`.

Simplify using `only [hb0, algebraMap_smul]`. Conclude with `hsL i`. Establish `hbb : ∀ i j, h (b0 i) (b0 j) = star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s j) * h (x i) (x j)`. Introduce `i j`. Simplify using `only [hb0, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hunit : ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn (Formalism.HermitianLattices.Ext.L3.WA.locRing P) (h (b0 i) (b0 i))`. Introduce `i`. Establish `hσ` using `(Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (s i)).2 (hsP i)`. Establish `hσs` using `(Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (conjO K (s i))).2 (Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl (hsP i))`.

Rewrite using `[hbb]`. Conclude with `isUnitIn_mul' (isUnitIn_mul' hσs hσ) (hxu i)`. Establish `horth : ∀ i j, i ≠ j → h (b0 i) (b0 j) = 0`. Introduce `i j hij`. Rewrite using `[hbb, hxo i j hij, mul_zero]`.

Establish `hint : ∀ i, h (b0 i) (b0 i) ∈ (1 : Submodule (𝓞 K) K)` using `fun i => hLi _ (hb0L i) _ (hb0L i)`. Use `choose u hu using fun i => Submodule.mem_one.1 (hint i)`. Establish `huP : ∀ i, u i ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P := by`. Introduce `i`. Use `(Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (u i)).1 ?_` and prove the remaining obligations.

Rewrite using `[hu i]`. Conclude with `hunit i`. Establish `hli : LinearIndependent K b0`. Rewrite using `[linearIndependent_iff']`. Introduce `t g hg i hi`.

Use `congrArg (h (b0 i)) hg` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero, Finset.sum_eq_single i]`. Rewrite `this` using `[map_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 this).resolve_right (hunit i).1`. Introduce `j _ hji`.

Rewrite using `[map_smul, horth i j (Ne.symm hji), smul_zero]`. Introduce `hi'`. Conclude with `absurd hi hi'`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range b0)` using `(Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])).ge`. Set `b` to `Basis.mk hli htop`.

Establish `hb : ⇑b = b0` using `Basis.coe_mk hli htop`. Use `⟨b, u, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hb]`. Conclude with `hb0L i`.

Rewrite using `[hb, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨t, ht, hy⟩`. Conclude with `⟨t, ht, (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb0L i)) hy⟩`. Introduce and unpack `y ⟨t, ht, hy⟩`.

Establish `hz : t • y ∈ Formalism.HermitianLatticesTheory.loc (K` using `K) P (Submodule.span (𝓞 K) (Set.range b0)) := by`. Rewrite using `[← b.sum_repr (t • y)]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `⟨u i, huP i, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_one.1 (hLi _ (hb0L i) _ hy)`.

Establish `hrep : h (b0 i) (t • y) = b.repr (t • y) i * h (b0 i) (b0 i)` using `by conv_lhs => rw [← b.sum_repr (t • y)]`. Rewrite using `[map_sum, Finset.sum_eq_single i]`. Rewrite using `[map_smul, smul_eq_mul, hb]`. Introduce `j _ hji`. Rewrite using `[map_smul, hb, horth i j (Ne.symm hji), smul_zero]`.

Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Establish `key : u i • (b.repr (t • y) i • b i) = a • b0 i`. Rewrite using `[← algebraMap_smul K (u i), smul_smul, hu i, mul_comm, ← hrep, ← ha, algebraMap_smul, hb]`. Rewrite using `[key]`.

Conclude with `Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨t', ht', hy'⟩` from `hz`. Conclude with `⟨t' * t, mul_mem ht' ht, by rw [mul_smul]; exact hy'⟩`. Introduce `i j`. Rewrite using `[hb, Matrix.diagonal_apply]`.

Use `split_ifs with hij`. Substitute `hij` using the available equality. Conclude with `hu i`. Rewrite using `[map_zero, horth i j hij]`. Introduce `i`.

Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Establish `h1 : algebraMap (𝓞 K) K (conjO K (u i)) = star (algebraMap (𝓞 K) K (u i))` using `rfl`. Rewrite using `[h1, hu i, ← starRingEnd_apply]`. Conclude with `hs.eq (b0 i) (b0 i)`. Introduce `i`.

Conclude with `sup_eq_top_of_mem_hcompl hK hF hP (huP i)`.
-/
theorem exists_orth_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (u : Fin (finrank K V) → 𝓞 K), (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
      (∀ i j, algebraMap (𝓞 K) K (diagonal u i j) = h (b i) (b j)) ∧
      (∀ i, conjO K (u i) = u i) ∧ ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  have hSD := Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hP.isPrime hU
  have hdd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hd x hx0 (Classical.arbitrary (NumberField.InfinitePlace K)).embedding
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl 0 this
  obtain ⟨x, hxM, hxo, hxu⟩ := Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame
    (Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing hK hP)
    (Formalism.HermitianLattices.Ext.L3.LocF.locRing_local hP.isPrime) hs hdd hSD
  have hx' : ∀ i, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • x i ∈ L := fun i => hxM i
  choose s hsP hsL using hx'
  set b0 : Fin (finrank K V) → V := fun i => algebraMap (𝓞 K) K (s i) • x i with hb0
  have hb0L : ∀ i, b0 i ∈ L := by
    intro i
    simp only [hb0, algebraMap_smul]
    exact hsL i
  have hbb : ∀ i j, h (b0 i) (b0 j) =
      star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s j) * h (x i) (x j) := by
    intro i j
    simp only [hb0, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply]
    ring
  have hunit : ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn (Formalism.HermitianLattices.Ext.L3.WA.locRing P) (h (b0 i) (b0 i)) := by
    intro i
    have hσ := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (s i)).2 (hsP i)
    have hσs := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (conjO K (s i))).2
      (Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl (hsP i))
    rw [hbb]
    exact isUnitIn_mul' (isUnitIn_mul' hσs hσ) (hxu i)
  have horth : ∀ i j, i ≠ j → h (b0 i) (b0 j) = 0 := by
    intro i j hij
    rw [hbb, hxo i j hij, mul_zero]
  have hint : ∀ i, h (b0 i) (b0 i) ∈ (1 : Submodule (𝓞 K) K) := fun i => hLi _ (hb0L i) _ (hb0L i)
  choose u hu using fun i => Submodule.mem_one.1 (hint i)
  have huP : ∀ i, u i ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    intro i
    refine (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (u i)).1 ?_
    rw [hu i]
    exact hunit i
  have hli : LinearIndependent K b0 := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have := congrArg (h (b0 i)) hg
    rw [map_sum, map_zero, Finset.sum_eq_single i] at this
    · rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (hunit i).1
    · intro j _ hji
      rw [map_smul, horth i j (Ne.symm hji), smul_zero]
    · intro hi'
      exact absurd hi hi'
  have htop : ⊤ ≤ Submodule.span K (Set.range b0) :=
    (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])).ge
  let b := Basis.mk hli htop
  have hb : ⇑b = b0 := Basis.coe_mk hli htop
  refine ⟨b, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hb0L i
  · rw [hb, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    apply le_antisymm
    · rintro y ⟨t, ht, hy⟩
      exact ⟨t, ht, (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb0L i)) hy⟩
    · rintro y ⟨t, ht, hy⟩
      have hz : t • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b0)) := by
        rw [← b.sum_repr (t • y)]
        refine Submodule.sum_mem _ fun i _ => ?_
        refine ⟨u i, huP i, ?_⟩
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hLi _ (hb0L i) _ hy)
        have hrep : h (b0 i) (t • y) = b.repr (t • y) i * h (b0 i) (b0 i) := by
          conv_lhs => rw [← b.sum_repr (t • y)]
          rw [map_sum, Finset.sum_eq_single i]
          · rw [map_smul, smul_eq_mul, hb]
          · intro j _ hji
            rw [map_smul, hb, horth i j (Ne.symm hji), smul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        have key : u i • (b.repr (t • y) i • b i) = a • b0 i := by
          rw [← algebraMap_smul K (u i), smul_smul, hu i, mul_comm, ← hrep, ← ha, algebraMap_smul, hb]
        rw [key]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨t', ht', hy'⟩ := hz
      exact ⟨t' * t, mul_mem ht' ht, by rw [mul_smul]; exact hy'⟩
  · intro i j
    rw [hb, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hu i
    · rw [map_zero, horth i j hij]
  · intro i
    apply IsFractionRing.injective (𝓞 K) K
    have h1 : algebraMap (𝓞 K) K (conjO K (u i)) = star (algebraMap (𝓞 K) K (u i)) := rfl
    rw [h1, hu i, ← starRingEnd_apply]
    exact hs.eq (b0 i) (b0 i)
  · intro i
    exact sup_eq_top_of_mem_hcompl hK hF hP (huP i)

end Formalism.HermitianLattices.Ext.L3.OrthogonalBases
