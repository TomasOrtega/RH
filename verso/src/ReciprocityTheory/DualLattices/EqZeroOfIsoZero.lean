import ReciprocityTheory.DualLattices.AvgFZero

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section LiftR

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

/- English proof (translation)
Establish `hsub : ∀ y : LinearMap.range (Matrix.mulVecLin M), y = 0` using `fun y => e.injective (Subsingleton.elim _ _)`. Use extensionality with `i j`. Establish `h` using `hsub ⟨M *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩`. Establish `h'` using `congrArg (fun y : LinearMap.range (Matrix.mulVecLin M) => (y : n → R) i) h`. Simplify `h'` using `[Matrix.mulVec_single_one]`.
-/
private lemma eq_zero_of_iso_zero {n : Type} [Fintype n] {M : Matrix n n R}
    (e : LinearMap.range (Matrix.mulVecLin M) ≃ₗ[R] (Fin 0 → R)) : M = 0 := by
  classical
  have hsub : ∀ y : LinearMap.range (Matrix.mulVecLin M), y = 0 := fun y =>
    e.injective (Subsingleton.elim _ _)
  ext i j
  have h := hsub ⟨M *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩
  have h' := congrArg (fun y : LinearMap.range (Matrix.mulVecLin M) => (y : n → R) i) h
  simpa [Matrix.mulVec_single_one] using h'

/- English proof (translation)
Establish `hb : bt2 H U * U.εT i = U.εL i * H.Bt * U.εT i`. Unfold `bt2`. Rewrite using `[Matrix.sum_mul, Finset.sum_eq_single i]`. Rewrite using `[Matrix.mul_assoc, U.εT_orth, if_pos rfl]`. Introduce `x _ hx`.

Rewrite using `[Matrix.mul_assoc, U.εT_orth, if_neg hx, Matrix.mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `key : ∑ k, c k • (fromRows H.Ht (bt2 H U) * U.εT i) k = c ᵥ* (fromRows H.Ht (bt2 H U) * U.εT i)`. Use extensionality with `j`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]`. Rewrite using `[key, Matrix.fromRows_mul, hb, Matrix.vecMul_fromRows]`. Simplify using `only [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]`.
-/
private lemma row_decomp {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m)
    (c : Fin g ⊕ Fin g → R) :
    ∑ k, c k • (fromRows H.Ht (bt2 H U) * U.εT i) k =
      ((c ∘ Sum.inl) ᵥ* H.Ht + ((c ∘ Sum.inr) ᵥ* U.εL i) ᵥ* H.Bt) ᵥ* U.εT i := by
  have hb : bt2 H U * U.εT i = U.εL i * H.Bt * U.εT i := by
    unfold bt2
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · rw [Matrix.mul_assoc, U.εT_orth, if_pos rfl]
    · intro x _ hx
      rw [Matrix.mul_assoc, U.εT_orth, if_neg hx, Matrix.mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∑ k, c k • (fromRows H.Ht (bt2 H U) * U.εT i) k =
      c ᵥ* (fromRows H.Ht (bt2 H U) * U.εT i) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  rw [key, Matrix.fromRows_mul, hb, Matrix.vecMul_fromRows]
  simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X hX`. Take `⟨G, _, _, β, hmul, h1, hcard, hfrob, hsepG, hnt⟩` from `hG p g C v R O σ cp hp2 hS H U`. Take `⟨κ, Λ, ε, hΛdet, hΛblock, hεdiv, hεprod, hcard_n, hspan⟩` from `hE p g C v R O σ cp hS H U X hX`. Take `⟨hrank, hrzero⟩` from `hR p g C v R O σ cp hS H U`. Use `haveI : Nontrivial R := ⟨⟨(p : R), 0, fun h => hS.p_ne (by rw [h, map_zero, map_zero])⟩⟩`.

Establish `hεT : ∀ j, U.εT (κ j) ≠ 0`. Introduce `j h0`. Establish `hb` using `hΛblock j`. Rewrite `hb` using `[h0, Matrix.vecMul_zero]`. Apply `hΛdet.ne_zero` to reduce the goal to its premises.

Conclude with `Matrix.det_eq_zero_of_row_eq_zero j (fun k => by rw [← hb]; rfl)`. Establish `hlift : ∀ j, ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧ (∀ y, v (u y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1) ∧ (fun y => algebraMap R C (ε j) * u y) ∈ augIdeal H.AA.carrier ∧ (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg (κ j) (β δ)) * u (red p g t))`. Introduce `j`. Establish `hmem : ε j • Λ j ∈ Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT (κ j)) k)`. Rewrite using `[hspan (κ j)]`.

Conclude with `Submodule.subset_span ⟨j, rfl, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hmem`. Rewrite `hc` using `[row_decomp U (κ j) c]`. Conclude with `lift_one (hS := hS) (hp2 := hp2) (U := U) (hmul := hmul) (h1 := h1) (hsep := hsepG) (hcardG := hcard) (hi := hεT j) (hnt := hnt (κ j) (hεT j)) (e := ε j) (lam := Λ j) (hdiv := hεdiv j) (wH := c ∘ Sum.inl) (wB := (c ∘ Sum.inr) ᵥ* U.εL (κ j)) (hrow := hc)`. Use `choose u hu1 hu2 hu3 hu4 using hlift`.

Conclude with `⟨{ κ := κ card_phi := fun i => by`. Take `⟨n, hn1, hn2⟩` from `hrank i`. Rewrite using `[hcard_n (U.φ i) n hn2, hcard_n i n hn1]`. Use `r_zero := fun i hno => by`. Take `⟨n, hn1, -⟩` from `hrank i`.

Establish `hc` using `hcard_n i n hn1`. Establish `h0 : (Finset.univ.filter fun j => κ j = i).card = 0`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `fun j _ => hno j`. Establish `hn : n = 0` using `by omega`.

Substitute `hn` using the available equality. Conclude with `hrzero i (eq_zero_of_iso_zero hn1.some)`. Use `Λ := Λ`. Use `Λ_det := hΛdet`. Use `Λ_block := hΛblock`.

Use `ε := ε`. Use `ε_ne := fun j h0 => by`. Take `⟨c, hc⟩` from `hεdiv j`. Rewrite `hc` using `[h0, zero_mul]`. Establish `hv` using `hS.cp_val`.

Establish `hp1 : p - 1 ≠ 0`. Use `(Fact.out : p.Prime).two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hv` using `[hc, map_zero, map_zero, zero_pow hp1]`. Conclude with `hS.p_ne hv.symm`.

Use `ε_prod := hεprod`. Use `u := u`. Use `u_int := hu1`. Use `u_cong := hu2`. Use `x_mem := hu3`.

Use `s := Fintype.card G`. Use `b := fun k => β ((Fintype.equivFin G).symm k)`. Use `eig := fun j k t => hu4 j _ t`. Use `frobChar := fun j k => hfrob (κ j) _ (hεT j)`. Use `sep := fun j j' hne => by`.

Take `⟨γ, hγ⟩` from `hsepG (κ j) (κ j') (hεT j) (hεT j') hne`. Conclude with `⟨Fintype.equivFin G γ, by simpa using hγ⟩ }⟩`.
-/
theorem lifts_of (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement) :
    EigenLiftsStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X hX
  obtain ⟨G, _, _, β, hmul, h1, hcard, hfrob, hsepG, hnt⟩ := hG p g C v R O σ cp hp2 hS H U
  obtain ⟨κ, Λ, ε, hΛdet, hΛblock, hεdiv, hεprod, hcard_n, hspan⟩ :=
    hE p g C v R O σ cp hS H U X hX
  obtain ⟨hrank, hrzero⟩ := hR p g C v R O σ cp hS H U
  haveI : Nontrivial R := ⟨⟨(p : R), 0, fun h => hS.p_ne (by rw [h, map_zero, map_zero])⟩⟩
  have hεT : ∀ j, U.εT (κ j) ≠ 0 := by
    intro j h0
    have hb := hΛblock j
    rw [h0, Matrix.vecMul_zero] at hb
    apply hΛdet.ne_zero
    exact Matrix.det_eq_zero_of_row_eq_zero j (fun k => by rw [← hb]; rfl)
  have hlift : ∀ j, ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C (ε j) * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg (κ j) (β δ)) * u (red p g t)) := by
    intro j
    have hmem : ε j • Λ j ∈ Submodule.span R
        (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT (κ j)) k) := by
      rw [hspan (κ j)]
      exact Submodule.subset_span ⟨j, rfl, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
    rw [row_decomp U (κ j) c] at hc
    exact lift_one (hS := hS) (hp2 := hp2) (U := U) (hmul := hmul) (h1 := h1) (hsep := hsepG)
      (hcardG := hcard) (hi := hεT j) (hnt := hnt (κ j) (hεT j)) (e := ε j) (lam := Λ j)
      (hdiv := hεdiv j) (wH := c ∘ Sum.inl) (wB := (c ∘ Sum.inr) ᵥ* U.εL (κ j)) (hrow := hc)
  choose u hu1 hu2 hu3 hu4 using hlift
  exact ⟨{
    κ := κ
    card_phi := fun i => by
      obtain ⟨n, hn1, hn2⟩ := hrank i
      rw [hcard_n (U.φ i) n hn2, hcard_n i n hn1]
    r_zero := fun i hno => by
      obtain ⟨n, hn1, -⟩ := hrank i
      have hc := hcard_n i n hn1
      have h0 : (Finset.univ.filter fun j => κ j = i).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun j _ => hno j
      have hn : n = 0 := by omega
      subst hn
      exact hrzero i (eq_zero_of_iso_zero hn1.some)
    Λ := Λ
    Λ_det := hΛdet
    Λ_block := hΛblock
    ε := ε
    ε_ne := fun j h0 => by
      obtain ⟨c, hc⟩ := hεdiv j
      rw [h0, zero_mul] at hc
      have hv := hS.cp_val
      have hp1 : p - 1 ≠ 0 := by
        have := (Fact.out : p.Prime).two_le
        omega
      rw [hc, map_zero, map_zero, zero_pow hp1] at hv
      exact hS.p_ne hv.symm
    ε_prod := hεprod
    u := u
    u_int := hu1
    u_cong := hu2
    x_mem := hu3
    s := Fintype.card G
    b := fun k => β ((Fintype.equivFin G).symm k)
    eig := fun j k t => hu4 j _ t
    frobChar := fun j k => hfrob (κ j) _ (hεT j)
    sep := fun j j' hne => by
      obtain ⟨γ, hγ⟩ := hsepG (κ j) (κ j') (hεT j) (hεT j') hne
      exact ⟨Fintype.equivFin G γ, by simpa using hγ⟩ }⟩

end LiftR

end ReciprocityTheory.PGsh.Up
