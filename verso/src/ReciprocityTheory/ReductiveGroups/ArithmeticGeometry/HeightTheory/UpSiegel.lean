import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormLineSectionPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PolyL2EqSqrtCoeffSum

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Establish `hF1 : F1 ≠ 0` using `hirr.ne_zero`. Take `⟨sF, hsF, hsFu⟩` from `Finset.exists_mem_eq_sup F1.support (Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF1)) uDeg`. Generalize the expression as in `hudef : F1.support.sup uDeg = u at hsFu`. Establish `hule : u ≤ (d.D + 1) * d.del` using `hsFu ▸ hu sF hsF`. Establish `hn96 : d.n96 = 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊)` using `rfl`.

Establish `hn : 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del ≤ d.n96`. Rewrite using `[hn96]; exact Nat.le_mul_of_pos_right _ (by omega)`. Establish `hdeln : d.del ≤ d.n96`. Use `le_trans ?_ hn` and prove the remaining obligations. Rewrite using `[show 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del = (8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1)) * d.del by ring]`.

Conclude with `Nat.le_mul_of_pos_left _ (by positivity)`. Establish `hdn : deF ≤ d.n96` using `le_trans hle hdeln`. Establish `hn' : d.n96' = 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del` using `rfl`. Establish `hun' : u ≤ d.n96'`. Establish `: (d.D + 1) * d.del ≤ d.n96'`.

Rewrite using `[hn', show 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del = (8 * d.n96 * ((d.D + 2) * (d.N + 1))) * ((d.D + 1) * d.del) by ring]`. Establish `: 0 < d.n96` using `by omega`. Conclude with `Nat.le_mul_of_pos_left _ (by positivity)`. Use linear arithmetic over natural numbers and integers. Establish `hadd : ∀ a ∈ F1.support, ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u), a + m ∈ upMono d.D d.N d.n96 d.n96'`.

Introduce `a ha m hm`. Rewrite `hm` using `[mem_upMono]`. Rewrite using `[mem_upMono, hups_xDeg_add, hups_uDeg_add, hx a ha]`. Establish `: uDeg a ≤ u` using `hudef ▸ Finset.le_sup ha`. Use linear arithmetic over natural numbers and integers.

Establish `hST : ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u), (F1 * MvPolynomial.monomial m 1).support ⊆ upMono d.D d.N d.n96 d.n96'`. Introduce `m hm s hs`. Take `⟨a, ha, m', hm', rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul _ _ hs)`. Establish `: m' = m` using `Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')`. Substitute `this` using the available equality.

Conclude with `hadd a ha m' hm`. Take `⟨b, hbL, hbli, hspan, hdeg⟩` from `satDeg_le K F1 hF1 (upMono d.D d.N d.n96 d.n96') (upMono d.D d.N (d.n96 - deF) (d.n96' - u)) (upMono d.D d.N d.n96 d.n96').equivFin hST`. Establish `hk : (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card < (upMono d.D d.N d.n96 d.n96').card`. Rewrite using `[card_upMono, card_upMono]`. Conclude with `hups_cardUX_lt _ _ _ _ _ _ h1 hdn`.

Take `⟨q, hqnot, hmean⟩` from `mink_sat K _ _ b hbli hbL hk`. Use `set e := (upMono d.D d.N d.n96 d.n96').equivFin with he`. Take `⟨Q, hQ⟩ : ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K), Q = ∑ i, MvPolynomial.monomial (e.symm i : UXVar d.D d.N →₀ ℕ) (q i)` from `⟨_, rfl⟩`. Establish `hQc : ∀ i, Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) = q i` using `fun i => by`. Rewrite using `[hQ, MvPolynomial.coeff_sum, Fintype.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `j hj`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Introduce `h`. Conclude with `hj (e.symm.injective (Subtype.ext h))`.

Establish `hQs : Q.support ⊆ upMono d.D d.N d.n96 d.n96'`. Introduce `s hs`. Assume the negation of the conclusion as `h`. Rewrite `hs` using `[MvPolynomial.mem_support_iff, hQ, MvPolynomial.coeff_sum]`. Apply `hs` to reduce the goal to its premises.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Conclude with `fun h' => h (h' ▸ (e.symm i).2)`. Establish `hQKs : (mapK Q).support ⊆ upMono d.D d.N d.n96 d.n96'` using `(MvPolynomial.support_map_subset _ _).trans hQs`. Establish `hQx : XHom d.n96 (mapK Q)` using `fun s hs => (mem_upMono.1 (hQKs hs)).1`.

Establish `hQu : UDegLE d.n96' (mapK Q)` using `fun s hs => (mem_upMono.1 (hQKs hs)).2`. Establish `hqQ : (fun i => ((q i : 𝓞 K) : K)) = fun i => ((Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) : 𝓞 K) : K)`. Use function extensionality and compare the values at `fun i => by rw [hQc]`. Use `⟨Q, hQx, hQu, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨P, hP⟩`.

Establish `hPS : P.support ⊆ upMono d.D d.N (d.n96 - deF) (d.n96' - u)` using `fun s hs => hups_cofactor hF1 hx hsF hsFu.symm (hP ▸ hQx) (hP ▸ hQu) s hs`. Apply `hqnot` to reduce the goal to its premises. Rewrite using `[hspan, Submodule.mem_span_range_iff_exists_fun]`. Use `⟨fun m => P.coeff m, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← hups_coeff_mul_of_supp F1 P _ hPS, ← hP, MvPolynomial.coeff_map, hQc]`. Establish `hqn : ∀ σ : K →+* ℂ, qnorm σ F1 d.n96 d.n96' Q = qdist σ b (fun i => ((q i : 𝓞 K) : K))` using `fun σ => by`. Rewrite using `[hqQ]`. Use `hups_qnorm_eq σ F1 _ _ (fun s hs => mem_upMono.1 hs) hadd ?_ e b hspan Q hQs` and prove the remaining obligations.

Introduce `P hPx hPu s hs`. Establish `hFσs : (MvPolynomial.map σ F1).support = F1.support` using `MvPolynomial.support_map_of_injective _ σ.injective`. Establish `hFσ0 : MvPolynomial.map σ F1 ≠ 0`. Introduce `h`. Apply `hF1` to reduce the goal to its premises.

Rewrite using `[← MvPolynomial.support_eq_empty, ← hFσs, h, MvPolynomial.support_zero]`. Conclude with `hups_cofactor hFσ0 (fun t ht => hx t (hFσs ▸ ht)) (hFσs ▸ hsF) hsFu.symm hPx hPu s hs`. Repeatedly rewrite using `[hqn]`. Use `hmean.trans ?_` and prove the remaining obligations. Establish `e4` using `hd.rd_le`.

Establish `e5` using `hups_log_rd_nonneg K`. Establish `hratio` using `hups_ratio d.D d.N d.n96 d.n96' deF u d.del h1 hle hule hn rfl`. Establish `hdK : (0 : ℝ) < Module.finrank ℚ K` using `Nat.cast_pos.2 Module.finrank_pos`. Establish `hkr : (((upMono d.D d.N d.n96 d.n96').card - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card : ℕ) : ℝ) = ((upMono d.D d.N d.n96 d.n96').card : ℝ) - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card` using `Nat.cast_sub hk.le`. Establish `hR : (0 : ℝ) < (((upMono d.D d.N d.n96 d.n96').card - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card : ℕ) : ℝ)` using `Nat.cast_pos.2 (Nat.sub_pos_of_lt hk)`.

Generalize the expression as in `ReciprocityTheory.MultiplicativeHeights.latDeg (K := K) (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K (upMono d.D d.N d.n96 d.n96').card) b) b = Ld at hdeg ⊢`. Simplify using `only [card_upMono] at hkr hR hdeg ⊢`. Generalize the expression as in `((cardUX d.D d.N d.n96 d.n96' - cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℕ) : ℝ) = R at hkr hR ⊢`. Generalize the expression as in `(cardUX d.D d.N d.n96 d.n96' : ℝ) = rr at hkr hratio ⊢`. Generalize the expression as in `(cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℝ) = kk at hkr hratio hdeg ⊢`.

Generalize the expression as in `(Module.finrank ℚ K : ℝ) = dK at hdK hdeg e4 e5 ⊢`. Generalize the expression as in `hT F1 = h at hpos hdeg ⊢`. Establish `hc : (0 : ℝ) < (d.D + 2) * deF` using `by positivity`. Establish `e1 : Ld / (dK * R) ≤ -(kk * h) / R`. Rewrite using `[div_le_div_iff₀ (by positivity) hR]`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : -(kk * h) / R ≤ -(d.n96 * h / ((d.D + 2) * deF))`. Rewrite using `[neg_div, neg_le_neg_iff, div_le_div_iff₀ hc hR]`. Establish `h' : (d.n96 : ℝ) * R ≤ (d.D + 2) * deF * kk` using `by rw [hkr]; nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h' hpos.le]`.

Establish `e3 : Real.log R ≤ Real.log rr` using `Real.log_le_log hR (by`. Establish `: (0 : ℝ) ≤ kk`. Assume the negation of the conclusion as `hneg`. Rewrite `hneg` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities.

Use the proof step `linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem up_siegel (hd : d.AxH 𝒜) (F1 : MvPolynomial (UXVar d.D d.N) K) (deF : ℕ)
    (h1 : 1 ≤ deF) (hle : deF ≤ d.del) (hirr : Irreducible F1) (hx : XHom deF F1)
    (hu : UDegLE ((d.D + 1) * d.del) F1) (hpos : 0 < hT F1) :
    ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K), XHom d.n96 (mapK Q) ∧ UDegLE d.n96' (mapK Q) ∧
      ¬ F1 ∣ mapK Q ∧
      meanK (fun σ => Real.log (qnorm σ F1 d.n96 d.n96' Q)) ≤
        -(d.n96 * hT F1 / ((d.D + 2) * deF)) +
          1 / 2 * Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO := by
  classical
  have hF1 : F1 ≠ 0 := hirr.ne_zero
  obtain ⟨sF, hsF, hsFu⟩ := Finset.exists_mem_eq_sup F1.support
    (Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF1)) uDeg
  generalize hudef : F1.support.sup uDeg = u at hsFu
  have hule : u ≤ (d.D + 1) * d.del := hsFu ▸ hu sF hsF
  have hn96 : d.n96 = 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊) := rfl
  have hn : 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del ≤ d.n96 := by
    rw [hn96]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hdeln : d.del ≤ d.n96 := by
    refine le_trans ?_ hn
    rw [show 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del =
      (8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1)) * d.del by ring]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hdn : deF ≤ d.n96 := le_trans hle hdeln
  have hn' : d.n96' = 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del := rfl
  have hun' : u ≤ d.n96' := by
    have : (d.D + 1) * d.del ≤ d.n96' := by
      rw [hn', show 8 * d.n96 * ((d.D + 2) * (d.N + 1)) * (d.D + 1) * d.del =
        (8 * d.n96 * ((d.D + 2) * (d.N + 1))) * ((d.D + 1) * d.del) by ring]
      have : 0 < d.n96 := by omega
      exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hadd : ∀ a ∈ F1.support, ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      a + m ∈ upMono d.D d.N d.n96 d.n96' := by
    intro a ha m hm
    rw [mem_upMono] at hm
    rw [mem_upMono, hups_xDeg_add, hups_uDeg_add, hx a ha]
    have : uDeg a ≤ u := hudef ▸ Finset.le_sup ha
    omega
  have hST : ∀ m ∈ upMono d.D d.N (d.n96 - deF) (d.n96' - u),
      (F1 * MvPolynomial.monomial m 1).support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro m hm s hs
    obtain ⟨a, ha, m', hm', rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hs)
    have : m' = m := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')
    subst this
    exact hadd a ha m' hm
  obtain ⟨b, hbL, hbli, hspan, hdeg⟩ := satDeg_le K F1 hF1 (upMono d.D d.N d.n96 d.n96')
    (upMono d.D d.N (d.n96 - deF) (d.n96' - u)) (upMono d.D d.N d.n96 d.n96').equivFin hST
  have hk : (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card < (upMono d.D d.N d.n96 d.n96').card := by
    rw [card_upMono, card_upMono]; exact hups_cardUX_lt _ _ _ _ _ _ h1 hdn
  obtain ⟨q, hqnot, hmean⟩ := mink_sat K _ _ b hbli hbL hk
  set e := (upMono d.D d.N d.n96 d.n96').equivFin with he
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (UXVar d.D d.N) (𝓞 K),
      Q = ∑ i, MvPolynomial.monomial (e.symm i : UXVar d.D d.N →₀ ℕ) (q i) := ⟨_, rfl⟩
  have hQc : ∀ i, Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) = q i := fun i => by
    rw [hQ, MvPolynomial.coeff_sum, Fintype.sum_eq_single i]
    · simp
    · intro j hj
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hj (e.symm.injective (Subtype.ext h))
  have hQs : Q.support ⊆ upMono d.D d.N d.n96 d.n96' := by
    intro s hs
    by_contra h
    rw [MvPolynomial.mem_support_iff, hQ, MvPolynomial.coeff_sum] at hs
    apply hs
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h' => h (h' ▸ (e.symm i).2)
  have hQKs : (mapK Q).support ⊆ upMono d.D d.N d.n96 d.n96' :=
    (MvPolynomial.support_map_subset _ _).trans hQs
  have hQx : XHom d.n96 (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).1
  have hQu : UDegLE d.n96' (mapK Q) := fun s hs => (mem_upMono.1 (hQKs hs)).2
  have hqQ : (fun i => ((q i : 𝓞 K) : K)) =
      fun i => ((Q.coeff (e.symm i : UXVar d.D d.N →₀ ℕ) : 𝓞 K) : K) :=
    funext fun i => by rw [hQc]
  refine ⟨Q, hQx, hQu, ?_, ?_⟩
  · rintro ⟨P, hP⟩
    have hPS : P.support ⊆ upMono d.D d.N (d.n96 - deF) (d.n96' - u) := fun s hs =>
      hups_cofactor hF1 hx hsF hsFu.symm (hP ▸ hQx) (hP ▸ hQu) s hs
    apply hqnot
    rw [hspan, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun m => P.coeff m, funext fun i => ?_⟩
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hups_coeff_mul_of_supp F1 P _ hPS, ← hP, MvPolynomial.coeff_map, hQc]
  · have hqn : ∀ σ : K →+* ℂ, qnorm σ F1 d.n96 d.n96' Q = qdist σ b (fun i => ((q i : 𝓞 K) : K)) :=
      fun σ => by
        rw [hqQ]
        refine hups_qnorm_eq σ F1 _ _ (fun s hs => mem_upMono.1 hs) hadd ?_ e b hspan Q hQs
        intro P hPx hPu s hs
        have hFσs : (MvPolynomial.map σ F1).support = F1.support :=
          MvPolynomial.support_map_of_injective _ σ.injective
        have hFσ0 : MvPolynomial.map σ F1 ≠ 0 := by
          intro h; apply hF1
          rw [← MvPolynomial.support_eq_empty, ← hFσs, h, MvPolynomial.support_zero]
        exact hups_cofactor hFσ0 (fun t ht => hx t (hFσs ▸ ht)) (hFσs ▸ hsF) hsFu.symm hPx hPu s hs
    simp_rw [hqn]
    refine hmean.trans ?_
    have e4 := hd.rd_le
    have e5 := hups_log_rd_nonneg K
    have hratio := hups_ratio d.D d.N d.n96 d.n96' deF u d.del h1 hle hule hn rfl
    have hdK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    have hkr : (((upMono d.D d.N d.n96 d.n96').card - (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card
        : ℕ) : ℝ) = ((upMono d.D d.N d.n96 d.n96').card : ℝ) -
          (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card := Nat.cast_sub hk.le
    have hR : (0 : ℝ) < (((upMono d.D d.N d.n96 d.n96').card -
        (upMono d.D d.N (d.n96 - deF) (d.n96' - u)).card : ℕ) : ℝ) :=
      Nat.cast_pos.2 (Nat.sub_pos_of_lt hk)
    generalize ReciprocityTheory.MultiplicativeHeights.latDeg (K := K) (fun _ => 1)
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K (upMono d.D d.N d.n96 d.n96').card) b) b = Ld at hdeg ⊢
    simp only [card_upMono] at hkr hR hdeg ⊢
    generalize ((cardUX d.D d.N d.n96 d.n96' - cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℕ) : ℝ) = R
      at hkr hR ⊢
    generalize (cardUX d.D d.N d.n96 d.n96' : ℝ) = rr at hkr hratio ⊢
    generalize (cardUX d.D d.N (d.n96 - deF) (d.n96' - u) : ℝ) = kk at hkr hratio hdeg ⊢
    generalize (Module.finrank ℚ K : ℝ) = dK at hdK hdeg e4 e5 ⊢
    generalize hT F1 = h at hpos hdeg ⊢
    have hc : (0 : ℝ) < (d.D + 2) * deF := by positivity
    have e1 : Ld / (dK * R) ≤ -(kk * h) / R := by
      rw [div_le_div_iff₀ (by positivity) hR]
      calc Ld * R ≤ -(kk * dK * h) * R := mul_le_mul_of_nonneg_right hdeg hR.le
        _ = _ := by ring
    have e2 : -(kk * h) / R ≤ -(d.n96 * h / ((d.D + 2) * deF)) := by
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hc hR]
      have h' : (d.n96 : ℝ) * R ≤ (d.D + 2) * deF * kk := by rw [hkr]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h' hpos.le]
    have e3 : Real.log R ≤ Real.log rr := Real.log_le_log hR (by
      have : (0 : ℝ) ≤ kk := by
        by_contra hneg
        rw [not_le] at hneg
        nlinarith
      linarith)
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
