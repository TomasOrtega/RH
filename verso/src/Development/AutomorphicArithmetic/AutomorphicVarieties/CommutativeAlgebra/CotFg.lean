import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {X : Type} [AddCommGroup X]

/- English proof (translation)
Use `Ideal.pow_le_pow_right hn ?_` and prove the remaining obligations. Rewrite using `[Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _`.
-/
private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

/- English proof (translation)
Rewrite using `[MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]`. Simplify using `[WPres.z]`.
-/
private lemma π_monomial (W : WPres O X R) (m : W.σ →₀ ℕ) :
    W.π (monomial m 1) = m.prod fun i k => W.z i ^ k := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
  simp [WPres.z]

/- English proof (translation)
Rewrite using `[RingHom.mem_ker, WPres.z, W.origin_π]`. Simplify using the standard rewrite rules.
-/
private lemma z_mem_ker (W : WPres O X R) (h : W.HasOrigin) (i : W.σ) : W.z i ∈ RingHom.ker (W.origin h) := by
  rw [RingHom.mem_ker, WPres.z, W.origin_π]
  simp

/- English proof (translation)
Break down `(by omega : m.degree = 0 ∨ m.degree = 1) with h | h` into its components or cases. Conclude with `Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)`. Use `right`. Take `⟨s, hs⟩` from `(Finsupp.sum_eq_one_iff m).1 (by rw [← h, Finsupp.degree_apply]; rfl)`. Conclude with `⟨s, hs⟩`.
-/
private lemma deg_lt_two {σ : Type} (m : σ →₀ ℕ) (hm : m.degree < 2) :
    m = 0 ∨ ∃ s, m = Finsupp.single s 1 := by
  rcases (by omega : m.degree = 0 ∨ m.degree = 1) with h | h
  · exact Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)
  · right
    obtain ⟨s, hs⟩ := (Finsupp.sum_eq_one_iff m).1 (by rw [← h, Finsupp.degree_apply]; rfl)
    exact ⟨s, hs⟩

/- English proof (translation)
Take `⟨μ, hμ, hs⟩` from `part_span O R X W {m | Finsupp.weight W.wt m = j ∧ 2 ≤ m.degree} j (fun _ hm => hm.1)`. Take `⟨b, hb, hbs⟩` from `hs g hg`. Establish `h3 : y = ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hy, hbs, map_sum]`.

Simplify using `[π_monomial, Finsupp.prod, WPres.zA]`. Rewrite using `[h3]`. Conclude with `Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _ (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)`.
-/
private lemma sq_mem [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) (j : X)
    (g : MvPowerSeries W.σ O) (hg : ∀ m, ¬ (Finsupp.weight W.wt m = j ∧ 2 ≤ m.degree) → coeff m g = 0)
    (y : W.A) (hy : W.π g = (y : R)) : y ∈ RingHom.ker (W.originA h) ^ 2 := by
  obtain ⟨μ, hμ, hs⟩ := part_span O R X W {m | Finsupp.weight W.wt m = j ∧ 2 ≤ m.degree} j (fun _ hm => hm.1)
  obtain ⟨b, hb, hbs⟩ := hs g hg
  have h3 : y = ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k := by
    apply Subtype.ext
    rw [← hy, hbs, map_sum]
    simp [π_monomial, Finsupp.prod, WPres.zA]
  rw [h3]
  exact Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _
    (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)

end

/- English proof (translation)
Introduce `O X R _ _ _ _ _ _ W h _ _ j`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨⟨f, hf, hfx⟩, hx⟩, rfl⟩`. Establish `hfx' : W.π f = (x : R)` using `hfx`. Establish `h0 : constantCoeff f = 0`.

Rewrite using `[← W.origin_π h, hfx']`. Conclude with `hx`. Establish `key : x - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s ∈ RingHom.ker (W.originA h) ^ 2`. Use `sq_mem W h j (f - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • MvPowerSeries.X s.1) (fun m hm => ?_) _ (by simp [hfx', WPres.zA, WPres.z])` and prove the remaining obligations. Rewrite using `[map_sub, map_sum]`.

Simplify using `only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hw : Finsupp.weight W.wt m = j`. Break down `deg_lt_two m (not_le.1 fun h2 => hm ⟨hw, h2⟩) with rfl | ⟨s, rfl⟩` into its components or cases. Rewrite using `[Finset.sum_eq_zero fun s _ => if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]`. Simplify using `using h0`.

Establish `hs : W.wt s = j` using `by simpa [Finsupp.weight_single] using hw`. Rewrite using `[Finset.sum_eq_single (⟨s, hs⟩ : {s // W.wt s = j}), if_pos rfl, sub_self]`. Introduce `t _ ht`. Rewrite using `[if_neg]`. Introduce `h2`.

Conclude with `ht (Subtype.ext (Finsupp.single_left_injective one_ne_zero h2).symm)`. Simplify using the standard rewrite rules. Rewrite using `[hf m hw, Finset.sum_eq_zero, sub_self]`. Introduce `s _`. Rewrite using `[if_neg]`.

Introduce and unpack `rfl`. Conclude with `hw (by simpa [Finsupp.weight_single] using s.2)`. Establish `h2 : (satSq (W.originA h)).mkQ x = (satSq (W.originA h)).mkQ (∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s)` using `(Submodule.Quotient.eq _).2 ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Rewrite using `[h2, map_sum]`. Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨s, rfl⟩, rfl⟩`. Conclude with `⟨W.zA s, ⟨W.z_mem s, z_mem_ker W h s⟩, rfl⟩`.
-/
theorem UpperTheory.V.Alg.cot_fg :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (j : X), cotLat (W.originA h) W.gr j = cotSpan (W.originA h) fun s : {s // W.wt s = j} => W.zA s := by
  intro O X R _ _ _ _ _ _ W h _ _ j
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨⟨f, hf, hfx⟩, hx⟩, rfl⟩
    have hfx' : W.π f = (x : R) := hfx
    have h0 : constantCoeff f = 0 := by
      rw [← W.origin_π h, hfx']
      exact hx
    have key : x - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s ∈
        RingHom.ker (W.originA h) ^ 2 := by
      refine sq_mem W h j (f - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • MvPowerSeries.X s.1)
        (fun m hm => ?_) _ (by simp [hfx', WPres.zA, WPres.z])
      rw [map_sub, map_sum]
      simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hw : Finsupp.weight W.wt m = j
      · rcases deg_lt_two m (not_le.1 fun h2 => hm ⟨hw, h2⟩) with rfl | ⟨s, rfl⟩
        · rw [Finset.sum_eq_zero fun s _ => if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
          simpa using h0
        · have hs : W.wt s = j := by simpa [Finsupp.weight_single] using hw
          rw [Finset.sum_eq_single (⟨s, hs⟩ : {s // W.wt s = j}), if_pos rfl, sub_self]
          · intro t _ ht
            rw [if_neg]
            intro h2
            exact ht (Subtype.ext (Finsupp.single_left_injective one_ne_zero h2).symm)
          · simp
      · rw [hf m hw, Finset.sum_eq_zero, sub_self]
        intro s _
        rw [if_neg]
        rintro rfl
        exact hw (by simpa [Finsupp.weight_single] using s.2)
    have h2 : (satSq (W.originA h)).mkQ x = (satSq (W.originA h)).mkQ
        (∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s) :=
      (Submodule.Quotient.eq _).2 ⟨1, one_ne_zero, by rwa [one_smul]⟩
    rw [h2, map_sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s, rfl⟩, rfl⟩
    exact ⟨W.zA s, ⟨W.z_mem s, z_mem_ker W h s⟩, rfl⟩
