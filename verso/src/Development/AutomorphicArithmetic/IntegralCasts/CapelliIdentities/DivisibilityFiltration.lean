import Mathlib

/- English proof (translation)
Introduce `A D _ _ _ l f ϖ σ R E e r s S Z hl hE hEe he0 hr hs hR hS`. Set `N : Submodule A D` to `Z ⊔ (Submodule.span A S).map (LinearMap.lsmul A D f)`. Establish `hZN : ∀ z ∈ Z, z ∈ N` using `fun z hz => Submodule.mem_sup_left hz`. Establish `hfN : ∀ w ∈ Submodule.span A S, f • w ∈ N` using `fun w hw => Submodule.mem_sup_right (Submodule.mem_map.2 ⟨w, hw, rfl⟩)`. Establish `hpow : ∀ (n : ℕ) (a : A), f ∣ l ^ n * a → f ∣ a`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro a h`. Simplify using `using h`. Consider the case `succ n ih`.

Introduce `a h`. Conclude with `ih a (hl _ (by rwa [← mul_assoc, ← pow_succ']))`. Take `⟨t, ht_def⟩ : ∃ t : ℕ → A, ∀ y, t y = s y * l ^ (e y - E y)` from `⟨_, fun _ => rfl⟩`. Establish `ht : ∀ y, l ^ E y * t y = l ^ σ * r y`. Introduce `y`.

Rewrite using `[ht_def, ← hs y]`. Combine the equalities or inequalities in the displayed calculation. Establish `hS' : ∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧ l ^ σ • x - ∑ y ∈ Finset.range (R + 1), t y • c y ∈ Z`. Introduce `x hx`. Take `⟨c, h0, h1, h2⟩` from `hS x hx`.

Use `⟨c, h0, h1, ?_⟩` and prove the remaining obligations. Simplify `h2` using `only [ht_def]`. Establish `hbig : ∀ y, R < y → f ∣ t y`. Introduce `y hy`. Use `hpow (E y) _ ?_` and prove the remaining obligations.

Rewrite using `[ht]`. Conclude with `Dvd.dvd.mul_left ((dvd_sub_right (hR y hy)).1 (hr y)) _`. Establish `hprod : ∀ y z, ∃ u, t y * t z = f * u + l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z)`. Introduce `y z`. Establish `hd : f ∣ t y * t z - l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z)`.

Use `hpow (E y + E z) _ ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hr y`. Take `⟨b, hb⟩` from `hr z`. Take `⟨c, hc⟩` from `hr (y + z)`. Establish `hy : r y = ϖ ^ y - f * a` using `by rw [← ha]; ring`.

Establish `hz : r z = ϖ ^ z - f * b` using `by rw [← hb]; ring`. Establish `hyz : r (y + z) = ϖ ^ (y + z) - f * c` using `by rw [← hc]; ring`. Establish `e1 : l ^ (E y + E z) * (t y * t z) = (l ^ σ * r y) * (l ^ σ * r z)`. Rewrite using `[← ht y, ← ht z]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z)) = l ^ σ * (l ^ σ * r (y + z))`. Rewrite using `[← ht (y + z)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_add l σ]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = l ^ σ * (l ^ E (y + z) * t (y + z)) := by`. Rewrite using `[← pow_add, Nat.add_sub_cancel' (hE y z)]`. Rewrite using `[mul_sub, e1, e2, hy, hz, hyz]`. Use `⟨l ^ σ * l ^ σ * (c - a * ϖ ^ z - b * ϖ ^ y + f * a * b), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add ϖ y z]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨u, hu⟩` from `hd`. Conclude with `⟨u, by rw [← hu]; ring⟩`. Establish `hkey : ∀ (n y : ℕ), R + 1 ≤ y + n → ∀ w ∈ S, (l ^ σ * t y) • w ∈ N`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `y hy w hw`. Take `⟨u, hu⟩` from `hbig y (by omega)`. Establish `: (l ^ σ * t y) • w = f • ((l ^ σ * u) • w)`.

Rewrite using `[hu, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span hw))`.

Consider the case `succ n ih`. Introduce `y hy w hw`. Take `⟨c, hc0, hcS, hcZ⟩` from `hS' w hw`. Establish `hsplit : (l ^ σ * t y) • w = t y • (l ^ σ • w - ∑ z ∈ Finset.range (R + 1), t z • c z) + ∑ z ∈ Finset.range (R + 1), (t y * t z) • c z`. Rewrite using `[smul_sub, Finset.smul_sum, smul_smul, mul_comm (t y) (l ^ σ)]`.

Simplify using `only [smul_smul, sub_add_cancel]`. Rewrite using `[hsplit]`. Use `N.add_mem (hZN _ (Z.smul_mem _ hcZ)) (N.sum_mem ?_)` and prove the remaining obligations. Introduce `z _`. Break down `Nat.eq_zero_or_pos z with rfl | hz` into its components or cases.

Rewrite using `[hc0, smul_zero]`. Conclude with `N.zero_mem`. Take `⟨u, hu⟩` from `hprod y z`. Establish `hsum : (t y * t z) • c z = f • (u • c z) + l ^ (E (y + z) - (E y + E z)) • ((l ^ σ * t (y + z)) • c z)`. Rewrite using `[hu, add_smul, smul_smul, smul_smul, pow_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Conclude with `N.add_mem (hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span (hcS z)))) (N.smul_mem _ (ih (y + z) (by omega) _ (hcS z)))`. Establish `hgen : ∀ x ∈ S, l ^ (2 * σ) • x ∈ N`.

Introduce `x hx`. Take `⟨c, _, hcS, hcZ⟩` from `hS' x hx`. Establish `hsplit : l ^ (2 * σ) • x = l ^ σ • (l ^ σ • x - ∑ z ∈ Finset.range (R + 1), t z • c z) + ∑ z ∈ Finset.range (R + 1), (l ^ σ * t z) • c z`. Rewrite using `[smul_sub, Finset.smul_sum, two_mul, pow_add, smul_smul]`. Simplify using `only [smul_smul, sub_add_cancel]`.

Rewrite using `[hsplit]`. Conclude with `N.add_mem (hZN _ (Z.smul_mem _ hcZ)) (N.sum_mem fun z _ => hkey (R + 1) z (by omega) _ (hcS z))`. Establish `hall : Submodule.span A S ≤ N.comap (LinearMap.lsmul A D (l ^ (2 * σ)))` using `Submodule.span_le.2 fun x hx => hgen x hx`. Introduce `p hp`. Take `⟨z, hz, v, hv, hzv⟩` from `Submodule.mem_sup.1 (hall hp)`.

Take `⟨p', hp', rfl⟩` from `Submodule.mem_map.1 hv`. Use `⟨p', hp', ?_⟩` and prove the remaining obligations. Establish `: l ^ (2 * σ) • p - f • p' = z`. Establish `h2 : l ^ (2 * σ) • p = z + f • p'` using `hzv.symm`. Rewrite using `[h2, add_sub_cancel_right]`.

Rewrite using `[this]`. Conclude with `hz`.
-/
theorem UpperTheory.divisibility_filtration :
    ∀ {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (l f ϖ : A) (σ R : ℕ) (E e : ℕ → ℕ)
        (r s : ℕ → A) (S : Set D) (Z : Submodule A D),
        (∀ a : A, f ∣ l * a → f ∣ a) →
        (∀ a b, E a + E b ≤ E (a + b)) → (∀ y, E y ≤ e y) → e 0 = 0 →
        (∀ y, f ∣ ϖ ^ y - r y) → (∀ y, l ^ e y * s y = l ^ σ * r y) → (∀ y, R < y → f ∣ ϖ ^ y) →
        (∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
          l ^ σ • x - ∑ y ∈ Finset.range (R + 1), (s y * l ^ (e y - E y)) • c y ∈ Z) →
        ∀ p ∈ Submodule.span A S, ∃ p' ∈ Submodule.span A S, l ^ (2 * σ) • p - f • p' ∈ Z := by
  intro A D _ _ _ l f ϖ σ R E e r s S Z hl hE hEe he0 hr hs hR hS
  classical
  let N : Submodule A D := Z ⊔ (Submodule.span A S).map (LinearMap.lsmul A D f)
  have hZN : ∀ z ∈ Z, z ∈ N := fun z hz => Submodule.mem_sup_left hz
  have hfN : ∀ w ∈ Submodule.span A S, f • w ∈ N := fun w hw =>
    Submodule.mem_sup_right (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
  have hpow : ∀ (n : ℕ) (a : A), f ∣ l ^ n * a → f ∣ a := by
    intro n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      exact ih a (hl _ (by rwa [← mul_assoc, ← pow_succ']))
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ → A, ∀ y, t y = s y * l ^ (e y - E y) := ⟨_, fun _ => rfl⟩
  have ht : ∀ y, l ^ E y * t y = l ^ σ * r y := by
    intro y
    rw [ht_def, ← hs y]
    calc l ^ E y * (s y * l ^ (e y - E y))
        = (l ^ E y * l ^ (e y - E y)) * s y := by ring
      _ = l ^ e y * s y := by rw [← pow_add, Nat.add_sub_cancel' (hEe y)]
  have hS' : ∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
      l ^ σ • x - ∑ y ∈ Finset.range (R + 1), t y • c y ∈ Z := by
    intro x hx
    obtain ⟨c, h0, h1, h2⟩ := hS x hx
    refine ⟨c, h0, h1, ?_⟩
    simpa only [ht_def] using h2
  have hbig : ∀ y, R < y → f ∣ t y := by
    intro y hy
    refine hpow (E y) _ ?_
    rw [ht]
    exact Dvd.dvd.mul_left ((dvd_sub_right (hR y hy)).1 (hr y)) _
  have hprod : ∀ y z, ∃ u, t y * t z =
      f * u + l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
    intro y z
    have hd : f ∣ t y * t z - l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
      refine hpow (E y + E z) _ ?_
      obtain ⟨a, ha⟩ := hr y
      obtain ⟨b, hb⟩ := hr z
      obtain ⟨c, hc⟩ := hr (y + z)
      have hy : r y = ϖ ^ y - f * a := by rw [← ha]; ring
      have hz : r z = ϖ ^ z - f * b := by rw [← hb]; ring
      have hyz : r (y + z) = ϖ ^ (y + z) - f * c := by rw [← hc]; ring
      have e1 : l ^ (E y + E z) * (t y * t z) = (l ^ σ * r y) * (l ^ σ * r z) := by
        rw [← ht y, ← ht z]; ring
      have e2 : l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
          = l ^ σ * (l ^ σ * r (y + z)) := by
        rw [← ht (y + z)]
        calc l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
            = l ^ σ * ((l ^ (E y + E z) * l ^ (E (y + z) - (E y + E z))) * t (y + z)) := by
              rw [pow_add l σ]; ring
          _ = l ^ σ * (l ^ E (y + z) * t (y + z)) := by
              rw [← pow_add, Nat.add_sub_cancel' (hE y z)]
      rw [mul_sub, e1, e2, hy, hz, hyz]
      refine ⟨l ^ σ * l ^ σ * (c - a * ϖ ^ z - b * ϖ ^ y + f * a * b), ?_⟩
      rw [pow_add ϖ y z]
      ring
    obtain ⟨u, hu⟩ := hd
    exact ⟨u, by rw [← hu]; ring⟩
  have hkey : ∀ (n y : ℕ), R + 1 ≤ y + n → ∀ w ∈ S, (l ^ σ * t y) • w ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy w hw
      obtain ⟨u, hu⟩ := hbig y (by omega)
      have : (l ^ σ * t y) • w = f • ((l ^ σ * u) • w) := by
        rw [hu, smul_smul]; congr 1; ring
      rw [this]
      exact hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span hw))
    | succ n ih =>
      intro y hy w hw
      obtain ⟨c, hc0, hcS, hcZ⟩ := hS' w hw
      have hsplit : (l ^ σ * t y) • w =
          t y • (l ^ σ • w - ∑ z ∈ Finset.range (R + 1), t z • c z)
            + ∑ z ∈ Finset.range (R + 1), (t y * t z) • c z := by
        rw [smul_sub, Finset.smul_sum, smul_smul, mul_comm (t y) (l ^ σ)]
        simp only [smul_smul, sub_add_cancel]
      rw [hsplit]
      refine N.add_mem (hZN _ (Z.smul_mem _ hcZ)) (N.sum_mem ?_)
      intro z _
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · rw [hc0, smul_zero]
        exact N.zero_mem
      · obtain ⟨u, hu⟩ := hprod y z
        have hsum : (t y * t z) • c z = f • (u • c z)
            + l ^ (E (y + z) - (E y + E z)) • ((l ^ σ * t (y + z)) • c z) := by
          rw [hu, add_smul, smul_smul, smul_smul, pow_add]
          congr 2
          ring
        rw [hsum]
        exact N.add_mem (hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span (hcS z))))
          (N.smul_mem _ (ih (y + z) (by omega) _ (hcS z)))
  have hgen : ∀ x ∈ S, l ^ (2 * σ) • x ∈ N := by
    intro x hx
    obtain ⟨c, _, hcS, hcZ⟩ := hS' x hx
    have hsplit : l ^ (2 * σ) • x =
        l ^ σ • (l ^ σ • x - ∑ z ∈ Finset.range (R + 1), t z • c z)
          + ∑ z ∈ Finset.range (R + 1), (l ^ σ * t z) • c z := by
      rw [smul_sub, Finset.smul_sum, two_mul, pow_add, smul_smul]
      simp only [smul_smul, sub_add_cancel]
    rw [hsplit]
    exact N.add_mem (hZN _ (Z.smul_mem _ hcZ))
      (N.sum_mem fun z _ => hkey (R + 1) z (by omega) _ (hcS z))
  have hall : Submodule.span A S ≤ N.comap (LinearMap.lsmul A D (l ^ (2 * σ))) :=
    Submodule.span_le.2 fun x hx => hgen x hx
  intro p hp
  obtain ⟨z, hz, v, hv, hzv⟩ := Submodule.mem_sup.1 (hall hp)
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.1 hv
  refine ⟨p', hp', ?_⟩
  have : l ^ (2 * σ) • p - f • p' = z := by
    have h2 : l ^ (2 * σ) • p = z + f • p' := hzv.symm
    rw [h2, add_sub_cancel_right]
  rw [this]
  exact hz
