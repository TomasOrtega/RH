import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

/- English proof (translation)
Introduce `A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂`. Unfold `UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂`. Establish `hM1 : (M₁ : A) ≠ 0` using `Nat.cast_ne_zero.mpr hpos.ne'`. Establish `hMc : (M₁ : A) = (t : A) * (M₂ : A)` using `by rw [hM]; push_cast; ring`. Use `set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁`.

Establish `hI₁0 : I₁ ≠ ⊥`. Introduce `h`. Establish `hmem : (M₁ : A) ∈ I₁` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `hM1 hmem`.

Establish `h𝔟0 : 𝔟₁ ≠ ⊥`. Introduce `h`. Rewrite `h₁` using `[h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hM1 h₁`. Establish `hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁`.

Introduce `J hJ`. Establish `h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁`. Rewrite using `[h₁]`. Conclude with `le_trans (Ideal.mul_mono_right hle) hJ`. Rewrite `h3`, the goal using `[← Ideal.dvd_iff_le]`.

Conclude with `(mul_dvd_mul_iff_right h𝔟0).mp h3`. Establish `hta : (t : A) * a₂ ∈ I₁`. Establish `hsp : Ideal.span {(t : A) * a₂} ≤ I₁`. Apply `hkey` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc, ← Ideal.span_singleton_mul_span_singleton, ← h₂]`.

Conclude with `Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)`. Conclude with `hsp (Ideal.mem_span_singleton_self _)`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hta`. Take `⟨ε, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`.

Use `⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩` and prove the remaining obligations. Establish `hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} = Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)})`. Rewrite using `[Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (sup_le ?_ ?_) le_sup_right` and prove the remaining obligations.

Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `hae : a₁ * ε = (t : A) * a₂ - d * M₁` using `by rw [← hyz]; ring`. Rewrite using `[hae]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Conclude with `Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, ← hyz]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_)) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `Ideal.mem_span_singleton_self _`. Apply `mul_left_cancel₀ hI₁0` to reduce the goal to its premises. Rewrite using `[h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂, Ideal.span_singleton_mul_span_singleton, ← hMc]`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.O.epsEx :
    UpperTheory.Gal.FiniteEtaleModels.O.EpsEx := by
  intro A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂
  unfold UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂
  have hM1 : (M₁ : A) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hMc : (M₁ : A) = (t : A) * (M₂ : A) := by rw [hM]; push_cast; ring
  set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁
  have hI₁0 : I₁ ≠ ⊥ := by
    intro h
    have hmem : (M₁ : A) ∈ I₁ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact hM1 hmem
  have h𝔟0 : 𝔟₁ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    exact hM1 h₁
  have hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁ := by
    intro J hJ
    have h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁ := by
      rw [h₁]
      exact le_trans (Ideal.mul_mono_right hle) hJ
    rw [← Ideal.dvd_iff_le] at h3 ⊢
    exact (mul_dvd_mul_iff_right h𝔟0).mp h3
  have hta : (t : A) * a₂ ∈ I₁ := by
    have hsp : Ideal.span {(t : A) * a₂} ≤ I₁ := by
      apply hkey
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc,
        ← Ideal.span_singleton_mul_span_singleton, ← h₂]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    exact hsp (Ideal.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hta
  obtain ⟨ε, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩
  have hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} =
      Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) := by
    rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have hae : a₁ * ε = (t : A) * a₂ - d * M₁ := by rw [← hyz]; ring
        rw [hae]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, ← hyz]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [mul_comm]
      exact Ideal.mem_span_singleton_self _
  apply mul_left_cancel₀ hI₁0
  rw [h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂,
    Ideal.span_singleton_mul_span_singleton, ← hMc]
