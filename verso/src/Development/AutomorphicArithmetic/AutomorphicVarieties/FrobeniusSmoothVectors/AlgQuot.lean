import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `key : ∀ x y : R, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] → x = y`. Introduce `x y hxy`. Rewrite `hxy` using `[h, Submodule.bot_smul]`. Conclude with `SModEq.bot.mp hxy`. Use `{ haus' := fun x hx => key x 0 (hx n), prec' := fun {f} hf => ⟨f n, fun m => ?_⟩ }` and prove the remaining obligations.

Break down `le_total m n with hmn | hnm` into its components or cases. Conclude with `hf hmn`. Rewrite using `[key _ _ (hf hnm)]`.
-/
private theorem adicComplete_of_pow_eq_bot {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (h : I ^ n = ⊥) :
    IsAdicComplete I R := by
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [h, Submodule.bot_smul] at hxy
    exact SModEq.bot.mp hxy
  refine { haus' := fun x hx => key x 0 (hx n), prec' := fun {f} hf => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hnm
  · exact hf hmn
  · rw [key _ _ (hf hnm)]

/- English proof (translation)
Introduce `O _ _ C _ _ _ D _ _ _ _ 𝔪 hV N`. Establish `hle : 𝔪 ^ (N + 1) ≤ 𝔪` using `Ideal.pow_le_self (Nat.succ_ne_zero N)`. Establish `hmax : 𝔪.IsMaximal`. Rewrite using `[Ideal.isMaximal_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Establish `h1' : (1 : C) ∈ 𝔪.comap (algebraMap C D)`. Rewrite using `[Ideal.mem_comap, map_one]`. Conclude with `h1`. Rewrite `h1'` using `[hV.comap]`.

Conclude with `(maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).mpr h1')`. Introduce `J x hJ hx hxJ`. Take `⟨c, hc⟩` from `hV.surj x`. Establish `hcu : IsUnit c`. Assume the negation of the conclusion as `hnu`.

Establish `hcm : c ∈ maximalIdeal C` using `hnu`. Rewrite `hcm` using `[← hV.comap, Ideal.mem_comap]`. Apply `hx` to reduce the goal to its premises. Use `𝔪.add_mem hc hcm` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hcJ : algebraMap C D c ∈ J`. Use `J.sub_mem hxJ (hJ hc)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[Ideal.eq_top_of_isUnit_mem J hcJ (hcu.map _)]`. Conclude with `Submodule.mem_top`.

Use `set M : Ideal (D ⧸ 𝔪 ^ (N + 1)) := 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) with hM`. Establish `hmem : ∀ d : D, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d ∈ M ↔ d ∈ 𝔪` using `fun d => Ideal.mem_quotient_iff_mem hle`. Establish `hMmax : M.IsMaximal`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (𝔪 ^ (N + 1))) Ideal.Quotient.mk_surjective hmax with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) 1 ∈ M`. Rewrite `h` using `[← hM]`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Conclude with `hmax.ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mp h1))`.

Conclude with `h`. Establish `hMpow : M ^ (N + 1) = ⊥`. Rewrite using `[hM, ← Ideal.map_pow, Ideal.map_quotient_self]`. Establish `hnil : nilradical (D ⧸ 𝔪 ^ (N + 1)) = M`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `nilradical_le_prime M`. Introduce `x hx`. Use `⟨N + 1, ?_⟩` and prove the remaining obligations. Use `Ideal.pow_mem_pow hx (N + 1)` as an intermediate fact. Rewrite `this` using `[hMpow]`.

Conclude with `(Submodule.mem_bot _).mp this`. Use `haveI : (nilradical (D ⧸ 𝔪 ^ (N + 1))).IsMaximal := hnil ▸ hMmax`. Use `haveI hloc : IsLocalRing (D ⧸ 𝔪 ^ (N + 1)) := IsLocalRing.of_isMaximal_nilradical _`. Establish `hMeq : maximalIdeal (D ⧸ 𝔪 ^ (N + 1)) = M` using `(IsLocalRing.eq_maximalIdeal hMmax).symm`. Establish `halg : ∀ a : O, algebraMap O (D ⧸ 𝔪 ^ (N + 1)) a = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (algebraMap O C a))`.

Introduce `a`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression. Use `haveI : IsNoetherianRing D := hV.noeth`. Use `⟨@IsCO.mk O (D ⧸ 𝔪 ^ (N + 1)) _ _ _ _ hloc inferInstance ?_ ?_ ?_, hMeq⟩` and prove the remaining obligations.

Rewrite using `[hMeq]`. Conclude with `adicComplete_of_pow_eq_bot M (N + 1) hMpow`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `hC : IsUnit (algebraMap O C a)`. Assume the negation of the conclusion as `hnu`.

Establish `hcm : algebraMap O C a ∈ maximalIdeal C` using `hnu`. Rewrite `hcm` using `[← hV.comap, Ideal.mem_comap, ← hmem, ← halg, ← hMeq]`. Conclude with `hcm ha`. Conclude with `(IsCO.isLocalHom (O := O) (R := C)).map_nonunit a hC`. Introduce `x`.

Take `⟨d, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨c, hc⟩` from `hV.surj d`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) c`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hMeq, halg, ← map_sub, hmem]`.

Establish `hca : algebraMap C D (c - algebraMap O C a) ∈ 𝔪`. Rewrite using `[← Ideal.mem_comap, hV.comap]`. Conclude with `ha`. Use `𝔪.add_mem hc hca` as an intermediate fact. Rewrite `this` using `[map_sub, sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Fr.alg_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ N : ℕ, ∃ h : IsCO O (D ⧸ 𝔪 ^ (N + 1)), @maximalIdeal _ _ h.toIsLocalRing = 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
  intro O _ _ C _ _ _ D _ _ _ _ 𝔪 hV N
  have hle : 𝔪 ^ (N + 1) ≤ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hmax : 𝔪.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      have h1' : (1 : C) ∈ 𝔪.comap (algebraMap C D) := by
        rw [Ideal.mem_comap, map_one]
        exact h1
      rw [hV.comap] at h1'
      exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).mpr h1')
    · intro J x hJ hx hxJ
      obtain ⟨c, hc⟩ := hV.surj x
      have hcu : IsUnit c := by
        by_contra hnu
        have hcm : c ∈ maximalIdeal C := hnu
        rw [← hV.comap, Ideal.mem_comap] at hcm
        apply hx
        have := 𝔪.add_mem hc hcm
        rwa [sub_add_cancel] at this
      have hcJ : algebraMap C D c ∈ J := by
        have := J.sub_mem hxJ (hJ hc)
        rwa [sub_sub_cancel] at this
      rw [Ideal.eq_top_of_isUnit_mem J hcJ (hcu.map _)]
      exact Submodule.mem_top
  set M : Ideal (D ⧸ 𝔪 ^ (N + 1)) := 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) with hM
  have hmem : ∀ d : D, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d ∈ M ↔ d ∈ 𝔪 :=
    fun d => Ideal.mem_quotient_iff_mem hle
  have hMmax : M.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (𝔪 ^ (N + 1)))
      Ideal.Quotient.mk_surjective hmax with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) 1 ∈ M := by
        rw [← hM] at h
        rw [h]
        exact Submodule.mem_top
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mp h1))
    · exact h
  have hMpow : M ^ (N + 1) = ⊥ := by
    rw [hM, ← Ideal.map_pow, Ideal.map_quotient_self]
  have hnil : nilradical (D ⧸ 𝔪 ^ (N + 1)) = M := by
    apply le_antisymm
    · exact nilradical_le_prime M
    · intro x hx
      refine ⟨N + 1, ?_⟩
      have := Ideal.pow_mem_pow hx (N + 1)
      rw [hMpow] at this
      exact (Submodule.mem_bot _).mp this
  haveI : (nilradical (D ⧸ 𝔪 ^ (N + 1))).IsMaximal := hnil ▸ hMmax
  haveI hloc : IsLocalRing (D ⧸ 𝔪 ^ (N + 1)) := IsLocalRing.of_isMaximal_nilradical _
  have hMeq : maximalIdeal (D ⧸ 𝔪 ^ (N + 1)) = M := (IsLocalRing.eq_maximalIdeal hMmax).symm
  have halg : ∀ a : O, algebraMap O (D ⧸ 𝔪 ^ (N + 1)) a
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (algebraMap O C a)) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  haveI : IsNoetherianRing D := hV.noeth
  refine ⟨@IsCO.mk O (D ⧸ 𝔪 ^ (N + 1)) _ _ _ _ hloc inferInstance ?_ ?_ ?_, hMeq⟩
  · rw [hMeq]
    exact adicComplete_of_pow_eq_bot M (N + 1) hMpow
  · refine ⟨fun a ha => ?_⟩
    have hC : IsUnit (algebraMap O C a) := by
      by_contra hnu
      have hcm : algebraMap O C a ∈ maximalIdeal C := hnu
      rw [← hV.comap, Ideal.mem_comap, ← hmem, ← halg, ← hMeq] at hcm
      exact hcm ha
    exact (IsCO.isLocalHom (O := O) (R := C)).map_nonunit a hC
  · intro x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := hV.surj d
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) c
    refine ⟨a, ?_⟩
    rw [hMeq, halg, ← map_sub, hmem]
    have hca : algebraMap C D (c - algebraMap O C a) ∈ 𝔪 := by
      rw [← Ideal.mem_comap, hV.comap]
      exact ha
    have := 𝔪.add_mem hc hca
    rwa [map_sub, sub_add_sub_cancel] at this
