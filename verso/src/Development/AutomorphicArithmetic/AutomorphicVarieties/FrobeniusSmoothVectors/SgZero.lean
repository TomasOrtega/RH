import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem sg_zero (R : Type) [CommRing R] : sg R 0 = 1 := by simp [sg]

/- English proof (translation)
Use `show (-1 : R) ^ (1 : ZMod 2).val = -1`. Rewrite using `[show (1 : ZMod 2).val = 1 from rfl, pow_one]`.
-/
private theorem sg_one (R : Type) [CommRing R] : sg R 1 = -1 := by
  show (-1 : R) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hF S x L hx σ hσ`. Establish `hl : l ≠ 2` using `hF.l_odd`. Establish `h2O : IsUnit (2 : L.O')`. Assume the negation of the conclusion as `h`. Establish `hm : (2 : L.O') ∈ maximalIdeal L.O'` using `(mem_maximalIdeal _).mpr h`.

Establish `hr : residue L.O' 2 = 0` using `(residue_eq_zero_iff _).mpr hm`. Rewrite `hr` using `[map_ofNat]`. Establish `hd : l ∣ 2` using `(CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)`. Establish `hp : l.Prime` using `Fact.out`. Break down `(Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1` into its components or cases.

Conclude with `hp.one_lt.ne' h1`. Conclude with `hl h1`. Establish `h2 : IsUnit (2 : L.R)`. Use `h2O.map (algebraMap L.O' L.R)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`.

Conclude with `this`. Establish `hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1`. Introduce `a b h`. Take `⟨k, hk⟩` from `h`. Use `show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1`.

Rewrite using `[hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]`. Establish `hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0`. Introduce `a b h`. Take `⟨k, hk⟩` from `h`. Use `show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0`.

Rewrite using `[hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]`. Apply `le_antisymm` to reduce the goal to its premises. Unfold `NRep.ee`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, i, j, hodd, rfl⟩`.

Apply `Ideal.subset_span` to reduce the goal to its premises. Establish `he` using `hσ.ent g i j`. Rewrite `he` using `[hpw i j hodd]`. Conclude with `he`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations.

Introduce `y hy`. Establish `hy' : σ y = sg L.R 1 * y` using `hy`. Rewrite `hy'` using `[sg_one]`. Establish `hIm : L.ρ.ee ≤ maximalIdeal L.R`. Unfold `NRep.ee`.

Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, i, j, hodd, rfl⟩`. Establish `hmem : S.u.r g i j ∈ S.u.ee` using `Ideal.subset_span ⟨g, i, j, hodd, rfl⟩`. Establish `hxm` using `hx hmem`. Rewrite `hxm` using `[← L.lies]`.

Conclude with `Ideal.mem_comap.mp hxm`. Use `haveI : Nontrivial (L.R ⧸ L.ρ.ee) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)`. Use `haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) := co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)`. Establish `key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})), Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩)`. Introduce `z hz`.

Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Break down `hz with hB | ⟨g, i, j, rfl⟩` into its components or cases. Establish `hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩` using `hσ.base ⟨z, hB⟩`. Rewrite `hb'` using `[sg_zero, one_mul]`.

Use `show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)`. Rewrite using `[hb']`. Establish `he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j` using `hσ.ent g i j show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)`. Break down `Int.even_or_odd (w 3 i - w 3 j) with h | h` into its components or cases. Rewrite `he'` using `[hpw0 i j h, sg_zero, one_mul]`.

Rewrite using `[he']`. Rewrite `he'` using `[hpw i j h, sg_one]`. Establish `hm : L.ρ.r g i j ∈ L.ρ.ee` using `Ideal.subset_span ⟨g, i, j, h, rfl⟩`. Rewrite using `[he', Ideal.Quotient.eq]`. Establish `hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j` using `by ring`.

Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_left _ _ hm`. Consider the case `algebraMap r => show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))`. Rewrite using `[L.ι.commutes]`. Establish `hc` using `(σ.restrictScalars O).commutes r`.

Rewrite `hc` using `[AlgHom.restrictScalars_apply]`. Rewrite using `[hc]`. Consider the case `add a b ha hb iha ihb => show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))`. Simplify using `only [map_add, iha, ihb]`. Consider the case `mul a b ha hb iha ihb => show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))`.

Simplify using `only [map_mul, iha, ihb]`. Establish `huniq` using `L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _`. Conclude with `res_map _ _)`. Establish `h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) = ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a`. Introduce and unpack `⟨z, hz⟩`.

Conclude with `key' z hz`. Establish `h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) = ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a` using `fun a => rfl`. Establish `heq` using `huniq.unique h1 h2'`. Establish `hyq` using `AlgHom.congr_fun heq y`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq`.

Establish `hd` using `Ideal.Quotient.eq.mp hyq`. Establish `h2y : 2 * y ∈ L.ρ.ee`. Establish `hc : 2 * y = -((-1 * y) - y)` using `by ring`. Rewrite using `[hc]`. Conclude with `neg_mem hd`.

Take `⟨u, hu⟩` from `h2`. Establish `hc : y = (↑u⁻¹ : L.R) * (2 * y)` using `by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Use `show y ∈ L.ρ.ee`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_left _ _ h2y`.
-/
theorem UpperTheory.V.Fr.ep_ee :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∀ σ, L.IsInv σ → L.ρ.ee = Ideal.span (evp σ 1 : Set L.R) := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx σ hσ
  have hl : l ≠ 2 := hF.l_odd
  have h2O : IsUnit (2 : L.O') := by
    by_contra h
    have hm : (2 : L.O') ∈ maximalIdeal L.O' := (mem_maximalIdeal _).mpr h
    have hr : residue L.O' 2 = 0 := (residue_eq_zero_iff _).mpr hm
    rw [map_ofNat] at hr
    have hd : l ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)
    have hp : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hl h1
  have h2 : IsUnit (2 : L.R) := by
    have := h2O.map (algebraMap L.O' L.R)
    rw [map_ofNat] at this
    exact this
  have hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  have hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0
    rw [hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  apply le_antisymm
  · unfold NRep.ee
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, i, j, hodd, rfl⟩
    apply Ideal.subset_span
    have he := hσ.ent g i j
    rw [hpw i j hodd] at he
    exact he
  · refine Ideal.span_le.mpr ?_
    intro y hy
    have hy' : σ y = sg L.R 1 * y := hy
    rw [sg_one] at hy'
    have hIm : L.ρ.ee ≤ maximalIdeal L.R := by
      unfold NRep.ee
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, i, j, hodd, rfl⟩
      have hmem : S.u.r g i j ∈ S.u.ee := Ideal.subset_span ⟨g, i, j, hodd, rfl⟩
      have hxm := hx hmem
      rw [← L.lies] at hxm
      exact Ideal.mem_comap.mp hxm
    haveI : Nontrivial (L.R ⧸ L.ρ.ee) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)
    haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) :=
      co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)
    have key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})),
        Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rcases hz with hB | ⟨g, i, j, rfl⟩
        · have hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩ := hσ.base ⟨z, hB⟩
          rw [sg_zero, one_mul] at hb'
          show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)
          rw [hb']
        · have he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j := hσ.ent g i j
          show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)
          rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
          · rw [hpw0 i j h, sg_zero, one_mul] at he'
            rw [he']
          · rw [hpw i j h, sg_one] at he'
            have hm : L.ρ.r g i j ∈ L.ρ.ee := Ideal.subset_span ⟨g, i, j, h, rfl⟩
            rw [he', Ideal.Quotient.eq]
            have hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j := by ring
            rw [hc]
            exact Ideal.mul_mem_left _ _ hm
      | algebraMap r =>
        show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))
        rw [L.ι.commutes]
        have hc := (σ.restrictScalars O).commutes r
        rw [AlgHom.restrictScalars_apply] at hc
        rw [hc]
      | add a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add, iha, ihb]
      | mul a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))
        simp only [map_mul, iha, ihb]
    have huniq := L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by
      show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _
      exact res_map _ _)
    have h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := by
      rintro ⟨z, hz⟩
      exact key' z hz
    have h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := fun a => rfl
    have heq := huniq.unique h1 h2'
    have hyq := AlgHom.congr_fun heq y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq
    have hd := Ideal.Quotient.eq.mp hyq
    have h2y : 2 * y ∈ L.ρ.ee := by
      have hc : 2 * y = -((-1 * y) - y) := by ring
      rw [hc]
      exact neg_mem hd
    obtain ⟨u, hu⟩ := h2
    have hc : y = (↑u⁻¹ : L.R) * (2 * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show y ∈ L.ρ.ee
    rw [hc]
    exact Ideal.mul_mem_left _ _ h2y
