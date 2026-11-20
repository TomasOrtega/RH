import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
open IsLocalRing

namespace GlobalTheory.CompleteNakayamaLocal

/- English proof (translation)
Take `⟨T, hT⟩` from `(Module.Finite.fg_top (R := B) (M := R ⧸ maximalIdeal R))`. Use `choose lift hlift using fun x : R ⧸ maximalIdeal R => Ideal.Quotient.mk_surjective x`. Establish `hTop : Submodule.span B (lift '' (T : Set _)) ⊔ (maximalIdeal R).restrictScalars B = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `r _`.

Establish `hr : Ideal.Quotient.mk (maximalIdeal R) r ∈ Submodule.span B (T : Set _)`. Rewrite using `[hT]`. Discharge the goal by the elementary cases of `trivial`. Establish `hmap : Submodule.span B (T : Set (R ⧸ maximalIdeal R)) = (Submodule.span B (lift '' (T : Set _))).map (Ideal.Quotient.mkₐ B (maximalIdeal R)).toLinearMap`. Rewrite using `[Submodule.map_span, ← Set.image_comp]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[hlift]`. Rewrite `hr` using `[hmap]`. Take `⟨t, ht, hte⟩` from `hr`.

Establish `hu : r - t ∈ maximalIdeal R`. Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `using hte.symm`. Rewrite using `[Submodule.mem_sup]`. Conclude with `⟨t, ht, r - t, hu, by ring⟩`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩`. Consider the case `succ n ih`. Take `⟨P, hP, hPtop⟩` from `ih`. Take `⟨gens, hgens⟩` from `(IsNoetherian.noetherian (maximalIdeal R ^ n) : (maximalIdeal R ^ n).FG)`.

Set `G : Set R` to `Set.image2 (· * ·) (lift '' (T : Set _)) (gens : Set R)`. Establish `hGf : G.Finite` using `((T.finite_toSet.image _).image2 _ gens.finite_toSet)`. Use `⟨P ⊔ Submodule.span B G, hP.sup (Submodule.fg_def.2 ⟨G, hGf, rfl⟩), ?_⟩` and prove the remaining obligations. Establish `key : ∀ y ∈ maximalIdeal R ^ n, ∀ r : R, r * y ∈ Submodule.span B G ⊔ (maximalIdeal R ^ (n + 1)).restrictScalars B`. Introduce `y hy`.

Rewrite `hy` using `[← hgens]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem g hg`. Introduce `r`. Establish `hr : r ∈ (⊤ : Submodule B R)` using `trivial`.

Rewrite `hr` using `[← hTop, Submodule.mem_sup]`. Take `⟨t, ht, u, hu, rfl⟩` from `hr`. Rewrite using `[add_mul]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Establish `: t * g ∈ (Submodule.span B (lift '' (T : Set _))).map (LinearMap.mulRight B g)` using `⟨t, ht, rfl⟩`.

Rewrite `this` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `⟨s, hs, g, hg, rfl⟩`. Use `show u * g ∈ maximalIdeal R ^ (n + 1)`.

Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul hu (hgens ▸ Submodule.subset_span hg)`. Consider the case `zero => intro r`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb => intro r`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ (ha r) (hb r)`. Consider the case `smul s a _ ha => intro r`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `ha (r * s)`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ (⊤ : Submodule B R)` using `trivial`. Rewrite `hx` using `[← hPtop, Submodule.mem_sup]`. Take `⟨p, hp, y, hy, rfl⟩` from `hx`.

Establish `hy'` using `key y hy 1`. Rewrite `hy'` using `[one_mul, Submodule.mem_sup]`. Take `⟨a, ha, c, hc, rfl⟩` from `hy'`. Rewrite using `[Submodule.mem_sup]`. Use `⟨p + a, Submodule.add_mem_sup hp ha, c, hc, by ring⟩` and prove the remaining obligations.
-/
theorem exists_fg_sup_pow_eq_top {B R : Type} [CommRing B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra B R]
    (hres : Module.Finite B (R ⧸ maximalIdeal R)) (n : ℕ) :
    ∃ P : Submodule B R, P.FG ∧ P ⊔ (maximalIdeal R ^ n).restrictScalars B = ⊤ := by
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top (R := B) (M := R ⧸ maximalIdeal R))
  choose lift hlift using fun x : R ⧸ maximalIdeal R => Ideal.Quotient.mk_surjective x

  have hTop : Submodule.span B (lift '' (T : Set _)) ⊔ (maximalIdeal R).restrictScalars B = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hr : Ideal.Quotient.mk (maximalIdeal R) r ∈ Submodule.span B (T : Set _) := by
      rw [hT]; trivial
    have hmap : Submodule.span B (T : Set (R ⧸ maximalIdeal R)) =
        (Submodule.span B (lift '' (T : Set _))).map
          (Ideal.Quotient.mkₐ B (maximalIdeal R)).toLinearMap := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      ext x
      simp [hlift]
    rw [hmap] at hr
    obtain ⟨t, ht, hte⟩ := hr
    have hu : r - t ∈ maximalIdeal R := by
      rw [← Ideal.Quotient.eq]
      simpa using hte.symm
    rw [Submodule.mem_sup]
    exact ⟨t, ht, r - t, hu, by ring⟩
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP, hPtop⟩ := ih
    obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian (maximalIdeal R ^ n) : (maximalIdeal R ^ n).FG)
    let G : Set R := Set.image2 (· * ·) (lift '' (T : Set _)) (gens : Set R)
    have hGf : G.Finite := ((T.finite_toSet.image _).image2 _ gens.finite_toSet)
    refine ⟨P ⊔ Submodule.span B G, hP.sup (Submodule.fg_def.2 ⟨G, hGf, rfl⟩), ?_⟩

    have key : ∀ y ∈ maximalIdeal R ^ n, ∀ r : R,
        r * y ∈ Submodule.span B G ⊔ (maximalIdeal R ^ (n + 1)).restrictScalars B := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        intro r
        have hr : r ∈ (⊤ : Submodule B R) := trivial
        rw [← hTop, Submodule.mem_sup] at hr
        obtain ⟨t, ht, u, hu, rfl⟩ := hr
        rw [add_mul]
        refine Submodule.add_mem_sup ?_ ?_
        · have : t * g ∈ (Submodule.span B (lift '' (T : Set _))).map (LinearMap.mulRight B g) :=
            ⟨t, ht, rfl⟩
          rw [Submodule.map_span] at this
          refine Submodule.span_mono ?_ this
          rintro _ ⟨s, hs, rfl⟩
          exact ⟨s, hs, g, hg, rfl⟩
        · show u * g ∈ maximalIdeal R ^ (n + 1)
          rw [pow_succ']
          exact Ideal.mul_mem_mul hu (hgens ▸ Submodule.subset_span hg)
      | zero => intro r; simp
      | add a b _ _ ha hb => intro r; rw [mul_add]; exact Submodule.add_mem _ (ha r) (hb r)
      | smul s a _ ha => intro r; rw [smul_eq_mul, ← mul_assoc]; exact ha (r * s)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : Submodule B R) := trivial
    rw [← hPtop, Submodule.mem_sup] at hx
    obtain ⟨p, hp, y, hy, rfl⟩ := hx
    have hy' := key y hy 1
    rw [one_mul, Submodule.mem_sup] at hy'
    obtain ⟨a, ha, c, hc, rfl⟩ := hy'
    rw [Submodule.mem_sup]
    refine ⟨p + a, Submodule.add_mem_sup hp ha, c, hc, by ring⟩

/- English proof (translation)
Introduce `B R _ _ _ _ _ _ ψ hB hψ hrad hres`. Use `letI : Algebra B R := ψ.toAlgebra`. Use `set J : Ideal R := (maximalIdeal B).map (algebraMap B R) with hJdef`. Establish `hJm : J ≤ maximalIdeal R`. Use `Ideal.map_le_iff_le_comap.2 fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ψ x h)`. Use `haveI : IsHausdorff J R := ⟨fun x hx => IsHausdorff.haus (I := maximalIdeal R) inferInstance x fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJm n))⟩`. Take `⟨e, he⟩ : ∃ e, maximalIdeal R ^ e ≤ J` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`. Establish `hres' : Module.Finite B (R ⧸ maximalIdeal R)` using `hres`.

Take `⟨P, hP, hPtop⟩` from `exists_fg_sup_pow_eq_top hres' e`. Use `haveI : Module.Finite B (R ⧸ J) := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `: (⊤ : Submodule B (R ⧸ J)) = P.map (Ideal.Quotient.mkₐ B J).toLinearMap`. Use `le_antisymm ?_ le_top` and prove the remaining obligations.

Introduce and unpack `z -`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `hx : x ∈ (⊤ : Submodule B R)` using `trivial`. Rewrite `hx` using `[← hPtop, Submodule.mem_sup]`. Take `⟨p, hp, y, hy, rfl⟩` from `hx`.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p + y)`. Rewrite using `[map_add, Ideal.Quotient.eq_zero_iff_mem.2 (he hy), add_zero]`. Rewrite using `[this]`. Conclude with `hP.map _`.

Conclude with `GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)`.
-/
theorem finite_of_maximalIdeal_le_radical : ∀ (B R : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R),
    IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ →
    maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite →
    ψ.Finite := by
  intro B R _ _ _ _ _ _ ψ hB hψ hrad hres
  letI : Algebra B R := ψ.toAlgebra
  set J : Ideal R := (maximalIdeal B).map (algebraMap B R) with hJdef
  have hJm : J ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ψ x h)
  haveI : IsHausdorff J R := ⟨fun x hx => IsHausdorff.haus (I := maximalIdeal R) inferInstance x
    fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJm n))⟩
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal R ^ e ≤ J :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hres' : Module.Finite B (R ⧸ maximalIdeal R) := hres
  obtain ⟨P, hP, hPtop⟩ := exists_fg_sup_pow_eq_top hres' e
  haveI : Module.Finite B (R ⧸ J) := by
    refine ⟨?_⟩
    have : (⊤ : Submodule B (R ⧸ J)) = P.map (Ideal.Quotient.mkₐ B J).toLinearMap := by
      refine le_antisymm ?_ le_top
      rintro z -
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ (⊤ : Submodule B R) := trivial
      rw [← hPtop, Submodule.mem_sup] at hx
      obtain ⟨p, hp, y, hy, rfl⟩ := hx
      refine ⟨p, hp, ?_⟩
      show Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p + y)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (he hy), add_zero]
    rw [this]
    exact hP.map _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)

/- English proof (translation)
The claim follows from `finite_of_maximalIdeal_le_radical`.
-/
example : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := finite_of_maximalIdeal_le_radical

end GlobalTheory.CompleteNakayamaLocal
