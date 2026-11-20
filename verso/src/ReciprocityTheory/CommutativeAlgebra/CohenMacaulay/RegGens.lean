import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RegGensA

open CategoryTheory CategoryTheory.Abelian IsLocalRing RingTheory.Sequence

universe u v

namespace ReciprocityTheory.CA.RegGens

open Pointwise in
/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `P _ _ hd`. Establish `hsf : (maximalIdeal P).spanFinrank = 0`.

Establish `h` using `IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)`. Rewrite `h` using `[hd]`. Conclude with `h` after adjusting the coercions. Establish `hbot : maximalIdeal P = ⊥` using `(Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hsf`. Conclude with `⟨[], rfl, IsRegular.nil P P, by rw [Ideal.ofList_nil, hbot]⟩`.

Consider the case `succ d IH`. Introduce `P _ _ hd`. Establish `hsq : ¬ maximalIdeal P ≤ maximalIdeal P ^ 2`. Introduce `hle`. Establish `hbot` using `RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq P hle`.

Establish `h` using `IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)`. Rewrite `h` using `[hd, hbot, Submodule.spanFinrank_bot]`. Establish `: (0 : ℕ) = d + 1` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal P ∧ x ∉ maximalIdeal P ^ 2 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hsq fun y hy => hc y hy`. Use `set I : Ideal P := Ideal.span ({x} : Set P) with hI`. Establish `hreg : IsRegularLocalRing (P ⧸ I)` using `RegA.IsRegularLocalRing.quotient_span_singleton hx hx2`.

Establish `hdim : ringKrullDim (P ⧸ I) = d`. Establish `h1` using `RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hx hx2`. Establish `h2` using `IsRegularLocalRing.spanFinrank_maximalIdeal (R := P ⧸ I)`. Rewrite `h1`, the goal using `[← h2]`. Rewrite `h1` using `[hd]`.

Establish `h3 : (maximalIdeal (P ⧸ I)).spanFinrank + 1 = d + 1` using `by exact_mod_cast h1`. Conclude with `(by omega : (maximalIdeal (P ⧸ I)).spanFinrank = d)` after adjusting the coercions. Take `⟨rs', hlen, hrs', hgen⟩` from `IH (P ⧸ I) hdim`. Set `lift : P ⧸ I → P` to `fun y => Quotient.out y`. Establish `hlift : ∀ y, Ideal.Quotient.mk I (lift y) = y` using `fun y => Ideal.Quotient.mk_out y`.

Establish `hmap : (rs'.map lift).map (Ideal.Quotient.mk I) = rs'`. Rewrite using `[List.map_map]`. Use `conv_rhs => rw [← List.map_id rs']`. Conclude with `List.map_congr_left fun y _ => hlift y`. Use `⟨x :: rs'.map lift, by simp [hlen], ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[isRegular_cons_iff', hmap]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx2 (zero_mem _)`.

Conclude with `(IsRegular.of_ne_zero hx0).left`. Establish `hsm : (x • ⊤ : Submodule P P) = I`. Rewrite using `[hI, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]`. Set `e : QuotSMulTop x P ≃ₗ[P] P ⧸ I` to `Submodule.quotEquivOfEq _ _ hsm`. Use `(e.toAddEquiv.isRegular_congr (as := rs') (bs := rs') ?_).mpr hrs'` and prove the remaining obligations.

Use `List.forall₂_same.mpr fun r _ y => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Both sides reduce to the same expression. Rewrite using `[Ideal.ofList_cons]`.

Establish `h1 : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) (Ideal.ofList (rs'.map lift))) = Ideal.ofList (rs'.map lift) ⊔ I`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Rewrite `h1` using `[Ideal.map_ofList, hmap, hgen]`. Establish `h2 : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I)) = maximalIdeal P`. Establish `: (Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I))).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`.

Conclude with `IsLocalRing.eq_maximalIdeal this`. Rewrite using `[← h2, h1, sup_comm]`.
-/
theorem exists_regular_generators_maxIdeal : ∀ (d : ℕ) (P : Type u) [CommRing P] [IsRegularLocalRing P],
    ringKrullDim P = d →
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P := by
  intro d
  induction d with
  | zero =>
    intro P _ _ hd
    have hsf : (maximalIdeal P).spanFinrank = 0 := by
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd] at h
      exact_mod_cast h
    have hbot : maximalIdeal P = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hsf
    exact ⟨[], rfl, IsRegular.nil P P, by rw [Ideal.ofList_nil, hbot]⟩
  | succ d IH =>
    intro P _ _ hd
    have hsq : ¬ maximalIdeal P ≤ maximalIdeal P ^ 2 := by
      intro hle
      have hbot := RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq P hle
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd, hbot, Submodule.spanFinrank_bot] at h
      have : (0 : ℕ) = d + 1 := by exact_mod_cast h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal P ∧ x ∉ maximalIdeal P ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    set I : Ideal P := Ideal.span ({x} : Set P) with hI
    have hreg : IsRegularLocalRing (P ⧸ I) :=
      RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
    have hdim : ringKrullDim (P ⧸ I) = d := by
      have h1 := RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hx hx2
      have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P ⧸ I)
      rw [← h2] at h1 ⊢
      rw [hd] at h1
      have h3 : (maximalIdeal (P ⧸ I)).spanFinrank + 1 = d + 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : (maximalIdeal (P ⧸ I)).spanFinrank = d)
    obtain ⟨rs', hlen, hrs', hgen⟩ := IH (P ⧸ I) hdim
    let lift : P ⧸ I → P := fun y => Quotient.out y
    have hlift : ∀ y, Ideal.Quotient.mk I (lift y) = y := fun y => Ideal.Quotient.mk_out y
    have hmap : (rs'.map lift).map (Ideal.Quotient.mk I) = rs' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id rs']
      exact List.map_congr_left fun y _ => hlift y
    refine ⟨x :: rs'.map lift, by simp [hlen], ?_, ?_⟩
    · rw [isRegular_cons_iff', hmap]
      refine ⟨?_, ?_⟩
      · have hx0 : x ≠ 0 := by
          rintro rfl
          exact hx2 (zero_mem _)
        exact (IsRegular.of_ne_zero hx0).left
      · have hsm : (x • ⊤ : Submodule P P) = I := by
          rw [hI, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
        let e : QuotSMulTop x P ≃ₗ[P] P ⧸ I := Submodule.quotEquivOfEq _ _ hsm
        refine (e.toAddEquiv.isRegular_congr (as := rs') (bs := rs') ?_).mpr hrs'
        refine List.forall₂_same.mpr fun r _ y => ?_
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rfl
    · rw [Ideal.ofList_cons]
      have h1 : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I)
          (Ideal.ofList (rs'.map lift))) = Ideal.ofList (rs'.map lift) ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
      rw [Ideal.map_ofList, hmap, hgen] at h1
      have h2 : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I)) = maximalIdeal P := by
        have : (Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I))).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        exact IsLocalRing.eq_maximalIdeal this
      rw [← h2, h1, sup_comm]

/- English proof (translation)
The claim follows from `exists_regular_generators_maxIdeal d P hd`.
-/
theorem exists_regular_gens (P : Type u) [CommRing P] [IsRegularLocalRing P] (d : ℕ)
    (hd : ringKrullDim P = d) :
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P :=
  exists_regular_generators_maxIdeal d P hd

end ReciprocityTheory.CA.RegGens
