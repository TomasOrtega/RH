import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]`. Conclude with `⟨β, by simp [h]⟩`.
-/
theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

/- English proof (translation)
Rewrite using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]`. Conclude with `⟨β, h.symm⟩`.
-/
private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

/- English proof (translation)
Introduce `R _ K I J f n`. Use `⟨fun c => ?_, fun c => ?_, fun c => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `c.mk_surjective`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Simplify using `only [cpush, cpost_mk] at hy`. Rewrite `hy` using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Take `⟨γ, hγ⟩` from `hy`. Rewrite `hγ` using `[coe_zcomp]`. Establish `ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0`.

Rewrite using `[δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl, Cocycle.δ_eq_zero, hγ]`. Simplify using `[Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]`. Use `⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩` and prove the remaining obligations. Simplify using `only [cpush, cpost_mk]`. Use `GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega) (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_` and prove the remaining obligations.

Rewrite using `[coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]`. Simplify using `[Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]`. Introduce and unpack `⟨c', hc'⟩`. Rewrite using `[← hc']`. Take `⟨x, rfl⟩` from `c'.mk_surjective`.

Simplify using `only [cpush, cpost_mk]`. Use `cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_` and prove the remaining obligations. Rewrite using `[δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1), mappingCone.δ_inl, Cocycle.δ_eq_zero]`. Simplify using `[coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]`. Take `⟨z, rfl⟩` from `c.mk_surjective`.

Prove the components needed by the constructor for the conclusion. Introduce `hz`. Rewrite `hz` using `[cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]`. Take `⟨c₀, hc₀⟩` from `hz`. Rewrite `hc₀` using `[coe_zcomp]`.

Establish `hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) + c₀.comp (Cochain.ofHom f) (add_zero n)) = 0`. Rewrite using `[δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀, Cocycle.δ_eq_zero]`. Simplify using `[Cochain.comp_assoc_of_third_is_zero_cochain]`. Use `⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩` and prove the remaining obligations. Simplify using `only [cpush, cpost_mk]`.

Use `GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega) (c₀.comp (mappingCone.inl f) rfl) ?_` and prove the remaining obligations. Rewrite using `[coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1), mappingCone.δ_inl, hc₀]`. Rewrite using `[mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]`. Prove the components needed by the constructor for the conclusion. Simplify using `[Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]`.

Simplify using `[Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]`. Introduce and unpack `⟨c', hc'⟩`. Rewrite using `[← hc']`. Take `⟨y, rfl⟩` from `c'.mk_surjective`. Simplify using `only [cpush, cpost_mk]`.

Use `cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_` and prove the remaining obligations. Simplify using `[coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]`. Take `⟨w, rfl⟩` from `c.mk_surjective`. Prove the components needed by the constructor for the conclusion. Introduce `hw`.

Simplify using `only [cpush, cpost_mk] at hw`. Rewrite `hw` using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]`. Take `⟨b, hb⟩` from `hw`. Rewrite `hb` using `[coe_zcomp]`. Use `⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl (by rw [δ_neg, hb]; simp)), ?_⟩` and prove the remaining obligations.

Rewrite using `[cpost_mk]`. Use `congr 1`. Apply `Cocycle.ext` to reduce the goal to its premises. Rewrite using `[coe_zcomp]`. Simplify using `[mappingCone.liftCochain_fst]`.

Introduce and unpack `⟨c', hc'⟩`. Rewrite using `[← hc']`. Take `⟨z, rfl⟩` from `c'.mk_surjective`. Simplify using `only [cpush, cpost_mk]`. Use `cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_` and prove the remaining obligations.

Rewrite using `[δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]`. Simplify using `[coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]`.
-/
theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
