import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

open GlobalTheory.Cong.LevelExt in
/- English proof (translation)
Introduce `E _ _ _ a w₀ hw K hK J hJo hJc`. Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL E a w₀ hw`. Set `s : GL (Fin a) (w₀.adicCompletion E) → UA E a` to `fun h => ((e.symm h : locU a w₀) : UA E a)`. Establish `hs_mem : ∀ h, s h ∈ locU a w₀` using `fun h => (e.symm h).2`. Establish `hs_loc : ∀ h, cLoc w₀ (s h) = h` using `fun h => by`.

Rewrite using `[← he]`. Conclude with `e.apply_symm_apply h`. Establish `hs_cont : Continuous s` using `continuous_subtype_val.comp e.symm.continuous`. Establish `hs_eq : ∀ x ∈ locU a w₀, s (cLoc w₀ x) = x` using `fun x hx => by`. Use `e.symm_apply_apply ⟨x, hx⟩` as an intermediate fact.

Rewrite `this` using `[he]`. Conclude with `congrArg Subtype.val this`. Establish `hcont` using `GlobalTheory.BCT.GlobLev.continuous_cLoc (E := E) (n := a) w₀`. Establish `hnap : ¬ Apart w₀ w₀` using `not_apart_self w₀`. Establish `hloc : ∀ k ∈ K, ∀ x, cLoc w₀ (k * x) = cLoc w₀ x` using `fun k hk x => by`.

Rewrite using `[map_mul, hK.one k hk w₀ hnap, one_mul]`. Establish `hnorm : ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)), K ≤ Subgroup.normalizer ((locU a w₀ ⊓ J'.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a))`. Introduce `J'`. Establish `hKL : ∀ k ∈ K, ∀ l ∈ locU a w₀ ⊓ J'.comap (cLoc w₀), k * l * k⁻¹ ∈ locU a w₀ ⊓ J'.comap (cLoc w₀)`. Introduce and unpack `k hk l ⟨hl1, hl2⟩`.

Establish `hl1'` using `(mem_locU_iff l).1 hl1`. Use `⟨(mem_locU_iff _).2 ⟨mul_mem (mul_mem (hK.fin hk) hl1'.1) (inv_mem (hK.fin hk)), fun u hu => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, hl1'.2 u hu, mul_one, mul_inv_cancel]`. Use `show cLoc w₀ (k * l * k⁻¹) ∈ J'`. Simplify using `only [map_mul, map_inv, hK.one k hk w₀ hnap, one_mul, inv_one, mul_one]`.

Conclude with `hl2`. Conclude with `fun k hk => Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hKL k hk l hl, fun hl => by`. Use `hKL k⁻¹ (inv_mem hk) _ hl` as an intermediate fact. Simplify `this⟩` using `[mul_assoc]`. Establish `hmem : ∀ (J' : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (c : UA E a), c ∈ lev K w₀ J' ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J' ∧ c = k * x`.

Introduce `J' c`. Use `show c ∈ K ⊔ (locU a w₀ ⊓ J'.comap (cLoc w₀)) ↔ _`. Rewrite using `[← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J'), Set.mem_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, x, hx, rfl⟩`.

Conclude with `⟨k, hk, x, hx.1, hx.2, rfl⟩`. Introduce and unpack `⟨k, hk, x, hx, hxJ, rfl⟩`. Conclude with `⟨k, hk, x, ⟨hx, hxJ⟩, rfl⟩`. Establish `hJmem : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J`. Introduce `c hc`.

Take `⟨k, hk, x, -, hxJ, rfl⟩` from `(hmem J c).1 hc`. Rewrite using `[hloc k hk]` and apply the resulting hypothesis. Establish `hLc : IsCompact ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a))`. Establish `: ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) = s '' (J : Set _)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx1, hx2⟩`. Conclude with `⟨cLoc w₀ x, hx2, hs_eq x hx1⟩`. Introduce and unpack `⟨h, hh, rfl⟩`. Use `⟨hs_mem h, ?_⟩` and prove the remaining obligations.

Use `show cLoc w₀ (s h) ∈ J`. Rewrite using `[hs_loc]`. Conclude with `hh`. Rewrite using `[this]`. Conclude with `hJc.image hs_cont`.

Use `⟨⟨sup_le hK.fin (fun x hx => ((mem_locU_iff x).1 (Subgroup.mem_inf.1 hx).1).1), ?_, ?_⟩, hmem J, hJmem, ?_, fun y => ⟨s y, hs_mem y, hs_loc y⟩, ?_⟩` and prove the remaining obligations. Use `show IsCompact ((K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀)) : Subgroup (UA E a)) : Set (UA E a))`. Rewrite using `[Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J)]`. Conclude with `hK.compact.mul hLc`. Take `⟨N₀, hN₀o, hN₀1, hN₀⟩` from `hK.isOpen`.

Set `k : UA E a → UA E a` to `fun x => x * (s (cLoc w₀ x))⁻¹`. Establish `hkc : Continuous k` using `continuous_id.mul ((hs_cont.comp hcont).inv)`. Establish `hs1 : s 1 = 1`. Use `hs_eq 1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Use `⟨k ⁻¹' N₀ ∩ cLoc w₀ ⁻¹' (J : Set _), (hN₀o.preimage hkc).inter (hJo.preimage hcont), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show k 1 ∈ N₀`. Establish `: k 1 = 1` using `by simp [k, hs1]`. Rewrite using `[this]`. Conclude with `hN₀1`.

Use `show cLoc w₀ 1 ∈ J`. Rewrite using `[map_one]`. Conclude with `J.one_mem`. Introduce and unpack `x ⟨⟨hxN, hxJ⟩, hxf⟩`. Establish `hkx : k x ∈ K`.

Use `hN₀ _ hxN ?_ ?_` and prove the remaining obligations. Conclude with `mul_mem hxf (inv_mem ((mem_locU_iff _).1 (hs_mem _)).1)`. Conclude with `one_of_cLoc hw _ (by simp only [k, map_mul, map_inv, hs_loc, mul_inv_cancel])`. Use `(hmem J x).2 ⟨k x, hkx, s (cLoc w₀ x), hs_mem _, ?_, by simp [k]⟩` and prove the remaining obligations. Rewrite using `[hs_loc]`.

Conclude with `hxJ`. Introduce `c hc h1`. Take `⟨k, hk, x, hx, -, rfl⟩` from `(hmem J c).1 hc`. Rewrite `h1` using `[hloc k hk]`. Establish `hx1 : x = 1`.

Establish `h2` using `hs_eq x hx`. Establish `hs1 : s 1 = 1`. Use `hs_eq 1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Rewrite `h2` using `[h1, hs1]`.

Conclude with `h2.symm`. Rewrite using `[hx1, mul_one]`. Conclude with `hk`. Introduce `J' c hc hcJ'`. Take `⟨k, hk, x, hx, -, rfl⟩` from `(hmem J c).1 hc`.

Rewrite `hcJ'` using `[hloc k hk]`. Conclude with `(hmem J' _).2 ⟨k, hk, x, hx, hcJ', rfl⟩`.
-/
theorem UpperTheory.Gal.Gen.levFacts_pf :
    UpperTheory.Gal.Gen.LevFacts := by
  intro E _ _ _ a w₀ hw K hK J hJo hJc
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let s : GL (Fin a) (w₀.adicCompletion E) → UA E a := fun h => ((e.symm h : locU a w₀) : UA E a)
  have hs_mem : ∀ h, s h ∈ locU a w₀ := fun h => (e.symm h).2
  have hs_loc : ∀ h, cLoc w₀ (s h) = h := fun h => by
    rw [← he]
    exact e.apply_symm_apply h
  have hs_cont : Continuous s := continuous_subtype_val.comp e.symm.continuous
  have hs_eq : ∀ x ∈ locU a w₀, s (cLoc w₀ x) = x := fun x hx => by
    have := e.symm_apply_apply ⟨x, hx⟩
    rw [he] at this
    exact congrArg Subtype.val this
  have hcont := GlobalTheory.BCT.GlobLev.continuous_cLoc (E := E) (n := a) w₀
  have hnap : ¬ Apart w₀ w₀ := not_apart_self w₀
  have hloc : ∀ k ∈ K, ∀ x, cLoc w₀ (k * x) = cLoc w₀ x := fun k hk x => by
    rw [map_mul, hK.one k hk w₀ hnap, one_mul]
  have hnorm : ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)),
      K ≤ Subgroup.normalizer ((locU a w₀ ⊓ J'.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    intro J'
    have hKL : ∀ k ∈ K, ∀ l ∈ locU a w₀ ⊓ J'.comap (cLoc w₀), k * l * k⁻¹ ∈ locU a w₀ ⊓ J'.comap (cLoc w₀) := by
      rintro k hk l ⟨hl1, hl2⟩
      have hl1' := (mem_locU_iff l).1 hl1
      refine ⟨(mem_locU_iff _).2 ⟨mul_mem (mul_mem (hK.fin hk) hl1'.1) (inv_mem (hK.fin hk)), fun u hu => ?_⟩, ?_⟩
      · simp only [map_mul, map_inv, hl1'.2 u hu, mul_one, mul_inv_cancel]
      · show cLoc w₀ (k * l * k⁻¹) ∈ J'
        simp only [map_mul, map_inv, hK.one k hk w₀ hnap, one_mul, inv_one, mul_one]
        exact hl2
    exact fun k hk => Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hKL k hk l hl, fun hl => by
      have := hKL k⁻¹ (inv_mem hk) _ hl
      simpa [mul_assoc] using this⟩
  have hmem : ∀ (J' : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (c : UA E a),
      c ∈ lev K w₀ J' ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J' ∧ c = k * x := by
    intro J' c
    show c ∈ K ⊔ (locU a w₀ ⊓ J'.comap (cLoc w₀)) ↔ _
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J'), Set.mem_mul]
    constructor
    · rintro ⟨k, hk, x, hx, rfl⟩
      exact ⟨k, hk, x, hx.1, hx.2, rfl⟩
    · rintro ⟨k, hk, x, hx, hxJ, rfl⟩
      exact ⟨k, hk, x, ⟨hx, hxJ⟩, rfl⟩
  have hJmem : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J := by
    intro c hc
    obtain ⟨k, hk, x, -, hxJ, rfl⟩ := (hmem J c).1 hc
    rwa [hloc k hk]
  have hLc : IsCompact ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    have : ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) = s '' (J : Set _) := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨cLoc w₀ x, hx2, hs_eq x hx1⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨hs_mem h, ?_⟩
        show cLoc w₀ (s h) ∈ J
        rw [hs_loc]
        exact hh
    rw [this]
    exact hJc.image hs_cont
  refine ⟨⟨sup_le hK.fin (fun x hx => ((mem_locU_iff x).1 (Subgroup.mem_inf.1 hx).1).1), ?_, ?_⟩, hmem J, hJmem,
    ?_, fun y => ⟨s y, hs_mem y, hs_loc y⟩, ?_⟩
  · show IsCompact ((K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀)) : Subgroup (UA E a)) : Set (UA E a))
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J)]
    exact hK.compact.mul hLc
  · obtain ⟨N₀, hN₀o, hN₀1, hN₀⟩ := hK.isOpen
    let k : UA E a → UA E a := fun x => x * (s (cLoc w₀ x))⁻¹
    have hkc : Continuous k := continuous_id.mul ((hs_cont.comp hcont).inv)
    have hs1 : s 1 = 1 := by
      have := hs_eq 1 (one_mem _)
      rwa [map_one] at this
    refine ⟨k ⁻¹' N₀ ∩ cLoc w₀ ⁻¹' (J : Set _), (hN₀o.preimage hkc).inter (hJo.preimage hcont), ⟨?_, ?_⟩, ?_⟩
    · show k 1 ∈ N₀
      have : k 1 = 1 := by simp [k, hs1]
      rw [this]
      exact hN₀1
    · show cLoc w₀ 1 ∈ J
      rw [map_one]
      exact J.one_mem
    · rintro x ⟨⟨hxN, hxJ⟩, hxf⟩
      have hkx : k x ∈ K := by
        refine hN₀ _ hxN ?_ ?_
        · exact mul_mem hxf (inv_mem ((mem_locU_iff _).1 (hs_mem _)).1)
        · exact one_of_cLoc hw _ (by simp only [k, map_mul, map_inv, hs_loc, mul_inv_cancel])
      refine (hmem J x).2 ⟨k x, hkx, s (cLoc w₀ x), hs_mem _, ?_, by simp [k]⟩
      rw [hs_loc]
      exact hxJ
  · intro c hc h1
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at h1
    have hx1 : x = 1 := by
      have h2 := hs_eq x hx
      have hs1 : s 1 = 1 := by
        have := hs_eq 1 (one_mem _)
        rwa [map_one] at this
      rw [h1, hs1] at h2
      exact h2.symm
    rw [hx1, mul_one]
    exact hk
  · intro J' c hc hcJ'
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at hcJ'
    exact (hmem J' _).2 ⟨k, hk, x, hx, hcJ', rfl⟩
