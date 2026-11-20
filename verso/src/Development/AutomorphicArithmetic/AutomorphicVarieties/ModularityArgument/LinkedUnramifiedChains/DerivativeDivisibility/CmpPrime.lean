import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial

namespace UpperTheory.V.J

/- English proof (translation)
Establish `finj : Function.Injective (algebraMap Λ (FractionRing Λ))` using `IsFractionRing.injective Λ (FractionRing Λ)`. Use `set e := (∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t with he`. Establish `memP : ∀ a : B, a ∈ J.colon {e} ↔ a * e ∈ J`. Introduce `a`. Simplify using `[Submodule.mem_colon]`.

Establish `gprime : Prime ((g i).map (algebraMap Λ (FractionRing Λ)))` using `(irr i).prime`. Establish `mapMonic : ∀ j, ((g j).map (algebraMap Λ (FractionRing Λ))).Monic` using `fun j => (monic j).map _`. Establish `desc : ∀ q : Λ[X], g i ∣ q ↔ (g i).map (algebraMap Λ (FractionRing Λ)) ∣ q.map (algebraMap Λ (FractionRing Λ))` using `fun q => (Polynomial.map_dvd_map (algebraMap Λ (FractionRing Λ)) finj (monic i)).symm`. Establish `notdvd : ¬ (g i).map (algebraMap Λ (FractionRing Λ)) ∣ (∏ j ∈ Finset.univ.erase i, g j).map (algebraMap Λ (FractionRing Λ))`. Rewrite using `[Polynomial.map_prod]`.

Introduce `h`. Take `⟨j, hj, hdvd⟩` from `(Prime.dvd_finset_prod_iff gprime _).1 h`. Establish `hji : j ≠ i` using `Finset.ne_of_mem_erase hj`. Establish `hassoc` using `(irr i).associated_of_dvd (irr j) hdvd`. Establish `heq` using `Polynomial.eq_of_monic_of_associated (mapMonic i) (mapMonic j) hassoc`.

Conclude with `hji (inj (Polynomial.map_injective _ finj heq)).symm`. Establish `key : ∀ q : Λ[X], q.eval₂ φ t ∈ J.colon {e} ↔ g i ∣ q`. Introduce `q`. Rewrite using `[memP, he, ← Polynomial.eval₂_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `hq`. Establish `h1` using `min _ hq i`. Rewrite `h1`, the goal using `[desc]`. Rewrite `h1` using `[Polynomial.map_mul]`. Conclude with `(gprime.dvd_or_dvd h1).resolve_right notdvd`.

Introduce and unpack `⟨a, rfl⟩`. Establish `hre : g i * a * ∏ j ∈ Finset.univ.erase i, g j = a * ∏ j, g j`. Rewrite using `[← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre, Polynomial.eval₂_mul]`.

Conclude with `J.mul_mem_left _ kill`. Establish `nunit : ∀ c : Λ, c ≠ 0 → φ c ∉ J.colon {e}`. Introduce `c hc hmem`. Establish `hC : (Polynomial.C c).eval₂ φ t ∈ J.colon {e}` using `by simpa using hmem`. Rewrite `hC` using `[key]`.

Establish `hdeg` using `Polynomial.natDegree_le_of_dvd hC (Polynomial.C_ne_zero.2 hc)`. Rewrite `hdeg` using `[Polynomial.natDegree_C]`. Establish `h1 : g i = 1` using `Polynomial.eq_one_of_monic_natDegree_zero (monic i) (by omega)`. Apply `(irr i).not_isUnit` to reduce the goal to its premises. Rewrite using `[h1, Polynomial.map_one]`.

Conclude with `isUnit_one`. Establish `scal : ∀ (c : Λ) (a : B), c ≠ 0 → (φ c * a ∈ J.colon {e} ↔ a ∈ J.colon {e})`. Introduce `c a hc`. Rewrite using `[memP, memP, mul_assoc]`. Conclude with `⟨tf c hc _, fun h => J.mul_mem_left _ h⟩`.

Establish `sub : ∀ x y : B, x - y ∈ J → (x ∈ J.colon {e} ↔ y ∈ J.colon {e})`. Introduce `x y hxy`. Rewrite using `[memP, memP]`. Establish `hd : x * e - y * e ∈ J` using `by rw [← sub_mul]; exact J.mul_mem_right _ hxy`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `h2` using `J.sub_mem hx hd`. Simplify using `using h2`. Introduce `hy`. Establish `h2` using `J.add_mem hd hy`.

Simplify using `using h2`. Use `⟨⟨?_, ?_⟩, key, nunit⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one]`. Establish `h1` using `nunit 1 one_ne_zero`. Simplify using `using h1`.

Introduce `a b hab`. Take `⟨c, hc, Pa, ha⟩` from `prim a`. Take `⟨d, hd, Pb, hb⟩` from `prim b`. Establish `hab' : φ (c * d) * (a * b) ∈ J.colon {e}` using `Ideal.mul_mem_left _ _ hab`. Establish `e1 : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t ∈ J`.

Establish `hre : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t = (φ c * a - Pa.eval₂ φ t) * (φ d * b) + Pa.eval₂ φ t * (φ d * b - Pb.eval₂ φ t)`. Rewrite using `[Polynomial.eval₂_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre]`. Conclude with `J.add_mem (J.mul_mem_right _ ha) (J.mul_mem_left _ hb)`.

Rewrite `hab'` using `[sub _ _ e1, key, desc, Polynomial.map_mul]`. Break down `gprime.dvd_or_dvd hab' with h | h` into its components or cases. Use `left`. Rewrite using `[← scal c a hc, sub _ _ ha, key, desc]`. Conclude with `h`.

Use `right`. Rewrite using `[← scal d b hd, sub _ _ hb, key, desc]`. Conclude with `h`.
-/
private theorem cmpPrime_core {Λ B : Type} [CommRing Λ] [IsDomain Λ] [CommRing B] (φ : Λ →+* B)
    (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X])
    (tf : ∀ c : Λ, c ≠ 0 → ∀ a : B, φ c * a ∈ J → a ∈ J)
    (prim : ∀ a : B, ∃ c : Λ, c ≠ 0 ∧ ∃ P : Λ[X], φ c * a - P.eval₂ φ t ∈ J)
    (monic : ∀ i, (g i).Monic)
    (irr : ∀ i, Irreducible ((g i).map (algebraMap Λ (FractionRing Λ))))
    (inj : Function.Injective g)
    (kill : (∏ i, g i).eval₂ φ t ∈ J)
    (min : ∀ q : Λ[X], q.eval₂ φ t ∈ J → ∀ i, g i ∣ q) (i : Fin s) :
    (J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t}).IsPrime ∧
    (∀ q : Λ[X], q.eval₂ φ t ∈ J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t} ↔ g i ∣ q) ∧
    ∀ c : Λ, c ≠ 0 → φ c ∉ J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t} := by
  classical
  have finj : Function.Injective (algebraMap Λ (FractionRing Λ)) := IsFractionRing.injective Λ (FractionRing Λ)
  set e := (∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t with he
  have memP : ∀ a : B, a ∈ J.colon {e} ↔ a * e ∈ J := by
    intro a
    simp [Submodule.mem_colon]
  have gprime : Prime ((g i).map (algebraMap Λ (FractionRing Λ))) := (irr i).prime
  have mapMonic : ∀ j, ((g j).map (algebraMap Λ (FractionRing Λ))).Monic := fun j => (monic j).map _
  have desc : ∀ q : Λ[X], g i ∣ q ↔
      (g i).map (algebraMap Λ (FractionRing Λ)) ∣ q.map (algebraMap Λ (FractionRing Λ)) := fun q =>
    (Polynomial.map_dvd_map (algebraMap Λ (FractionRing Λ)) finj (monic i)).symm
  have notdvd : ¬ (g i).map (algebraMap Λ (FractionRing Λ)) ∣
      (∏ j ∈ Finset.univ.erase i, g j).map (algebraMap Λ (FractionRing Λ)) := by
    rw [Polynomial.map_prod]
    intro h
    obtain ⟨j, hj, hdvd⟩ := (Prime.dvd_finset_prod_iff gprime _).1 h
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hassoc := (irr i).associated_of_dvd (irr j) hdvd
    have heq := Polynomial.eq_of_monic_of_associated (mapMonic i) (mapMonic j) hassoc
    exact hji (inj (Polynomial.map_injective _ finj heq)).symm
  have key : ∀ q : Λ[X], q.eval₂ φ t ∈ J.colon {e} ↔ g i ∣ q := by
    intro q
    rw [memP, he, ← Polynomial.eval₂_mul]
    constructor
    · intro hq
      have h1 := min _ hq i
      rw [desc] at h1 ⊢
      rw [Polynomial.map_mul] at h1
      exact (gprime.dvd_or_dvd h1).resolve_right notdvd
    · rintro ⟨a, rfl⟩
      have hre : g i * a * ∏ j ∈ Finset.univ.erase i, g j = a * ∏ j, g j := by
        rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]
        ring
      rw [hre, Polynomial.eval₂_mul]
      exact J.mul_mem_left _ kill
  have nunit : ∀ c : Λ, c ≠ 0 → φ c ∉ J.colon {e} := by
    intro c hc hmem
    have hC : (Polynomial.C c).eval₂ φ t ∈ J.colon {e} := by simpa using hmem
    rw [key] at hC
    have hdeg := Polynomial.natDegree_le_of_dvd hC (Polynomial.C_ne_zero.2 hc)
    rw [Polynomial.natDegree_C] at hdeg
    have h1 : g i = 1 := Polynomial.eq_one_of_monic_natDegree_zero (monic i) (by omega)
    apply (irr i).not_isUnit
    rw [h1, Polynomial.map_one]
    exact isUnit_one
  have scal : ∀ (c : Λ) (a : B), c ≠ 0 → (φ c * a ∈ J.colon {e} ↔ a ∈ J.colon {e}) := by
    intro c a hc
    rw [memP, memP, mul_assoc]
    exact ⟨tf c hc _, fun h => J.mul_mem_left _ h⟩
  have sub : ∀ x y : B, x - y ∈ J → (x ∈ J.colon {e} ↔ y ∈ J.colon {e}) := by
    intro x y hxy
    rw [memP, memP]
    have hd : x * e - y * e ∈ J := by rw [← sub_mul]; exact J.mul_mem_right _ hxy
    constructor
    · intro hx
      have h2 := J.sub_mem hx hd
      simpa using h2
    · intro hy
      have h2 := J.add_mem hd hy
      simpa using h2
  refine ⟨⟨?_, ?_⟩, key, nunit⟩
  · rw [Ideal.ne_top_iff_one]
    have h1 := nunit 1 one_ne_zero
    simpa using h1
  · intro a b hab
    obtain ⟨c, hc, Pa, ha⟩ := prim a
    obtain ⟨d, hd, Pb, hb⟩ := prim b
    have hab' : φ (c * d) * (a * b) ∈ J.colon {e} := Ideal.mul_mem_left _ _ hab
    have e1 : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t ∈ J := by
      have hre : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t
          = (φ c * a - Pa.eval₂ φ t) * (φ d * b) + Pa.eval₂ φ t * (φ d * b - Pb.eval₂ φ t) := by
        rw [Polynomial.eval₂_mul, map_mul]
        ring
      rw [hre]
      exact J.add_mem (J.mul_mem_right _ ha) (J.mul_mem_left _ hb)
    rw [sub _ _ e1, key, desc, Polynomial.map_mul] at hab'
    rcases gprime.dvd_or_dvd hab' with h | h
    · left
      rw [← scal c a hc, sub _ _ ha, key, desc]
      exact h
    · right
      rw [← scal d b hd, sub _ _ hb, key, desc]
      exact h

/- English proof (translation)
Introduce `O Λ B _ _ _ _ _ _ lam J t s g h i`. Conclude with `cmpPrime_core (lam : Λ →+* B) J t g h.tf h.prim h.monic h.irr h.inj h.kill h.min i`.
-/
theorem cmpPrime : CmpPrime := by
  intro O Λ B _ _ _ _ _ _ lam J t s g h i
  exact cmpPrime_core (lam : Λ →+* B) J t g h.tf h.prim h.monic h.irr h.inj h.kill h.min i

end UpperTheory.V.J
