import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IntClosPf

/- English proof (translation)
Set `A'` to `(algebraMap A C).range`. Use `letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra`. Establish `: IsScalarTower A A' C` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hsurj : Function.Surjective (algebraMap A A')` using `(algebraMap A C).rangeRestrict_surjective`. Establish `: Algebra.IsIntegral A A'` using `⟨fun x => by`.

Take `⟨a, rfl⟩` from `hsurj x`. Conclude with `isIntegral_algebraMap⟩`. Use `set p' := p.map (algebraMap A A') with hp'def`. Establish `h1 : Polynomial.aeval z p' = 0` using `by rw [Polynomial.aeval_map_algebraMap]; exact hz`. Establish `hp' : p' ≠ 0`.

Introduce `h0`. Take `⟨n, hn⟩` from `hp`. Apply `hn` to reduce the goal to its premises. Establish `: p'.coeff n = 0` using `by rw [h0]; rfl`. Rewrite `this` using `[hp'def, Polynomial.coeff_map]`.

Use `congrArg Subtype.val this` as an intermediate fact. Conclude with `this`. Establish `hint` using `isIntegral_leadingCoeff_smul p' z h1`. Take `⟨a, ha⟩` from `hsurj p'.leadingCoeff`. Establish `hlc : p'.leadingCoeff ≠ 0` using `Polynomial.leadingCoeff_ne_zero.mpr hp'`.

Establish `hval : algebraMap A C a = (p'.leadingCoeff : C)` using `by rw [← ha]; rfl`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Introduce `h`. Conclude with `hlc (Subtype.ext h)`.

Establish `h2 : algebraMap A C a * z = p'.leadingCoeff • z` using `by rw [Algebra.smul_def, hval]; rfl`. Rewrite using `[h2]`. Conclude with `isIntegral_trans _ hint`.
-/
theorem intMul {A C : Type} [CommRing A] [CommRing C] [IsDomain C] [Algebra A C] (z : C) (p : Polynomial A)
    (hp : ∃ n, algebraMap A C (p.coeff n) ≠ 0) (hz : Polynomial.aeval z p = 0) :
    ∃ a : A, algebraMap A C a ≠ 0 ∧ IsIntegral A (algebraMap A C a * z) := by
  let A' := (algebraMap A C).range
  letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap A A') := (algebraMap A C).rangeRestrict_surjective
  have : Algebra.IsIntegral A A' := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hsurj x
    exact isIntegral_algebraMap⟩
  set p' := p.map (algebraMap A A') with hp'def
  have h1 : Polynomial.aeval z p' = 0 := by rw [Polynomial.aeval_map_algebraMap]; exact hz
  have hp' : p' ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hp
    apply hn
    have : p'.coeff n = 0 := by rw [h0]; rfl
    rw [hp'def, Polynomial.coeff_map] at this
    have := congrArg Subtype.val this
    exact this
  have hint := isIntegral_leadingCoeff_smul p' z h1
  obtain ⟨a, ha⟩ := hsurj p'.leadingCoeff
  have hlc : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hval : algebraMap A C a = (p'.leadingCoeff : C) := by rw [← ha]; rfl
  refine ⟨a, ?_, ?_⟩
  · rw [hval]; intro h; exact hlc (Subtype.ext h)
  · have h2 : algebraMap A C a * z = p'.leadingCoeff • z := by rw [Algebra.smul_def, hval]; rfl
    rw [h2]
    exact isIntegral_trans _ hint

/- English proof (translation)
Introduce `A C c _ hSH hAIC hAR`. Take `⟨hHA, -⟩` from `hSH`. Use `letI : Algebra A C := c.hom.toAlgebra`. Set `B` to `integralClosure A C`. Use `⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Both sides reduce to the same expression. Introduce `x`. Conclude with `integralClosure.isIntegral x`. Conclude with `Subtype.val_injective`.

Establish `hne : Nontrivial B` using `inferInstance`. Take `⟨h⟩` from `hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by`. Break down `(IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h` into its components or cases. Use `left`. Conclude with `Subtype.ext h`.

Use `right`. Conclude with `Subtype.ext h)`. Conclude with `h.toIsLocalRing`. Introduce `p hm hdeg`. Establish `hm' : (p.map B.val.toRingHom).Monic` using `hm.map _`.

Establish `hdeg' : 0 < (p.map B.val.toRingHom).natDegree`. Rewrite using `[Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]`. Conclude with `hdeg`. Take `⟨r, hr⟩` from `hAIC _ hm' hdeg'`. Establish `hrB : IsIntegral B r` using `⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩`.

Establish `hrA : IsIntegral A r` using `isIntegral_trans _ hrB`. Establish `hrM : r ∈ B` using `hrA`. Use `⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩` and prove the remaining obligations. Use `show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0`. Rewrite using `[← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]`.

Conclude with `hr`. Introduce `z`. Establish `hQ : (⊥ : Ideal C).IsPrime` using `Ideal.isPrime_bot`. Take `⟨p, ⟨n, hn⟩, hz⟩` from `hAR ⊥ hQ z`. Take `⟨a, ha, hint⟩` from `intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩ (by rw [Ideal.mem_bot] at hz; exact hz)`.

Use `⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩` and prove the remaining obligations.
-/
theorem IntClos_of (hH : HensInt) : IntClos := by
  intro A C c _ hSH hAIC hAR
  obtain ⟨hHA, -⟩ := hSH
  letI : Algebra A C := c.hom.toAlgebra
  let B := integralClosure A C
  refine ⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; rfl
  · intro x; exact integralClosure.isIntegral x
  · exact Subtype.val_injective
  · have hne : Nontrivial B := inferInstance
    obtain ⟨h⟩ := hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
    exact h.toIsLocalRing
  · intro p hm hdeg
    have hm' : (p.map B.val.toRingHom).Monic := hm.map _
    have hdeg' : 0 < (p.map B.val.toRingHom).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]; exact hdeg
    obtain ⟨r, hr⟩ := hAIC _ hm' hdeg'
    have hrB : IsIntegral B r := ⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩
    have hrA : IsIntegral A r := isIntegral_trans _ hrB
    have hrM : r ∈ B := hrA
    refine ⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩
    show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  · intro z
    have hQ : (⊥ : Ideal C).IsPrime := Ideal.isPrime_bot
    obtain ⟨p, ⟨n, hn⟩, hz⟩ := hAR ⊥ hQ z
    obtain ⟨a, ha, hint⟩ := intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩
      (by rw [Ideal.mem_bot] at hz; exact hz)
    refine ⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩

end LateralTheory.E.IntClosPf
