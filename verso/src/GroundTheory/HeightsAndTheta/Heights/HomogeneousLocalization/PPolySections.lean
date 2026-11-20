import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
  GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra algebraOfOver

noncomputable section

namespace SectionsLatticeFS.PolySections

variable {A : Type u} [CommRing A] {N : ℕ}

/- English proof (translation)
Rewrite using `[← h, Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression.
-/
lemma degree_eq_of_weight {e : Fin (N + 1) →₀ ℕ} {n : ℕ} (h : Finsupp.weight 1 e = n) :
    e.degree = n := by
  rw [← h, Finsupp.degree_eq_weight_one]
  rfl

/- English proof (translation)
Introduce `m hm`. Distinguish the cases in `hr : m ∈ Set.range (expHom N)`. Take `⟨e, rfl⟩` from `hr`. Rewrite `hm` using `[coeff_toLaurent_expHom]`. Use `⟨?_, fun j _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[sum_expHom]`. Conclude with `degree_eq_of_weight ((mem_homogeneousSubmodule n P).mp hP hm)` after adjusting the coercions. Simplify using `[expHom]`. Conclude with `(hm (coeff_toLaurent_eq_zero hr)).elim`.
-/
lemma toLaurent_mem_LDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (s : Set (Fin (N + 1))) : toLaurent A N P ∈ LDeg A s n := by
  intro m hm
  by_cases hr : m ∈ Set.range (expHom N)
  · obtain ⟨e, rfl⟩ := hr
    rw [coeff_toLaurent_expHom] at hm
    refine ⟨?_, fun j _ => ?_⟩
    · rw [sum_expHom]
      exact_mod_cast degree_eq_of_weight ((mem_homogeneousSubmodule n P).mp hP hm)
    · simp [expHom]
  · exact (hm (coeff_toLaurent_eq_zero hr)).elim

/- English proof (translation)
Establish `hnn : ∀ m, ℓ.coeff m ≠ 0 → ∀ i, 0 ≤ m i`. Introduce `m hm i`. Distinguish the cases in `h : ∃ j, j ≠ i`. Take `⟨j, hj⟩` from `h`. Conclude with `(hℓ j m hm).2 i (by simpa [eq_comm] using hj)`.

Use `push Not at h`. Establish `hs : ∑ j, m j = m i` using `Finset.sum_eq_single i (fun j _ hj => absurd (h j) hj) (by simp)`. Use `(hℓ i m hm).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hrange : ∀ m, ℓ.coeff m ≠ 0 → m ∈ Set.range (expHom N)`.

Introduce `m hm`. Use `⟨Finsupp.equivFunOnFinite.symm fun i => (m i).toNat, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[expHom, Int.toNat_of_nonneg (hnn m hm i)]`. Set `S : Finset (Fin (N + 1) →₀ ℕ)` to `ℓ.coeff.support.preimage (expHom N) expHom_injective.injOn`. Set `P : MvPolynomial (Fin (N + 1)) A` to `∑ e ∈ S, monomial e (ℓ.coeff (expHom N e))`.

Establish `hcoeff : ∀ e, P.coeff e = ℓ.coeff (expHom N e)`. Introduce `e`. Simplify using `only [P, coeff_sum, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with he`.

Both sides reduce to the same expression. Simplify using `only [S, Finset.mem_preimage, Finsupp.mem_support_iff, not_not] at he`. Conclude with `he.symm`. Use `⟨P, (mem_homogeneousSubmodule n P).mpr fun e he => ?_, ?_⟩` and prove the remaining obligations. Rewrite `he` using `[hcoeff]`.

Establish `h1` using `(hℓ 0 _ he).1`. Rewrite `h1` using `[sum_expHom]`. Establish `h2 : e.degree = n` using `by exact_mod_cast h1`. Rewrite using `[← h2, Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression.

Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `m`. Distinguish the cases in `hm : m ∈ Set.range (expHom N)`. Take `⟨e, rfl⟩` from `hm`. Rewrite using `[coeff_toLaurent_expHom, hcoeff]`.

Rewrite using `[coeff_toLaurent_eq_zero hm]`. Assume the negation of the conclusion as `h`. Conclude with `hm (hrange m (Ne.symm h))`.
-/
lemma exists_toLaurent_eq {n : ℕ} {ℓ : Laurent A N} (hℓ : ∀ j, ℓ ∈ LDeg A {j} (n : ℤ)) :
    ∃ P ∈ grading A N n, toLaurent A N P = ℓ := by
  classical
  have hnn : ∀ m, ℓ.coeff m ≠ 0 → ∀ i, 0 ≤ m i := by
    intro m hm i
    by_cases h : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := h
      exact (hℓ j m hm).2 i (by simpa [eq_comm] using hj)
    · push Not at h
      have hs : ∑ j, m j = m i :=
        Finset.sum_eq_single i (fun j _ hj => absurd (h j) hj) (by simp)
      have := (hℓ i m hm).1
      omega
  have hrange : ∀ m, ℓ.coeff m ≠ 0 → m ∈ Set.range (expHom N) := by
    intro m hm
    refine ⟨Finsupp.equivFunOnFinite.symm fun i => (m i).toNat, funext fun i => ?_⟩
    simp [expHom, Int.toNat_of_nonneg (hnn m hm i)]
  let S : Finset (Fin (N + 1) →₀ ℕ) :=
    ℓ.coeff.support.preimage (expHom N) expHom_injective.injOn
  let P : MvPolynomial (Fin (N + 1)) A := ∑ e ∈ S, monomial e (ℓ.coeff (expHom N e))
  have hcoeff : ∀ e, P.coeff e = ℓ.coeff (expHom N e) := by
    intro e
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with he
    · rfl
    · simp only [S, Finset.mem_preimage, Finsupp.mem_support_iff, not_not] at he
      exact he.symm
  refine ⟨P, (mem_homogeneousSubmodule n P).mpr fun e he => ?_, ?_⟩
  · rw [hcoeff] at he
    have h1 := (hℓ 0 _ he).1
    rw [sum_expHom] at h1
    have h2 : e.degree = n := by exact_mod_cast h1
    rw [← h2, Finsupp.degree_eq_weight_one]
    rfl
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    by_cases hm : m ∈ Set.range (expHom N)
    · obtain ⟨e, rfl⟩ := hm
      rw [coeff_toLaurent_expHom, hcoeff]
    · rw [coeff_toLaurent_eq_zero hm]
      by_contra h
      exact hm (hrange m (Ne.symm h))

variable (A N) in

def lpoly (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) : Laurent A N :=
  lval (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => 0)

/- English proof (translation)
The claim follows from `(mem_cocycles _).1 (globalCocycle (twistAb A N n) (cover A N) s).2`.
-/
lemma isCocycle (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) :
    d _ _ 0 (globalCocycle (twistAb A N n) (cover A N) s).1 = 0 :=
  (mem_cocycles _).1 (globalCocycle (twistAb A N n) (cover A N) s).2

/- English proof (translation)
Establish `h` using `lval_mem (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => j)`. Rewrite using `[lpoly, lval_eq_of_cocycle _ (isCocycle n s) (fun _ => 0) (fun _ => j)]`. Rewrite `h` using `[range_const_fin_one]`. Then use the resulting hypothesis.
-/
lemma lpoly_mem (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) (j : Fin (N + 1)) :
    lpoly A N n s ∈ LDeg A {j} (n : ℤ) := by
  have h := lval_mem (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => j)
  rw [lpoly, lval_eq_of_cocycle _ (isCocycle n s) (fun _ => 0) (fun _ => j)]
  rwa [range_const_fin_one] at h

/- English proof (translation)
Introduce `s t h`. Apply `globalCocycle_injective (twistAb A N n) (cover A N) (modulesAb (twistingSheaf (grading A N) (n : ℤ))).property iSup_stdOpen` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `cochain_ext` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[lval_eq_of_cocycle _ (isCocycle n s) i (fun _ => 0), lval_eq_of_cocycle _ (isCocycle n t) i (fun _ => 0)]`. Conclude with `h`.
-/
lemma lpoly_injective (n : ℕ) : Function.Injective (lpoly A N n) := by
  intro s t h
  apply globalCocycle_injective (twistAb A N n) (cover A N)
    (modulesAb (twistingSheaf (grading A N) (n : ℤ))).property iSup_stdOpen
  apply Subtype.ext
  apply cochain_ext
  intro i
  rw [lval_eq_of_cocycle _ (isCocycle n s) i (fun _ => 0),
    lval_eq_of_cocycle _ (isCocycle n t) i (fun _ => 0)]
  exact h

/- English proof (translation)
Establish `h` using `ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos 0) (k := (n : ℤ)) (n := 0) (j := n) (a := P) hP (by simp)`. Establish `e : ProjTwist.fpow (xprod (A` using `A) i) 0 = 1 := Subtype.ext (pow_zero _)`. Rewrite `h` using `[e, Localization.mk_one_eq_algebraMap]`. Then use the resulting hypothesis.
-/
lemma algebraMap_mem_awayDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (i : Fin 1 → Fin (N + 1)) :
    algebraMap (MvPolynomial (Fin (N + 1)) A) (Localization.Away (xprod (A := A) i)) P ∈
      ProjTwist.awayDeg (grading A N) (xprod_mem i) (Nat.succ_pos 0) (n : ℤ) := by
  have h := ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos 0) (k := (n : ℤ)) (n := 0) (j := n)
    (a := P) hP (by simp)
  have e : ProjTwist.fpow (xprod (A := A) i) 0 = 1 := Subtype.ext (pow_zero _)
  rwa [e, Localization.mk_one_eq_algebraMap] at h

/- English proof (translation)
Establish `hz : (awayDegEquiv (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)).symm ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ = ⟨_, algebraMap_mem_awayDeg hP _⟩`. Rewrite using `[AddEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[awayDegEquiv_apply, awayToLaurent_algebraMap]`. Establish `key : (globalCocycle (twistAb A N n) (cover A N) (ProjScheme.polySection hP)).1 (fun _ => 0) = theta (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ) ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩`.

Apply `ProjTwist.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Rewrite using `[val_theta, hz]`. Use `Eq.trans ?_ (ProjTwist.locMap_algebraMap (𝒜 := grading A N) x.1 _ P).symm` and prove the remaining obligations. Rewrite using `[← Localization.mk_one_eq_algebraMap]`.

Both sides reduce to the same expression. Rewrite using `[lpoly, lval, key, AddEquiv.symm_apply_apply]`.
-/
lemma lpoly_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n) :
    lpoly A N n (ProjScheme.polySection hP) = toLaurent A N P := by
  have hz : (awayDegEquiv (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)).symm
      ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ = ⟨_, algebraMap_mem_awayDeg hP _⟩ := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [awayDegEquiv_apply, awayToLaurent_algebraMap]
  have key : (globalCocycle (twistAb A N n) (cover A N) (ProjScheme.polySection hP)).1
      (fun _ => 0) = theta (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)
        ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ := by
    apply ProjTwist.ext
    funext x
    rw [val_theta, hz]
    refine Eq.trans ?_ (ProjTwist.locMap_algebraMap (𝒜 := grading A N) x.1 _ P).symm
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  rw [lpoly, lval, key, AddEquiv.symm_apply_apply]

/- English proof (translation)
Apply `ProjTwist.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Conclude with `(Localization.add_mk_self P 1 Q).symm`.
-/
lemma polySection_add {n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (hQ : Q ∈ grading A N n) (hPQ : P + Q ∈ grading A N n) :
    ProjScheme.polySection hPQ = ProjScheme.polySection hP + ProjScheme.polySection hQ := by
  apply ProjTwist.ext
  funext x
  exact (Localization.add_mk_self P 1 Q).symm

/- English proof (translation)
Apply `ProjTwist.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `Localization.mk (a • P) 1 = projValue (grading A N) (algebraMap A Γ(projectiveSpace A N, ⊤) a) x.1 trivial * Localization.mk P 1`. Rewrite using `[projValue_algebraMap, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, smul_eq_C_mul]`.
-/
lemma polySection_smul {n : ℕ} (a : A) {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (haP : a • P ∈ grading A N n) :
    ProjScheme.polySection haP = a • ProjScheme.polySection hP := by
  apply ProjTwist.ext
  funext x
  change Localization.mk (a • P) 1 =
    projValue (grading A N) (algebraMap A Γ(projectiveSpace A N, ⊤) a) x.1 trivial *
      Localization.mk P 1
  rw [projValue_algebraMap, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one,
    smul_eq_C_mul]

/- English proof (translation)
Introduce `A _ N n`. Set `f : grading A N n →ₗ[A] (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)` to `{ toFun := fun P => ProjScheme.polySection P.2 map_add' := fun P Q => polySection_add P.2 Q.2 _ map_smul' := fun a P => polySection_smul a P.2 _ }`. Establish `hinj : Function.Injective f`. Introduce `P Q h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `toLaurent_injective` to reduce the goal to its premises. Rewrite using `[← lpoly_polySection P.2, ← lpoly_polySection Q.2]`. Conclude with `congrArg (lpoly A N n) h`. Establish `hsurj : Function.Surjective f`. Introduce `s`.

Take `⟨P, hP, hPs⟩` from `exists_toLaurent_eq (lpoly_mem n s)`. Conclude with `⟨⟨P, hP⟩, lpoly_injective n (by rw [← hPs]; exact lpoly_polySection hP)⟩`. Conclude with `⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩`.
-/
theorem proof : SectionsLatticeFS.PolySections.Statement.{u} := by
  intro A _ N n
  let f : grading A N n →ₗ[A] (ProjScheme.self A N).H0 (ProjScheme.twistN A N n) :=
    { toFun := fun P => ProjScheme.polySection P.2
      map_add' := fun P Q => polySection_add P.2 Q.2 _
      map_smul' := fun a P => polySection_smul a P.2 _ }
  have hinj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply toLaurent_injective
    rw [← lpoly_polySection P.2, ← lpoly_polySection Q.2]
    exact congrArg (lpoly A N n) h
  have hsurj : Function.Surjective f := by
    intro s
    obtain ⟨P, hP, hPs⟩ := exists_toLaurent_eq (lpoly_mem n s)
    exact ⟨⟨P, hP⟩, lpoly_injective n (by rw [← hPs]; exact lpoly_polySection hP)⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

end SectionsLatticeFS.PolySections

end

end GroundTheory.Heights₂.Heights
