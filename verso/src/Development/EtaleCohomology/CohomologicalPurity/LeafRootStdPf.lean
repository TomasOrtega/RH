import Development.EtaleCohomology.CohomologicalPurity.LeafRootPf
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

/- English proof (translation)
Establish `h` using `modByMonic_add_div f (X - C a)`. Rewrite `h` using `[modByMonic_X_sub_C_eq_C_eval]`. Rewrite using `[add_comm]`. Conclude with `h.symm`.
-/
lemma std_decomp {A : Type} [CommRing A] (f : A[X]) (a : A) :
    f = (X - C a) * (f /ₘ (X - C a)) + C (f.eval a) := by
  have h := modByMonic_add_div f (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  rw [add_comm]; exact h.symm

/- English proof (translation)
Use `conv_lhs => rw [std_decomp f a]`. Simplify using `[Polynomial.map_mul, Polynomial.map_sub]`.
-/
lemma std_eval {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (f : A[X]) (a : A) (c : B) :
    (f.map ψ).eval c = (c - ψ a) * ((f /ₘ (X - C a)).map ψ).eval c + ψ (f.eval a) := by
  conv_lhs => rw [std_decomp f a]
  simp [Polynomial.map_mul, Polynomial.map_sub]

/- English proof (translation)
Establish `h : f.derivative.eval a = (derivative ((X - C a) * (f /ₘ (X - C a)) + C (f.eval a))).eval a` using `congrArg (fun p => (derivative p).eval a) (std_decomp f a)`. Rewrite using `[h]`. Simplify using `[derivative_mul]`.
-/
lemma std_deriv {A : Type} [CommRing A] (f : A[X]) (a : A) :
    f.derivative.eval a = (f /ₘ (X - C a)).eval a := by
  have h : f.derivative.eval a = (derivative ((X - C a) * (f /ₘ (X - C a)) + C (f.eval a))).eval a :=
    congrArg (fun p => (derivative p).eval a) (std_decomp f a)
  rw [h]; simp [derivative_mul]

/- English proof (translation)
Rewrite using `[aeval_def, eval_map]`.
-/
lemma aeval_eq_eval_map {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (p : A[X]) (x : B) :
    aeval x p = (p.map (algebraMap A B)).eval x := by
  rw [aeval_def, eval_map]

/- English proof (translation)
Introduce `A _ I f a hf hfa hu`. Use `set q := f /ₘ (X - C a) with hq`. Set `P : StandardEtalePair A` to `⟨f, hf, f.derivative * q, ⟨q, 0, 1, by ring⟩⟩`. Use `set φ := algebraMap A P.Ring with hφ`. Establish `hX` using `P.hasMap_X`.

Establish `hroot : (f.map φ).eval P.X = 0`. Rewrite using `[← aeval_eq_eval_map]`. Conclude with `hX.1`. Establish `hgunit : IsUnit ((f.derivative.map φ).eval P.X * (q.map φ).eval P.X)`. Establish `h2` using `hX.2`.

Express the relevant statement in the definitionally equal form `IsUnit (aeval P.X (f.derivative * q)) at h2`. Rewrite `h2` using `[map_mul, aeval_eq_eval_map, aeval_eq_eval_map]`. Then use the resulting hypothesis. Establish `hqunit : IsUnit ((q.map φ).eval P.X)` using `isUnit_of_mul_isUnit_right hgunit`. Establish `hba : P.X - φ a ∈ I.map φ`. Establish `e` using `std_eval φ f a P.X`.

Rewrite `e` using `[hroot]`. Establish `e2 : (P.X - φ a) * (q.map φ).eval P.X = -φ (f.eval a)` using `by linear_combination -e`. Take `⟨u, hu'⟩` from `hqunit`. Rewrite `e2` using `[← hu']`. Establish `e3 : P.X - φ a = ((P.X - φ a) * u) * ↑u⁻¹` using `by simp [mul_assoc]`.

Rewrite using `[e3, e2]`. Conclude with `Ideal.mul_mem_right _ _ (neg_mem (Ideal.mem_map_of_mem _ hfa))`. Establish `hmk : ∀ p : A[X], aeval (Ideal.Quotient.mk I a) p = Ideal.Quotient.mk I (p.eval a)`. Introduce `p`. Rewrite using `[← Ideal.Quotient.algebraMap_eq]`.

Conclude with `aeval_algebraMap_apply_eq_algebraMap_eval a p`. Establish `hga : IsUnit (Ideal.Quotient.mk I ((f.derivative * q).eval a))`. Rewrite using `[eval_mul, ← std_deriv, map_mul]`. Conclude with `hu.mul hu`. Establish `hm : P.HasMap (Ideal.Quotient.mk I a)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval _ f = 0`. Rewrite using `[hmk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hfa`. Express the relevant statement in the definitionally equal form `IsUnit (aeval _ (f.derivative * q))`.

Rewrite using `[hmk]`. Conclude with `hga`. Use `⟨P.Ring, inferInstance, φ, P.X, (RingHom.etale_algebraMap).mpr inferInstance, ⟨(P.lift _ hm : P.Ring →+* A ⧸ I), (AlgHom.comp_algebraMap (P.lift _ hm)).trans (Ideal.Quotient.algebraMap_eq I)⟩, ?_, hroot, hba, ?_, ?_⟩` and prove the remaining obligations. Use `set J := I.map φ with hJ`. Set `π` to `Ideal.Quotient.mk J`.

Set `R'` to `(π.comp φ).range`. Establish `hXm : π P.X ∈ R'` using `⟨a, (Ideal.Quotient.eq.mpr hba).symm⟩`. Take `⟨v, hv⟩` from `hga`. Take `⟨u, hu2⟩` from `Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)`. Establish `hgu : ((f.derivative * q).eval a) * u - 1 ∈ I`.

Rewrite using `[← Ideal.Quotient.eq, map_mul, map_one, ← hv, hu2]`. Simplify using the standard rewrite rules. Establish `hgb : π (aeval P.X P.g) = π (φ ((f.derivative * q).eval a))`. Apply `Ideal.Quotient.eq.mpr` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `aeval P.X (f.derivative * q) - _ ∈ J`.

Rewrite using `[aeval_eq_eval_map, ← hφ]`. Establish `hd` using `sub_dvd_eval_sub P.X (φ a) ((f.derivative * q).map φ)`. Establish `hev : ((f.derivative * q).map φ).eval (φ a) = φ ((f.derivative * q).eval a)`. Rewrite using `[eval_map, eval₂_at_apply]`. Rewrite `hd` using `[hev]`.

Take `⟨w, hw⟩` from `hd`. Rewrite using `[hw]`. Conclude with `Ideal.mul_mem_right _ _ hba`. Set `mkP : A[X][X] →+* P.Ring` to `Ideal.Quotient.mk (Ideal.span {C P.f, X * C P.g - 1})`. Establish `hY : π (mkP X) ∈ R'`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `h1 : aeval P.X P.g * mkP X = 1` using `P.aeval_X_g_mul_mk_X`. Establish `e1 : π (aeval P.X P.g) * π (mkP X) = 1` using `by rw [← map_mul, h1, map_one]`. Establish `h3 : π (φ ((f.derivative * q).eval a)) * π (φ u) = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_one π, ← map_one φ]`.

Conclude with `Ideal.Quotient.eq.mpr (by rw [← map_sub]; exact Ideal.mem_map_of_mem _ hgu)`. Express the relevant statement in the definitionally equal form `π (φ u) = _`. Take the linear combination `(-π (φ u)) * e1 + (π (mkP X) * π (φ u)) * hgb + π (mkP X) * h3`. Establish `hin : ∀ c : A[X], π (mkP (C c)) ∈ R'`. Introduce `c`.

Use `Polynomial.induction_on c (fun a0 => ⟨a0, rfl⟩) ?_ ?_` and prove the remaining obligations. Introduce `p1 p2 h1 h2`. Rewrite using `[C_add, map_add, map_add]`. Conclude with `add_mem h1 h2`. Introduce `n a0 ih`.

Rewrite using `[pow_succ, ← mul_assoc, C_mul, map_mul, map_mul]`. Conclude with `mul_mem ih hXm`. Establish `hall : ∀ p : A[X][X], π (mkP p) ∈ R'`. Introduce `p`. Use `Polynomial.induction_on p hin ?_ ?_` and prove the remaining obligations.

Introduce `p1 p2 h1 h2`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem h1 h2`. Introduce `n a0 ih`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, map_mul]`.

Conclude with `mul_mem ih hY`. Introduce `s`. Take `⟨p, rfl⟩ : ∃ p, mkP p = s` from `Ideal.Quotient.mk_surjective s`. Take `⟨a', ha'⟩` from `hall p`. Conclude with `⟨a', Ideal.Quotient.eq.mp ha'.symm⟩`.

Introduce `B _ χ₁ χ₂ h hb`. Use `letI : Algebra A B := (χ₁.comp φ).toAlgebra`. Set `e₁ : P.Ring →ₐ[A] B` to `⟨χ₁, fun _ => rfl⟩`. Set `e₂ : P.Ring →ₐ[A] B` to `⟨χ₂, fun r => (congrArg (fun g : A →+* B => g r) h).symm⟩`. Use `StandardEtalePair.hom_ext (f := e₁) (g := e₂) hb` as an intermediate fact.

Use extensionality with `s`. Conclude with `congrArg (fun e : P.Ring →ₐ[A] B => e s) this`. Introduce `B _ ψ c hc h1 h2`. Use `letI : Algebra A B := ψ.toAlgebra`. Establish `hm' : P.HasMap c`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval c f = 0`. Rewrite using `[aeval_eq_eval_map]`. Conclude with `hc`. Express the relevant statement in the definitionally equal form `IsUnit (aeval c (f.derivative * q))`.

Rewrite using `[map_mul, aeval_eq_eval_map, aeval_eq_eval_map]`. Conclude with `h1.mul h2`. Conclude with `⟨(P.lift c hm' : P.Ring →+* B), AlgHom.comp_algebraMap (P.lift c hm'), P.lift_X c hm'⟩`.
-/
theorem LeafRootStd_of : LeafRootStd := by
  intro A _ I f a hf hfa hu
  set q := f /ₘ (X - C a) with hq
  let P : StandardEtalePair A := ⟨f, hf, f.derivative * q, ⟨q, 0, 1, by ring⟩⟩
  set φ := algebraMap A P.Ring with hφ
  have hX := P.hasMap_X
  have hroot : (f.map φ).eval P.X = 0 := by
    rw [← aeval_eq_eval_map]; exact hX.1
  have hgunit : IsUnit ((f.derivative.map φ).eval P.X * (q.map φ).eval P.X) := by
    have h2 := hX.2
    change IsUnit (aeval P.X (f.derivative * q)) at h2
    rwa [map_mul, aeval_eq_eval_map, aeval_eq_eval_map] at h2
  have hqunit : IsUnit ((q.map φ).eval P.X) := isUnit_of_mul_isUnit_right hgunit
  have hba : P.X - φ a ∈ I.map φ := by
    have e := std_eval φ f a P.X
    rw [hroot] at e
    have e2 : (P.X - φ a) * (q.map φ).eval P.X = -φ (f.eval a) := by linear_combination -e
    obtain ⟨u, hu'⟩ := hqunit
    rw [← hu'] at e2
    have e3 : P.X - φ a = ((P.X - φ a) * u) * ↑u⁻¹ := by simp [mul_assoc]
    rw [e3, e2]
    exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.mem_map_of_mem _ hfa))
  have hmk : ∀ p : A[X], aeval (Ideal.Quotient.mk I a) p = Ideal.Quotient.mk I (p.eval a) := by
    intro p
    rw [← Ideal.Quotient.algebraMap_eq]
    exact aeval_algebraMap_apply_eq_algebraMap_eval a p
  have hga : IsUnit (Ideal.Quotient.mk I ((f.derivative * q).eval a)) := by
    rw [eval_mul, ← std_deriv, map_mul]; exact hu.mul hu
  have hm : P.HasMap (Ideal.Quotient.mk I a) := by
    refine ⟨?_, ?_⟩
    · change aeval _ f = 0
      rw [hmk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    · change IsUnit (aeval _ (f.derivative * q))
      rw [hmk]; exact hga
  refine ⟨P.Ring, inferInstance, φ, P.X, (RingHom.etale_algebraMap).mpr inferInstance,
    ⟨(P.lift _ hm : P.Ring →+* A ⧸ I),
      (AlgHom.comp_algebraMap (P.lift _ hm)).trans (Ideal.Quotient.algebraMap_eq I)⟩,
    ?_, hroot, hba, ?_, ?_⟩
  ·
    set J := I.map φ with hJ
    let π := Ideal.Quotient.mk J
    let R' := (π.comp φ).range
    have hXm : π P.X ∈ R' := ⟨a, (Ideal.Quotient.eq.mpr hba).symm⟩

    obtain ⟨v, hv⟩ := hga
    obtain ⟨u, hu2⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)
    have hgu : ((f.derivative * q).eval a) * u - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, map_one, ← hv, hu2]; simp
    have hgb : π (aeval P.X P.g) = π (φ ((f.derivative * q).eval a)) := by
      apply Ideal.Quotient.eq.mpr
      change aeval P.X (f.derivative * q) - _ ∈ J
      rw [aeval_eq_eval_map, ← hφ]
      have hd := sub_dvd_eval_sub P.X (φ a) ((f.derivative * q).map φ)
      have hev : ((f.derivative * q).map φ).eval (φ a) = φ ((f.derivative * q).eval a) := by
        rw [eval_map, eval₂_at_apply]
      rw [hev] at hd
      obtain ⟨w, hw⟩ := hd
      rw [hw]; exact Ideal.mul_mem_right _ _ hba
    let mkP : A[X][X] →+* P.Ring := Ideal.Quotient.mk (Ideal.span {C P.f, X * C P.g - 1})
    have hY : π (mkP X) ∈ R' := by
      refine ⟨u, ?_⟩
      have h1 : aeval P.X P.g * mkP X = 1 := P.aeval_X_g_mul_mk_X
      have e1 : π (aeval P.X P.g) * π (mkP X) = 1 := by rw [← map_mul, h1, map_one]
      have h3 : π (φ ((f.derivative * q).eval a)) * π (φ u) = 1 := by
        rw [← map_mul, ← map_mul, ← map_one π, ← map_one φ]
        exact Ideal.Quotient.eq.mpr (by rw [← map_sub]; exact Ideal.mem_map_of_mem _ hgu)
      change π (φ u) = _
      linear_combination (-π (φ u)) * e1 + (π (mkP X) * π (φ u)) * hgb + π (mkP X) * h3
    have hin : ∀ c : A[X], π (mkP (C c)) ∈ R' := by
      intro c
      refine Polynomial.induction_on c (fun a0 => ⟨a0, rfl⟩) ?_ ?_
      · intro p1 p2 h1 h2; rw [C_add, map_add, map_add]; exact add_mem h1 h2
      · intro n a0 ih
        rw [pow_succ, ← mul_assoc, C_mul, map_mul, map_mul]; exact mul_mem ih hXm
    have hall : ∀ p : A[X][X], π (mkP p) ∈ R' := by
      intro p
      refine Polynomial.induction_on p hin ?_ ?_
      · intro p1 p2 h1 h2; rw [map_add, map_add]; exact add_mem h1 h2
      · intro n a0 ih
        rw [pow_succ, ← mul_assoc, map_mul, map_mul]; exact mul_mem ih hY
    intro s
    obtain ⟨p, rfl⟩ : ∃ p, mkP p = s := Ideal.Quotient.mk_surjective s
    obtain ⟨a', ha'⟩ := hall p
    exact ⟨a', Ideal.Quotient.eq.mp ha'.symm⟩
  · intro B _ χ₁ χ₂ h hb
    letI : Algebra A B := (χ₁.comp φ).toAlgebra
    let e₁ : P.Ring →ₐ[A] B := ⟨χ₁, fun _ => rfl⟩
    let e₂ : P.Ring →ₐ[A] B := ⟨χ₂, fun r => (congrArg (fun g : A →+* B => g r) h).symm⟩
    have := StandardEtalePair.hom_ext (f := e₁) (g := e₂) hb
    ext s
    exact congrArg (fun e : P.Ring →ₐ[A] B => e s) this
  · intro B _ ψ c hc h1 h2
    letI : Algebra A B := ψ.toAlgebra
    have hm' : P.HasMap c := by
      refine ⟨?_, ?_⟩
      · change aeval c f = 0
        rw [aeval_eq_eval_map]; exact hc
      · change IsUnit (aeval c (f.derivative * q))
        rw [map_mul, aeval_eq_eval_map, aeval_eq_eval_map]; exact h1.mul h2
    exact ⟨(P.lift c hm' : P.Ring →+* B), AlgHom.comp_algebraMap (P.lift c hm'), P.lift_X c hm'⟩

end LateralTheory.CohomologicalPurity.Hz
