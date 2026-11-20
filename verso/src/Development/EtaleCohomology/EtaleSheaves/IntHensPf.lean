import Development.EtaleCohomology.EtaleSheaves.IntPBPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.IntHensPf

/- English proof (translation)
Use `choose a ha hag using fun i => (g i).2`. Use `⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `S.val _ = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, smul_eq_mul, ← hag]`. Both sides reduce to the same expression.
-/
theorem mem_sub (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) (S : Subalgebra A B)
    {n : ℕ} (c : Fin n → B) (g : Fin n → (algebraMap A B '' (m : Set A))) (hc : ∀ i, c i ∈ S) :
    ∃ y ∈ m.map (algebraMap A S), (y : B) = ∑ i, c i • (g i : B) := by
  choose a ha hag using fun i => (g i).2
  refine ⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩
  change S.val _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, smul_eq_mul, ← hag]; rfl

/- English proof (translation)
Rewrite using `[Ideal.jacobson, le_sInf_iff]`. Introduce and unpack `n ⟨-, hn⟩`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Establish `: (n.comap (algebraMap A B)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n`. Conclude with `le_of_eq (IsLocalRing.eq_maximalIdeal this).symm`.
-/
theorem jac (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm

/- English proof (translation)
Rewrite using `[eval_map]`. Conclude with `(eval₂_hom S.val.toRingHom y).symm`.
-/
theorem evalS (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Subalgebra A B) (p : S[X]) (y : S) :
    ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := by
  rw [eval_map]; exact (eval₂_hom S.val.toRingHom y).symm

/- English proof (translation)
Use `⟨jac A B, fun f hf a0 h0 h1 => ?_⟩` and prove the remaining obligations. Use `set J := (maximalIdeal A).map (algebraMap A B) with hJ`. Take `⟨n1, c1, g1, hs1⟩` from `Submodule.mem_span_set'.1 h0`. Take `⟨v, hv⟩` from `h1.exists_left_inv`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective v`.

Establish `hu : u * f.derivative.eval a0 - 1 ∈ J`. Rewrite using `[← Ideal.Quotient.eq, map_mul, hv, map_one]`. Take `⟨n2, c2, g2, hs2⟩` from `Submodule.mem_span_set'.1 hu`. Use `set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))`. Set `S` to `Algebra.adjoin A (s : Set B)`.

Establish `hsS : ∀ x ∈ s, x ∈ S` using `fun x hx => Algebra.subset_adjoin hx`. Use `haveI : Module.Finite A S := Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)`. Set `JS` to `(maximalIdeal A).map (algebraMap A S)`. Use `haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)`. Establish `hc : (↑f.coeffs : Set B) ⊆ S.toSubring` using `fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])`.

Set `g : S[X]` to `f.toSubring S.toSubring hc`. Establish `hgf : g.map S.val.toRingHom = f` using `f.map_toSubring S.toSubring hc`. Set `b0 : S` to `⟨a0, hsS a0 (by simp [s])⟩`. Set `uS : S` to `⟨u, hsS u (by simp [s])⟩`. Establish `hgm : g.Monic`.

Rewrite `hf` using `[← hgf]`. Conclude with `Polynomial.monic_of_injective Subtype.val_injective hf`. Establish `h0S : g.eval b0 ∈ JS`. Take `⟨y, hy, hyv⟩` from `mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))`. Use `hy using 1` and compare the differences between its conclusion and the goal.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hyv, hs1, evalS, hgf]`. Establish `h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0))`. Take `⟨y, hy, hyv⟩` from `mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))`. Establish `: uS * g.derivative.eval b0 - 1 ∈ JS`.

Use `hy using 1` and compare the differences between its conclusion and the goal. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hyv, hs2]`. Simplify using `only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]`. Rewrite using `[← derivative_map, hgf]`.

Rewrite `this` using `[← Ideal.Quotient.eq, map_mul, map_one]`. Conclude with `⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩`. Take `⟨a, ha, ha'⟩` from `HenselianRing.is_henselian g hgm b0 h0S h1S`. Use `⟨(a : B), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsRoot.def, ← hgf, ← evalS, ha.eq_zero]`.

Both sides reduce to the same expression. Use `Ideal.mem_map_of_mem S.val.toRingHom ha'` as an intermediate fact. Rewrite `this` using `[Ideal.map_map]`. Simplify using `using this`.
-/
theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Algebra A B]
    [Algebra.IsIntegral A B] : HenselianRing B ((maximalIdeal A).map (algebraMap A B)) := by
  classical
  refine ⟨jac A B, fun f hf a0 h0 h1 => ?_⟩
  set J := (maximalIdeal A).map (algebraMap A B) with hJ
  obtain ⟨n1, c1, g1, hs1⟩ := Submodule.mem_span_set'.1 h0
  obtain ⟨v, hv⟩ := h1.exists_left_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hu : u * f.derivative.eval a0 - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  obtain ⟨n2, c2, g2, hs2⟩ := Submodule.mem_span_set'.1 hu
  set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))
  let S := Algebra.adjoin A (s : Set B)
  have hsS : ∀ x ∈ s, x ∈ S := fun x hx => Algebra.subset_adjoin hx
  haveI : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)
  let JS := (maximalIdeal A).map (algebraMap A S)
  haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, hsS a0 (by simp [s])⟩
  let uS : S := ⟨u, hsS u (by simp [s])⟩
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  have h0S : g.eval b0 ∈ JS := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))
    convert hy using 1
    apply Subtype.ext
    rw [hyv, hs1, evalS, hgf]
  have h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0)) := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))
    have : uS * g.derivative.eval b0 - 1 ∈ JS := by
      convert hy using 1
      apply Subtype.ext
      rw [hyv, hs2]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]
      rw [← derivative_map, hgf]
    rw [← Ideal.Quotient.eq, map_mul, map_one] at this
    exact ⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian g hgm b0 h0S h1S
  refine ⟨(a : B), ?_, ?_⟩
  · rw [IsRoot.def, ← hgf, ← evalS, ha.eq_zero]; rfl
  · have := Ideal.mem_map_of_mem S.val.toRingHom ha'
    rw [Ideal.map_map] at this
    simpa using this

/- English proof (translation)
Introduce `A B _ _ _ φ hφ`. Use `letI : Algebra A B := φ.toAlgebra`. Use `haveI : Algebra.IsIntegral A B := ⟨hφ⟩`. Conclude with `hens A B`.
-/
theorem IntHens_of : LateralTheory.E.IntPBPf.IntHens := by
  intro A B _ _ _ φ hφ
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  exact hens A B

end LateralTheory.E.IntHensPf
