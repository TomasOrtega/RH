import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes

open Polynomial Finset

noncomputable section

namespace PI.SqfPrimeFactor.W

/- English proof (translation)
Unfold `monicDeg`. Rewrite using `[Finset.mem_image]`. Use `⟨fun i => q.coeff i, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Substitute `hd` using the available equality. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i) q.natDegree]`.

Conclude with `hq.as_sum.symm`.
-/
lemma irr_mem_monicDeg {g d : ℕ} [Fact g.Prime] {q : (ZMod g)[X]} (hq : q.Monic)
    (hd : q.natDegree = d) : q ∈ monicDeg g d := by
  unfold monicDeg
  rw [Finset.mem_image]
  refine ⟨fun i => q.coeff i, Finset.mem_univ _, ?_⟩
  subst hd
  rw [Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i) q.natDegree]
  exact hq.as_sum.symm

/- English proof (translation)
Introduce `g p _ hp`. Set `_ : Fintype (GaloisField g p)` to `Fintype.ofFinite _`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `hcardK : Fintype.card (GaloisField g p) = g ^ p`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Conclude with `GaloisField.card g p hp0`. Establish `hfin : Module.finrank (ZMod g) (GaloisField g p) = p` using `GaloisField.finrank g hp0`. Establish `hint : ∀ x : GaloisField g p, IsIntegral (ZMod g) x` using `fun x => Algebra.IsIntegral.isIntegral x`. Use `set A := (univ : Finset (GaloisField g p)).filter (fun x => x ∉ (algebraMap (ZMod g) (GaloisField g p)).range) with hA`. Use `set B := (univ : Finset (GaloisField g p)).filter (fun x => x ∈ (algebraMap (ZMod g) (GaloisField g p)).range) with hB`.

Establish `hAB : B.card + A.card = g ^ p`. Rewrite using `[hA, hB, card_filter_add_card_filter_not, card_univ, hcardK]`. Establish `hBle : B.card ≤ g`. Establish `hsub : B ⊆ (univ : Finset (ZMod g)).image (algebraMap (ZMod g) (GaloisField g p))`. Introduce `x hx`.

Rewrite `hx` using `[hB, mem_filter]`. Take `⟨y, rfl⟩` from `hx.2`. Conclude with `mem_image_of_mem _ (mem_univ y)`. Combine the equalities or inequalities in the displayed calculation. Establish `hdegA : ∀ x ∈ A, (minpoly (ZMod g) x).natDegree = p`.

Introduce `x hx`. Rewrite `hx` using `[hA, mem_filter]`. Establish `hdvd` using `minpoly.degree_dvd (hint x)`. Rewrite `hdvd` using `[hfin]`. Break down `(Nat.dvd_prime hp).1 hdvd with h | h` into its components or cases.

Conclude with `absurd (minpoly.natDegree_eq_one_iff.1 h) hx.2`. Conclude with `h`. Establish `himg : A.image (minpoly (ZMod g)) ⊆ irrDeg g p`. Introduce `q hq`. Rewrite `hq` using `[mem_image]`.

Take `⟨x, hx, rfl⟩` from `hq`. Unfold `irrDeg`. Rewrite using `[mem_filter]`. Conclude with `⟨irr_mem_monicDeg (minpoly.monic (hint x)) (hdegA x hx), minpoly.irreducible (hint x)⟩`. Establish `hfib : ∀ q ∈ A.image (minpoly (ZMod g)), (A.filter (fun x => minpoly (ZMod g) x = q)).card ≤ p`.

Introduce `q hq`. Take `⟨x0, hx0, rfl⟩` from `mem_image.1 hq`. Establish `hne : (minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p)) ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero (hint x0))`. Establish `hsub : A.filter (fun x => minpoly (ZMod g) x = minpoly (ZMod g) x0) ⊆ ((minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p))).roots.toFinset`. Introduce `y hy`.

Rewrite `hy` using `[mem_filter]`. Rewrite using `[Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_map_algebraMap, ← hy.2]`. Conclude with `minpoly.aeval _ _`. Combine the equalities or inequalities in the displayed calculation. Establish `hAle : A.card ≤ p * (A.image (minpoly (ZMod g))).card` using `card_le_mul_card_image A p hfib`.

Establish `hAle' : A.card ≤ p * (irrDeg g p).card` using `hAle.trans (Nat.mul_le_mul_left _ (card_le_card himg))`. Establish `hN : g ^ p ≤ p * (irrDeg g p).card + g` using `by omega`. Establish `hR : ((g ^ p : ℕ) : ℝ) ≤ ((p * (irrDeg g p).card + g : ℕ) : ℝ)` using `by exact_mod_cast hN`. Move the coercions through the operations in `at hR`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem irreducible_count_lower_bound : IrrLower := by
  intro g p _ hp
  classical
  let _ : Fintype (GaloisField g p) := Fintype.ofFinite _
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcardK : Fintype.card (GaloisField g p) = g ^ p := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g p hp0
  have hfin : Module.finrank (ZMod g) (GaloisField g p) = p := GaloisField.finrank g hp0
  have hint : ∀ x : GaloisField g p, IsIntegral (ZMod g) x :=
    fun x => Algebra.IsIntegral.isIntegral x
  set A := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∉ (algebraMap (ZMod g) (GaloisField g p)).range) with hA
  set B := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∈ (algebraMap (ZMod g) (GaloisField g p)).range) with hB
  have hAB : B.card + A.card = g ^ p := by
    rw [hA, hB, card_filter_add_card_filter_not, card_univ, hcardK]
  have hBle : B.card ≤ g := by
    have hsub : B ⊆ (univ : Finset (ZMod g)).image (algebraMap (ZMod g) (GaloisField g p)) := by
      intro x hx
      rw [hB, mem_filter] at hx
      obtain ⟨y, rfl⟩ := hx.2
      exact mem_image_of_mem _ (mem_univ y)
    calc B.card ≤ _ := card_le_card hsub
      _ ≤ (univ : Finset (ZMod g)).card := card_image_le
      _ = g := by rw [card_univ, ZMod.card]
  have hdegA : ∀ x ∈ A, (minpoly (ZMod g) x).natDegree = p := by
    intro x hx
    rw [hA, mem_filter] at hx
    have hdvd := minpoly.degree_dvd (hint x)
    rw [hfin] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h) hx.2
    · exact h
  have himg : A.image (minpoly (ZMod g)) ⊆ irrDeg g p := by
    intro q hq
    rw [mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    unfold irrDeg
    rw [mem_filter]
    exact ⟨irr_mem_monicDeg (minpoly.monic (hint x)) (hdegA x hx), minpoly.irreducible (hint x)⟩
  have hfib : ∀ q ∈ A.image (minpoly (ZMod g)),
      (A.filter (fun x => minpoly (ZMod g) x = q)).card ≤ p := by
    intro q hq
    obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hq
    have hne : (minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p)) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (hint x0))
    have hsub : A.filter (fun x => minpoly (ZMod g) x = minpoly (ZMod g) x0) ⊆
        ((minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p))).roots.toFinset := by
      intro y hy
      rw [mem_filter] at hy
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_map_algebraMap, ← hy.2]
      exact minpoly.aeval _ _
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = (minpoly (ZMod g) x0).natDegree := natDegree_map _
      _ = p := hdegA x0 hx0
  have hAle : A.card ≤ p * (A.image (minpoly (ZMod g))).card := card_le_mul_card_image A p hfib
  have hAle' : A.card ≤ p * (irrDeg g p).card :=
    hAle.trans (Nat.mul_le_mul_left _ (card_le_card himg))
  have hN : g ^ p ≤ p * (irrDeg g p).card + g := by omega
  have hR : ((g ^ p : ℕ) : ℝ) ≤ ((p * (irrDeg g p).card + g : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast at hR
  linarith

end PI.SqfPrimeFactor.W
