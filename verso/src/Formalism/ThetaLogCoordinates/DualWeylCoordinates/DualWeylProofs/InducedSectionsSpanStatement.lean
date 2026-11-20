import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhCountAll

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨N, P, hNP⟩` from `IsLocalization.Away.surj (genMat R n).det f`. Establish `hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ)`. Introduce `a`. Establish `h1` using `Int.self_le_toNat (-mu a)`. Establish `h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat` using `Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Use `set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM`. Establish `hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M`. Rewrite using `[rename_rename, Prod.swap_swap_eq, rename_id_apply]`.

Establish `hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) = f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M)`. Rewrite using `[hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]`. Establish `hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) = algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M)`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]`. Use `⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]`. Establish `hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈ inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ))`. Rewrite using `[hmain, mul_comm, ← hunit]`. Establish `h` using `qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf`. Establish `e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu`.

Use function extensionality and compare the values at `a`. Rewrite using `[Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]`. Rewrite using `[e]`. Conclude with `h`. Conclude with `qh_mem_dualWeyl _ _ hmem`.
-/
lemma qh_reduce [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by
  obtain ⟨N, P, hNP⟩ := IsLocalization.Away.surj (genMat R n).det f
  have hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ) := by
    intro a
    have h1 := Int.self_le_toNat (-mu a)
    have h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat :=
      Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)
    push_cast
    omega
  set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM
  have hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M := by
    rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]
  have hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) =
      f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]
  have hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]
  refine ⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩
  · rw [hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · have hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈
        inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) := by
      rw [hmain, mul_comm, ← hunit]
      have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf
      have e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu := by
        funext a
        rw [Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]
      rw [e]
      exact h
    exact qh_mem_dualWeyl _ _ hmem

/- English proof (translation)
Set `L : MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n` to `(LinearMap.mulLeft R u).comp ((IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap.comp (rename Prod.swap).toLinearMap)`. Establish `hle : Submodule.span R S ≤ T.comap L` using `Submodule.span_le.mpr (fun x hx => h x hx)`. Conclude with `hle hQ`.
-/
lemma qh_span_transfer (T : Submodule R (GLCoord R n)) (u : GLCoord R n)
    (S : Set (MvPolynomial (Fin n × Fin n) R))
    (h : ∀ x ∈ S, u * algebraMap _ (GLCoord R n) (rename Prod.swap x) ∈ T)
    (Q : MvPolynomial (Fin n × Fin n) R) (hQ : Q ∈ Submodule.span R S) :
    u * algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ T := by
  let L : MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
    (LinearMap.mulLeft R u).comp ((IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap.comp
      (rename Prod.swap).toLinearMap)
  have hle : Submodule.span R S ≤ T.comap L := Submodule.span_le.mpr (fun x hx => h x hx)
  exact hle hQ

/- English proof (translation)
Introduce `a b hab`. Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`. Simplify using `only [Fin.mk_le_mk] at hab`. Use `revert hb`.

Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base => intro hb`. Conclude with `le_rfl`. Consider the case `succ b hab ih`. Introduce `hb`.

Conclude with `(h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))`.
-/
private theorem antitone_of_step_lemma {n : ℕ} (g : Fin n → ℤ) (h : ∀ l j : Fin n, (j : ℕ) = l + 1 → g j ≤ g l) :
    Antitone g := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))

/- English proof (translation)
Introduce `n _ mu R _ _ _`. Prove the components needed by the constructor for the conclusion. Introduce `hmu`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `f hf`.

Take `⟨k, Q, hk, hfQ, hQ⟩` from `qh_reduce mu f hf`. Rewrite `hQ` using `[Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n]`. Rewrite using `[SetLike.mem_coe, hfQ]`. Use `qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ` and prove the remaining obligations. Introduce and unpack `x ⟨K, sz, hsz, I, hsh, rfl⟩`.

Conclude with `qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))`. Conclude with `qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)`. Introduce `hmu`. Use extensionality with `f`. Simplify using `only [Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hf`. Take `⟨k, Q, hk, hfQ, hQ⟩` from `qh_reduce mu f hf`. Assume the negation of the conclusion as `hf0`. Establish `hQ0 : Q ≠ 0`.

Introduce and unpack `rfl`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[hfQ]`. Simplify using the standard rewrite rules. Apply `hmu` to reduce the goal to its premises.

Establish `hInt` using `Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0`. Establish `hcol` using `Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)`. Use `set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q`. Apply `antitone_of_step_lemma mu` to reduce the goal to its premises. Introduce `l j hlj`.

Establish `hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m` using `hInt l j hlj`. Establish `hI2` using `hI (lastIdx n)`. Establish `e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j)`. Rewrite using `[Finset.filter_true_of_mem (fun b _ => qh_le_last b)]`. Establish `e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l)` using `Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)`.

Establish `cj` using `hcol j`. Establish `cl` using `hcol l`. Establish `tj` using `Int.toNat_of_nonneg (hk j)`. Establish `tl` using `Int.toNat_of_nonneg (hk l)`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `rfl`. Conclude with `qh_zero_mem mu`.
-/
theorem highest_weight_corollary_one : InducedSectionsSpanStatement := by
  intro n _ mu R _ _ _
  constructor
  · intro hmu
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n] at hQ
      rw [SetLike.mem_coe, hfQ]
      refine qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ
      rintro x ⟨K, sz, hsz, I, hsh, rfl⟩
      exact qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))
    · exact qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)
  · intro hmu
    ext f
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      by_contra hf0
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hf0
        rw [hfQ]
        simp
      apply hmu
      have hInt := Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0
      have hcol := Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)
      set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q
      apply antitone_of_step_lemma mu
      intro l j hlj
      have hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m := hInt l j hlj
      have hI2 := hI (lastIdx n)
      have e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j) := by
        rw [Finset.filter_true_of_mem (fun b _ => qh_le_last b)]
      have e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have cj := hcol j
      have cl := hcol l
      have tj := Int.toNat_of_nonneg (hk j)
      have tl := Int.toNat_of_nonneg (hk l)
      omega
    · rintro rfl
      exact qh_zero_mem mu

end Formalism.InvariantFactorPaths.ColumnFamilies
